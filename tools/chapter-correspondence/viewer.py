"""Read-only viewer projection of a validated chapter and the actual native AST.

No Lean checking or interpretation approval is performed here. Stale snapshots
retain their historical evidence but never receive a current semantic AST.
"""

import argparse
import hashlib
import json
from pathlib import Path

import check as chapter
from chapter_config import REGISTRY, load_chapter


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def latest_snapshot(root, source):
    paths = sorted(
        (root / "build/validation").glob("correspondence-*/report.json"),
        key=lambda path: path.stat().st_mtime_ns,
        reverse=True,
    )
    for path in paths:
        try:
            report = json.loads(path.read_text())
            formulas = json.loads(path.with_name("formulas.json").read_text())
            if formulas.get("source") == source:
                return path.stat().st_mtime_ns, path, report, formulas
        except (OSError, ValueError):
            continue
    return None


def read_artifact(path):
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return {}


def compact_operator(node):
    keys = (
        "start",
        "end",
        "operatorStart",
        "operatorEnd",
        "line",
        "rule",
        "sourceExpression",
        "sourceOperator",
        "sourceAmbient",
        "sourceRestriction",
        "lowering",
        "expectedHead",
        "targetStatus",
        "operandStatus",
        "implicitArgumentStatus",
        "requirementStatus",
        "expectedOperands",
        "expectedImplicitArguments",
        "operandSpans",
        "bindingComponents",
        "semanticRequirements",
        "implicitArgumentCoverage",
    )
    result = {key: node[key] for key in keys if key in node}
    result["calls"] = []
    for call in node.get("calls", [node]):
        elaborated = call.get("elaborated", {})
        result["calls"].append(
            {
                "head": elaborated.get("head"),
                "expression": elaborated.get("expression"),
                "arguments": [
                    {key: argument.get(key) for key in ("parameter", "value", "type", "implicit", "instance")}
                    for argument in elaborated.get("arguments", [])
                ],
                "targetStatus": call.get("targetStatus"),
                "operandStatus": call.get("operandStatus"),
                "implicitArgumentStatus": call.get("implicitArgumentStatus"),
                "requirementStatus": call.get("requirementStatus"),
            }
        )
    return result


def viewer_report(source, *, include_ast=True):
    root = chapter.ROOT
    requested = root / source
    if Path(source).is_absolute() or not requested.resolve().is_relative_to(root):
        raise ValueError("Source must be inside the repository")
    config = next(
        (
            config
            for path in sorted(REGISTRY.glob("*.json"))
            if (config := load_chapter(path.stem)).source.resolve() == requested.resolve()
        ),
        None,
    )
    if config is None:
        return {"status": "unavailable", "reason": "unregistered-source", "source": source, "formulas": []}
    chapter.configure(config.name)
    canonical = str(config.source.relative_to(root))
    snapshot = latest_snapshot(root, canonical)
    if snapshot is None:
        return {"status": "unavailable", "reason": "no-validation", "source": canonical, "formulas": []}
    _, path, report, formulas = snapshot
    operators = read_artifact(path.with_name("operators.json"))
    dependencies = read_artifact(path.with_name("dependencies.json"))
    reasons = []
    if formulas.get("sourceHash") != digest(config.source):
        reasons.append("source-changed")
    if formulas.get("interpretationRulesHash") != chapter.rules_hash():
        reasons.append("rules-changed")
    if report.get("configurationHash") != config.fingerprint:
        reasons.append("configuration-changed")
    if report.get("reviewHash") != digest(config.review):
        reasons.append("review-changed")
    if not report.get("passed"):
        reasons.append("validation-failed")
    if (operators.get("sourceHash"), operators.get("interpretationRulesHash")) != (
        formulas.get("sourceHash"),
        formulas.get("interpretationRulesHash"),
    ):
        reasons.append("inconsistent-reports")
    # Reuse the cache's content hashing, including source files and compiled
    # dependencies. This does not start Lean or download/build dependencies.
    from lean_probe_cache import Environment

    environment = Environment(root / config.project, root / "build/chapter-correspondence/cache")
    current = environment.snapshot((*config.modules, "Lean")) if not reasons else None
    if current is not None and current["fingerprint"] != dependencies.get("fingerprint"):
        reasons.append("lean-changed")
    rows = [dict(row, operators=[]) for row in formulas["formulas"]]
    by_index = {row["index"]: row for row in rows}
    for row in operators.get("formulas", []):
        by_index[row["formulaIndex"]]["operators"] = [compact_operator(node) for node in row["nodes"]]
    if not reasons and include_ast:
        text = config.source.read_text()
        anchors = chapter.request({"action": "formulaAnchors", "source": canonical, "text": text})["formulas"]
        for row, anchor in zip(rows, anchors, strict=True):
            if row["bodyStart"] != anchor["bodyStart"]:
                raise ValueError("Formula anchor source positions disagree")
            row["pdfTag"] = anchor["pdfTag"]
        prepared = chapter.analyze_chapter(
            text,
            chapter.scopes(text),
            formulas["leanEvidence"],
            constants=chapter.CONSTANTS,
            conventions=chapter.CONVENTIONS,
            include_ast=True,
        )
        for job, result in zip(prepared["expressions"], prepared["translations"], strict=True):
            row = by_index[job["formulaIndex"]]
            expected = row if job["fragmentIndex"] is None else row["expressionFragments"][job["fragmentIndex"]]
            if not result["supported"] or (result["rendering"]["ordinary"], result.get("context")) != (
                expected.get("lean"),
                expected.get("context"),
            ):
                reasons.append("interpretation-mismatch")
            row.setdefault("semanticExpressions", []).append(
                {
                    "fragmentIndex": job["fragmentIndex"],
                    "supported": result["supported"],
                    "ast": result.get("semanticAST"),
                    "reason": result.get("reason"),
                }
            )
        if reasons or (
            digest(config.source) != formulas["sourceHash"]
            or chapter.rules_hash() != formulas["interpretationRulesHash"]
            or digest(config.review) != report["reviewHash"]
            or environment.snapshot((*config.modules, "Lean"))["fingerprint"] != current["fingerprint"]
        ):
            reasons.append("changed-during-inspection")
            for row in rows:
                row.pop("semanticExpressions", None)
    return {
        "schemaVersion": 1,
        "status": "stale" if reasons else "current",
        "reasons": reasons,
        "source": canonical,
        "requestedSource": source,
        "chapter": config.name,
        "report": str(path.relative_to(root)),
        "sourceHash": formulas["sourceHash"],
        "offsetConvention": formulas["offsetConvention"],
        "coverage": report.get("coverage"),
        "formulas": rows,
        # Consumed and removed by the live server; never sent to the browser.
        # These include the exact Lean source/compiled dependency files whose
        # contents were checked above, plus chapter-specific source evidence.
        "_cacheInputs": [
            str(config.source),
            str(config.review),
            str(REGISTRY / (config.name + ".json")),
            *dependencies.get("files", {}),
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True)
    parser.add_argument("--lean-source", action="store_true")
    args = parser.parse_args()
    if args.lean_source:
        from lean_locations import lean_locations

        report = lean_locations(args.source)
    else:
        report = viewer_report(args.source)
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    main()
