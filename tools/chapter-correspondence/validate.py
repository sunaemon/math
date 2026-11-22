"""Build and check a registered chapter's complete expression correspondence.

Reports include every formula. A successful exit requires reviewed source and
rules, current Lean evidence, complete typing, and checked operator arguments.
This command never grants or refreshes interpretation approval.
"""

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
import time
from contextlib import ExitStack
from pathlib import Path

import operator_evidence as operators
from lean_export import cached_probes
from lean_probe_cache import Environment, ProbeCache

chapter = operators.chapter


def coverage_findings(formulas, evidence):
    findings = []
    if formulas["reviewStatus"] != "reviewed":
        findings.append("Interpretation review is stale")
    rows = formulas["formulas"]
    if not rows:
        findings.append("No source formulas")
    for row in rows:
        prefix = f"Formula {row['index']}: "
        if row["syntaxStatus"] != "parsed" or row["typeStatus"] != "typechecked":
            findings.append(prefix + "parsing or Lean typing incomplete")
        if any(part["typeStatus"] != "typechecked" for part in row.get("expressionFragments", [])):
            findings.append(prefix + "fragment typing incomplete")
        if any(variable["status"] != "resolved" for variable in row["variables"]):
            findings.append(prefix + "unresolved source variable")
    if any(scope["status"] != "matched" for scope in formulas["scopeContexts"]):
        findings.append("Unresolved proof-local scope")
    if (
        evidence["sourceHash"] != formulas["sourceHash"]
        or evidence["interpretationRulesHash"] != formulas["interpretationRulesHash"]
    ):
        findings.append("Operator evidence does not belong to this formula report")
    if [row["formulaIndex"] for row in evidence["formulas"]] != [row["index"] for row in rows]:
        findings.append("Operator inventory omitted, duplicated, or reordered source formulas")
    for row in evidence["formulas"]:
        prefix = f"Formula {row['formulaIndex']}: "
        if row["unresolved"] or row["untracedOperators"]:
            findings.append(prefix + "unresolved expressions or untraced operators")
        for node in row["nodes"]:
            if (
                node.get("targetStatus") != "matched"
                or node.get("operandStatus") != "matched"
                or node.get("implicitArgumentStatus") not in {"matched", "not-required"}
                or node.get("requirementStatus") not in {"proved", "not-required"}
            ):
                findings.append(prefix + f"unchecked operator at {node['operatorStart']}")
    return findings


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--chapter", default="polish-spaces")
    parser.add_argument("--full", action="store_true", help="Execute every Lean probe without reading cached evidence")
    args = parser.parse_args()
    operators.configure(args.chapter)
    config = chapter.CONFIG
    base = chapter.ROOT / "build/validation"
    base.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix=f"correspondence-{config.name}-", dir=base))
    summary = {"chapter": config.name, "passed": False, "findings": [], "artifacts": {}}
    started = time.monotonic()
    resources = ExitStack()
    probe_cache = None
    print("Correspondence report:", output / "report.json", flush=True)
    try:
        subprocess.run(["make", "build/book-filter"], cwd=chapter.ROOT, check=True)
        subprocess.run(
            ["make", "validate-lean", "LEAN_PROJECTS=" + config.project, "LEAN_MODULES=" + " ".join(config.modules)],
            cwd=chapter.ROOT,
            check=True,
        )
        cache_dir = chapter.ROOT / "build/chapter-correspondence/cache"
        environment = Environment(chapter.ROOT / config.project, cache_dir)
        imports = (*config.modules, "Lean")
        dependencies = environment.snapshot(imports)
        write_json(output / "dependencies.json", dependencies)
        summary["artifacts"]["dependencies"] = "dependencies.json"
        probe_cache = ProbeCache(cache_dir / "probes", dependencies, force=args.full)
        resources.enter_context(cached_probes(probe_cache))
        print(
            f"Dependency environment: {len(dependencies['modules'])} modules; "
            + ("full probe execution" if args.full else "reuse unchanged probes"),
            flush=True,
        )
        text = config.source.read_text()
        if re.search(r"\\(?:vars|infer\w*|assume|signature)\s*\{", text):
            raise ValueError("Migrated chapter still contains legacy sort declarations")
        review_bytes = config.review.read_bytes()
        scopes = chapter.scopes(text)
        records = chapter.evidence(chapter.source_declarations(scopes) | chapter.INTERPRETATION_DECLARATIONS)
        trusted = chapter.review_matches(json.loads(review_bytes), text, records)
        print("Checking all source expressions; interpretation review:", "current" if trusted else "stale", flush=True)
        formulas = chapter.report(text, scopes, records, trusted=trusted)
        write_json(output / "formulas.json", formulas)
        summary["artifacts"]["formulas"] = "formulas.json"
        if not trusted:
            raise ValueError("Source, rules, or Lean evidence changed: interpretation review required")

        def progress(done, total):
            if done % 10 == 0 or done == total:
                print(f"Inspected operators in {done}/{total} formulas", flush=True)

        evidence = operators.inspect_chapter_report(formulas, progress)
        write_json(output / "operators.json", evidence)
        summary["artifacts"]["operators"] = "operators.json"
        summary["findings"] = coverage_findings(formulas, evidence)
        summary["coverage"] = {
            "parsing": formulas["parsing"],
            "variables": formulas["variableResolution"],
            "expressions": formulas["expressionTypes"],
            "interpretationUnits": sum(len(row.get("expressionFragments", [])) or 1 for row in formulas["formulas"]),
            "operators": evidence["summary"],
        }
        # Recheck the live dependencies after the long Lean inspection. Never
        # combine a fresh header with evidence from a changing source tree.
        operators.assert_current_code()
        operators.validate_inventory(formulas)
        if config.review.read_bytes() != review_bytes:
            raise ValueError("Interpretation review changed during validation")
        summary.update(
            sourceHash=formulas["sourceHash"],
            configurationHash=config.fingerprint,
            interpretationRulesHash=chapter.rules_hash(),
            operatorExtractorHash=operators.LOADED_EXTRACTOR_HASH,
            reviewHash=hashlib.sha256(review_bytes).hexdigest(),
        )
        if environment.snapshot(imports)["fingerprint"] != dependencies["fingerprint"]:
            raise ValueError("Lean sources or compiled dependencies changed during validation; discard this run")
        summary["passed"] = not summary["findings"]
    except KeyboardInterrupt:
        summary["findings"].append("Validation interrupted; no complete evidence produced")
    except (ValueError, RuntimeError, OSError, KeyError, subprocess.CalledProcessError) as error:
        summary["findings"].append(str(error))
    finally:
        resources.close()
        if probe_cache is not None:
            summary["cache"] = probe_cache.statistics()
            write_json(output / "probes.json", probe_cache.requests)
            summary["artifacts"]["probes"] = "probes.json"
        summary["elapsedSeconds"] = round(time.monotonic() - started, 2)
        write_json(output / "report.json", summary)
        print(json.dumps(summary, ensure_ascii=False, indent=2), flush=True)
    raise SystemExit(0 if summary["passed"] else 1)


if __name__ == "__main__":
    main()
