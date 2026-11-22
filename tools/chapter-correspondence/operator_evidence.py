"""Elaborated evidence for parser-owned operator nodes; not a semantic proof."""

import copy
import hashlib
import importlib.util
from pathlib import Path

CHECK = Path(__file__).with_name("check.py")
SPEC = importlib.util.spec_from_file_location("chapter_operator_check", CHECK)
chapter = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(chapter)
from notation_rules import EXPECTED_HEADS

LOADED_RULES_HASH = chapter.rules_hash()
LOADED_EXTRACTOR_HASH = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def assert_current_code():
    if (
        chapter.rules_hash() != LOADED_RULES_HASH
        or hashlib.sha256(Path(__file__).read_bytes()).hexdigest() != LOADED_EXTRACTOR_HASH
    ):
        raise ValueError("Correspondence code changed during inspection; discard this run and regenerate the report.")


def header():
    from native import prelude

    return prelude("operatorHeader", chapter.CONFIG.imports(), chapter.CONFIG.opens())


def __getattr__(name):
    from native import prelude

    if name == "HEADER":
        return header()
    if name == "LEAN":
        return prelude("operatorLean")
    raise AttributeError(name)


def configure(name):
    global LOADED_RULES_HASH
    chapter.configure(name)
    LOADED_RULES_HASH = chapter.rules_hash()


def inspect_many(requests):
    """Inspect independent formulas in one Lean process; retain each probe's checks."""
    if chapter.cache_active() and len(requests) > 1:
        return [inspect_many([request])[0] for request in requests]
    probes = [
        prepare_probe(tree, variables, records, "" if i == 0 else f"_{i}")
        for i, (tree, variables, records) in enumerate(requests)
    ]
    if not any(source for _, source in probes):
        return [[] for _ in probes]
    observed = chapter.export(header() + "".join(source for _, source in probes))
    results = [
        check_probe(mappings, observed["operators" + ("" if i == 0 else f"_{i}")]["nodes"], observed) if source else []
        for i, (mappings, source) in enumerate(probes)
    ]

    provenance = chapter.cache_provenance()
    if provenance is not None:
        for nodes in results:
            for node in nodes:
                node["validationOrigin"] = provenance
    return results


def inspect_many_isolated(requests):
    """Keep per-formula errors; bisect only batches that Lean rejects."""
    results = [None] * len(requests)
    ready = []
    for i, request in enumerate(requests):
        try:
            prepare_probe(*request, suffix="")
            ready.append(i)
        except ValueError as error:
            results[i] = error

    def run(indices):
        if not indices:
            return
        try:
            checked = inspect_many([requests[i] for i in indices])
        except ValueError as error:
            if len(indices) == 1:
                results[indices[0]] = error
            else:
                middle = len(indices) // 2
                run(indices[:middle])
                run(indices[middle:])
        else:
            for i, evidence in zip(indices, checked, strict=True):
                results[i] = evidence

    run(ready)
    return results


def inspect(tree, variables, records):
    return inspect_many([(tree, variables, records)])[0]


def prepare_probe(tree, variables, records, suffix):
    # Validate the ordinary candidate first: instrumentation must not let an
    # otherwise ambiguous standalone numeral acquire Lean's default Nat type.
    reference_term, reference_context = chapter.translate(tree, variables, records)
    mappings = []
    term, context = chapter.translate(tree, variables, records, trace=mappings)
    if not mappings:
        return mappings, ""
    from native import operator_probe

    return operator_probe(reference_term, reference_context, term, context, mappings, records, suffix)


def implicit_argument_coverage(elaborated, expectations, checks):
    from native import request

    return request(
        {"action": "implicitCoverage", "elaborated": elaborated, "expectations": expectations, "checks": checks}
    )["coverage"]


def check_probe(mappings, nodes, consumers=None):
    from native import request

    return request(
        {
            "action": "checkOperatorProbe",
            "mappings": mappings,
            "nodes": nodes,
            "consumers": consumers,
            "heads": EXPECTED_HEADS,
        }
    )["mappings"]


def operator_candidates(tree):
    return chapter.native_structure("operatorCandidates", tree)


def merge_operator_call(evidence, mapping):
    """One source operator can lower to several calls; never hide a failed call."""
    key = (mapping["operatorStart"], mapping["operatorEnd"], mapping["rule"])
    if "interpretationId" in mapping:
        key += (mapping["interpretationId"],)
    from native import request

    merged = request({"action": "mergeOperatorCall", "mapping": mapping, "existing": evidence.get(key)})["node"]
    if key in evidence:
        evidence[key].update(merged)
    else:
        evidence[key] = merged


def validate_inventory(report):
    import hashlib

    if report.get("chapter") != chapter.CONFIG.name or report.get("configurationHash") != chapter.CONFIG.fingerprint:
        raise ValueError("Formula inventory belongs to another chapter or configuration")
    if report.get("interpretationRulesHash") != chapter.rules_hash():
        raise ValueError("Formula inventory was generated by different interpretation rules")
    if report["sourceHash"] != hashlib.sha256(chapter.SOURCE.read_bytes()).hexdigest():
        raise ValueError("Formula inventory is stale relative to the Markdown source")
    fresh = chapter.evidence(set(report["leanEvidence"]))
    if any(
        fresh[name][key] != old[key] for name, old in report["leanEvidence"].items() for key in ("signature", "body")
    ):
        raise ValueError("Lean correspondence evidence changed; refresh the formula inventory")


def inspect_formula_report(report, index, *, validated=False, root_evidence=None):
    if not validated:
        validate_inventory(report)
    row = report["formulas"][index]
    plan = chapter.native_structure("inspectionPlan", row["syntax"])
    fragments = plan["fragments"]
    nodes = plan["nodes"]
    fragment_evidence = []
    pending_fragments = []
    for part in fragments or []:
        fragment = {
            **({"interpretationId": part["interpretationId"]} if "interpretationId" in part else {}),
            "start": row["bodyStart"] + part["start"],
            "end": row["bodyStart"] + part["end"],
            "typeStatus": "unresolved",
        }
        fragment_evidence.append(fragment)
        variables = [v for v in row["variables"] if part["start"] <= v["formulaOffset"] < part["end"]]
        try:
            term, context = chapter.translate(part, variables, report["leanEvidence"])
            fragment.update(lean=term, context=context)
            pending_fragments.append(fragment)
        except ValueError as error:
            fragment["typeReason"] = str(error)
    chapter.batch_check(pending_fragments, report["leanEvidence"])
    evidence = {}
    failures = []
    covered = []
    for job in nodes:
        node = job["tree"]
        if "interpretationId" not in node and any(
            start <= node["start"] and node["end"] <= end for start, end in covered
        ):
            continue
        variables = [v for v in row["variables"] if node["start"] <= v["formulaOffset"] < node["end"]]
        try:
            if job["root"] and root_evidence is not None:
                if isinstance(root_evidence, ValueError):
                    raise root_evidence
                mappings = copy.deepcopy(root_evidence)
            else:
                mappings = inspect(node, variables, report["leanEvidence"])
        except ValueError as error:
            failures.append({"start": row["bodyStart"] + node["start"], "reason": str(error)})
            continue
        covered.append((node["start"], node["end"]))
        for mapping in mappings:
            for key in ("start", "end", "operatorStart", "operatorEnd"):
                mapping[key] += row["bodyStart"]
            for operand in mapping["operandSpans"] + mapping.get("bindingComponents", []):
                operand["start"] += row["bodyStart"]
                operand["end"] += row["bodyStart"]
            source = chapter.SOURCE.read_text()
            mapping["sourceExpression"] = source[mapping["start"] : mapping["end"]]
            mapping["sourceOperator"] = source[mapping["operatorStart"] : mapping["operatorEnd"]]
            mapping["line"] = source.count("\n", 0, mapping["operatorStart"]) + 1
            merge_operator_call(evidence, mapping)
    traced_spans = {(m["operatorStart"], m["operatorEnd"]) for m in evidence.values()}
    for mapping in evidence.values():
        traced_spans.update((c["start"], c["end"]) for c in mapping.get("bindingComponents", []))
    untraced = []
    source = chapter.SOURCE.read_text()
    for candidate in plan["operators"]:
        start, end = (row["bodyStart"] + candidate[k] for k in ("start", "end"))
        if (start, end) not in traced_spans:
            untraced.append(
                {
                    "start": start,
                    "end": end,
                    "sourceOperator": source[start:end],
                    **({"notation": candidate["notation"]} if "notation" in candidate else {}),
                }
            )
    return {
        "expressionFragments": fragment_evidence,
        "untracedOperators": untraced,
        "formulaIndex": index,
        "inventoryParentTypeStatus": row["typeStatus"],
        "source": report["source"],
        "offsetConvention": "zero-based Unicode character offsets, half-open",
        "sourceHash": report["sourceHash"],
        "interpretationRulesHash": LOADED_RULES_HASH,
        "extractorHash": LOADED_EXTRACTOR_HASH,
        "nodes": list(evidence.values()),
        "unresolved": failures,
    }


def translation_inventory(report, *, validated=False):
    """Count source occurrences with their actual expression-list/row semantics.

    This checks translation availability only, never kernel or semantic approval.
    """
    if not validated:
        validate_inventory(report)
    formulas = []
    for row in report["formulas"]:
        tree = row.get("syntax")
        units = []
        if tree is None:
            units.append({"status": "unresolved", "reason": "No parsed source expression"})
        else:
            parts = chapter.native_structure("inspectionPlan", tree)["fragments"] or [tree]
            for part in parts:
                unit = {"start": row["bodyStart"] + part["start"], "end": row["bodyStart"] + part["end"]}
                if "interpretationId" in part:
                    unit["interpretationId"] = part["interpretationId"]
                variables = [v for v in row["variables"] if part["start"] <= v["formulaOffset"] < part["end"]]
                try:
                    lean, context = chapter.translate(part, variables, report["leanEvidence"])
                    unit.update(status="translated", lean=lean, context=context)
                except ValueError as error:
                    unit.update(status="unresolved", reason=str(error))
                units.append(unit)
        formulas.append(
            {
                "formulaIndex": row["index"],
                "units": units,
                "status": "translated" if all(u["status"] == "translated" for u in units) else "unresolved",
            }
        )
    return {
        "sourceHash": report["sourceHash"],
        "interpretationRulesHash": LOADED_RULES_HASH,
        "formulas": formulas,
        "summary": {
            "formulaCount": len(formulas),
            "unitCount": sum(len(f["units"]) for f in formulas),
            "translatableFormulas": sum(f["status"] == "translated" for f in formulas),
            "unresolvedFormulas": sum(f["status"] == "unresolved" for f in formulas),
        },
        "meaning": "Translation candidates only; not kernel validation or semantic approval.",
    }


def inspect_chapter_report(report, progress=None):
    """Keep every formula, including failures and formulas with no traced nodes."""
    from collections import Counter

    validate_inventory(report)
    formulas = []
    for start in range(0, len(report["formulas"]), 8):
        indices = range(start, min(start + 8, len(report["formulas"])))
        candidates = [
            i
            for i in indices
            if report["formulas"][i].get("syntax") is not None
            and not chapter.native_structure("inspectionPlan", report["formulas"][i]["syntax"])["fragments"]
        ]
        requests = [
            (report["formulas"][i]["syntax"], report["formulas"][i]["variables"], report["leanEvidence"])
            for i in candidates
        ]
        cached = dict(zip(candidates, inspect_many_isolated(requests), strict=True))
        for index in indices:
            kwargs = {"root_evidence": cached[index]} if index in cached else {}
            formulas.append(inspect_formula_report(report, index, validated=True, **kwargs))
            if progress is not None:
                progress(index + 1, len(report["formulas"]))
    nodes = [node for row in formulas for node in row["nodes"]]
    return {
        "source": report["source"],
        "sourceHash": report["sourceHash"],
        "interpretationRulesHash": LOADED_RULES_HASH,
        "summary": {
            "formulas": len(formulas),
            "formulasWithTraces": sum(bool(row["nodes"]) for row in formulas),
            "tracedOperators": len(nodes),
            "elaboratedCalls": sum(len(node.get("calls", [node])) for node in nodes),
            "targetStatuses": dict(Counter(node["targetStatus"] for node in nodes)),
            "operandStatuses": dict(Counter(node.get("operandStatus", "unreviewed") for node in nodes)),
            "implicitArgumentStatuses": dict(
                Counter(node.get("implicitArgumentStatus", "unreviewed") for node in nodes)
            ),
            "untracedKnownOperators": sum(len(row["untracedOperators"]) for row in formulas),
            "requirementStatuses": dict(Counter(node.get("requirementStatus", "not-required") for node in nodes)),
            "unresolvedSubexpressions": sum(len(row["unresolved"]) for row in formulas),
            "rules": dict(Counter(node["rule"] for node in nodes)),
        },
        "formulas": formulas,
    }


def main():
    import argparse
    import json

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--chapter", default="polish-spaces")
    parser.add_argument("--report", type=Path, required=True)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--formula-index", type=int)
    selection.add_argument("--all", action="store_true")
    selection.add_argument("--translation-inventory", action="store_true")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    configure(args.chapter)
    report = json.loads(args.report.read_text())
    if args.translation_inventory:
        result = translation_inventory(report)
    elif args.all:

        def progress(done, total):
            if done % 10 == 0 or done == total:
                print(f"Inspected {done}/{total} formulas", flush=True)

        result = inspect_chapter_report(report, progress)
    else:
        result = inspect_formula_report(report, args.formula_index)
    if not args.translation_inventory:
        result["meaning"] = "Observed elaborated calls for selected parser nodes; not semantic or proof approval."
    assert_current_code()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    if args.all or args.translation_inventory:
        print(json.dumps(result["summary"], ensure_ascii=False))
    else:
        print(f"{len(result['nodes'])} traced nodes; {len(result['unresolved'])} unresolved subexpressions")


if __name__ == "__main__":
    main()
