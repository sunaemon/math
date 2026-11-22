#!/usr/bin/env python3
"""Bounded book/Lean correspondence experiment; no general prose type checker."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PILOT = ROOT / "tools/sort-pilot"

sys.path.insert(0, str(PILOT))
from formula_types import classify
from formula_types import self_test as formula_self_test
from lean_export import (
    export,
    parse_export_result,  # compatibility for existing clients
)
from sort_coverage import check_coverage, render_report
from source_bindings import resolve

__all__ = ["export", "parse_export_result"]

PREFIX = "PolishSpaceBook.LambdaIndexPCA."
BRIDGE = {
    "Nat": "Nat",
    "Name": "Name",
    "Carrier": "Set(Point)",  # Explicit book-set / Lean-carrier convention in this passage only.
    "CarrierElement": "Point",
    "Representation": "PartialFun(Name,Point)",
    "Assembly": "Assembly(Point)",
}


def digest(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def passage(text: str, manifest: dict | None = None) -> str:
    if manifest and "startAnchor" in manifest:
        start, end = manifest["startAnchor"], manifest["endAnchor"]
        if text.count(start) != 1 or text.count(end) != 1:
            raise ValueError("source anchors missing or ambiguous")
        a = text.index(start)
        b = text.index(end, a)
        return text[a:b]

    anchor = "For a representation $\\delta$ of $X$, let $A_\\delta$ have underlying set"
    if text.count(anchor) != 1:
        raise ValueError("source anchor missing or ambiguous")
    pos = text.index(anchor)
    start = text.rfind("\\begin{mathmeta}", 0, pos)
    end = text.index("\\end{mathmeta}", text.index("\\scopeend", pos)) + len("\\end{mathmeta}")
    return text[start:end]


def fingerprint(record: dict) -> str:
    return digest(record["signature"] + "\n" + record["body"])


def check(manifest: dict, text: str, records: dict) -> list[dict]:
    findings = []

    def issue(kind: str, detail: str) -> None:
        findings.append({"kind": kind, "detail": detail})

    try:
        manifest = resolve(manifest, text, records)
        selected = passage(text, manifest)
    except (ValueError, TypeError) as error:
        return [{"kind": "unresolved-source", "detail": str(error)}]
    if manifest.get("sourceScope") and manifest["actualAnnotationHash"] != manifest["annotationHash"]:
        issue("stale-annotation", "The reviewed source-to-Lean mapping changed; review the new target.")
    if digest(selected) != manifest["sourceHash"]:
        issue("stale-source", "The reviewed passage changed; correspondence needs review.")
    for name, expected in manifest["leanFingerprints"].items():
        if name not in records:
            issue("unresolved-lean", name)
        elif fingerprint(records[name]) != expected:
            issue("stale-lean", name)
    declarations = dict(re.findall(r"\\vars\{([^{}]+)\}\{([^{}]+)\}", selected))
    for binding in manifest["bindings"]:
        symbol, name, slot = binding["symbol"], binding["declaration"], binding["slot"]
        record = records.get(name)
        if record is None:
            issue("unresolved-lean", symbol)
            continue
        if "leanType" in binding:
            if binding.get("occurrence", symbol) not in selected:
                issue("missing-occurrence", symbol)
            if slot == "result":
                actual = record["result"]
            elif isinstance(slot, int) and 0 <= slot < len(record["binders"]):
                actual = record["binders"][slot]["type"]
            else:
                issue("unresolved-binder", symbol)
                continue
            if actual != binding["leanType"]:
                issue("binding-type-mismatch", f"{symbol}: expected {binding['leanType']}, got {actual}")
            continue
        if slot == "result":
            shape = record["resultShape"]
        elif isinstance(slot, int) and 0 <= slot < len(record["binders"]):
            shape = record["binders"][slot]["shape"]
        else:
            issue("unresolved-binder", symbol)
            continue
        expected = BRIDGE.get(shape)
        if expected is None:
            issue("unsupported-shape", symbol)
        elif symbol not in declarations:
            issue("missing-declaration", symbol)
        elif declarations[symbol] != expected:
            issue("sort-mismatch", f"{symbol}: book {declarations[symbol]}, Lean projection {expected}")
    for expression in manifest.get("expressions", []):
        if expression["book"] not in selected:
            issue("missing-expression", expression["book"])
        if expression["lean"] not in records:
            issue("unresolved-expression", expression["lean"])
    coverage_findings, _ = check_coverage(manifest, selected, text, records)
    return findings + coverage_findings


def extended_self_test(manifests: list[dict], records: dict, source: str) -> dict:
    results = {}
    for manifest in manifests:
        if manifest.get("sourceScope"):
            continue
        text = (ROOT / manifest["source"]).read_text()
        changed = copy.deepcopy(manifest)
        first = changed["bindings"][0]
        first["slot"] = manifest["badSlot"]
        if "binding-type-mismatch" not in {f["kind"] for f in check(changed, text, records)}:
            raise ValueError(f"binder mutation not detected: {manifest['id']}")
        results[manifest["id"] + "_wrong_binder"] = "binding-type-mismatch"
    forcing = next(m for m in manifests if m["id"] == "forcing")
    text = (ROOT / forcing["source"]).read_text()
    for label, change, kind in [
        ("missing_formula", lambda m: m["expressions"].pop(), "formula-coverage"),
        ("missing_assumption", lambda m: m["coverage"]["assumptions"].pop(), "assumption-coverage"),
        ("missing_argument", lambda m: m["coverage"]["boundArguments"].pop(), "argument-coverage"),
    ]:
        changed = copy.deepcopy(forcing)
        change(changed)
        if kind not in {f["kind"] for f in check(changed, text, records)}:
            raise ValueError(f"coverage mutation not detected: {label}")
        results[label] = kind
    for label, changed_text, kind in [
        (
            "out_of_scope_occurrence",
            text.replace(
                "<!-- lean-correspondence-end: ordinal-preservation -->",
                "<!-- lean-correspondence-end: ordinal-preservation --> $M$",
            ),
            "unresolved-source",
        ),
        (
            "nested_scope",
            text.replace(
                "\\begin{proposition*}[Ordinal preservation]",
                '<!-- lean-correspondence {"scope":"nested","lean":{},"bindings":{}} -->\\begin{proposition*}[Ordinal preservation]',
            ),
            "unresolved-source",
        ),
        ("unknown_binder", text.replace('"bound.τ"', '"bound.missing"'), "unresolved-source"),
        ("same_type_retarget_requires_review", text.replace('"bound.τ"', '"bound.α"'), "stale-annotation"),
        ("duplicate_symbol", text.replace('["M", "statement.M"]', '["P", "statement.M"]'), "unresolved-source"),
        (
            "missing_scope_end",
            text.replace("lean-correspondence-end: ordinal-preservation", "lean-correspondence-end: absent"),
            "unresolved-source",
        ),
        ("unmapped_variable", text.replace('"M", "statement.M"', '"N", "statement.M"'), "variable-coverage"),
        ("duplicate_identity", text.replace('"rank-bound":', '"name":'), "unresolved-source"),
    ]:
        if kind not in {f["kind"] for f in check(forcing, changed_text, records)}:
            raise ValueError(f"source annotation mutation not detected: {label}")
        results[label] = kind
    # Position changes alone are harmless: names are resolved against fresh Lean binders.
    reordered = copy.deepcopy(records)
    declaration = "PolishSpaceBook.SetTheoryModels.ordinal_mem_extension_iff_of_axioms"
    reordered[declaration]["binders"].reverse()
    rebound = resolve(forcing, text, reordered)
    ground = next(b for b in rebound["bindings"] if b["symbol"] == "M")
    if ground["slot"] != len(reordered[declaration]["binders"]) - 1:
        raise ValueError("binder positions were not derived by name")
    results["derive_position_by_name"] = "resolved after position change"
    changed_text = text.replace(r"\alpha=\beta", r"\alpha=\gamma")
    if "unsupported-token" not in {f["kind"] for f in check(forcing, changed_text, records)}:
        raise ValueError("new variable not detected independently of source hash")
    results["new_variable"] = "unsupported-token"
    # Genuine Lean expression errors, not just stale-source hashes.
    for label, before, after in [
        ("word_graph_is_not_numeric_code", "pair (wordAsSet s) (natOrdinal n)", "pair (wordCode s) (natOrdinal n)"),
        ("chain_child_is_not_word", "chainWord q n ++ [chainChild q n]", "chainWord q n ++ [chainWord q n]"),
        ("rank_requires_set_conversion", "τ.rank.toZFSet", "τ.rank"),
    ]:
        try:
            export(source.replace(before, after))
        except ValueError as error:
            if "Lean adapter/export failed" not in str(error) or not any(
                marker in str(error).lower() for marker in ("type mismatch", "happend (list ℕ)")
            ):
                raise
            results[label] = "Lean type mismatch"
        else:
            raise ValueError(f"Lean accepted mutation: {label}")
    try:
        export(source.replace("let β := τ.rank.toZFSet", "let β := α"))
    except ValueError as error:
        if "Lean adapter/export failed" not in str(error):
            raise
        results["wrong_rank_witness_same_type"] = "Lean proof rejected"
    else:
        raise ValueError("Lean accepted arbitrary alpha as rank witness")
    return results


def self_test(manifest: dict, text: str, records: dict, source: str) -> dict:
    results = {}

    def expect(label: str, findings: list[dict], kind: str) -> None:
        if kind not in {item["kind"] for item in findings}:
            raise ValueError(f"mutation was not detected: {label}")
        results[label] = kind

    swapped = copy.deepcopy(manifest)
    for binding in swapped["bindings"]:
        if binding["symbol"] in {"e", "p"}:
            binding["slot"] = 1 - binding["slot"]
    expect("swap_index_and_name_binders", check(swapped, text, records), "sort-mismatch")
    expect(
        "change_book_variable", check(manifest, text.replace(r"\delta(p)=x", r"\delta(e)=x"), records), "stale-source"
    )
    expect(
        "remove_book_declaration", check(manifest, text.replace(r"\vars{e}{Nat}", ""), records), "missing-declaration"
    )
    missing = dict(records)
    del missing[PREFIX + "ComputesName"]
    expect("missing_lean_evidence", check(manifest, text, missing), "unresolved-lean")
    altered = source.replace(
        "run_cmd liftTermElabM do",
        "def PilotChanged (_extra : True) (e : ℕ) (p : ℕ → ℕ) : Prop := ComputesName e p\n\nrun_cmd liftTermElabM do",
    ).replace("[``ComputesName,", "[``PilotChanged,")
    changed = export(altered)
    changed[PREFIX + "ComputesName"] = changed.pop("PilotChanged")
    expect("extra_lean_hypothesis", check(manifest, text, changed), "stale-lean")
    # A weaker interpretation must fail in Lean, even though the variable types agree.
    try:
        export(source.replace("ComputesName e p ↔ ∀ n,", "ComputesName e p ↔ ∃ n,"))
    except ValueError as error:
        if "Lean adapter/export failed" not in str(error):
            raise
        results["replace_totality_with_one_input"] = "Lean rejection"
    else:
        raise ValueError("Lean accepted the weakened computation adapter")
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    # Fresh imports are mandatory; no skip-build switch that could bless stale oleans.
    subprocess.run(
        [
            "make",
            "validate-lean",
            "LEAN_PROJECTS=polish-space",
            (
                "LEAN_MODULES=PolishSpaceBook.LambdaComputablePointAssemblies "
                "PolishSpaceBook.ForcingOrdinalPreservation PolishSpaceBook.SetTheoryInternalListCodes "
                "PolishSpaceBook.LambdaBorelSyntax"
            ),
        ],
        cwd=ROOT,
        check=True,
    )
    manifest = json.loads((PILOT / "assembly.json").read_text())
    text = (ROOT / manifest["source"]).read_text()
    source = (PILOT / "Export.lean").read_text()
    records = export(source)
    findings = check(manifest, text, records)
    report = {
        "passed": not findings,
        "mappedVariables": len(manifest["bindings"]),
        "findings": findings,
        "evidence": records,
    }
    if args.self_test and not findings:
        report["mutationChecks"] = self_test(manifest, text, records, source)
    extended_source = (PILOT / "Correspondences.lean").read_text()
    extended_records = export(extended_source)
    manifests = [json.loads(path.read_text()) for path in sorted(PILOT.glob("case-*.json"))]
    report["cases"] = []
    for case in manifests:
        case_text = (ROOT / case["source"]).read_text()
        case_findings = check(case, case_text, extended_records)
        try:
            resolved_case = resolve(case, case_text, extended_records)
        except (ValueError, TypeError):
            resolved_case = dict(case, bindings=[])

        report["cases"].append(
            {
                "id": case["id"],
                "mappedVariables": len(resolved_case["bindings"]),
                "bindings": resolved_case["bindings"],
                "mappedExpressions": len(case["expressions"]),
                "findings": case_findings,
            }
        )
        if case.get("coverage") and resolved_case["bindings"]:
            formula_report = classify(
                resolved_case, passage(case_text, case), case_text, export, trusted=not case_findings
            )
            report["cases"][-1]["formulaTypes"] = formula_report
            if args.self_test and not case_findings:
                report["formulaTypeChecks"] = formula_self_test(
                    resolved_case, passage(case_text, case), case_text, export
                )

            output = ROOT / "build/sort-pilot/forcing.html"
            output.parent.mkdir(parents=True, exist_ok=True)
            report["cases"][-1]["coverage"] = render_report(
                resolved_case,
                (ROOT / case["source"]).read_text(),
                passage((ROOT / case["source"]).read_text(), case),
                extended_records,
                case_findings,
                output,
                formula_report,
            )
        elif case.get("coverage"):
            output = ROOT / "build/sort-pilot/forcing.html"
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(
                "<!doctype html><meta charset='utf-8'><h1>FAIL</h1><p>Source bindings could not be resolved. See report.json for diagnostics.</p>"
            )
        findings.extend(case_findings)
    report["passed"] = not findings
    report["reverseBindings"] = {}
    for case in report["cases"]:
        for binding in case["bindings"]:
            if "id" in binding:
                key = binding["declaration"] + "/" + binding["leanName"]
                report["reverseBindings"].setdefault(key, []).append(
                    {"id": binding["id"], "source": next(m["source"] for m in manifests if m["id"] == case["id"])}
                )
    report["extendedEvidence"] = extended_records
    if args.self_test and not findings:
        report["extendedMutationChecks"] = extended_self_test(manifests, extended_records, extended_source)
    destination = ROOT / "build/sort-pilot/report.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(
        f"{'PASS' if not findings else 'FAIL'}: sort pilot; {len(manifest['bindings'])} explicit bindings; {len(findings)} findings"
    )
    print(f"Additional cases: {len(manifests)}; expressions: {sum(len(c['expressions']) for c in manifests)}")
    for case in report["cases"]:
        if "formulaTypes" in case:
            counts = case["formulaTypes"]
            print(
                f"Formula types ({case['id']}): {counts['typechecked']}/{counts['total']} checked; {counts['unresolved']} unresolved"
            )
    print(f"Report: {destination}")
    return int(bool(findings))


if __name__ == "__main__":
    raise SystemExit(main())
