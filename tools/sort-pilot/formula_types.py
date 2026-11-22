"""Inventory every formula occurrence; check explicitly reviewed Lean interpretations."""

import re
from collections import defaultdict, deque

from sort_coverage import MATH

PRELUDE = """import PolishSpaceBook.ForcingOrdinalPreservation
import Lean
set_option autoImplicit false
open PolishSpaceBook ZFSet
open PolishSpaceBook.ForcingNames PolishSpaceBook.SetTheoryModels
"""


def lean_source(items):
    definitions = []
    for row in items:
        params = " ".join(f"({b['name']} : {b['type']})" for b in row["context"])
        definitions.append(
            f"section\nvariable {params}\nnoncomputable def FormulaTypes.f{row['index']} :=\n  {row['term']}\nend\n"
        )
    names = ", ".join(f"``FormulaTypes.f{row['index']}" for row in items)
    return (
        PRELUDE
        + "\n".join(definitions)
        + f"""
open Lean Meta Elab Command
run_cmd liftTermElabM do
  for name in [{names}] do
    let info ← getConstInfo name
    forallTelescope info.type fun xs result => do
      let mut binders : Array Json := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        binders := binders.push <| Json.mkObj [
          ("name", toJson d.userName.toString), ("type", toJson (← ppExpr d.type).pretty)]
      logInfo m!"SORT_PILOT {{(Json.mkObj [
        ("declaration", toJson name.toString), ("binders", toJson binders),
        ("result", toJson (← ppExpr result).pretty)]).compress}}"
"""
    )


def classify(manifest, selected, source, export, trusted=True):
    mappings = defaultdict(deque)
    for expression in manifest["expressions"]:
        mappings[expression["book"]].append(expression)
    start = source.index(selected)
    rows, pending = [], []
    for index, match in enumerate(MATH.finditer(selected)):
        book = match[1] if match[1] is not None else match[2]
        offset = start + match.start()
        row = {
            "index": index,
            "book": book,
            "line": source.count("\n", 0, offset) + 1,
            "offset": offset,
            "status": "unresolved",
        }
        rows.append(row)
        mapping = mappings[book].popleft() if mappings[book] else {}
        row["reason"] = mapping.get("unresolvedReason", "No reviewed Lean expression is registered.")
        if not trusted:
            row["reason"] = "Source or correspondence evidence needs repair/review; no checked status is granted."
            continue
        if "term" not in mapping:
            continue
        row["term"] = mapping["term"]
        identifiers = set(re.findall(r"\w+", row["term"]))
        row["context"] = [
            {"id": b["id"], "name": b["leanName"], "type": b["leanType"].replace("{u}", "{0}")}
            for b in manifest["bindings"]
            if b["leanName"] in identifiers
        ]
        pending.append(row)

    def accept(row, records):
        record = records[f"FormulaTypes.f{row['index']}"]
        row.update(status="typechecked", inferredType=record["result"], checkedBinders=record["binders"])
        row["context"] = [b for b in row["context"] if b["name"] in {x["name"] for x in record["binders"]}]
        row.pop("reason", None)

    if pending:
        try:
            records = export(lean_source(pending))
        except ValueError:
            # Isolate failures so one unsupported expression cannot hide the rest.
            for row in pending:
                try:
                    accept(row, export(lean_source([row])))
                except ValueError as error:
                    row["reason"] = "Lean rejected the proposed interpretation."
                    row["diagnostic"] = str(error)
        else:
            for row in pending:
                accept(row, records)
    checked = sum(row["status"] == "typechecked" for row in rows)
    return {
        "total": len(rows),
        "typechecked": checked,
        "unresolved": len(rows) - checked,
        "typecheckedPercent": 100 * checked / len(rows) if rows else None,
        "typeCoverageComplete": checked == len(rows),
        "meaning": "Types of reviewed Lean interpretations, not automatic proof of prose equivalence or truth.",
        "formulas": rows,
    }


def self_test(manifest, selected, source, export):
    import copy

    missing = copy.deepcopy(manifest)
    missing["expressions"] = []
    result = classify(missing, selected, source, export)
    assert result["total"] == 14 and result["unresolved"] == 14
    result = classify(manifest, selected, source, export, trusted=False)
    assert result["typechecked"] == 0 and result["unresolved"] == 14
    broken = copy.deepcopy(manifest)
    broken["expressions"] = [{"book": "M", "term": "(M : Nat)"}]
    result = classify(broken, selected, source, export)
    assert result["total"] == 14 and result["unresolved"] == 14
    assert "diagnostic" in result["formulas"][0]
    return {
        "missing_interpretation": "all 14 retained as unresolved",
        "stale_evidence": "no checked status granted",
        "invalid_lean_expression": "Lean rejection retained in inventory",
    }
