"""Compare a migration with a reviewed Git revision; never updates review approval.

Requires a previously validated formula report for its original Lean evidence.
The comparison checks interpretation output, not fresh Lean validity.
"""

import argparse
import ast
import json
import subprocess
import sys
import types
from pathlib import Path

import check as current


def first_difference(before, after, path="$"):
    if isinstance(before, dict) and isinstance(after, dict):
        if before.keys() != after.keys():
            return f"{path}: keys differ: {sorted(before.keys() ^ after.keys())}"
        for key in before:
            if before[key] != after[key]:
                return first_difference(before[key], after[key], path + "." + str(key))
    if isinstance(before, list) and isinstance(after, list):
        if len(before) != len(after):
            return f"{path}: lengths differ: {len(before)} -> {len(after)}"
        for index, (old, new) in enumerate(zip(before, after, strict=True)):
            if old != new:
                return first_difference(old, new, f"{path}[{index}]")
    return f"{path}: {str(before)[:1000]!r} -> {str(after)[:1000]!r}"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--revision", required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    args = parser.parse_args()
    filename = "tools/chapter-correspondence/check.py"
    source = subprocess.check_output(["git", "show", f"{args.revision}:{filename}"], cwd=current.ROOT, text=True)
    previous = types.ModuleType("previous_correspondence")
    previous.__file__ = str(current.ROOT / filename)
    sys.modules[previous.__name__] = previous
    # Deliberately execute the explicitly selected trusted repository revision.
    exec(compile(source, previous.__file__, "exec"), previous.__dict__)  # noqa: S102
    operator_filename = "tools/chapter-correspondence/operator_evidence.py"
    operator_source = subprocess.check_output(
        ["git", "show", f"{args.revision}:{operator_filename}"], cwd=current.ROOT, text=True
    )
    operator_function = next(
        node
        for node in ast.parse(operator_source).body
        if isinstance(node, ast.FunctionDef) and node.name == "operator_candidates"
    )
    operator_namespace = {"chapter": previous}
    exec(  # noqa: S102 -- independently selected trusted repository revision
        compile(ast.get_source_segment(operator_source, operator_function), operator_filename, "exec"),
        operator_namespace,
    )
    baseline = json.loads(args.baseline.read_text())
    records = baseline["leanEvidence"]
    text = current.SOURCE.read_text()

    def comparison_only(row, _records):
        row.update(typeStatus="typechecked", inferredType="comparison only, not Lean validation")

    before = previous.report(text, previous.scopes(text), records, check=comparison_only)
    after = current.report(text, current.scopes(text), records, check=comparison_only)
    for report in (before, after):
        report.pop("interpretationRulesHash")
    if before != after:
        raise SystemExit("Formula report changed: " + first_difference(before, after))
    count = traces = 0
    for row in after["formulas"]:
        old_candidates = operator_namespace["operator_candidates"](row["syntax"])
        new_candidates = current.native_structure("operatorCandidates", row["syntax"])
        if old_candidates != new_candidates:
            raise SystemExit(
                f"Operator candidates changed for formula {row['index']}: "
                + first_difference(old_candidates, new_candidates)
            )
        for tree in current.expression_list(row["syntax"]) or [row["syntax"]]:
            variables = [v for v in row["variables"] if tree["start"] <= v["formulaOffset"] < tree["end"]]
            old_trace, new_trace = [], []
            old_term = previous.translate(tree, variables, records, old_trace)
            new_term = current.translate(tree, variables, records, new_trace)
            if (old_term, old_trace) != (new_term, new_trace):
                raise SystemExit(
                    f"Term or operator trace changed for formula {row['index']}: "
                    + first_difference(list(old_term) + old_trace, list(new_term) + new_trace)
                )
            count += 1
            traces += len(new_trace)
    print(
        json.dumps(
            {"formulas": len(after["formulas"]), "interpretations": count, "operatorCalls": traces, "equal": True}
        )
    )


if __name__ == "__main__":
    main()
