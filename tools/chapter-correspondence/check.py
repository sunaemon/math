#!/usr/bin/env python3
"""Shared chapter correspondence: source positions, MathExpr syntax, identities and Lean types.

Run from any directory. Unsupported syntax and interpretations are report rows,
not successful checks. This is independent of the legacy Sort vocabulary.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from lean_export import cache_active, cache_provenance, export

sys.path.insert(0, str(Path(__file__).resolve().parent))
from chapter_config import load_chapter
from native import (
    analyze_chapter,
    expression_definition,
    prelude,
    request,
    semantic_translation,
    structural,
)
from notation_rules import (
    MACROS,  # noqa: F401 -- compatibility export of the native registry
    select_profiles,
)
from proof_contexts import inspection_source_many

CONFIG = load_chapter()
SOURCE = CONFIG.source
CONSTANTS, INTERPRETATION_DECLARATIONS, CONVENTIONS = select_profiles(CONFIG.profiles)


def configure(name):
    global CONFIG, SOURCE, CONSTANTS, INTERPRETATION_DECLARATIONS, CONVENTIONS
    CONFIG = load_chapter(name)
    SOURCE = CONFIG.source
    CONSTANTS, INTERPRETATION_DECLARATIONS, CONVENTIONS = select_profiles(CONFIG.profiles)


def __getattr__(name):
    if name == "METRIC_POINT_ELAB":
        return prelude("metricPrelude")
    raise AttributeError(name)


def context_reference(context):
    return request({"action": "contextReference", "context": context})["reference"]


def scopes(text):
    return request({"action": "sourceScopes", "text": text})["scopes"]


def source_declarations(source_scopes):
    return set(request({"action": "scopeDeclarations", "scopes": list(source_scopes)})["declarations"])


def resolve_literal_interpretations(tree, row, source_scopes):
    return request(
        {"action": "normalizeSource", "stage": "literal", "tree": tree, "row": row, "scopes": source_scopes}
    )["tree"]


def resolve_rational_ambient(tree, row, source_scopes):
    return request(
        {"action": "normalizeSource", "stage": "rational", "tree": tree, "row": row, "scopes": source_scopes}
    )["tree"]


def resolve_numeric_domain(tree, row, source_scopes):
    return request(
        {"action": "normalizeSource", "stage": "numeric", "tree": tree, "row": row, "scopes": source_scopes}
    )["tree"]


def resolve_generator_restrictions(tree, row, source_scopes):
    return request(
        {"action": "normalizeSource", "stage": "restrictions", "tree": tree, "row": row, "scopes": source_scopes}
    )["tree"]


def resolve_prefix_predicate(tree, row, source_scopes):
    return request({"action": "normalizeSource", "stage": "prefix", "tree": tree, "row": row, "scopes": source_scopes})[
        "tree"
    ]


def occurrences(text):
    return request({"action": "sourceOccurrences", "text": text})["occurrences"]


def syntax(formulas):
    return request({"action": "parseFormulas", "formulas": list(formulas)})["formulas"]


def located(node, offset=0):
    """Consume the shared Haskell parser's source positions without reconstructing them."""
    if offset != 0:
        raise ValueError("Located syntax must use formula-relative offsets.")
    if node.get("start") != 0 or not isinstance(node.get("end"), int):
        raise ValueError("Expected located syntax from the shared Haskell parser.")
    return node, node["end"]


def native_structure(operation, node):
    try:
        return structural(operation, node)
    except ValueError as error:
        raise Unsupported(str(error)) from error


def sequence_binder(node):
    return native_structure("sequenceBinder", node)


def typed_map_shape(node):
    return native_structure("typedMapShape", node)


def is_conjunction_token(node):
    return native_structure("isConjunctionToken", node)


def conjunction_shape(node):
    return native_structure("conjunctionShape", node)


def convergence_shape(node):
    return native_structure("convergenceShape", node)


def aligned_expression_rows(node):
    return native_structure("alignedRows", node)


def expression_list(node):
    return native_structure("expressionList", node)


def mapsto_shape(node):
    return native_structure("mapstoShape", node)


def bounded_infimum(node):
    return native_structure("boundedInfimum", node)


def ball_family_chunks(node):
    return native_structure("ballFamilies", node)


def predicate_set_chunks(node):
    return native_structure("predicateSets", node)


def summation_chunks(node):
    return native_structure("summationChunks", node)


def natural_lower_bound(node):
    return native_structure("naturalLowerBound", node)


def indexed_singleton_shapes(node):
    return native_structure("indexedSingletons", node)


def natural_type_family_shapes(node):
    return native_structure("naturalFamilies", node)


def natural_type_family_shape(node):
    return native_structure("naturalFamily", node)


def starred_name(node):
    return native_structure("starredName", node)


def numeric_subscript_name(node):
    return native_structure("numericSubscriptName", node)


def leaves(tree):
    result = native_structure("extractBindings", tree)
    return result["variables"], result["effects"]


def declaration_export(names):
    names = ", ".join(json.dumps(n, ensure_ascii=False) for n in sorted(names))
    return (
        CONFIG.imports()
        + """open Lean Meta Elab Command
set_option pp.universes false
run_cmd liftTermElabM do
  for rawName in ["""
        + names
        + """] do
    let name := rawName.toName
    let info ← getConstInfo name
    forallTelescope info.type fun xs result => do
      let mut binders : Array Json := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        binders := binders.push <| Json.mkObj [
          ("name", toJson d.userName.toString),
          ("instance", toJson d.binderInfo.isInstImplicit),
          ("type", toJson (← ppExpr d.type).pretty)]
      logInfo m!"BOOK_LEAN_EXPORT {(Json.mkObj [
        ("declaration", toJson name.toString), ("binders", toJson binders),
        ("result", toJson (← ppExpr result).pretty),
        ("declarationType", toJson (← ppExpr info.type).pretty),
        ("signature", toJson (reprStr info.type)), ("body", toJson (reprStr (info.value? (allowOpaque := true))))]).compress}"
"""
    )


def evidence(declarations):
    roots = {name.split("@", 1)[0] for name in declarations}
    records = export(declaration_export(roots)) if roots else {}
    local_targets = sorted(name for name in declarations if "@" in name)
    contexts = (
        export(inspection_source_many((target.split("@", 1) for target in local_targets), imports=CONFIG.imports()))
        if local_targets
        else {}
    )
    for target in local_targets:
        root, _ = target.split("@", 1)
        if target not in contexts:
            raise ValueError("Missing proof-local context: " + target)
        context = contexts[target]
        context["signature"] = json.dumps(context["binders"], ensure_ascii=False, sort_keys=True)
        context["body"] = (
            json.dumps(
                {
                    "root": contexts[root]["body"],
                    "unfoldings": {name: contexts[name] for name in context["unfoldings"]},
                },
                sort_keys=True,
            )
            if context.get("unfoldings")
            else contexts[root]["body"]
        )
        records[target] = context
    return records


def resolve_variables(variables, effects, row, source_scopes, records):
    compact_records = {
        name: {key: value for key, value in record.items() if key in {"binders", "declarationType"}}
        for name, record in records.items()
    }
    result = request(
        {
            "action": "resolveVariables",
            "variables": variables,
            "effects": effects,
            "scopes": source_scopes,
            "row": row,
            "records": compact_records,
        }
    )
    effects[:] = result["effects"]
    return result["variables"]


class Unsupported(ValueError):
    pass


def numeric_power(node):
    return native_structure("numericPower", node)


def expression_tokens(node):
    return native_structure("expressionTokens", node)


def shared_context(names, records):
    selected_records = (
        None
        if records is None
        else {name: {"binders": records[name].get("binders")} for name in names if name in records}
    )
    try:
        return request({"action": "contextBridge", "names": list(names), "records": selected_records})["context"]
    except ValueError as error:
        raise Unsupported(str(error)) from error


def translate(tree, variables, records=None, trace=None):
    """Transport one expression to the sole semantic interpreter in Haskell."""
    occupied = {binder["name"] for record in (records or {}).values() for binder in record.get("binders", [])}
    result = semantic_translation(
        tree,
        variables,
        occupied,
        len(trace) if trace is not None else 0,
        constants=CONSTANTS,
        conventions=CONVENTIONS,
        records=records,
        standalone=True,
        resolve_context=True,
    )
    if not result["supported"]:
        raise Unsupported(result["reason"])
    context = result["context"]
    rendering = result["rendering"]
    if trace is not None:
        trace.extend(rendering["mappings"])
        return rendering["instrumented"], context
    return rendering["ordinary"], context


def batch_check(rows, records):
    grouped = {}
    for row in rows:
        grouped.setdefault((row["lean"], row["context"]), []).append(row)
    groups = list(grouped.values())

    def run(groups):
        source = (
            CONFIG.imports()
            + CONFIG.opens()
            + """set_option autoImplicit false
-- This generated adapter retains the complete source telescope deliberately.
set_option linter.unusedVariables false
"""
            + prelude("metricPrelude")
            + "\n".join(
                expression_definition(group[0], records, f"ChapterExpression.f{i}") for i, group in enumerate(groups)
            )
            + """
open Lean Meta Elab Command
run_cmd liftTermElabM do
  for (name, contextSize) in ["""
            + ", ".join(
                f"(``ChapterExpression.f{i}, {sum(b.get('value') is None for b in records[group[0]['context']]['binders']) if group[0]['context'] else 0})"
                for i, group in enumerate(groups)
            )
            + """] do
    let info ← getConstInfo name
    forallBoundedTelescope info.type (some contextSize) fun _ result => do
      logInfo m!"BOOK_LEAN_EXPORT {(Json.mkObj [("declaration", toJson name.toString),
        ("result", toJson (← ppExpr result).pretty)]).compress}"
"""
        )
        try:
            checked = export(source)
        except ValueError as error:
            if len(groups) > 1:
                midpoint = len(groups) // 2
                run(groups[:midpoint])
                run(groups[midpoint:])
            else:
                for row in groups[0]:
                    row.update(typeReason="Lean rejected the interpretation.", diagnostic=str(error))
        else:
            for i, group in enumerate(groups):
                for row in group:
                    row.update(typeStatus="typechecked", inferredType=checked[f"ChapterExpression.f{i}"]["result"])
                    row.pop("typeReason", None)
                    if cache_provenance() is not None:
                        row["validationOrigin"] = cache_provenance()

    batch_size = 1 if cache_active() else 2
    for start in range(0, len(groups), batch_size):
        run(groups[start : start + batch_size])


def lean_check(row, records):
    batch_check([row], records)


def report(text, source_scopes, records, parse=syntax, check=lean_check, trusted=True):
    parsed = None if parse is syntax else parse([row["book"] for row in occurrences(text)])
    prepared = analyze_chapter(
        text, source_scopes, records, constants=CONSTANTS, conventions=CONVENTIONS, parsed=parsed, interpret=trusted
    )
    rows = prepared["rows"]
    pending = []
    translation_jobs = []
    for job in prepared["expressions"]:
        row = rows[job["formulaIndex"]]
        candidate = row if job["fragmentIndex"] is None else row["expressionFragments"][job["fragmentIndex"]]
        if trusted:
            translation_jobs.append((candidate, job))
        else:
            candidate["typeReason"] = (
                "Source or interpretation rules changed since review; no typechecked status granted."
            )
    if translation_jobs:
        translated = prepared["translations"]
        if len(translated) != len(translation_jobs):
            raise ValueError("Semantic translation lost expression jobs")
        for (candidate, _), result in zip(translation_jobs, translated, strict=True):
            try:
                if not result["supported"]:
                    raise Unsupported(result["reason"])
                candidate.update(lean=result["rendering"]["ordinary"], context=result["context"])
                if check is lean_check:
                    pending.append(candidate)
                else:
                    check(candidate, records)
            except Unsupported as error:
                candidate["typeReason"] = str(error)
            except ValueError as error:
                candidate["typeReason"] = "Lean rejected the interpretation."
                candidate["diagnostic"] = str(error)
    batch_check(pending, records)
    for row in rows:
        fragments = row.get("expressionFragments")
        if fragments and all(part["typeStatus"] == "typechecked" for part in fragments):
            row.update(typeStatus="typechecked", inferredTypes=[part["inferredType"] for part in fragments])
            row.pop("typeReason", None)
    variables = [v for r in rows for v in r["variables"]]
    checked = sum(r["typeStatus"] == "typechecked" for r in rows)
    parsed_count = sum(r["syntaxStatus"] == "parsed" for r in rows)
    resolved = sum(v["status"] == "resolved" for v in variables)
    return {
        "schemaVersion": 1,
        "chapter": CONFIG.name,
        "configurationHash": CONFIG.fingerprint,
        "interpretationRulesHash": rules_hash(),
        "reviewStatus": "reviewed" if trusted else "stale",
        "source": str(SOURCE.relative_to(ROOT)),
        "sourceHash": hashlib.sha256(text.encode()).hexdigest(),
        "offsetConvention": "zero-based Unicode character offsets, half-open; line numbers one-based",
        "meaning": "Structural TeX parsing, variable resolution and Lean expression typing are separate. Typing proves neither intended interpretation nor the book's assertion.",
        "legacyProtection": "This chapter uses source-owned scopes and Lean expression/operator checks; no legacy sort annotations are required.",
        "parsing": {"total": len(rows), "parsed": parsed_count, "unsupported": len(rows) - parsed_count},
        "variableResolution": {"total": len(variables), "resolved": resolved, "unresolved": len(variables) - resolved},
        "expressionTypes": {"total": len(rows), "typechecked": checked, "unresolved": len(rows) - checked},
        "scopes": source_scopes,
        "scopeContexts": prepared["scopeContexts"],
        "leanEvidence": records,
        "formulas": rows,
    }


def rules_hash():
    paths = [
        Path(__file__),
        Path(__file__).with_name("proof_contexts.py"),
        Path(__file__).with_name("chapter_config.py"),
        Path(__file__).with_name("notation_rules.py"),
        Path(__file__).with_name("native.py"),
        ROOT / "tools/book-filter/Correspondence.hs",
        ROOT / "tools/book-filter/ChapterPreparation.hs",
        ROOT / "tools/book-filter/FormulaAnchors.hs",
        ROOT / "tools/book-filter/LeanSourceRanges.hs",
        ROOT / "tools/book-filter/StructuralSyntax.hs",
        ROOT / "tools/book-filter/VariableResolution.hs",
        ROOT / "tools/book-filter/SourceScopes.hs",
        ROOT / "tools/book-filter/SourceJSON.hs",
        ROOT / "tools/book-filter/SourceNormalization.hs",
        ROOT / "tools/book-filter/SemanticExpr.hs",
        ROOT / "tools/book-filter/SemanticAST.hs",
        ROOT / "tools/book-filter/SemanticInspection.hs",
        ROOT / "tools/book-filter/SemanticTrace.hs",
        ROOT / "tools/book-filter/ChapterMappingRules.hs",
        ROOT / "tools/book-filter/SemanticTranslation.hs",
        ROOT / "tools/book-filter/ProofContexts.hs",
        ROOT / "tools/book-filter/OperatorEvidence.hs",
        ROOT / "tools/book-filter/OperatorProbe.hs",
        ROOT / "tools/book-filter/ProbeTemplates.hs",
        ROOT / "tools/book-filter/ContextTemplates.hs",
        ROOT / "tools/lean_export.py",
        ROOT / "tools/lean_probe_cache.py",
        ROOT / "tools/book-filter/Main.hs",
        ROOT / "tools/book-filter/MathSyntax.hs",
        ROOT / "tools/book-filter/MathSyntaxCLI.hs",
        ROOT / "tools/book-filter/LocatedMath.hs",
    ]
    return hashlib.sha256(
        b"\0".join([*(path.read_bytes() for path in paths), load_chapter(CONFIG.name).fingerprint.encode()])
    ).hexdigest()


def review_matches(review, text, records):
    current = {
        "sourceHash": hashlib.sha256(text.encode()).hexdigest(),
        "rulesHash": rules_hash(),
        "leanFingerprints": {
            name: hashlib.sha256((record["signature"] + "\n" + record["body"]).encode()).hexdigest()
            for name, record in records.items()
        },
    }
    return request({"action": "reviewMatches", "recorded": review, "current": current})["matched"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--chapter", default="polish-spaces")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    configure(args.chapter)
    args.output = args.output or ROOT / "build/chapter-correspondence" / CONFIG.name / "formulas.json"
    subprocess.run(["make", "build/book-filter"], cwd=ROOT, check=True)
    subprocess.run(
        [
            "make",
            "validate-lean",
            "LEAN_PROJECTS=" + CONFIG.project,
            "LEAN_MODULES=" + " ".join(CONFIG.modules),
        ],
        cwd=ROOT,
        check=True,
    )
    text = SOURCE.read_text()
    source_scopes = scopes(text)
    names = source_declarations(source_scopes)
    records = evidence(names | INTERPRETATION_DECLARATIONS)
    review = json.loads(CONFIG.review.read_text())
    trusted = review_matches(review, text, records)
    result = report(text, source_scopes, records, trusted=trusted)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("parsing", "variableResolution", "expressionTypes")}, indent=2))
    print("Report:", args.output)
    if not trusted:
        raise SystemExit("Source or rules changed: interpretation review required.")
    if (
        result["parsing"]["unsupported"]
        or result["variableResolution"]["unresolved"]
        or result["expressionTypes"]["unresolved"]
    ):
        raise SystemExit("Incomplete formula correspondence; inspect the report.")


if __name__ == "__main__":
    main()
