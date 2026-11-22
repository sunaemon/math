"""Operator correspondence uses elaborated calls, not only result types."""

import copy
import importlib.util
import re
import unittest
from pathlib import Path
from unittest.mock import patch

from correspondence_oracle import corrupt_native_terms, legacy_oracle

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "operator_evidence", ROOT / "tools/chapter-correspondence/operator_evidence.py"
)
operators = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(operators)


def inspect_formula(formula, types=None):
    types = types or {}
    chapter = operators.chapter
    tree, _ = chapter.located(chapter.syntax([formula])[0]["tree"])
    variables, _ = chapter.leaves(tree)
    for variable in variables:
        variable.update(
            id="fixture/" + variable["symbol"],
            status="resolved",
            declaration="D",
            leanName=variable["symbol"],
            leanType=types.get(variable["symbol"], "ℝ"),
            formulaOffset=variable["start"],
        )
    records = {
        "D": {
            "binders": [
                {"name": n, "type": types.get(n, "ℝ"), "instance": False}
                for n in sorted({v["symbol"] for v in variables})
            ]
        }
    }
    return operators.inspect(tree, variables, records)


class SharedLiteralTests(unittest.TestCase):
    def fixture(self):
        import json

        c = operators.chapter
        annotation = {
            "scope": "initial-zero",
            "bindings": {},
            "literalInterpretations": [
                {
                    "id": name,
                    "constant": constant,
                    "consumer": {
                        "declaration": f"PolishSpaceBook.{name}_space_not_connected",
                        "callee": "PolishSpaceBook.not_connected_of_initialSymbolCylinder",
                        "argumentPosition": 3,
                    },
                }
                for name, constant in [("cantor", "Bool.false"), ("baire", "Nat.zero")]
            ],
        }
        text = "<!-- chapter-correspondence " + json.dumps(annotation) + " -->$0$"
        text += "<!-- chapter-correspondence-end: initial-zero -->"
        return c, annotation, text

    def test_shared_source_span_retains_both_kernel_checked_consumers(self):
        c, _, text = self.fixture()
        scopes = c.scopes(text)
        records = c.evidence(c.source_declarations(scopes))
        with patch.object(c, "SOURCE") as source:
            source.read_text.return_value = text
            source.relative_to.return_value = "fixture.md"
            report = c.report(text, scopes, records, trusted=False)
            result = operators.inspect_formula_report(report, 0, validated=True)
        self.assertEqual(len(report["formulas"]), 1)
        self.assertEqual(report["formulas"][0]["expressionKind"], "contextual-interpretations")
        self.assertEqual(len(result["expressionFragments"]), 2)
        self.assertTrue(all(f["typeStatus"] == "typechecked" for f in result["expressionFragments"]))
        self.assertEqual(
            [n["interpretationId"] for n in result["nodes"]], ["initial-zero/cantor", "initial-zero/baire"]
        )
        self.assertEqual(len({(n["start"], n["end"]) for n in result["nodes"]}), 1)
        self.assertTrue(all(n["sourceOperator"] == "0" for n in result["nodes"]))
        self.assertTrue(
            all(n["targetStatus"] == n["operandStatus"] == n["consumerStatus"] == "matched" for n in result["nodes"])
        )
        self.assertTrue(
            all(
                n["implicitArgumentStatus"] == "not-required" and n["requirementStatus"] == "proved"
                for n in result["nodes"]
            )
        )
        self.assertFalse(result["unresolved"] or result["untracedOperators"])
        inventory = operators.translation_inventory(report, validated=True)
        self.assertEqual(
            inventory["summary"],
            {"formulaCount": 1, "unitCount": 2, "translatableFormulas": 1, "unresolvedFormulas": 0},
        )
        parts = c.expression_list(report["formulas"][0]["syntax"])
        for part in parts:
            wrong = copy.deepcopy(part)
            wrong["consumer"]["argumentPosition"] = 4
            node = operators.inspect(wrong, [], records)[0]
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["consumerStatus"], "mismatch")
            self.assertEqual(node["requirementStatus"], "unresolved")
        missing = copy.deepcopy(report)
        del missing["leanEvidence"]["Nat.zero"]
        inventory = operators.translation_inventory(missing, validated=True)
        self.assertEqual(inventory["summary"]["unitCount"], 2)
        self.assertEqual(inventory["summary"]["unresolvedFormulas"], 1)
        self.assertEqual([u["status"] for u in inventory["formulas"][0]["units"]], ["translated", "unresolved"])

    def test_shared_literal_schema_rejects_missing_or_duplicate_contexts(self):
        import json

        c, annotation, _ = self.fixture()
        for change in ["single", "duplicate", "negative-position", "invalid-constant"]:
            data = copy.deepcopy(annotation)
            if change == "single":
                data["literalInterpretations"].pop()
            elif change == "duplicate":
                data["literalInterpretations"][1]["id"] = "cantor"
            elif change == "negative-position":
                data["literalInterpretations"][0]["consumer"]["argumentPosition"] = -1
            else:
                data["literalInterpretations"][0]["constant"] = "(false : Bool)"
            text = (
                "<!-- chapter-correspondence "
                + json.dumps(data)
                + " -->$0$<!-- chapter-correspondence-end: initial-zero -->"
            )
            with self.subTest(change=change), self.assertRaises(ValueError):
                c.scopes(text)


class ImplicitCoverageTests(unittest.TestCase):
    def coverage(self, flags, positions, checks):
        return operators.implicit_argument_coverage(
            {"arguments": [{"implicit": flag} for flag in flags]},
            [{"argumentPosition": position} for position in positions],
            checks,
        )

    def test_absence_requires_observed_empty_implicit_telescope(self):
        self.assertEqual(self.coverage([], [], [])["status"], "not-required")
        self.assertEqual(self.coverage([False], [], [])["status"], "not-required")
        self.assertEqual(operators.implicit_argument_coverage({}, [], [])["status"], "unreviewed")
        self.assertEqual(operators.implicit_argument_coverage({"arguments": [{}]}, [], [])["status"], "unreviewed")

    def test_successful_partial_checks_do_not_hide_missing_positions(self):
        result = self.coverage([True, True, False], [0], [{"status": "matched"}])
        self.assertEqual(result["status"], "unreviewed")
        self.assertEqual(result["missingPositions"], [1])
        self.assertEqual(self.coverage([True], [], [])["status"], "unreviewed")

    def test_complete_checks_and_wrong_expectations(self):
        matched = {"status": "matched"}
        self.assertEqual(self.coverage([True, False, True], [0, 2], [matched, matched])["status"], "matched")
        self.assertEqual(self.coverage([False], [0], [matched])["status"], "mismatch")
        self.assertEqual(self.coverage([True], [0, 0], [matched, matched])["status"], "mismatch")
        self.assertEqual(self.coverage([True], [0], [])["status"], "mismatch")
        self.assertEqual(self.coverage([True], [0], [{"status": "mismatch"}])["status"], "mismatch")
        self.assertEqual(self.coverage([True], [0], None)["status"], "unreviewed")

    def test_merged_calls_preserve_absence_and_incomplete_coverage(self):
        node = {
            "operatorStart": 0,
            "operatorEnd": 1,
            "rule": "test",
            "headStatus": "matched",
            "targetStatus": "matched",
            "operandStatus": "matched",
            "implicitArgumentStatus": "not-required",
        }
        evidence = {}
        operators.merge_operator_call(evidence, node)
        result = next(iter(evidence.values()))
        self.assertEqual(result["implicitArgumentStatus"], "not-required")
        operators.merge_operator_call(evidence, dict(node, implicitArgumentStatus="matched"))
        self.assertEqual(result["implicitArgumentStatus"], "matched")
        operators.merge_operator_call(evidence, dict(node, implicitArgumentStatus="unreviewed"))
        self.assertEqual(result["implicitArgumentStatus"], "unreviewed")


class OperatorEvidenceTests(unittest.TestCase):
    def assert_native_translation(self, tree, variables, records):
        occupied = {binder["name"] for record in records.values() for binder in record.get("binders", [])}
        result = operators.chapter.semantic_translation(
            tree, variables, occupied, constants=operators.chapter.CONSTANTS, records=records
        )
        self.assertTrue(result["supported"], result)
        return result

    def test_native_comparison_of_abstract_ordered_values_checks_the_order_instance(self):
        c = operators.chapter
        tree, _ = c.located(c.syntax(["f(x)<f(y)"])[0]["tree"])
        variables, _ = c.leaves(tree)
        types = {"f": "X → X", "x": "X", "y": "X"}
        for variable in variables:
            name = variable["symbol"]
            variable.update(
                id="scope/" + name,
                status="resolved",
                declaration="D",
                leanName=name,
                leanType=types[name],
                formulaOffset=variable["start"],
            )
        records = {
            "D": {
                "binders": [
                    {"name": name, "type": ty, "instance": instance}
                    for name, ty, instance in [
                        ("X", "Type", False),
                        ("order", "Preorder X", True),
                        ("f", "X → X", False),
                        ("x", "X", False),
                        ("y", "X", False),
                    ]
                ]
            }
        }
        native = c.semantic_translation(tree, variables, [], records=records)
        self.assertTrue(native["supported"], native)
        nodes = operators.inspect(tree, variables, records)
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        original = c.translate

        def wrong_order(*args, **kwargs):
            result = original(*args, **kwargs)
            for mapping in kwargs.get("trace") or []:
                if mapping["rule"] == "infix:<":
                    mapping["expectedImplicitArguments"][1]["candidate"] = "(inferInstance : LT Nat)"
            return result

        with patch.object(c, "translate", side_effect=wrong_order):
            changed = operators.inspect(tree, variables, records)[-1]
        self.assertEqual(changed["targetStatus"], "matched")
        self.assertEqual(changed["operandStatus"], "mismatch")

    def test_native_comparison_rendering_does_not_approve_invalid_source_operations(self):
        c = operators.chapter
        source = "f(x)<f(y)"
        tree, _ = c.located(c.syntax([source])[0]["tree"])
        variables, _ = c.leaves(tree)
        types = {"f": "Real → Type", "x": "Real", "y": "Real"}
        for variable in variables:
            name = variable["symbol"]
            variable.update(
                id="scope/" + name,
                status="resolved",
                declaration="D",
                leanName=name,
                leanType=types[name],
                formulaOffset=variable["start"],
            )
        records = {"D": {"binders": [{"name": n, "type": ty, "instance": False} for n, ty in types.items()]}}
        native = c.semantic_translation(tree, variables, [], records=records)
        self.assertTrue(native["supported"], native)
        with self.assertRaises(ValueError):
            operators.inspect(tree, variables, records)

    def test_source_distance_zero_limit_uses_sequence_codomain(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        row = next(row for row in c.occurrences(text) if row["book"] == r"d'(x_n,x)\to 0")
        selected = [scope for scope in scopes if scope["start"] <= row["start"] < scope["end"]]
        records = c.evidence(c.source_declarations(selected))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        native = c.semantic_translation(tree, variables, [], constants=c.CONSTANTS, records=records)
        self.assertTrue(native["supported"], native)
        nodes = operators.inspect(tree, variables, records)
        self.assertTrue(all(node["targetStatus"] == node["operandStatus"] == "matched" for node in nodes))
        self.assertTrue(all(node["implicitArgumentStatus"] in {"matched", "not-required"} for node in nodes))
        numeral = next(node for node in nodes if node["rule"] == "literal:sequence-limit")
        self.assertEqual(row["book"][numeral["operatorStart"] : numeral["operatorEnd"]], "0")
        self.assertEqual(numeral["implicitArgumentCoverage"]["actualPositions"], [0, 2])
        term, context = c.translate(tree, variables, records)
        intended = "Filter.Tendsto (fun n : Nat => «d'» (u n) x) Filter.atTop (nhds (0 : Real))"
        proof = f"(show ({term}) = ({intended}) from rfl)"
        source = operators.HEADER + c.expression_definition(
            {"lean": proof, "context": context}, records, "SourceDistanceZeroLimit"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"source_distance_zero_limit\\"}"\n'
        self.assertIn("source_distance_zero_limit", c.export(source))
        original = c.translate

        def wrong_numeral_type(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace", []):
                if node["rule"] == "literal:sequence-limit":
                    node["expectedImplicitArguments"][0]["candidate"] = "Nat"
            return result

        with patch.object(c, "translate", side_effect=wrong_numeral_type):
            wrong = operators.inspect(tree, variables, records)
        numeral = next(node for node in wrong if node["rule"] == "literal:sequence-limit")
        self.assertEqual(numeral["implicitArgumentStatus"], "mismatch")

    def test_implicit_coverage_uses_the_lean_telescope(self):
        node = inspect_formula(r"\TwoPointSpace")[0]
        self.assertEqual(node["implicitArgumentStatus"], "not-required")
        self.assertEqual(node["implicitArgumentCoverage"]["actualPositions"], [])
        c = operators.chapter
        original = c.translate

        def omit_topology(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace", []):
                if node["rule"] == "macro:Closure":
                    node["expectedImplicitArguments"] = node["expectedImplicitArguments"][:1]
            return result

        with patch.object(c, "translate", side_effect=omit_topology):
            node = inspect_formula(r"\Closure{C}", {"C": "Set ℝ"})[0]
        self.assertEqual(node["operandStatus"], "matched")
        self.assertEqual(node["implicitArgumentChecks"][0]["status"], "matched")
        self.assertEqual(node["implicitArgumentStatus"], "unreviewed")
        self.assertEqual(node["implicitArgumentCoverage"]["missingPositions"], [1])

    def test_translation_inventory_keeps_failed_list_members_and_unparsed_rows(self):
        c = operators.chapter
        trees = [c.located(row["tree"])[0] for row in c.syntax(["x,y", r"\R"])]
        variables, _ = c.leaves(trees[0])
        for var in variables:
            var.update(
                id="fixture/" + var["symbol"],
                formulaOffset=var["start"],
                status="resolved" if var["symbol"] == "x" else "unresolved",
                leanName=var["symbol"],
                leanType="ℝ",
                declaration="D",
                reason="missing y binding",
            )
        report = {
            "sourceHash": "test",
            "leanEvidence": {"D": {"binders": [{"name": "x", "type": "ℝ", "instance": False}]}},
            "formulas": [
                {"index": 0, "bodyStart": 10, "syntax": trees[0], "variables": variables},
                {"index": 1, "bodyStart": 20, "syntax": trees[1], "variables": []},
                {"index": 2, "bodyStart": 30, "variables": []},
            ],
        }
        result = operators.translation_inventory(report, validated=True)
        self.assertEqual(
            result["summary"], {"formulaCount": 3, "unitCount": 4, "translatableFormulas": 1, "unresolvedFormulas": 2}
        )
        self.assertEqual([u["status"] for u in result["formulas"][0]["units"]], ["translated", "unresolved"])
        self.assertEqual(result["formulas"][0]["units"][1]["start"], 12)
        self.assertEqual(result["formulas"][2]["units"][0]["reason"], "No parsed source expression")
        self.assertIn("not kernel validation", result["meaning"])

    def test_shared_membership_tracks_both_points_and_the_common_domain(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        row = next(r for r in c.occurrences(text) if r["book"] == r"x,y\in X")
        selected = [s for s in scopes if s["start"] <= row["start"] < s["end"]]
        records = c.evidence(c.source_declarations(selected))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        nodes = operators.inspect(tree, variables, records)
        members = [n for n in nodes if n["rule"] == "set:in"]
        self.assertEqual(len(members), 2)
        self.assertEqual([n["lowering"]["member"] for n in members], [0, 1])
        self.assertNotEqual(
            next(a for a in members[0]["expectedOperands"] if a["sourceOperand"] == 0),
            next(a for a in members[1]["expectedOperands"] if a["sourceOperand"] == 0),
        )
        self.assertEqual(
            next(a for a in members[0]["expectedOperands"] if a["sourceOperand"] == 1),
            next(a for a in members[1]["expectedOperands"] if a["sourceOperand"] == 1),
        )
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or i in checked for i, a in enumerate(node["elaborated"].get("arguments", [])))
            )
            if checked:
                self.assertEqual(node["implicitArgumentStatus"], "matched")
        term, context = c.translate(tree, variables, records)
        proof = f"(show {term} from ⟨Set.mem_univ _, Set.mem_univ _⟩)"
        source = operators.HEADER + c.expression_definition(
            {"lean": proof, "context": context}, records, "SharedMembership"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"shared_membership\\"}"\n'
        self.assertIn("shared_membership", c.export(source))

    def test_shared_membership_does_not_hide_a_wrong_second_point(self):
        c = operators.chapter
        original = c.translate

        def corrupt(*args, **kwargs):
            result = original(*args, **kwargs)
            trace = kwargs.get("trace")
            if trace is not None:
                member = [n for n in trace if n["rule"] == "set:in"][1]
                next(a for a in member["expectedOperands"] if a["sourceOperand"] == 0)["candidate"] += " + 1"
            return result

        with patch.object(c, "translate", side_effect=corrupt):
            nodes = inspect_formula(r"x,y\in A", {"x": "ℝ", "y": "ℝ", "A": "Set ℝ"})
        members = [n for n in nodes if n["rule"] == "set:in"]
        self.assertEqual([n["operandStatus"] for n in members], ["matched", "mismatch"])
        merged = {}
        for member in members:
            operators.merge_operator_call(merged, member)
        self.assertEqual(len(merged), 1)
        self.assertEqual(next(iter(merged.values()))["operandStatus"], "mismatch")
        with self.assertRaises(c.Unsupported):
            inspect_formula(r"x,y\in A", {"A": "ℝ"})

    def test_standalone_function_declaration_checks_source_domain_and_codomain(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        row = next(r for r in c.occurrences(text) if r["book"] == r"f:X\to Y")
        selected = [s for s in scopes if s["start"] <= row["start"] < s["end"]]
        records = c.evidence(c.source_declarations(selected))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        nodes = operators.inspect(tree, variables, records)
        self.assertEqual({n["rule"] for n in nodes}, {"type:function-arrow", "declaration:function-type"})
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            self.assertFalse(any(a["implicit"] for a in node["elaborated"].get("arguments", [])))
        invalid = copy.deepcopy(variables)
        next(v for v in invalid if v["symbol"] == "X")["leanType"] = "Set ℝ"
        with self.assertRaises(c.Unsupported):
            c.translate(tree, invalid, records)

    def test_finite_power_checks_dimension_operand_independently(self):
        c = operators.chapter
        original = c.translate

        def wrong_dimension(*args, **kwargs):
            result = original(*args, **kwargs)
            trace = kwargs.get("trace")
            if trace is not None:
                finite = next(n for n in trace if n["rule"] == "type:finite-index")
                finite["expectedOperands"][0]["candidate"] += " + 1"
            return result

        with patch.object(c, "translate", side_effect=wrong_dimension):
            nodes = inspect_formula(r"\R^n", {"n": "ℕ"})
        finite = next(n for n in nodes if n["rule"] == "type:finite-index")
        self.assertEqual(finite["targetStatus"], "matched")
        self.assertEqual(finite["operandStatus"], "mismatch")

    def test_source_finite_powers_preserve_dimension_and_coordinate_carrier(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "polish-examples")
        records = c.evidence(c.source_declarations([scope]))
        source = operators.HEADER
        rows = [r for r in c.occurrences(text) if r["book"] in {r"\R^n", r"\QQ^n"}]
        self.assertEqual(len(rows), 2)
        for row in rows:
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            nodes = operators.inspect(tree, variables, records)
            self.assertEqual({n["rule"] for n in nodes}, {"type:finite-index", "binder:sequence-power"})
            for node in nodes:
                self.assertEqual(node["targetStatus"], "matched")
                self.assertEqual(node["operandStatus"], "matched")
                self.assertFalse(any(a["implicit"] for a in node["elaborated"].get("arguments", [])))
            term, context = c.translate(tree, variables, records)
            expected = "PolishSpaceBook.euclidean_space n" if row["book"] == r"\R^n" else "(Fin n → ℚ)"
            source += c.expression_definition(
                {"lean": f"(show ({term}) = ({expected}) from rfl)", "context": context},
                records,
                f"FinitePower{row['index']}",
            )
        source += r"""
example (n : ℕ) : DenseRange (fun q : Fin n → ℚ => fun i => (q i : ℝ)) := by
  exact DenseRange.piMap (fun _ => Rat.denseRange_cast)
run_cmd Lean.logInfo "SORT_PILOT {\"declaration\":\"finite_power_source\"}"
"""
        self.assertIn("finite_power_source", c.export(source))

    def test_finite_power_rejects_non_natural_dimension_and_checks_zero(self):
        for ty in ("ℝ", "ℤ", "Set ℕ"):
            with self.subTest(type=ty), self.assertRaises(operators.chapter.Unsupported):
                inspect_formula(r"\R^n", {"n": ty})
        for formula in (r"\R^0", r"\QQ^{12}"):
            with self.subTest(formula=formula):
                nodes = inspect_formula(formula)
                self.assertTrue(all(n["targetStatus"] == "matched" and n["operandStatus"] == "matched" for n in nodes))

    def test_source_rational_singleton_union_tracks_real_cast_and_all_arguments(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        row = next(r for r in c.occurrences(text) if r"\QQ = \bigcup" in r["book"])
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        tree = c.resolve_rational_ambient(tree, row, scopes)
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, {})
        self.assert_native_translation(tree, variables, {})
        self.assertTrue(all(v.get("localBinder") and v["leanType"] == "ℚ" for v in variables))
        self.assertEqual(len({v["leanName"] for v in variables}), 1)
        nodes = operators.inspect(tree, variables, {})
        self.assertEqual(
            {n["rule"] for n in nodes},
            {
                "set:embedded-rationals",
                "coercion:rational-real",
                "set:singleton",
                "binder:mapsto",
                "set:indexed-union",
                "set:=",
            },
        )
        union = next(n for n in nodes if n["rule"] == "set:indexed-union")
        ambient = union["sourceAmbient"]
        self.assertEqual(ambient["scope"], "rationals-proof")
        self.assertLessEqual(ambient["start"], row["start"])
        self.assertGreaterEqual(ambient["end"], row["end"])
        covered = set()
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            if node["expectedImplicitArguments"]:
                self.assertEqual(node["implicitArgumentStatus"], "matched")
            implicit = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or i in implicit for i, a in enumerate(node["elaborated"].get("arguments", [])))
            )
            covered.add((node["operatorStart"], node["operatorEnd"]))
            covered.update((part["start"], part["end"]) for part in node.get("bindingComponents", []))
        for candidate in operators.operator_candidates(tree):
            self.assertIn((candidate["start"], candidate["end"]), covered)
        term, context = c.translate(tree, variables, {})
        self.assertIsNone(context)
        source = operators.HEADER + f"\nexample : {term} := by ext x; simp\n"
        source += 'run_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"source_rational_union\\"}"\n'
        self.assertIn("source_rational_union", c.export(source))

    def test_rational_singleton_union_rejects_wrong_cast_operand_and_index_type(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        row = next(r for r in c.occurrences(text) if r"\QQ = \bigcup" in r["book"])
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        tree = c.resolve_rational_ambient(tree, row, scopes)
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, {})
        original = c.translate
        for rule in ("coercion:rational-real", "set:indexed-union", "set:singleton"):
            with self.subTest(rule=rule):

                def corrupt(*args, rule=rule, **kwargs):
                    result = original(*args, **kwargs)
                    trace = kwargs.get("trace")
                    if trace is not None:
                        node = next(n for n in trace if n["rule"] == rule)
                        if rule == "coercion:rational-real":
                            node["expectedOperands"][0]["candidate"] += " + 1"
                        elif rule == "set:indexed-union":
                            node["expectedImplicitArguments"][1]["candidate"] = "Nat"
                        else:
                            node["expectedImplicitArguments"][0]["candidate"] = "Rat"
                    return result

                with patch.object(c, "translate", side_effect=corrupt):
                    nodes = operators.inspect(tree, variables, {})
                node = next(n for n in nodes if n["rule"] == rule)
                field = "operandStatus" if rule == "coercion:rational-real" else "implicitArgumentStatus"
                self.assertEqual(node[field], "mismatch")

    def test_rational_singleton_union_bridge_preserves_real_ambient(self):
        source = (
            operators.HEADER
            + r"""
example : Set.range ((↑) : ℚ → ℝ) = ⋃ q : ℚ, ({(q : ℝ)} : Set ℝ) := by
  ext x
  simp
example : (⋃ q : ℚ, ({(q : ℝ)} : Set ℝ)) =
    ⋃₀ Set.range (fun q : ℚ => ({(q : ℝ)} : Set ℝ)) := by
  ext x
  simp
example : IsFsigma (⋃ q : ℚ, ({(q : ℝ)} : Set ℝ)) := by
  have h : Set.range ((↑) : ℚ → ℝ) = ⋃ q : ℚ, ({(q : ℝ)} : Set ℝ) := by
    ext x
    simp
  rw [← h]
  exact PolishSpaceBook.rationals_are_fsigma
run_cmd Lean.logInfo "SORT_PILOT {\"declaration\":\"rational_singleton_bridge\"}"
"""
        )
        self.assertIn("rational_singleton_bridge", operators.chapter.export(source))

    def guarded_ball_fixture(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "alexandrov-ball-union")
        row = next(r for r in c.occurrences(text) if r"V_n \;=\; \bigcup" in r["book"])
        records = c.evidence(c.source_declarations([scope]))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        tree = c.resolve_generator_restrictions(tree, row, scopes)
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, [scope], records)
        return row, tree, variables, records, scope

    def test_guarded_ball_union_matches_source_and_original_definition(self):
        c = operators.chapter
        _row, tree, variables, records, _ = self.guarded_ball_fixture()
        self.assert_native_translation(tree, variables, records)
        self.assertTrue(all(v["status"] == "resolved" for v in variables))
        points = [v for v in variables if v["symbol"] == "x"]
        radii = [v for v in variables if v["symbol"] == r"\delta"]
        self.assertTrue(all(v["localBinder"] and v["leanType"] == "X" for v in points))
        self.assertTrue(all(v["localBinder"] and v["leanType"] == "ℝ" for v in radii))
        self.assertEqual(len({v["leanName"] for v in points + radii}), 2)
        nodes = operators.inspect(tree, variables, records)
        covered = {(n["operatorStart"], n["operatorEnd"]) for n in nodes}
        covered.update((b["start"], b["end"]) for n in nodes for b in n.get("bindingComponents", []))
        self.assertTrue(all((n["start"], n["end"]) in covered for n in operators.operator_candidates(tree)))
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            implicit = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or i in implicit for i, a in enumerate(node["elaborated"].get("arguments", [])))
            )
        diameter = next(n for n in nodes if n["rule"] == "macro:MetricDiameter")
        self.assertEqual(diameter["requirementStatus"], "proved")
        union = next(n for n in nodes if n["rule"] == "set:generated-union")
        premise = union["sourceRestriction"]["source"]
        self.assertEqual(c.SOURCE.read_text()[premise["start"] : premise["end"]], premise["text"])
        term, context = c.translate(tree, variables, records)
        proof = r"""(show TERM from by
  simp only [V, smallTrace]
  congr 1
  ext B
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, δ, hδ, hB, hs⟩
    subst B
    have h := (bookSmallTraceIff this_book_9 _ (bound n)).mp hs
    refine ⟨x, δ, hδ, ?_, rfl, ?_⟩
    · simp only [bookSubtypeSet, Set.preimage_inter, Subtype.coe_preimage_self, Set.inter_univ]
      change @Bornology.IsBounded A this_book_9.toPseudoMetricSpace.toBornology
        (((↑) : A → X) ⁻¹' Metric.ball x δ)
      exact h.1
    · simp only [bookSubtypeSet, Set.preimage_inter, Subtype.coe_preimage_self, Set.inter_univ]
      change @Metric.diam A this_book_9.toPseudoMetricSpace (((↑) : A → X) ⁻¹' Metric.ball x δ) < bound n
      exact h.2
  · rintro ⟨x, δ, hδ, hb, hB, hd⟩
    refine ⟨x, δ, hδ, hB, ?_⟩
    subst B
    apply (bookSmallTraceIff this_book_9 _ (bound n)).mpr
    simp only [bookSubtypeSet, Set.preimage_inter, Subtype.coe_preimage_self, Set.inter_univ] at hb hd
    change @Bornology.IsBounded A this_book_9.toPseudoMetricSpace.toBornology
      (((↑) : A → X) ⁻¹' Metric.ball x δ) at hb
    change @Metric.diam A this_book_9.toPseudoMetricSpace (((↑) : A → X) ⁻¹' Metric.ball x δ) < bound n at hd
    exact ⟨hb, hd⟩)""".replace("TERM", "(" + term + ")")
        source = operators.HEADER + c.expression_definition(
            {"lean": proof, "context": context}, records, "GuardedBallUnion"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"guarded_ball_union\\"}"\n'
        self.assertIn("guarded_ball_union", c.export(source))

    def test_guarded_ball_union_rejects_missing_premise_and_changed_binding(self):
        c = operators.chapter
        row, tree, variables, records, scope = self.guarded_ball_fixture()
        unguarded = dict(tree)
        unguarded.pop("generatorRestrictions")
        unknown, effects = c.leaves(unguarded)
        unknown = c.resolve_variables(unknown, effects, row, [scope], records)
        self.assertFalse(c.semantic_translation(unguarded, unknown, [], records=records)["supported"])
        with self.assertRaises(c.Unsupported):
            c.translate(unguarded, unknown, records)
        changed = copy.deepcopy(tree)
        changed["generatorRestrictions"][0]["metric"]["target"] = scope["bindings"]["d"]["target"]
        self.assertFalse(c.semantic_translation(changed, variables, [], records=records)["supported"])
        with self.assertRaisesRegex(c.Unsupported, "active metric"):
            c.translate(changed, variables, records)

    def test_guarded_ball_union_checks_the_entire_generator_predicate(self):
        c = operators.chapter
        _, tree, variables, records, _ = self.guarded_ball_fixture()
        original = c.translate

        def changed(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "binder:predicate-set" and "sourceRestriction" in node:
                    candidate = node["expectedOperands"][0]["candidate"]
                    self.assertIn(" > (0)", candidate)
                    node["expectedOperands"][0]["candidate"] = candidate.replace(" > (0)", " > (1)")
            return result

        with patch.object(c, "translate", side_effect=changed):
            nodes = operators.inspect(tree, variables, records)
        family = next(n for n in nodes if n["rule"] == "binder:predicate-set")
        self.assertEqual(family["targetStatus"], "matched")
        self.assertEqual(family["operandStatus"], "mismatch")

    def test_guarded_ball_union_cannot_prove_boundedness_without_its_guard(self):
        c = operators.chapter
        _, tree, variables, records, _ = self.guarded_ball_fixture()
        original = c.translate

        def without_guard(*args, **kwargs):
            term, context = original(*args, **kwargs)
            marker = "∃ «book_ball_bounded» : "
            start = term.index(marker)
            opening = start + len(marker)
            self.assertEqual(term[opening], "(")
            depth = 0
            for end in range(opening, len(term)):
                depth += (term[end] == "(") - (term[end] == ")")
                if depth == 0:
                    break
            self.assertEqual(term[end + 1 : end + 3], ", ")
            return term[:start] + term[end + 3 :], context

        with patch.object(c, "translate", side_effect=without_guard):
            nodes = operators.inspect(tree, variables, records)
        diameter = next(n for n in nodes if n["rule"] == "macro:MetricDiameter")
        self.assertEqual(diameter["requirementStatus"], "unresolved")

    def test_ball_union_scope_preserves_original_index_and_boundedness_metric(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "alexandrov-ball-union")
        context = c.context_reference(scope["context"])
        records = c.evidence(c.source_declarations([scope]))
        row = next(r for r in c.occurrences(text) if r"V_n \;=\; \bigcup" in r["book"])
        tree, _ = c.located(c.syntax(["V_n"])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, [scope], records)
        term, actual = c.translate(tree, variables, records)
        self.assertEqual(actual, context)
        self.assertEqual(next(v for v in variables if v["symbol"] == "n").get("indexOffset", 0), 0)
        self.assertEqual(next(v for v in variables if v["symbol"] == "V").get("indexOrigin", 0), 0)
        proof = f"(show ({term}) = V n from rfl)"
        source = operators.HEADER + c.expression_definition(
            {"lean": proof, "context": context}, records, "GeneratedBallSourceIndex"
        )
        source += c.expression_definition(
            {
                "lean": r"""(show ∀ S : Set A,
            @Metric.ediam A this_book_9.toPseudoMetricSpace.toPseudoEMetricSpace.toEDist S < ENNReal.ofReal (bound n) ↔
            @Bornology.IsBounded A this_book_9.toPseudoMetricSpace.toBornology S ∧
            @Metric.diam A this_book_9.toPseudoMetricSpace S < bound n from by
              intro S
              exact bookSmallTraceIff this_book_9 S (bound n))""",
                "context": context,
            },
            records,
            "GeneratedBallSourceMetric",
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"ball_source_scope\\"}"\n'
        self.assertIn("ball_source_scope", c.export(source))

    def test_indexed_predicate_domains_shadow_outer_bindings_and_reject_sets(self):
        import json

        c = operators.chapter
        formula = r"\bigcap_{n\in\omega}\{x\in X:d(x,F)<1/(n+1)\}"
        types = {"X": "Type", "F": "Set X", "d": "MetricSpace X", "n": "ℝ", "x": "ℝ"}
        scope = {"scope": "nested", "bindings": {name: {"symbol": name, "target": "D/" + name} for name in types}}
        text = "<!-- chapter-correspondence " + json.dumps(scope) + " -->$" + formula + "$"
        text += "<!-- chapter-correspondence-end: nested -->"
        row = c.occurrences(text)[0]
        scopes = c.scopes(text)
        for domain in ("Type", "Set ℝ"):
            records = {
                "D": {
                    "binders": [
                        {"name": name, "type": domain if name == "X" else ty, "instance": False}
                        for name, ty in types.items()
                    ]
                }
            }
            tree, _ = c.located(c.syntax([formula])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            bound = [v for v in variables if v["symbol"] in {"n", "x"}]
            self.assertTrue(all(v["localBinder"] for v in bound))
            if domain == "Type":
                self.assertTrue(all(v["status"] == "resolved" for v in variables))
                self.assertEqual({v["leanType"] for v in bound if v["symbol"] == "n"}, {"ℕ"})
                self.assertEqual({v["leanType"] for v in bound if v["symbol"] == "x"}, {"X"})
                self.assertEqual(len({v["scopeStart"] for v in bound}), 2)
            else:
                self.assertTrue(all(v["status"] == "unresolved" for v in bound))
                with self.assertRaises(c.Unsupported):
                    c.translate(tree, variables, records)

    def test_alexandrov_closed_distance_source_uses_original_cover(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "alexandrov-closed-distance")
        records = c.evidence(c.source_declarations([scope]))
        source = operators.HEADER
        seen = []
        for row in c.occurrences(text):
            if not scope["start"] <= row["start"] < scope["end"]:
                continue
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, [scope], records)
            self.assertTrue(all(v["status"] == "resolved" for v in variables), variables)
            nodes = operators.inspect(tree, variables, records)
            for node in nodes:
                self.assertEqual(node["targetStatus"], "matched")
                self.assertEqual(node["operandStatus"], "matched")
                covered = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or i in covered for i, a in enumerate(node["elaborated"].get("arguments", []))
                    )
                )
                if node["rule"] == "application:distance-to-set":
                    self.assertEqual(node["requirementStatus"], "proved")
            term, context = c.translate(tree, variables, records)
            evidence = "hne.ne_empty" if r"\ne" in row["book"] else "hcov"
            source += c.expression_definition(
                {"lean": f"(show ({term}) from {evidence})", "context": context},
                records,
                f"ClosedDistanceSource{len(seen)}",
            )
            seen.append(row["book"])
        self.assertEqual(len(seen), 2)
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"closed_distance_source\\"}"\n'
        self.assertIn("closed_distance_source", c.export(source))

    def test_alexandrov_subspace_trace_diameters_tend_to_zero(self):
        c = operators.chapter
        scope = next(s for s in c.scopes(c.SOURCE.read_text()) if s["scope"] == "alexandrov-converse-limits")
        context = c.context_reference(scope["context"])
        records = c.evidence({context})
        proof = r"""(show Filter.Tendsto
          (fun n : ℕ => @Metric.diam A this_book_9.toPseudoMetricSpace
            (((↑) : A → X) ⁻¹' (W n ∩ A))) Filter.atTop (nhds 0) from by
          have htrace : ∀ n : ℕ,
              @Bornology.IsBounded A this_book_9.toPseudoMetricSpace.toBornology
                (((↑) : A → X) ⁻¹' (W n ∩ A)) ∧
              @Metric.diam A this_book_9.toPseudoMetricSpace
                (((↑) : A → X) ⁻¹' (W n ∩ A)) < bound n := by
            intro n
            have hs : W n ⊆ U n := by
              intro y hy
              exact hy.1 (U n) ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩
            have he : (((↑) : A → X) ⁻¹' (W n ∩ A)) = ((↑) : A → X) ⁻¹' W n := by
              ext a
              change (a.val ∈ W n ∧ a.val ∈ A) ↔ a.val ∈ W n
              exact ⟨And.left, fun h => ⟨h, a.property⟩⟩
            rw [he]
            apply (bookSmallTraceIff this_book_9 _ (bound n)).mp
            exact (Metric.ediam_mono (Set.preimage_mono hs)).trans_lt (hUsmall n)
          exact squeeze_zero
            (fun n => @Metric.diam_nonneg A
              (((↑) : A → X) ⁻¹' (W n ∩ A)) this_book_9.toPseudoMetricSpace)
            (fun n => (htrace n).2.le)
            (show Filter.Tendsto bound Filter.atTop (nhds 0) from
              tendsto_one_div_add_atTop_nhds_zero_nat))"""
        source = operators.HEADER + c.expression_definition(
            {"lean": proof, "context": context}, records, "TraceDiametersLimit"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"trace_diameters_limit\\"}"\n'
        self.assertIn("trace_diameters_limit", c.export(source))

    def test_alexandrov_source_limits_preserve_subspace_and_ambient_targets(self):
        c = operators.chapter
        from proof_contexts import inspection_source

        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        outer = next(s for s in scopes if s["scope"] == "alexandrov-converse-limits")
        selected = [
            s
            for s in scopes
            if s["scope"]
            in {
                "alexandrov-converse-metrics",
                "alexandrov-converse-point",
                "alexandrov-converse-limits",
                "alexandrov-converse-ambient-limit",
            }
        ]
        found = c.export(inspection_source("PolishSpaceBook.polish_subspace_isGdelta", "hax"))
        final = next(k for k in found if "@" in k)
        records = c.evidence(c.source_declarations(selected) | {final})
        source = operators.HEADER
        seen = []
        verified = set()
        for row in c.occurrences(text):
            book = re.sub(r"\s+", " ", row["book"]).strip()
            if not outer["start"] <= row["start"] < outer["end"]:
                continue
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            tree = c.resolve_numeric_domain(tree, row, scopes)
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            self.assertTrue(all(v["status"] == "resolved" for v in variables), variables)
            nodes = operators.inspect(tree, variables, records)
            for node in nodes:
                self.assertEqual(node["targetStatus"], "matched")
                self.assertEqual(node["operandStatus"], "matched")
                covered = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or i in covered for i, a in enumerate(node["elaborated"].get("arguments", []))
                    )
                )
            term, context = c.translate(tree, variables, records)
            if book == r"\Sequence{a_n}{n\in\omega}":
                proof = f"""(show ({term}) = aSeq ∧ CauchySeq ({term}) from by
                  exact ⟨rfl, haSeq_cauchy⟩)"""
            elif book in {r"\rho", "X", "0"}:
                expected = {r"\rho": "completeMetricOnA.toMetricSpace", "X": "X", "0": "(0 : ℝ)"}[book]
                proof = f"(show ({term}) = ({expected}) from rfl)"
            elif book == r"B_n \cap A":
                proof = f"(show ({term}) = W n ∩ A from rfl)"
            elif book == r"\MetricDiameter{d}{B_n}\to 0":
                self.assertEqual(
                    next(n for n in nodes if n["rule"] == "macro:MetricDiameter")["requirementStatus"], "proved"
                )
                proof = f"""(show ({term}) from by
                  have hb : ∀ n : ℕ, Metric.diam (W n) ≤ 2 * bound n := by
                    intro n
                    have hs : W n ⊆ Metric.ball x (bound n) := Set.inter_subset_right
                    exact (Metric.diam_mono hs Metric.isBounded_ball).trans
                      (Metric.diam_ball (bound_pos n).le)
                  have ht : Filter.Tendsto (fun n : ℕ => 2 * bound n) Filter.atTop (nhds 0) := by
                    simpa only [mul_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
                  have hl := squeeze_zero (fun n => Metric.diam_nonneg (s := W n)) hb ht
                  exact hl)"""
            else:
                if book in {"a=x", r"a_n \to x", r"x \in A"}:
                    self.assertEqual(c.shared_context({context, final}, records), final)
                    context = final
                projected = any(v.get("projection") == "Subtype.val" for v in variables)
                evidence = {
                    r"a_n \to a": "ha_lim_X" if projected else "ha_lim",
                    r"a_n \to x": "hx_lim_X",
                    "a=x": "hax",
                    r"a \in A": "a.property",
                    r"a_n \in B_n": "haSeq_W n",
                    r"x \in A": "hax ▸ a.property",
                }[book]
                proof = f"(show ({term}) from {evidence})"
            if (proof, context) not in verified:
                source += c.expression_definition(
                    {"lean": proof, "context": context}, records, f"ConverseLimitSource{len(seen)}"
                )
                verified.add((proof, context))
            seen.append(book)
        self.assertEqual(seen.count(r"a_n \to a"), 2)
        self.assertEqual(len(seen), 19)
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"converse_source_limits\\"}"\n'
        self.assertIn("converse_source_limits", c.export(source))

    def test_positive_sequence_ranges_preserve_original_family_and_tail(self):
        c = operators.chapter
        source = operators.HEADER
        for i, start in enumerate([1, 2, 10]):
            row, records = self.indexed_set_fixture(
                r"\Sequence{G_n}{n\ge" + str(start) + "}", index_origin=1, index_offset=5, index_type="Nat"
            )
            nodes = operators.inspect(row["syntax"], row["variables"], records)
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
            self.assertEqual(nodes[-1]["lowering"]["sourceOrigin"], start)
            term, context = c.translate(row["syntax"], row["variables"], records)
            source += c.expression_definition(
                {
                    "lean": f"(show ({term}) = (fun k : Nat => G (k + {start - 1})) from by funext k; congr 1)",
                    "context": context,
                },
                records,
                f"PositiveSequence{i}",
            )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"positive_sequences\\"}"\n'
        self.assertIn("positive_sequences", c.export(source))
        row, records = self.indexed_set_fixture(r"\Sequence{G_n}{n\ge0}", index_origin=1)
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)

    def test_conjunction_keeps_sequence_binders_inside_their_clause(self):
        c = operators.chapter
        row, records = self.indexed_set_fixture(
            r"G_n \to x \qquad\text{and}\qquad n\ge1",
            family_type="ℕ → ℝ",
            extra_types={"x": "ℝ"},
            index_origin=1,
            index_offset=5,
            index_type="Nat",
        )
        indices = [v for v in row["variables"] if v["symbol"] == "n"]
        self.assertEqual([bool(v.get("localBinder")) for v in indices], [True, False])
        self.assertEqual([v["indexOffset"] for v in indices], [1, 5])
        nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        term, context = c.translate(row["syntax"], row["variables"], records)
        source = operators.HEADER + c.expression_definition(
            {
                "lean": f"(show ({term}) = (Filter.Tendsto G Filter.atTop (nhds x) ∧ n + 5 ≥ 1) from by simp only [Nat.add_sub_cancel])",
                "context": context,
            },
            records,
            "ConjunctionScope",
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"conjunction_scope\\"}"\n'
        self.assertIn("conjunction_scope", c.export(source))

    def test_decreasing_chain_requires_one_family_and_consecutive_indices(self):
        c = operators.chapter
        row, records = self.indexed_set_fixture(r"G_1 \supseteq G_2 \supseteq \cdots", index_origin=1)
        self.assert_native_translation(row["syntax"], row["variables"], records)
        nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(nodes[0]["targetStatus"], "matched")
        self.assertEqual(nodes[0]["operandStatus"], "matched")
        term, context = c.translate(row["syntax"], row["variables"], records)
        source = operators.HEADER + c.expression_definition(
            {"lean": f"(show ({term}) = Antitone G from by simp only [Nat.add_sub_cancel])", "context": context},
            records,
            "DecreasingChain",
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"decreasing_chain\\"}"\n'
        self.assertIn("decreasing_chain", c.export(source))
        for formula in [
            r"G_1 \supseteq G_3 \supseteq \cdots",
            r"G_0 \supseteq G_1 \supseteq \cdots",
            r"G_1 \supseteq H_2 \supseteq \cdots",
        ]:
            row, records = self.indexed_set_fixture(formula, extra_types={"H": "ℕ → Set ℝ"}, index_origin=1)
            with self.assertRaises(ValueError):
                operators.inspect(row["syntax"], row["variables"], records)

    def test_convergence_reindexes_positive_families_and_shadows_free_offset(self):
        c = operators.chapter
        source = operators.HEADER
        for i, (formula, expected) in enumerate(
            [
                (r"G_n \to x", "G"),
                (r"G_n + H_n \to x", "fun k : Nat => G k + H (k + 1)"),
            ]
        ):
            row, records = self.indexed_set_fixture(
                formula,
                family_type="ℕ → ℝ",
                extra_types={"H": "ℕ → ℝ", "x": "ℝ"},
                index_origin=1,
                index_offset=5,
                index_type="Nat",
            )
            indices = [v for v in row["variables"] if v["symbol"] == "n"]
            self.assertTrue(all(v["localBinder"] and v.get("indexOffset") == 1 for v in indices))
            nodes = operators.inspect(row["syntax"], row["variables"], records)
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
            self.assertEqual(nodes[-1]["lowering"]["sourceOrigin"], 1)
            term, context = c.translate(row["syntax"], row["variables"], records)
            source += c.expression_definition(
                {
                    "lean": f"(show ({term}) = Filter.Tendsto ({expected}) Filter.atTop (nhds x) from by simp only [Nat.add_sub_cancel])",
                    "context": context,
                },
                records,
                f"PositiveConvergence{i}",
            )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"positive_convergence\\"}"\n'
        self.assertIn("positive_convergence", c.export(source))

    def test_alexandrov_shrinking_diameter_converges_in_source_metric(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        selected = [
            s for s in scopes if s["scope"] in {"alexandrov-converse-metrics", "alexandrov-shrunk-neighborhoods"}
        ]
        records = c.evidence(c.source_declarations(selected))
        row = next(r for r in c.occurrences(text) if r["book"].startswith(r"B_0 \supseteq B_1"))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        index = next(v for v in variables if v["symbol"] == "n")
        self.assertTrue(index["localBinder"])
        self.assertEqual(index.get("indexOffset", 0), 0)
        nodes = operators.inspect(tree, variables, records)
        self.assertEqual(nodes[-1]["rule"], "logic:and")
        self.assertTrue(any(n["rule"] == "relation:decreasing-family" for n in nodes))
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            covered = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or i in covered for i, a in enumerate(node["elaborated"].get("arguments", [])))
            )
        diameter = next(n for n in nodes if n["rule"] == "macro:MetricDiameter")
        self.assertEqual(diameter["requirementStatus"], "proved")
        term, context = c.translate(tree, variables, records)
        proof = f"""(show ({term}) from by
          have hm : Antitone W := by
            intro m n hmn y hy
            constructor
            · intro T hT
              rcases hT with ⟨i, rfl⟩
              exact hy.1 (U i) ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hmn)⟩, rfl⟩
            · have hb : bound n ≤ bound m := by
                dsimp only [bound]
                gcongr
              exact (Metric.mem_ball.1 hy.2).trans_le hb
          have hb : ∀ n : ℕ, Metric.diam (W n) ≤ 2 * bound n := by
            intro n
            have hs : W n ⊆ Metric.ball x (bound n) := Set.inter_subset_right
            exact (Metric.diam_mono hs Metric.isBounded_ball).trans
              (Metric.diam_ball (bound_pos n).le)
          have ht : Filter.Tendsto (fun n : ℕ => 2 * bound n) Filter.atTop (nhds 0) := by
            simpa only [mul_zero] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
          have hl := squeeze_zero (fun n => Metric.diam_nonneg (s := W n)) hb ht
          simpa only [Nat.add_sub_cancel] using And.intro hm hl)"""
        source = operators.HEADER + c.expression_definition(
            {"lean": proof, "context": context}, records, "ShrinkingDiameterLimit"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"shrinking_diameter_limit\\"}"\n'
        self.assertIn("shrinking_diameter_limit", c.export(source))

    def test_finite_intersection_preserves_endpoints_and_reindexing(self):
        c = operators.chapter
        source = operators.HEADER
        for i, (formula, expected) in enumerate(
            [
                (r"G_1 \cap \cdots \cap G_n", "⋂ i : Fin (n + 1), G i.val"),
                (r"G_1 \cap \cdots \cap G_1", "G 0"),
                (r"G_2 \cap \cdots \cap G_3", "G 1 ∩ G 2"),
            ]
        ):
            row, records = self.indexed_set_fixture(formula, index_origin=1, index_offset=1, index_type="Nat")
            self.assert_native_translation(row["syntax"], row["variables"], records)
            nodes = operators.inspect(row["syntax"], row["variables"], records)
            self.assertEqual(len(nodes), 1)
            self.assertEqual(nodes[0]["targetStatus"], "matched")
            self.assertEqual(nodes[0]["operandStatus"], "matched")
            self.assertEqual(nodes[0]["lowering"]["kind"], "finite-natural-interval")
            term, context = c.translate(row["syntax"], row["variables"], records)
            proof = [
                "by simp only [Nat.add_sub_cancel]; rfl",
                "by ext x; simp",
                "by change (⋂ i : Fin 2, G (i.val + 2 - 1)) = G 1 ∩ G 2; ext x; simp [Fin.forall_fin_succ]",
            ][i]
            source += c.expression_definition(
                {"lean": f"(show ({term}) = ({expected}) from {proof})", "context": context},
                records,
                f"FiniteIntersection{i}",
            )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"finite_intersections\\"}"\n'
        self.assertIn("finite_intersections", c.export(source))
        for formula, offset in [
            (r"G_1 \cap \cdots \cap G_n", None),
            (r"G_3 \cap \cdots \cap G_2", 1),
            (r"G_0 \cap \cdots \cap G_n", 1),
        ]:
            row, records = self.indexed_set_fixture(formula, index_origin=1, index_offset=offset, index_type="Nat")
            with self.assertRaises(ValueError):
                operators.inspect(row["syntax"], row["variables"], records)

    def test_alexandrov_source_finite_intersection_is_the_original_W(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        selected = [
            s
            for s in scopes
            if s["scope"]
            in {"alexandrov-converse-metrics", "alexandrov-converse-point", "alexandrov-chosen-neighborhoods"}
        ]
        records = c.evidence(c.source_declarations(selected))
        row = next(r for r in c.occurrences(text) if r["book"].startswith(r"B_0 \cap \cdots \cap B_n"))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        nodes = operators.inspect(tree, variables, records)
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            covered = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or i in covered for i, a in enumerate(node["elaborated"].get("arguments", [])))
            )
        self.assertTrue(any(n.get("lowering", {}).get("kind") == "finite-natural-interval" for n in nodes))
        term, context = c.translate(tree, variables, records)
        source = operators.HEADER + c.expression_definition(
            {
                "lean": f"(show ({term}) = W N from by simp only [Nat.add_sub_cancel, W, Set.sInter_range]; rfl)",
                "context": context,
            },
            records,
            "SourceFiniteIntersection",
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"source_finite_intersection\\"}"\n'
        self.assertIn("source_finite_intersection", c.export(source))

    def test_finite_intersection_rejects_other_family_and_wrong_endpoint(self):
        row, records = self.indexed_set_fixture(
            r"G_1 \cap \cdots \cap H_n",
            extra_types={"H": "ℕ → Set ℝ"},
            index_origin=1,
            index_offset=1,
            index_type="Nat",
        )
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)
        row, records = self.indexed_set_fixture(
            r"G_1 \cap \cdots \cap G_n", index_origin=1, index_offset=1, index_type="Nat"
        )
        original = operators.chapter.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node.get("lowering", {}).get("kind") == "finite-natural-interval":
                    node["expectedImplicitArguments"][1]["candidate"] = "Fin n"
            return result

        with patch.object(operators.chapter, "translate", side_effect=wrong):
            nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(nodes[0]["targetStatus"], "matched")
        self.assertEqual(nodes[0]["implicitArgumentChecks"][1]["status"], "mismatch")

    def test_repeated_binary_union_uses_the_same_range_and_checks_its_lattice(self):
        c = operators.chapter
        formula = r"G_1 \cup \cdots \cup G_n"
        row, records = self.indexed_set_fixture(formula, index_origin=1, index_offset=1, index_type="Nat")
        native = self.assert_native_translation(row["syntax"], row["variables"], records)
        self.assertEqual(native["rendering"]["mappings"][-1]["expectedConstant"], "iSup")
        nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(len(nodes), 1)
        self.assertEqual(nodes[0]["rule"], "set:indexed-union")
        self.assertEqual(nodes[0]["targetStatus"], "matched")
        self.assertEqual(nodes[0]["operandStatus"], "matched")
        term, context = c.translate(row["syntax"], row["variables"], records)
        proof = f"(show ({term}) = (⋃ i : Fin (n + 1), G i.val) from by simp only [Nat.add_sub_cancel]; rfl)"
        source = operators.HEADER + c.expression_definition(
            {"lean": proof, "context": context}, records, "RepeatedBinaryUnion"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"repeated_union\\"}"\n'
        self.assertIn("repeated_union", c.export(source))
        original = c.translate

        def wrong_lattice(*args, **kwargs):
            result = original(*args, **kwargs)
            for mapping in kwargs.get("trace") or []:
                if mapping["rule"] == "set:indexed-union":
                    mapping["expectedImplicitArguments"][2]["candidate"] = "(inferInstance : InfSet (Set Real))"
            return result

        with patch.object(c, "translate", side_effect=wrong_lattice):
            altered = operators.inspect(row["syntax"], row["variables"], records)[0]
        self.assertEqual(altered["targetStatus"], "matched")
        self.assertEqual(altered["implicitArgumentStatus"], "mismatch")
        for unsupported in (r"G_1 \cup \cdots \cup G_0", r"G_1 \cup \cdots \cap G_n", r"G_1 - \cdots - G_n"):
            row, records = self.indexed_set_fixture(unsupported, index_origin=1, index_offset=1, index_type="Nat")
            self.assertFalse(c.semantic_translation(row["syntax"], row["variables"], [], records=records)["supported"])

    def test_explicit_metric_ball_checks_metric_center_and_real_radius(self):
        nodes = inspect_formula(r"\MetricBall{d}{x}{1/n}", {"d": "MetricSpace ℝ", "x": "ℝ", "n": "Nat"})
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        self.assertEqual(nodes[-1]["rule"], "macro:MetricBall")
        self.assertEqual(len(nodes[-1]["implicitArgumentChecks"]), 2)
        membership = inspect_formula(
            r"y \in \MetricBall{d}{x}{1/n}", {"d": "MetricSpace ℝ", "x": "ℝ", "y": "ℝ", "n": "Nat"}
        )
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in membership))
        with self.assertRaises(ValueError):
            inspect_formula(r"\MetricBall{d}{x}{1/n}", {"d": "ℝ → ℝ → ℝ", "x": "ℝ", "n": "Nat"})
        with self.assertRaises(ValueError):
            inspect_formula(r"\MetricBall{d}{x}{1/n}", {"d": "MetricSpace ℝ", "x": "Bool", "n": "Nat"})

    def test_explicit_metric_ball_rejects_another_metric_on_the_same_carrier(self):
        original = operators.chapter.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "macro:MetricBall":
                    node["expectedImplicitArguments"][1]["candidate"] = "(inferInstance : PseudoMetricSpace Real)"
            return result

        with patch.object(operators.chapter, "translate", side_effect=wrong):
            nodes = inspect_formula(r"\MetricBall{d}{x}{1/n}", {"d": "MetricSpace ℝ", "x": "ℝ", "n": "Nat"})
        ball = nodes[-1]
        self.assertEqual(ball["targetStatus"], "matched")
        self.assertEqual(ball["implicitArgumentChecks"][1]["status"], "mismatch")

    def test_alexandrov_source_metric_ball_matches_shrinking_definition(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        selected = [
            s
            for s in scopes
            if s["scope"]
            in {"alexandrov-converse-metrics", "alexandrov-converse-point", "alexandrov-chosen-neighborhoods"}
        ]
        records = c.evidence(c.source_declarations(selected))
        row = next(r for r in c.occurrences(text) if r["book"].startswith(r"B_0 \cap \cdots \cap B_n"))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        ball = next(t for t in tree["items"] if t.get("name") == "MetricBall")
        variables, effects = c.leaves(ball)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        nodes = operators.inspect(ball, variables, records)
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            covered = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or i in covered for i, a in enumerate(node["elaborated"].get("arguments", [])))
            )
        term, context = c.translate(ball, variables, records)
        proofs = {
            "Ball": f"(show ({term}) = Metric.ball x (bound N) from rfl)",
            "FiniteIntersection": f"""(show
              (⋂ i : Fin (N + 1), U i.val) ∩ ({term}) = W N from by
              simp only [W, Set.sInter_range]
              rfl)""",
        }
        source = operators.HEADER
        for name, proof in proofs.items():
            source += c.expression_definition({"lean": proof, "context": context}, records, "ShrinkingSource" + name)
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"shrinking_source_ball\\"}"\n'
        self.assertIn("shrinking_source_ball", c.export(source))

    def test_set_relations_ignore_only_terminal_sentence_punctuation(self):
        for formula, types in [
            (r"x \in A.", {"x": "ℝ", "A": "Set ℝ"}),
            (r"A \IncludedIn B,", {"A": "Set ℝ", "B": "Set ℝ"}),
        ]:
            nodes = inspect_formula(formula, types)
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
            self.assertEqual(nodes[-1]["end"], len(formula) - 1)
        with self.assertRaises(ValueError):
            inspect_formula(r"x \in A,B", {"x": "ℝ", "A": "Set ℝ", "B": "Set ℝ"})

    def test_alexandrov_reverse_point_is_original_membership_witness(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        outer = next(s for s in scopes if s["scope"] == "alexandrov-converse-metrics")
        point = next(s for s in scopes if s["scope"] == "alexandrov-converse-point")
        records = c.evidence(c.source_declarations([outer, point]))
        rows = [
            r
            for r in c.occurrences(text)
            if point["start"] <= r["start"] < point["end"] and r["book"].startswith(r"x \in \AmbientClosure{X}{A}")
        ]
        self.assertEqual(len(rows), 2)
        source = operators.HEADER
        for i, row in enumerate(rows):
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            nodes = operators.inspect(tree, variables, records)
            for node in nodes:
                self.assertEqual(node["targetStatus"], "matched")
                self.assertEqual(node["operandStatus"], "matched")
                checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or j in checked for j, a in enumerate(node["elaborated"].get("arguments", []))
                    )
                )
            term, context = c.translate(tree, variables, records)
            proof = "hx_closure"
            if r"\bigcap" in row["book"]:
                proof = r"""by
                  change x ∈ closure A ∩ ⋂ n, V n
                  exact hx"""
            source += c.expression_definition(
                {"lean": f"(show ({term}) from {proof})", "context": context}, records, f"SourceReversePoint{i}"
            )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"source_reverse_point\\"}"\n'
        self.assertIn("source_reverse_point", c.export(source))

    def test_alexandrov_source_set_identities_follow_original_proof(self):
        c = operators.chapter
        from proof_contexts import inspection_source

        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "alexandrov-converse-metrics")
        found = c.export(inspection_source("PolishSpaceBook.polish_subspace_isGdelta", "h_eq"))
        final_context = next(name for name in found if "@" in name)
        records = c.evidence(c.source_declarations([scope]) | {final_context})
        rows = [
            r
            for r in c.occurrences(text)
            if scope["start"] <= r["start"] < scope["end"]
            and r"\bigcap_{n\in\omega}" in r["book"]
            and ("=" in r["book"] or r"\IncludedIn" in r["book"])
        ]
        self.assertEqual(len(rows), 3)
        source = operators.HEADER
        for i, row in enumerate(rows):
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            term, context = c.translate(tree, variables, records)
            self.assertEqual(c.shared_context({context, final_context}, records), final_context)
            relation = "⊆" if r"\IncludedIn" in row["book"] else "="
            finish = "exact h_eq" if relation == "=" else "exact fun x hx => ⟨subset_closure hx, hA_subset_V hx⟩"
            proof = f"(show ({term}) from by {finish})"
            source += c.expression_definition(
                {"lean": proof, "context": final_context}, records, f"SourceConverseIdentity{i}"
            )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"source_converse_identities\\"}"\n'
        self.assertIn("source_converse_identities", c.export(source))

    def test_alexandrov_zero_based_intersection_uses_original_V(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "alexandrov-converse-metrics")
        records = c.evidence(c.source_declarations([scope]))
        rows = [
            r
            for r in c.occurrences(text)
            if scope["start"] <= r["start"] < scope["end"] and r["book"] == r"\bigcap_{n\in\omega} V_n"
        ]
        self.assertTrue(rows)
        source = operators.HEADER
        for i, row in enumerate(rows):
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            nodes = operators.inspect(tree, variables, records)
            for node in nodes:
                self.assertEqual(node["targetStatus"], "matched")
                self.assertEqual(node["operandStatus"], "matched")
                checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or j in checked for j, a in enumerate(node["elaborated"].get("arguments", []))
                    )
                )
            term, context = c.translate(tree, variables, records)
            proof = f"(show ({term}) = ⋂ n, V n from rfl)"
            source += c.expression_definition({"lean": proof, "context": context}, records, f"SourcePositiveV{i}")
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"source_positive_V\\"}"\n'
        self.assertIn("source_positive_V", c.export(source))

    def test_subspace_diameter_checks_boundedness_and_lifted_set(self):
        c = operators.chapter
        tree, _ = c.located(c.syntax([r"\MetricDiameter{\rho}{B \cap A}"])[0]["tree"])
        variables, _ = c.leaves(tree)
        types = {
            "A": "Set ℝ",
            "B": "Set ℝ",
            "m": "MetricSpace ↑A",
            "hb": "@Bornology.IsBounded A m.toPseudoMetricSpace.toBornology (Subtype.val ⁻¹' (B ∩ A))",
        }
        for v in variables:
            name = "m" if v["symbol"] == r"\rho" else v["symbol"]
            v.update(
                id="fixture/" + v["symbol"],
                status="resolved",
                declaration="D",
                leanName=name,
                leanType=types[name],
                formulaOffset=v["start"],
            )
        records = {"D": {"binders": [{"name": n, "type": t, "instance": False} for n, t in types.items()]}}
        nodes = operators.inspect(tree, variables, records)
        diameter = next(n for n in nodes if n["rule"] == "macro:MetricDiameter")
        self.assertEqual(diameter["operandStatus"], "matched")
        self.assertEqual(diameter["implicitArgumentStatus"], "matched")
        self.assertEqual(diameter["requirementStatus"], "proved")
        self.assertTrue(all(r["kernelChecked"] for r in diameter["semanticRequirements"]))
        original = c.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "macro:MetricDiameter":
                    node["expectedOperands"][0]["candidate"] = "(∅ : Set A)"
            return result

        with patch.object(c, "translate", side_effect=wrong):
            nodes = operators.inspect(tree, variables, records)
        self.assertEqual(next(n for n in nodes if n["rule"] == "macro:MetricDiameter")["operandStatus"], "mismatch")

    def test_metric_diameter_lifts_only_contained_subspace_sets(self):
        nodes = inspect_formula(
            r"\MetricDiameter{\rho}{B \cap A}", {"A": "Set ℝ", "B": "Set ℝ", r"\rho": "MetricSpace ↑A"}
        )
        diameter = next(n for n in nodes if n["rule"] == "macro:MetricDiameter")
        self.assertEqual(diameter["targetStatus"], "matched")
        self.assertEqual(diameter["operandStatus"], "matched")
        containment = next(r for r in diameter["semanticRequirements"] if r["kind"] == "metric-subspace-containment")
        self.assertEqual(containment["status"], "proved")
        self.assertTrue(containment["kernelChecked"])
        # Containment does not supply boundedness in an independently chosen metric.
        self.assertEqual(diameter["requirementStatus"], "unresolved")
        with self.assertRaises(ValueError):
            inspect_formula(r"\MetricDiameter{\rho}{B \cup A}", {"A": "Set ℝ", "B": "Set ℝ", r"\rho": "MetricSpace ↑A"})

    def test_alexandrov_converse_source_metrics_are_the_original_choices(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "alexandrov-converse-metrics")
        records = c.evidence(c.source_declarations([scope]))
        source = operators.HEADER
        seen = []
        verified = set()
        for row in c.occurrences(text):
            if not scope["start"] <= row["start"] < scope["end"] or row["book"] not in {"d", r"\rho"}:
                continue
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            self.assertTrue(all(v["status"] == "resolved" for v in variables))
            term, context = c.translate(tree, variables, records)
            seen.append(row["book"])
            if (term, context) in verified:
                continue
            verified.add((term, context))
            original = "completeMetricOnX" if row["book"] == "d" else "completeMetricOnA"
            carrier = "X" if row["book"] == "d" else "A"
            source += c.expression_definition(
                {"lean": f"(show ({term}) = {original}.toMetricSpace from rfl)", "context": context},
                records,
                f"ConverseSourceMetric{len(seen)}",
            )
            source += c.expression_definition(
                {
                    "lean": f"(show ({term}).toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace {carrier}) from rfl)",
                    "context": context,
                },
                records,
                f"ConverseSourceTopology{len(seen)}",
            )
        self.assertEqual(set(seen), {"d", r"\rho"})
        self.assertGreaterEqual(len(seen), 10)
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"converse_metrics\\"}"\n'
        self.assertIn("converse_metrics", c.export(source))

    def test_real_diameter_bridge_retains_boundedness(self):
        source = (
            operators.HEADER
            + r"""
example {Y : Type} [MetricSpace Y] (S : Set Y) (h : ¬ Bornology.IsBounded S) :
    Metric.diam S < 1 ∧ ¬ Metric.ediam S < ENNReal.ofReal 1 := by
  constructor
  · rw [Metric.diam_eq_zero_of_unbounded h]
    norm_num
  · intro hs
    exact h ((bookSmallTraceIff (inferInstance : MetricSpace Y) S 1).1 hs).1
"""
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"boundedness_required\\"}"\n'
        self.assertIn("boundedness_required", operators.chapter.export(source))

    def test_alexandrov_converse_real_diameter_and_positive_reindexing(self):
        c = operators.chapter
        from proof_contexts import inspection_source

        found = c.export(inspection_source("PolishSpaceBook.polish_subspace_isGdelta", "hVopen"))
        context = next(name for name in found if "@" in name)
        records = c.evidence({context})
        proofs = {
            "RealDiameter": r"""(show ∀ (S : Set X) (n : ℕ), smallTrace S n ↔
                @Bornology.IsBounded A completeMetricOnA.toPseudoMetricSpace.toBornology (((↑) : A → X) ⁻¹' S) ∧
                Metric.diam (((↑) : A → X) ⁻¹' S) < bound n from by
              intro S n
              exact bookSmallTraceIff completeMetricOnA.toMetricSpace _ (bound n))""",
            "PositiveBound": r"""(show ∀ k : {n : ℕ // 1 ≤ n},
                bound (k.val - 1) = 1 / (k.val : ℝ) from by
              intro k
              have hk : k.val - 1 + 1 = k.val := Nat.sub_add_cancel k.property
              have hc : ((k.val - 1 : ℕ) : ℝ) + 1 = (k.val : ℝ) := by exact_mod_cast hk
              dsimp only [bound]
              rw [hc])""",
            "PositiveIntersection": r"""(show
                (⋂ k : {n : ℕ // 1 ≤ n}, V (k.val - 1)) = ⋂ n, V n from by
              ext x
              simp only [Set.mem_iInter]
              constructor
              · intro h n
                simpa only [Nat.add_sub_cancel] using h ⟨n + 1, by omega⟩
              · intro h k
                exact h (k.val - 1))""",
            "SubspaceTrace": r"""(show ∀ S : Set X,
                (((↑) : A → X) ⁻¹' (S ∩ A)) = ((↑) : A → X) ⁻¹' S from by
              intro S
              ext a
              simp only [Set.mem_preimage, Set.mem_inter_iff, a.property, and_true])""",
            "MetricSubspaceTrace": r"""(show ∀ S : Set X,
                (bookMetricSet% (completeMetricOnA.toMetricSpace), (S ∩ A)) =
                  ((↑) : A → X) ⁻¹' S from by
              intro S
              ext a
              change (a.val ∈ S ∧ a.val ∈ A) ↔ a.val ∈ S
              exact ⟨And.left, fun h => ⟨h, a.property⟩⟩)""",
        }
        proofs["PositiveOpenFamily"] = r"""(show ∀ k : {n : ℕ // 1 ≤ n},
            V (k.val - 1) = ⋃₀ {B : Set X | ∃ x : X, ∃ δ > 0,
              B = Metric.ball x δ ∧
              @Bornology.IsBounded A completeMetricOnA.toPseudoMetricSpace.toBornology
                (((↑) : A → X) ⁻¹' B) ∧
              Metric.diam (((↑) : A → X) ⁻¹' B) < 1 / (k.val : ℝ)} from by
            have hsmall := SMALL_TRACE_BRIDGE
            have hbound := POSITIVE_BOUND_BRIDGE
            intro k
            ext x
            simp only [V, hsmall, hbound k])""".replace("SMALL_TRACE_BRIDGE", proofs["RealDiameter"]).replace(
            "POSITIVE_BOUND_BRIDGE", proofs["PositiveBound"]
        )
        proofs["PositiveGeneratedBallFamily"] = (
            r"""(show ∀ k : {n : ℕ // 1 ≤ n},
            V (k.val - 1) = ⋃₀ {B : Set X | ∃ x : X, ∃ δ > 0,
              B = Metric.ball x δ ∧
              @Bornology.IsBounded A completeMetricOnA.toPseudoMetricSpace.toBornology
                (((↑) : A → X) ⁻¹' (Metric.ball x δ ∩ A)) ∧
              Metric.diam (((↑) : A → X) ⁻¹' (Metric.ball x δ ∩ A)) < 1 / (k.val : ℝ)} from by
            have hsmall := SMALL_TRACE_BRIDGE
            have hbound := POSITIVE_BOUND_BRIDGE
            have htrace := SUBSPACE_TRACE_BRIDGE
            intro k
            simp only [V, hsmall, hbound k, htrace]
            congr 1
            ext B
            simp only [Set.mem_ofPred_eq]
            constructor <;> rintro ⟨x, δ, hδ, hB, hb, hd⟩ <;> subst B <;>
              exact ⟨x, δ, hδ, rfl, hb, hd⟩)""".replace("SMALL_TRACE_BRIDGE", proofs["RealDiameter"])
            .replace("POSITIVE_BOUND_BRIDGE", proofs["PositiveBound"])
            .replace("SUBSPACE_TRACE_BRIDGE", proofs["SubspaceTrace"])
        )
        source = operators.HEADER
        for suffix, proof in proofs.items():
            source += c.expression_definition({"lean": proof, "context": context}, records, "Converse" + suffix)
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"converse_bridges\\"}"\n'
        self.assertIn("converse_bridges", c.export(source))

    def test_alexandrov_shrinking_neighborhoods_retain_source_conditions(self):
        c = operators.chapter
        from proof_contexts import inspection_source

        found = c.export(inspection_source("PolishSpaceBook.polish_subspace_isGdelta", "haSeq_W"))
        context = next(name for name in found if "@" in name)
        records = c.evidence({context})
        subset = r"""(show ∀ n : ℕ, W n ⊆ U n from by
          intro n y hy
          exact hy.1 (U n) ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩)"""
        proofs = {
            "TraceSubset": subset,
            "Decreasing": r"""(show ∀ m n : ℕ, m ≤ n → W n ⊆ W m from by
              intro m n hmn y hy
              constructor
              · intro T hT
                rcases hT with ⟨i, rfl⟩
                exact hy.1 (U i) ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hmn)⟩, rfl⟩
              · have hbound : bound n ≤ bound m := by
                  dsimp only [bound]
                  gcongr
                exact (Metric.mem_ball.1 hy.2).trans_le hbound)""",
            "AmbientDiameter": r"""(show ∀ n : ℕ,
                Bornology.IsBounded (W n) ∧ Metric.diam (W n) ≤ 2 * bound n from by
              intro n
              have hs : W n ⊆ Metric.ball x (bound n) := Set.inter_subset_right
              exact ⟨Metric.isBounded_ball.subset hs,
                (Metric.diam_mono hs Metric.isBounded_ball).trans
                  (Metric.diam_ball (bound_pos n).le)⟩)""",
            "TraceDiameter": r"""(show ∀ n : ℕ,
                @Bornology.IsBounded A completeMetricOnA.toPseudoMetricSpace.toBornology
                  (((↑) : A → X) ⁻¹' W n) ∧
                Metric.diam (((↑) : A → X) ⁻¹' W n) < bound n from by
              intro n
              apply (bookSmallTraceIff completeMetricOnA.toMetricSpace _ (bound n)).mp
              have hs := TRACE_SUBSET
              exact (Metric.ediam_mono (Set.preimage_mono (hs n))).trans_lt (hUsmall n))""".replace(
                "TRACE_SUBSET", subset
            ),
            "SelectedPoint": r"""(show ∀ n : ℕ, (aSeq n : X) ∈ W n ∩ A from by
              intro n
              exact ⟨haSeq_W n, (aSeq n).property⟩)""",
        }
        source = operators.HEADER
        for suffix, proof in proofs.items():
            source += c.expression_definition({"lean": proof, "context": context}, records, "Shrinking" + suffix)
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"shrinking_bridges\\"}"\n'
        self.assertIn("shrinking_bridges", c.export(source))

    def test_alexandrov_source_neighborhoods_use_the_original_families(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        selected = [
            s for s in scopes if s["scope"] in {"alexandrov-chosen-neighborhoods", "alexandrov-shrunk-neighborhoods"}
        ]
        ancestors = [s for s in scopes if s["scope"] in {"alexandrov-converse-metrics", "alexandrov-converse-point"}]
        records = c.evidence(c.source_declarations(selected + ancestors))
        source = operators.HEADER
        seen = []
        for row in c.occurrences(text):
            owner = next((s for s in selected if s["start"] <= row["start"] < s["end"]), None)
            if owner is None or row["book"] not in {"B_n", r"n \in \omega", r"a_n \in B_n \cap A"}:
                continue
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            self.assertTrue(all(v["status"] == "resolved" for v in variables))
            nodes = operators.inspect(tree, variables, records)
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
            for node in nodes:
                covered = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or i in covered for i, a in enumerate(node["elaborated"].get("arguments", []))
                    )
                )
            term, context = c.translate(tree, variables, records)
            family = "U" if owner["scope"] == "alexandrov-chosen-neighborhoods" else "W"
            checked = f"(show ({term}) = ({family} N) from rfl)"
            if row["book"] == r"n \in \omega":
                checked = f"(show ({term}) from Set.mem_univ N)"
            if row["book"] == r"a_n \in B_n \cap A":
                checked = f"""(show ({term}) from by
                  simpa only [Nat.add_sub_cancel] using
                    (show (aSeq N : X) ∈ W N ∩ A from
                      ⟨(Classical.choose_spec (hA_W_nonempty N)).2, (aSeq N).property⟩))"""
            source += c.expression_definition(
                {"lean": checked, "context": context},
                records,
                f"SourceNeighborhood{len(seen)}",
            )
            seen.append((owner["scope"], row["book"]))
        self.assertIn(("alexandrov-chosen-neighborhoods", r"n \in \omega"), seen)
        self.assertIn(("alexandrov-chosen-neighborhoods", "B_n"), seen)
        self.assertIn(("alexandrov-shrunk-neighborhoods", "B_n"), seen)
        self.assertIn(("alexandrov-shrunk-neighborhoods", r"a_n \in B_n \cap A"), seen)
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"source_neighborhoods\\"}"\n'
        self.assertIn("source_neighborhoods", c.export(source))

    def test_alexandrov_source_diameter_uses_original_small_trace(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        selected = [
            s for s in scopes if s["scope"] in {"alexandrov-converse-metrics", "alexandrov-chosen-neighborhoods"}
        ]
        records = c.evidence(c.source_declarations(selected))
        row = next(r for r in c.occurrences(text) if r["book"] == r"\MetricDiameter{\rho}{B_n \cap A} < 1/(n+1).")
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        nodes = operators.inspect(tree, variables, records)
        self.assertEqual(len(nodes), 6)
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            covered = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or i in covered for i, a in enumerate(node["elaborated"].get("arguments", [])))
            )
        diameter = next(n for n in nodes if n["rule"] == "macro:MetricDiameter")
        self.assertEqual(diameter["requirementStatus"], "proved")
        self.assertEqual(
            {r["kind"] for r in diameter["semanticRequirements"]}, {"bounded-set", "metric-subspace-containment"}
        )
        self.assertTrue(all(r["kernelChecked"] for r in diameter["semanticRequirements"]))
        term, context = c.translate(tree, variables, records)
        proof = f"""(show ({term}) from by
          have hd := ((bookSmallTraceIff this_book_9
            (((↑) : A → X) ⁻¹' U N) (bound N)).mp (hUsmall N)).2
          simp only [bookSubtypeSet, Set.preimage_inter, Subtype.coe_preimage_self,
            Set.inter_univ]
          change @Metric.diam A this_book_9.toPseudoMetricSpace (((↑) : A → X) ⁻¹' U N) < 1 / ((N : ℝ) + 1)
          exact hd)"""
        source = operators.HEADER + c.expression_definition(
            {"lean": proof, "context": context}, records, "SourceTraceDiameter"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"source_trace_diameter\\"}"\n'
        self.assertIn("source_trace_diameter", c.export(source))

    def typed_map_fixture(self, function_type="↑A → (n : ℕ) → ↑(U n)"):
        import json

        c = operators.chapter
        bindings = {name: {"symbol": name, "target": "D/" + name} for name in ["A", "U", "f", "x"]}
        text = "<!-- chapter-correspondence " + json.dumps({"scope": "typed", "bindings": bindings}) + " -->"
        text += r"$f : A \to \prod_n U_n,\qquad f(x)=\Tuple{x,x,\ldots}$"
        text += "<!-- chapter-correspondence-end: typed -->"
        types = [
            ("A", "Set ℝ"),
            ("B", "Set ℝ"),
            ("U", "ℕ → Set ℝ"),
            ("h", "∀ n, A ⊆ U n"),
            ("f", function_type),
            ("g", "↑A → (n : ℕ) → ↑(U n)"),
            ("x", "ℤ"),
        ]
        records = {"D": {"binders": [{"name": n, "type": t, "instance": False} for n, t in types]}}
        row = c.report(text, c.scopes(text), records, trusted=False)["formulas"][0]
        return row, records

    def test_typed_map_shadows_outer_input_and_checks_signature(self):
        row, records = self.typed_map_fixture()
        inputs = [v for v in row["variables"] if v["symbol"] == "x"]
        self.assertTrue(all(v["localBinder"] and v["leanType"] == "Subtype «A»" for v in inputs))
        nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        row, records = self.typed_map_fixture("↑B → (n : ℕ) → ↑(U n)")
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)

    def test_native_typed_map_checks_subspace_domain_and_shadows_outer_point(self):
        import json

        c = operators.chapter
        bindings = {name: {"symbol": name, "target": "D/" + name} for name in ["A", "f", "x"]}
        text = "<!-- chapter-correspondence " + json.dumps({"scope": "typed", "bindings": bindings}) + " -->"
        text += r"$f:A\to\R, f(x)=f(x)$<!-- chapter-correspondence-end: typed -->"
        for function_type, valid in (("↑A → ℝ", True), ("↑B → ℝ", False)):
            records = {
                "D": {
                    "binders": [
                        {"name": name, "type": ty, "instance": False}
                        for name, ty in [("A", "Set ℝ"), ("B", "Set ℝ"), ("f", function_type), ("x", "ℤ")]
                    ]
                }
            }
            row = c.report(text, c.scopes(text), records, trusted=False)["formulas"][0]
            inputs = [v for v in row["variables"] if v["symbol"] == "x"]
            self.assertTrue(all(v["localBinder"] and v["leanType"] == "Subtype «A»" for v in inputs))
            native = c.semantic_translation(row["syntax"], row["variables"], [], constants=c.CONSTANTS)
            self.assertTrue(native["supported"], native)
            if valid:
                nodes = operators.inspect(row["syntax"], row["variables"], records)
                self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
            else:
                with self.assertRaises(ValueError):
                    operators.inspect(row["syntax"], row["variables"], records)

    def test_typed_map_checks_domain_codomain_and_function_independently(self):
        c = operators.chapter
        row, records = self.typed_map_fixture()
        original = c.translate
        for rule, index, candidate in [
            ("type:function-arrow", 0, "ℝ"),
            ("type:function-arrow", 1, "ℤ"),
            ("declaration:function-type", 1, "g"),
        ]:

            def wrong(*args, _rule=rule, _index=index, _candidate=candidate, **kwargs):
                result = original(*args, **kwargs)
                for node in kwargs.get("trace") or []:
                    if node["rule"] == _rule:
                        node["expectedOperands"][_index]["candidate"] = _candidate
                return result

            with patch.object(c, "translate", side_effect=wrong):
                nodes = operators.inspect(row["syntax"], row["variables"], records)
            node = next(n for n in nodes if n["rule"] == rule)
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "mismatch")

    def test_alexandrov_typed_diagonal_definition(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "alexandrov-forward")
        records = c.evidence(c.source_declarations([scope]))
        row = next(r for r in c.occurrences(text) if r"\iota : A" in r["book"])
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        self.assertTrue(all(v["status"] == "resolved" for v in variables))
        inputs = [v for v in variables if v["symbol"] == "x"]
        self.assertEqual(len(inputs), 4)
        self.assertTrue(all(v["localBinder"] for v in inputs))
        self.assertEqual(len({v["leanName"] for v in inputs}), 1)
        nodes = operators.inspect(tree, variables, records)
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched", node["rule"])
            self.assertEqual(node["operandStatus"], "matched", node["rule"])
            checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or i in checked for i, a in enumerate(node["elaborated"].get("arguments", [])))
            )
        term, context = c.translate(tree, variables, records)
        source = operators.HEADER + c.expression_definition(
            {
                "lean": f"(show ({term}) from ⟨True.intro, by intro x; funext n; simp only [ite_self]; rfl⟩)",
                "context": context,
            },
            records,
            "AlexandrovTypedDiagonal",
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"typed_diagonal\\"}"\n'
        self.assertIn("typed_diagonal", c.export(source))

    def test_repeated_tuple_checks_body_and_index_type_independently(self):
        c = operators.chapter
        original = c.translate
        for index, candidate in [(0, "(0 : ℝ)"), (1, "ℤ")]:

            def wrong(*args, _index=index, _candidate=candidate, **kwargs):
                result = original(*args, **kwargs)
                for node in kwargs.get("trace") or []:
                    if node["rule"] == "binder:repeated-tuple":
                        node["expectedOperands"][_index]["candidate"] = _candidate
                return result

            with patch.object(c, "translate", side_effect=wrong):
                nodes = inspect_formula(r"f(x)=\Tuple{x,x,\ldots}", {"f": "ℝ → ℕ → ℝ", "x": "ℝ"})
            node = next(n for n in nodes if n["rule"] == "binder:repeated-tuple")
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "mismatch")

    def test_repeated_tuple_constructs_coordinates_and_rejects_ambiguous_ellipsis(self):
        c = operators.chapter
        with self.assertRaises(ValueError):
            inspect_formula(r"f(x)=\Tuple{x}", {"f": "ℝ → ℕ → ℝ", "x": "ℝ"})
        source = (
            operators.HEADER
            + """
example (x : ℝ) (f : ℕ → ℝ) :
    (bookRepeatedTuple% (f), [x, x, x]) = (fun _ : ℕ => x) := by
  funext n
  simp only [ite_self]
"""
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"repeated_tuple\\"}"\n'
        self.assertIn("repeated_tuple", c.export(source))
        for binders, points, result_type in [
            ("(x y : ℝ) (f : ℕ → ℝ)", "x, y", "ℕ → ℝ"),
            ("(x : ℝ) (f : ℕ → ℝ)", "x", "ℕ → ℝ"),
            ("(x : ℝ) (f : ℤ → ℝ)", "x, x", "ℤ → ℝ"),
            ("(A B : Set ℝ) (x : A) (f : ℕ → B)", "x, x", "ℕ → B"),
        ]:
            source = operators.HEADER
            source += f"\nexample {binders} : {result_type} := bookRepeatedTuple% (f), [{points}]\n"
            source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"bad_tuple\\"}"\n'
            with self.subTest(binders=binders), self.assertRaises(ValueError):
                c.export(source)

    def test_convergence_subspace_conversion_requires_inclusion(self):
        for binders, succeeds in [
            ("(A B : Set ℝ) (h : A ⊆ B) (x : A) (b : B)", True),
            ("(A B : Set ℝ) (x : A) (b : B)", False),
            ("(A B : Set ℝ) (h : B ⊆ A) (x : A) (b : B)", False),
            ("(A : Set ℕ) (B : Set ℝ) (x : A) (b : B)", False),
        ]:
            source = operators.HEADER
            source += f"\nexample {binders} : B := bookConvergencePoint% (b), (x)\n"
            source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"subspace_convergence\\"}"\n'
            with self.subTest(binders=binders):
                if succeeds:
                    self.assertIn("subspace_convergence", operators.chapter.export(source))
                else:
                    with self.assertRaises(ValueError):
                        operators.chapter.export(source)

    def test_subtype_argument_checks_the_promoted_point_independently(self):
        c = operators.chapter
        tree, _ = c.located(c.syntax(["f(x)"])[0]["tree"])
        variables, _ = c.leaves(tree)
        types = {"A": "Set ℝ", "f": "↑A → ℝ", "x": "ℝ", "hx": "x ∈ A", "y": "ℝ", "hy": "y ∈ A"}
        for variable in variables:
            variable.update(
                id="fixture/" + variable["symbol"],
                status="resolved",
                declaration="D",
                leanName=variable["symbol"],
                leanType=types[variable["symbol"]],
                formulaOffset=variable["start"],
            )
        records = {"D": {"binders": [{"name": n, "type": t, "instance": False} for n, t in types.items()]}}
        original = c.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "application:subtype-argument":
                    node["expectedOperands"][0]["candidate"] = "(⟨y, hy⟩ : A)"
            return result

        with patch.object(c, "translate", side_effect=wrong):
            nodes = operators.inspect(tree, variables, records)
        self.assertEqual(nodes[0]["targetStatus"], "matched")
        self.assertEqual(nodes[0]["operandStatus"], "mismatch")
        self.assertEqual(nodes[0]["requirementStatus"], "proved")

    def test_subtype_argument_requires_membership_of_the_actual_point(self):
        c = operators.chapter
        cases = [
            ("(A : Set ℝ) (f : A → ℝ) (x : ℝ) (hx : x ∈ A)", "rfl", True),
            ("(A : Set ℝ) (f : A → ℝ) (x : ℝ)", "rfl", False),
            ("(A : Set ℝ) (f : A → ℝ) (x y : ℝ) (hy : y ∈ A)", "rfl", False),
            ("(A B : Set ℝ) (f : A → ℝ) (x : ℝ) (hx : x ∈ B)", "rfl", False),
            ("(A : Set ℝ) (f : A → ℝ) (x : ℕ)", "rfl", False),
        ]
        for binders, proof, succeeds in cases:
            source = operators.HEADER
            source += f"\nexample {binders} : (bookSubtypeArgument% (f), (x)).val = x := {proof}\n"
            source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"promotion\\"}"\n'
            with self.subTest(binders=binders):
                if succeeds:
                    self.assertIn("promotion", c.export(source))
                else:
                    with self.assertRaises(ValueError):
                        c.export(source)

    def test_membership_chain_checks_equality_points_and_domain(self):
        c = operators.chapter
        formula = r"x=y \in A"
        types = {"x": "ℝ", "y": "↑A", "A": "Set ℝ"}
        nodes = inspect_formula(formula, types)
        equality = next(n for n in nodes if n["rule"] == "relation:membership-chain-equality")
        self.assertEqual(equality["targetStatus"], "matched")
        self.assertEqual(equality["operandStatus"], "matched")
        original = c.translate
        for field, index, candidate in [
            ("expectedOperands", 0, "(0 : ℝ)"),
            ("expectedOperands", 1, "(0 : ℝ)"),
            ("expectedImplicitArguments", 0, "ℕ"),
        ]:

            def wrong(*args, _field=field, _index=index, _candidate=candidate, **kwargs):
                result = original(*args, **kwargs)
                for node in kwargs.get("trace") or []:
                    if node["rule"] == "relation:membership-chain-equality":
                        node[_field][_index]["candidate"] = _candidate
                return result

            with patch.object(c, "translate", side_effect=wrong):
                altered = inspect_formula(formula, types)
            equality = next(n for n in altered if n["rule"] == "relation:membership-chain-equality")
            self.assertEqual(equality["operandStatus"], "mismatch")
        with self.assertRaises(ValueError):
            inspect_formula(formula, {"x": "ℕ", "y": "↑A", "A": "Set ℝ"})

    def test_alexandrov_inclusion_is_the_actual_coordinate_map(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "alexandrov-forward")
        row = next(
            r
            for r in c.occurrences(text)
            if scope["start"] <= r["start"] < scope["end"] and r["book"] == r"A \hookrightarrow U_n"
        )
        records = c.evidence(c.source_declarations([scope]))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        nodes = operators.inspect(tree, variables, records)
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or j in checked for j, a in enumerate(node["elaborated"].get("arguments", [])))
            )
        inclusion = next(n for n in nodes if n["rule"] == "map:inclusion")
        self.assertEqual(inclusion["requirementStatus"], "proved")
        self.assertTrue(inclusion["semanticRequirements"][0]["kernelChecked"])
        self.assertEqual(row["book"][inclusion["operatorStart"] : inclusion["operatorEnd"]], r"\hookrightarrow")
        term, context = c.translate(tree, variables, records)
        source = operators.HEADER + c.expression_definition(
            {"lean": f"(show ({term}) = (fun z : s => diag z n) from rfl)", "context": context},
            records,
            "AlexandrovInclusion",
        )
        source += c.expression_definition(
            {
                "lean": f"(show Topology.IsEmbedding ({term}) from Topology.IsEmbedding.of_comp "
                f"(continuous_subtype_val.subtype_mk (fun z => (({term}) z).property)) continuous_subtype_val "
                f"(show Topology.IsEmbedding (((↑) : U n → X) ∘ ({term})) from Topology.IsEmbedding.subtypeVal))",
                "context": context,
            },
            records,
            "AlexandrovCoordinateEmbedding",
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"alexandrov_inclusion\\"}"\n'
        self.assertIn("alexandrov_inclusion", c.export(source))

    def test_inclusion_arrow_requires_a_proved_subset_relation(self):
        with self.assertRaises(ValueError):
            inspect_formula(r"A\hookrightarrow B", {"A": "Set ℝ", "B": "Set ℝ"})
        for formula, types in [
            (r"A\hookrightarrow B", {"A": "Type", "B": "Type"}),
            (r"A\hookrightarrow x", {"A": "Set ℝ", "x": "ℝ"}),
        ]:
            with self.subTest(formula=formula, types=types), self.assertRaises(ValueError):
                inspect_formula(formula, types)
        nodes = inspect_formula(r"A\hookrightarrow A", {"A": "Set ℝ"})
        inclusion = next(n for n in nodes if n["rule"] == "map:inclusion")
        self.assertEqual(inclusion["operandStatus"], "matched")
        self.assertEqual(inclusion["requirementStatus"], "proved")

    def test_inclusion_arguments_are_checked_independently(self):
        c = operators.chapter
        original = c.translate
        for position, candidate in [(0, "Nat"), (1, "(∅ : Set ℝ)"), (2, "(∅ : Set ℝ)")]:

            def wrong(*args, _position=position, _candidate=candidate, **kwargs):
                result = original(*args, **kwargs)
                for node in kwargs.get("trace") or []:
                    if node["rule"] == "map:inclusion":
                        node["expectedImplicitArguments"][_position]["candidate"] = _candidate
                return result

            with self.subTest(position=position), patch.object(c, "translate", side_effect=wrong):
                nodes = inspect_formula(r"A\hookrightarrow A", {"A": "Set ℝ"})
            inclusion = next(n for n in nodes if n["rule"] == "map:inclusion")
            self.assertEqual(inclusion["targetStatus"], "matched")
            self.assertEqual(inclusion["implicitArgumentChecks"][position]["status"], "mismatch")
            self.assertEqual(inclusion["operandStatus"], "mismatch")

    def test_subtype_range_distinguishes_images_from_set_valued_arguments(self):
        nodes = inspect_formula("f(A)", {"f": "↑A → ℝ", "A": "Set ℝ"})
        image = next(n for n in nodes if n["rule"] == "application:subtype-range")
        self.assertEqual(image["targetStatus"], "matched")
        self.assertEqual(image["operandStatus"], "matched")
        self.assertEqual([a["argumentPosition"] for a in image["expectedImplicitArguments"]], [0, 1])
        self.assertEqual(image["expectedImplicitArguments"][1]["sourceOperand"], 1)
        nodes = inspect_formula("f(A)", {"f": "Set ℝ → ℝ", "A": "Set ℝ"})
        self.assertEqual([n["rule"] for n in nodes], ["application:function"])
        self.assertEqual(nodes[0]["operandStatus"], "matched")

    def test_decorated_subtype_range_checks_every_callee_trace_in_the_kernel(self):
        chapter = operators.chapter
        tree = chapter.syntax(["f^*(A)"])[0]["tree"]
        variables, _ = chapter.leaves(tree)
        for variable in variables:
            name = "f" if variable["start"] == 0 else "A"
            variable.update(
                id="fixture/" + name,
                status="resolved",
                declaration="D",
                leanName=name,
                leanType="↑A → ℝ" if name == "f" else "Set ℝ",
                formulaOffset=variable["start"],
            )
        records = {
            "D": {
                "binders": [
                    {"name": "A", "type": "Set ℝ", "instance": False},
                    {"name": "f", "type": "↑A → ℝ", "instance": False},
                ]
            }
        }
        nodes = operators.inspect(tree, variables, records)
        self.assertEqual([n["rule"] for n in nodes], ["name:star", "application:subtype-range"])
        self.assertTrue(all(n["targetStatus"] == "matched" for n in nodes))
        self.assertTrue(all(n["operandStatus"] == "matched" for n in nodes))
        self.assertEqual(nodes[-1]["implicitArgumentStatus"], "matched")

    def test_subtype_range_rejects_a_different_domain_set(self):
        c = operators.chapter
        original = c.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "application:subtype-range":
                    node["expectedImplicitArguments"][1]["candidate"] = "Subtype (∅ : Set ℝ)"
            return result

        with patch.object(c, "translate", side_effect=wrong):
            nodes = inspect_formula("f(A)", {"f": "↑A → ℝ", "A": "Set ℝ"})
        self.assertEqual(nodes[0]["targetStatus"], "matched")
        self.assertEqual(nodes[0]["implicitArgumentStatus"], "mismatch")
        self.assertEqual(nodes[0]["operandStatus"], "mismatch")
        # Even a forged textual signature cannot bypass the kernel domain check.
        source = operators.HEADER + "\nexample (A B : Set ℝ) (f : A → ℝ) := bookSubtypeRange% (f), (B)\n"
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"bad_range\\"}"\n'
        with self.assertRaisesRegex(ValueError, "Source set does not define"):
            c.export(source)

    def test_alexandrov_open_family_matches_original_intersection(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "alexandrov-forward")
        rows = [r for r in c.occurrences(text) if scope["start"] <= r["start"] < scope["end"]][:3]
        self.assertEqual(
            [r["book"].strip() for r in rows], [r"A = \bigcap_{n \in \omega} U_n", r"U_n \IncludedIn X", "U_n"]
        )
        records = c.evidence(c.source_declarations([scope]))
        source = operators.HEADER
        for i, row in enumerate(rows):
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            self.assertTrue(all(v["status"] == "resolved" for v in variables))
            nodes = operators.inspect(tree, variables, records)
            for node in nodes:
                self.assertEqual(node["targetStatus"], "matched")
                self.assertEqual(node["operandStatus"], "matched")
                checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or j in checked for j, a in enumerate(node["elaborated"].get("arguments", []))
                    )
                )
            term, context = c.translate(tree, variables, records)
            proof = (
                f"(show ({term}) from hsU)"
                if i == 0
                else (f"(show ({term}) from Set.subset_univ _)" if i == 1 else f"(show IsOpen ({term}) from hUopen n)")
            )
            source += c.expression_definition({"lean": proof, "context": context}, records, f"AlexandrovFamily{i}")
        source += c.expression_definition(
            {
                "lean": "(show ∀ z : s, ((diag z n : U n) : X) = (z : X) from fun _ => rfl)",
                "context": context,
            },
            records,
            "AlexandrovDiagonalCoordinate",
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"alexandrov_family\\"}"\n'
        self.assertIn("alexandrov_family", c.export(source))

    def test_alexandrov_image_is_original_diagonal_range(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "alexandrov-forward")
        rows = [
            r for r in c.occurrences(text) if scope["start"] <= r["start"] < scope["end"] and r["book"] == r"\iota(A)"
        ]
        self.assertEqual(len(rows), 3)
        records = c.evidence(c.source_declarations([scope]))
        source = operators.HEADER
        for i, row in enumerate(rows):
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            nodes = operators.inspect(tree, variables, records)
            self.assertEqual([n["rule"] for n in nodes], ["application:subtype-range"])
            image = nodes[0]
            self.assertEqual(image["targetStatus"], "matched")
            self.assertEqual(image["operandStatus"], "matched")
            self.assertEqual(image["lowering"]["domainSet"], "s")
            checked = {a["argumentPosition"] for a in image["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or j in checked for j, a in enumerate(image["elaborated"].get("arguments", [])))
            )
            term, context = c.translate(tree, variables, records)
            source += c.expression_definition(
                {"lean": f"(show ({term}) = Set.range diag from rfl)", "context": context},
                records,
                f"AlexandrovRange{i}",
            )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"alexandrov_range\\"}"\n'
        self.assertIn("alexandrov_range", c.export(source))

    def test_source_baire_initial_bound_uses_the_first_ball_radius(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "baire-first-bound")
        row = next(r for r in c.occurrences(text) if scope["start"] <= r["start"] < scope["end"])
        self.assertEqual(row["book"], "1")
        records = c.evidence(c.source_declarations([scope]))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        tree = c.resolve_numeric_domain(tree, row, scopes)
        nodes = operators.inspect(tree, [], records)
        self.assertEqual(len(nodes), 1)
        self.assertEqual(nodes[0]["rule"], "literal:numeral")
        self.assertEqual(nodes[0]["targetStatus"], "matched")
        self.assertEqual(nodes[0]["operandStatus"], "matched")
        term, context = c.translate(tree, [], records)
        binders = {b["name"]: b for b in records[context]["binders"]}
        self.assertEqual(binders["r"]["type"], "ℝ")
        self.assertEqual(binders["r"]["value"], "min (r₀ / 2) (1 / 2)")
        source = operators.HEADER + c.expression_definition(
            {"lean": f"(show ({term}) = (1 : ℝ) from rfl)", "context": context}, records, "BaireInitialBound"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"baire_initial_bound\\"}"\n'
        self.assertIn("baire_initial_bound", c.export(source))

    def test_source_relative_meager_formulas_use_the_original_subspace(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "baire-meager-open")
        records = c.evidence(c.source_declarations([scope]))
        source = operators.HEADER
        checked_formulas = []
        for row in c.occurrences(text):
            if not scope["start"] <= row["start"] < scope["end"]:
                continue
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            self.assertTrue(all(v["status"] == "resolved" for v in variables), row["book"])
            nodes = operators.inspect(tree, variables, records)
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes), row["book"])
            for node in nodes:
                checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or j in checked for j, a in enumerate(node["elaborated"].get("arguments", []))
                    ),
                    row["book"],
                )
            term, context = c.translate(tree, variables, records)
            binders = {b["name"]: b for b in records[context]["binders"]}
            self.assertEqual(binders["relativeSpace"]["value"], "↑U")
            proof = None
            if row["book"] == r"U=\bigcup_n N_n":
                proof = f"(show ({term}) from hNcover)"
            elif row["book"] == r"\SetDifference{U}{\AmbientClosure{U}{N_n}}":
                proof = f"(show ({term}) = H n from by ext z; simp [H])"
            if proof:
                source += c.expression_definition(
                    {"lean": proof, "context": context}, records, f"RelativeSource{len(checked_formulas)}"
                )
            checked_formulas.append(row["book"])
        self.assertIn(r"\SetDifference{U}{\AmbientClosure{U}{N_n}}", checked_formulas)
        self.assertIn(r"U=\bigcup_n N_n", checked_formulas)
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"relative_source\\"}"\n'
        self.assertIn("relative_source", c.export(source))

    def test_ambient_closure_checks_carrier_topology_and_set(self):
        nodes = inspect_formula(r"\AmbientClosure{\R}{A}", {"A": "Set ℝ"})
        closure = next(n for n in nodes if n["rule"] == "macro:AmbientClosure")
        self.assertEqual(closure["targetStatus"], "matched")
        self.assertEqual(closure["operandStatus"], "matched")
        self.assertEqual([a["argumentPosition"] for a in closure["expectedImplicitArguments"]], [0, 1])
        self.assertEqual(closure["expectedImplicitArguments"][0]["sourceOperand"], 0)
        self.assertEqual(closure["expectedOperands"][0]["sourceOperand"], 1)

    def test_ambient_closure_rejects_wrong_topology(self):
        c = operators.chapter
        original = c.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "macro:AmbientClosure":
                    node["expectedImplicitArguments"][1]["candidate"] = "(⊥ : TopologicalSpace ℝ)"
            return result

        with patch.object(c, "translate", side_effect=wrong):
            nodes = inspect_formula(r"\AmbientClosure{\R}{A}", {"A": "Set ℝ"})
        self.assertEqual(nodes[-1]["targetStatus"], "matched")
        self.assertEqual(nodes[-1]["implicitArgumentStatus"], "mismatch")
        self.assertEqual(nodes[-1]["operandStatus"], "mismatch")

    def test_ambient_closure_rejects_unregistered_subspace_and_wrong_carrier(self):
        with self.assertRaisesRegex(ValueError, "resolved.*carrier"):
            inspect_formula(r"\AmbientClosure{U}{A}", {"U": "Set ℝ", "A": "Set ℝ"})
        with self.assertRaises(ValueError):
            inspect_formula(r"\AmbientClosure{\omega}{A}", {"A": "Set ℝ"})

    def test_baire_successor_keeps_selected_ball_data(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "baire-next")
        row = next(r for r in c.occurrences(text) if scope["start"] <= r["start"] < scope["end"])
        self.assertEqual(row["book"], r"V_{n+1}:=\Ball{x}{r}")
        records = c.evidence(c.source_declarations([scope]))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        nodes = operators.inspect(tree, variables, records)
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        equality = next(n for n in nodes if n["rule"] == "definition:=")
        self.assertEqual(equality["requirementStatus"], "proved")
        self.assertTrue(equality["semanticRequirements"][0]["kernelChecked"])
        term, context = c.translate(tree, variables, records)
        binders = {b["name"]: b for b in records[context]["binders"]}
        self.assertEqual(binders["x"]["value"], "B.center")
        self.assertEqual(binders["r"]["value"], "B.radius")
        proof_source = operators.HEADER + c.expression_definition(
            {"lean": f"(show ({term}) from hVnext)", "context": context}, records, "BaireSuccessor"
        )
        proof_source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"baire_successor\\"}"\n'
        self.assertIn("baire_successor", c.export(proof_source))

    def test_aligned_baire_rows_preserve_spans_and_original_proofs(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "baire-proof")
        occurrence = next(
            r
            for r in c.occurrences(text)
            if r"\begin{aligned}" in r["book"] and r"\MetricDiameter{d}{\Closure{V_n}}" in r["book"]
        )
        records = c.evidence(c.source_declarations([scope]))
        tree, _ = c.located(c.syntax([occurrence["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, occurrence, scopes, records)
        rows = c.aligned_expression_rows(tree)
        self.assertEqual(len(rows), 2)
        self.assertEqual(
            occurrence["book"][rows[0]["start"] : rows[0]["end"]], r"\Closure{V_{n+1}} &\IncludedIn V_n\cap G_n"
        )
        source = operators.HEADER
        for i, (row, proof) in enumerate(zip(rows, ["hnest n", "(hV n).2.2.2.2"], strict=True)):
            local = [v for v in variables if row["start"] <= v["formulaOffset"] < row["end"]]
            nodes = operators.inspect(row, local, records)
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
            self.assertTrue(all(n["requirementStatus"] != "unresolved" for n in nodes))
            for node in nodes:
                checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or j in checked for j, a in enumerate(node["elaborated"].get("arguments", []))
                    )
                )
            term, context = c.translate(row, local, records)
            source += c.expression_definition(
                {"lean": f"(show ({term}) from {proof})", "context": context}, records, f"BaireRow{i}"
            )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"baire_aligned\\"}"\n'
        self.assertIn("baire_aligned", c.export(source))

    def test_aligned_rows_reject_ambiguous_layouts(self):
        c = operators.chapter
        for formula in [
            r"\begin{aligned}x&=y&=z\end{aligned}",
            r"\begin{aligned}x&=y\\\\z&=x\end{aligned}",
            r"\begin{aligned}x&=y\end{array}",
        ]:
            tree, _ = c.located(c.syntax([formula])[0]["tree"])
            self.assertIsNone(c.aligned_expression_rows(tree))

    def diameter_fixture(self, bounded, formula=r"\MetricDiameter{d}{A}"):
        c = operators.chapter
        tree, _ = c.located(c.syntax([formula])[0]["tree"])
        variables, _ = c.leaves(tree)
        types = {"d": "MetricSpace ℝ", "A": "Set ℝ", "n": "Nat"}
        for v in variables:
            v.update(
                id="fixture/" + v["symbol"],
                status="resolved",
                declaration="D",
                leanName=v["symbol"],
                leanType=types[v["symbol"]],
                formulaOffset=v["start"],
            )
        binders = [{"name": n, "type": types[n], "instance": False} for n in types]
        if bounded:
            binders.append(
                {
                    "name": "bounded",
                    "type": "@Bornology.IsBounded ℝ d.toPseudoMetricSpace.toBornology A",
                    "instance": False,
                }
            )
        return tree, variables, {"D": {"binders": binders}}

    def test_diameter_comparison_uses_real_division_for_natural_indices(self):
        c = operators.chapter
        tree, variables, records = self.diameter_fixture(True, r"\MetricDiameter{d}{A} < 1/n.")
        nodes = operators.inspect(tree, variables, records)
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        division = next(n for n in nodes if n["rule"] == "infix:/")
        self.assertTrue(all(a["status"] == "matched" for a in division["implicitArgumentChecks"]))
        term, context = c.translate(tree, variables, records)
        source = operators.HEADER + c.expression_definition(
            {
                "lean": f"(show ({term}) = (@Metric.diam ℝ d.toPseudoMetricSpace A < 1 / (n : ℝ)) from rfl)",
                "context": context,
            },
            records,
            "RealDiameterDivision",
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"real_diameter_division\\"}"\n'
        self.assertIn("real_diameter_division", c.export(source))

    def test_diameter_checks_explicit_metric_and_boundedness(self):
        for bounded in [False, True]:
            node = operators.inspect(*self.diameter_fixture(bounded))[-1]
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            self.assertEqual(node["implicitArgumentStatus"], "matched")
            self.assertEqual(node["requirementStatus"], "proved" if bounded else "unresolved")
            if bounded:
                self.assertTrue(node["semanticRequirements"][0]["kernelChecked"])

    def test_diameter_rejects_another_metric_on_same_carrier(self):
        c = operators.chapter
        original = c.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "macro:MetricDiameter":
                    node["expectedImplicitArguments"][1]["candidate"] = (
                        "PseudoMetricSpace.induced (fun _ : ℝ => (0 : ℝ)) inferInstance"
                    )
            return result

        with patch.object(c, "translate", side_effect=wrong):
            node = operators.inspect(*self.diameter_fixture(True))[-1]
        self.assertEqual(node["targetStatus"], "matched")
        self.assertEqual(node["implicitArgumentStatus"], "mismatch")
        self.assertEqual(node["operandStatus"], "mismatch")

    def named_subscript_fixture(self, formula, named=True, family=False):
        import json

        c = operators.chapter
        bindings = {"r": {"symbol": "r", "target": "D/r"}}
        if named:
            bindings["r0"] = {"symbol": "r_0", "target": "D/radius0"}
        text = "<!-- chapter-correspondence " + json.dumps({"scope": "radii", "bindings": bindings})
        text += " -->$" + formula + "$<!-- chapter-correspondence-end: radii -->"
        records = {
            "D": {
                "binders": [
                    {"name": "r", "type": "ℕ → ℝ" if family else "ℝ", "instance": False},
                    {"name": "radius0", "type": "ℝ", "instance": False},
                ]
            }
        }
        row = c.report(text, c.scopes(text), records)["formulas"][0]
        return row, records

    def test_named_subscript_requires_explicit_binding(self):
        for formula in (r"r_0", r"r_{0}", r"0<r<r_0"):
            row, records = self.named_subscript_fixture(formula)
            nodes = operators.inspect(row["syntax"], row["variables"], records)
            named = next(n for n in nodes if n["rule"] == "name:subscript")
            self.assertEqual(named["targetStatus"], "matched")
            self.assertEqual(named["expectedVariable"], "radius0")
            var = next(v for v in row["variables"] if v["symbol"] == "r_0")
            self.assertTrue(var["namedSubscript"])
        row, records = self.named_subscript_fixture(r"r_0", named=False)
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)
        row, records = self.named_subscript_fixture(r"r_0", named=False, family=True)
        nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(nodes[-1]["rule"], "index:subscript")
        self.assertEqual(nodes[-1]["operandStatus"], "matched")

    def test_named_subscript_does_not_capture_other_indices(self):
        for formula in (r"r_1", r"r_{01}", r"r_{0+1}"):
            row, records = self.named_subscript_fixture(formula)
            self.assertFalse(any(v.get("namedSubscript") for v in row["variables"]))
            with self.assertRaises(ValueError):
                operators.inspect(row["syntax"], row["variables"], records)

    def test_ball_checks_center_radius_and_ambient_metric(self):
        for formula in (r"\Ball{x}{r}", r"\Closure{\Ball{x}{r}}\IncludedIn A"):
            nodes = inspect_formula(formula, {"x": "ℝ", "r": "ℝ", "A": "Set ℝ"})
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
            ball = next(n for n in nodes if n["rule"] == "macro:Ball")
            self.assertEqual(ball["implicitArgumentStatus"], "matched")
            self.assertEqual([a["role"] for a in ball["expectedImplicitArguments"]], ["ball-domain", "ball-metric"])
            self.assertEqual(len(ball["operandChecks"]), 2)
        with self.assertRaises(ValueError):
            inspect_formula(r"\Ball{x}{r}", {"r": "Set ℝ"})

    def test_ball_in_original_baire_small_ball_context(self):
        import json

        c = operators.chapter
        path = (
            "root.body.body.body.body.body.body."
            "body.body.body.body.body.value.body."
            "body.body.body.unfold.body.body.body."
            "body.body.body.body"
        )
        declaration = "PolishSpaceBook.baire_nested_open_sets"
        text = (
            "<!-- chapter-correspondence "
            + json.dumps(
                {
                    "scope": "small-ball",
                    "context": {"declaration": declaration, "path": path},
                    "bindings": {
                        "x": {"symbol": "x", "target": "x"},
                        "r": {"symbol": "r", "target": "r"},
                        "r0": {"symbol": "r_0", "target": "r₀"},
                        "d": {"symbol": "d", "target": "book_hyg_1"},
                        "n": {"symbol": "n", "target": "n"},
                    },
                }
            )
            + r" -->$\Closure{\Ball{x}{r}}\IncludedIn\Ball{x}{r_0}$<!-- chapter-correspondence-end: small-ball -->"
        )
        records = c.evidence(c.source_declarations(c.scopes(text)))
        row = c.report(text, c.scopes(text), records)["formulas"][0]
        nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(nodes[-1]["targetStatus"], "matched")
        self.assertEqual(nodes[-1]["operandStatus"], "matched")
        self.assertEqual(nodes[-1]["implicitArgumentStatus"], "matched")
        context = records[declaration + "@" + path]
        radius = next(b for b in context["binders"] if b["name"] == "r")
        self.assertIn("min", radius["value"])
        self.assertIn("n + 1", radius["value"])
        term, proof_context = c.translate(row["syntax"], row["variables"], records)
        proof = f"(show ({term}) from Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball hrr₀))"
        source = operators.HEADER + c.expression_definition(
            {"lean": proof, "context": proof_context}, records, "BaireSmallBallInclusion"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"baire_small_ball\\"}"\n'
        self.assertIn("baire_small_ball", c.export(source))
        diameter_text = text.replace(
            r"\Closure{\Ball{x}{r}}\IncludedIn\Ball{x}{r_0}",
            r"\MetricDiameter{d}{\Closure{\Ball{x}{r}}}\le 2^{-(n+1)}",
        )
        diameter_row = c.report(diameter_text, c.scopes(diameter_text), records)["formulas"][0]
        diameter_nodes = operators.inspect(diameter_row["syntax"], diameter_row["variables"], records)
        diameter = next(node for node in diameter_nodes if node["rule"] == "macro:MetricDiameter")
        self.assertEqual(diameter["targetStatus"], "matched")
        self.assertEqual(diameter["operandStatus"], "matched")
        self.assertEqual(diameter["implicitArgumentStatus"], "matched")
        self.assertEqual(diameter["requirementStatus"], "proved")
        self.assertTrue(diameter["semanticRequirements"][0]["kernelChecked"])
        diameter_term, diameter_context = c.translate(diameter_row["syntax"], diameter_row["variables"], records)
        diameter_proof = f"(show ({diameter_term}) from by rw [Metric.diam_closure]; apply (Metric.diam_ball hr.le).trans; dsimp [r]; push_cast; linarith [min_le_right (r₀ / 2) ((2 : ℝ) ^ (-(↑n + 1 : ℤ)) / 2)])"
        diameter_source = operators.HEADER + c.expression_definition(
            {"lean": diameter_proof, "context": diameter_context}, records, "BaireSmallBallDiameter"
        )
        diameter_source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"baire_small_diameter\\"}"\n'
        self.assertIn("baire_small_diameter", c.export(diameter_source))

    def test_ball_rejects_wrong_metric_expectation(self):
        c = operators.chapter
        original = c.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "macro:Ball":
                    node["expectedImplicitArguments"][1]["candidate"] = (
                        "PseudoMetricSpace.induced (fun _ : ℝ => (0 : ℝ)) inferInstance"
                    )
            return result

        with patch.object(c, "translate", side_effect=wrong):
            nodes = inspect_formula(r"\Ball{x}{r}")
        self.assertEqual(nodes[-1]["targetStatus"], "matched")
        self.assertEqual(nodes[-1]["implicitArgumentStatus"], "mismatch")
        self.assertEqual(nodes[-1]["operandStatus"], "mismatch")

    def test_empty_set_uses_source_carrier_on_either_side(self):
        for formula in (r"A\ne\emptyset", r"\emptyset=A", r"A\cap B\ne\emptyset"):
            nodes = inspect_formula(formula, {"A": "Set ℝ", "B": "Set ℝ"})
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
            empty = next(n for n in nodes if n["rule"] == "set:empty")
            self.assertEqual(empty["implicitArgumentStatus"], "matched")
            self.assertEqual(empty["expectedImplicitArguments"][0]["role"], "empty-set-type")

    def test_empty_set_rejects_wrong_type_and_instance_expectations(self):
        c = operators.chapter
        original = c.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "set:empty":
                    node["expectedImplicitArguments"][0]["candidate"] = "Set Nat"
                    node["expectedImplicitArguments"][1]["candidate"] = "(inferInstance : EmptyCollection (Set Nat))"
            return result

        with patch.object(c, "translate", side_effect=wrong):
            nodes = inspect_formula(r"A\ne\emptyset", {"A": "Set ℝ"})
        empty = next(n for n in nodes if n["rule"] == "set:empty")
        self.assertEqual(empty["targetStatus"], "matched")
        self.assertEqual(empty["operandStatus"], "mismatch")
        self.assertEqual([a["status"] for a in empty["implicitArgumentChecks"]], ["mismatch", "mismatch"])

    def test_empty_set_rejects_missing_or_nonset_carrier(self):
        for formula in (r"\emptyset=\emptyset", r"x=\emptyset", r"x=\emptyset[1]", r"x=\emptyset{1}"):
            with self.assertRaises(ValueError):
                inspect_formula(formula)

    def indexed_set_fixture(
        self,
        formula,
        family_type="ℕ → Set ℝ",
        extra_types=None,
        index_origin=None,
        index_offset=None,
        index_type="Real",
    ):
        import json

        c = operators.chapter
        annotation = {
            "scope": "sets",
            "bindings": {
                "G": {"symbol": "G", "target": "D/G"},
                "n": {"symbol": "n", "target": "D/n"},
            },
        }
        for name in extra_types or {}:
            annotation["bindings"][name] = {"symbol": name, "target": "D/" + name}
        if index_origin is not None:
            annotation["bindings"]["G"]["indexOrigin"] = index_origin
        if index_offset is not None:
            annotation["bindings"]["n"]["indexOffset"] = index_offset
        text = "<!-- chapter-correspondence " + json.dumps(annotation) + " -->$" + formula
        text += "$<!-- chapter-correspondence-end: sets -->"
        records = {
            "D": {
                "binders": [
                    {"name": "G", "type": family_type, "instance": False},
                    {"name": "n", "type": index_type, "instance": False},
                ]
            }
        }
        records["D"]["binders"].extend(
            {"name": name, "type": ty, "instance": False} for name, ty in (extra_types or {}).items()
        )
        row = c.report(text, c.scopes(text), records)["formulas"][0]
        return row, records

    def test_free_positive_index_roundtrips_to_original_family_index(self):
        c = operators.chapter
        source = operators.HEADER
        for i, (formula, proof) in enumerate(
            [
                ("G_n", lambda t: f"(show ({t}) = G n from by simp only [Nat.add_sub_cancel])"),
                ("n", lambda t: f"(show ({t}) = n + 1 from rfl)"),
                (r"n\ge1", lambda t: f"(show ({t}) from by omega)"),
            ]
        ):
            row, records = self.indexed_set_fixture(formula, index_origin=1, index_offset=1, index_type="Nat")
            nodes = operators.inspect(row["syntax"], row["variables"], records)
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
            term, context = c.translate(row["syntax"], row["variables"], records)
            source += c.expression_definition(
                {"lean": proof(term), "context": context}, records, f"FreePositiveIndex{i}"
            )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"free_positive_index\\"}"\n'
        self.assertIn("free_positive_index", c.export(source))
        row, records = self.indexed_set_fixture(r"\bigcap_{n\ge1}G_n", index_origin=1, index_offset=1, index_type="Nat")
        indices = [v for v in row["variables"] if v["symbol"] == "n"]
        self.assertTrue(all(v["localBinder"] and "indexOffset" not in v for v in indices))
        nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        row, records = self.indexed_set_fixture("G_n", index_origin=1, index_offset=1, index_type="Real")
        self.assertTrue(any(v["status"] == "unresolved" for v in row["variables"]))
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)

    def test_positive_origin_reindexes_the_actual_family(self):
        c = operators.chapter
        row, records = self.indexed_set_fixture(r"\bigcap_{n\ge1}G_n", index_origin=1)
        nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        indexed = next(n for n in nodes if n["rule"] == "index:subscript")
        self.assertEqual(indexed["lowering"]["sourceOrigin"], 1)
        self.assertEqual(indexed["operandChecks"][0]["actual"]["function"]["name"], "HSub.hSub")
        term, context = c.translate(row["syntax"], row["variables"], records)
        proof = f"""(show ({term}) = ⋂ n, G n from by
          ext x
          change (x ∈ ⋂ k : {{n : ℕ // 1 ≤ n}}, G (k.val - 1)) ↔ x ∈ ⋂ n, G n
          simp only [Set.mem_iInter]
          constructor
          · intro h n
            simpa only [Nat.add_sub_cancel] using h ⟨n + 1, by omega⟩
          · intro h k
            exact h (k.val - 1))"""
        source = operators.HEADER + c.expression_definition(
            {"lean": proof, "context": context}, records, "PositiveOrigin"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"positive_origin\\"}"\n'
        self.assertIn("positive_origin", c.export(source))
        for formula in [r"\bigcap_{n\ge0}G_n", r"\bigcap_n G_n", "G_0", "G"]:
            row, records = self.indexed_set_fixture(formula, index_origin=1)
            with self.subTest(formula=formula), self.assertRaises(ValueError):
                operators.inspect(row["syntax"], row["variables"], records)

    def test_positive_origin_detects_an_off_by_one_operand(self):
        c = operators.chapter
        row, records = self.indexed_set_fixture(r"\bigcap_{n\ge1}G_n", index_origin=1)
        original = c.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "index:subscript":
                    node["expectedOperands"][0]["candidate"] = node["expectedOperands"][0]["candidate"].replace(
                        " - 1", " - 2"
                    )
            return result

        with patch.object(c, "translate", side_effect=wrong):
            nodes = operators.inspect(row["syntax"], row["variables"], records)
        node = next(n for n in nodes if n["rule"] == "index:subscript")
        self.assertEqual(node["targetStatus"], "matched")
        self.assertEqual(node["operandStatus"], "mismatch")

    def test_composite_indexed_sets_check_body_scope_and_family_domains(self):
        extra = {"U": "Set ℝ", "H": "ℕ → Set ℝ"}
        for formula in (r"\bigcap_n(G_n\cap U)", r"U\cap\bigcup_{n\in\omega}(G_n\cap H_n)"):
            row, records = self.indexed_set_fixture(formula, extra_types=extra)
            nodes = operators.inspect(row["syntax"], row["variables"], records)
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
            covered = {(n["operatorStart"], n["operatorEnd"]) for n in nodes}
            covered.update((b["start"], b["end"]) for n in nodes for b in n.get("bindingComponents", []))
            self.assertTrue(
                all((n["start"], n["end"]) in covered for n in operators.operator_candidates(row["syntax"]))
            )
        row, _ = self.indexed_set_fixture(r"\bigcap_n(G_n\cap U)\cap G_n", extra_types=extra)
        indices = [v for v in row["variables"] if v["symbol"] == "n"]
        self.assertTrue(all(v.get("localBinder") for v in indices[:-1]))
        self.assertFalse(indices[-1].get("localBinder", False))
        self.assertEqual(indices[-1]["leanType"], "Real")
        for formula, types in (
            (r"\bigcap_n(G_n=U)", extra),
            (r"\bigcap_n(G_n\cap H_n)", {"H": "ℤ → Set ℝ"}),
        ):
            row, records = self.indexed_set_fixture(formula, extra_types=types)
            with self.assertRaises(ValueError):
                operators.inspect(row["syntax"], row["variables"], records)

    def test_baire_intersection_distribution_formula_is_kernel_proved(self):
        formula = r"U\cap\bigcap_n(G_n\cap U)=U\cap\bigcap_n G_n"
        row, records = self.indexed_set_fixture(formula, extra_types={"U": "Set ℝ"})
        c = operators.chapter
        self.assertIn(formula, c.SOURCE.read_text())
        nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        first = next(n for n in nodes if n["rule"] == "set:indexed-intersection")
        self.assertEqual(formula[first["start"] : first["end"]], r"\bigcap_n(G_n\cap U)")
        term, context = c.translate(row["syntax"], row["variables"], records)
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook Set Topology\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n" + c.METRIC_POINT_ELAB
        proof = f"(show {term} from by ext x; simp only [Set.mem_inter_iff]; aesop)"
        source += c.expression_definition({"lean": proof, "context": context}, records, "IntersectionDistribution")
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"intersection_distribution\\"}"\n'
        self.assertIn("intersection_distribution", c.export(source))

    def test_indexed_sets_bind_their_own_natural_index(self):
        for formula in (r"\bigcap_n G_n", r"\bigcup_{n}G_n", r"\bigcap_{n\in\omega} G_n"):
            with self.subTest(formula=formula):
                row, records = self.indexed_set_fixture(formula)
                indices = [v for v in row["variables"] if v["symbol"] == "n"]
                self.assertTrue(all(v["localBinder"] and v["leanType"] == "ℕ" for v in indices))
                self.assertEqual(len({v["leanName"] for v in indices}), 1)
                nodes = operators.inspect(row["syntax"], row["variables"], records)
                self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
                self.assertEqual(nodes[-1]["implicitArgumentStatus"], "matched")
                covered = {(n["operatorStart"], n["operatorEnd"]) for n in nodes}
                covered.update((b["start"], b["end"]) for n in nodes for b in n.get("bindingComponents", []))
                self.assertTrue(
                    all((n["start"], n["end"]) in covered for n in operators.operator_candidates(row["syntax"]))
                )
        for formula, domain in (
            (r"\bigcap_n G_n", "ℤ → Set ℝ"),
            (r"\bigcap_{n>1}G_n", "ℕ → Set ℝ"),
            (r"\bigcap_{n\ge1 2}G_n", "ℕ → Set ℝ"),
            (r"\bigcap_{n\ge m}G_n", "ℕ → Set ℝ"),
        ):
            row, records = self.indexed_set_fixture(formula, domain)
            with self.assertRaises(ValueError):
                operators.inspect(row["syntax"], row["variables"], records)

    def test_restricted_indexed_sets_preserve_lower_bound_and_projection(self):
        for formula in (r"\bigcap_{n\ge1}G_n", r"\bigcup_{n\ge12}(G_n\cap U)"):
            row, records = self.indexed_set_fixture(formula, extra_types={"U": "Set ℝ"})
            nodes = operators.inspect(row["syntax"], row["variables"], records)
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
            self.assertEqual(nodes[-1]["implicitArgumentStatus"], "matched")
            self.assertEqual(nodes[-1]["lowering"]["projection"], "Subtype.val")
            indexed = next(n for n in nodes if n["rule"] == "index:subscript")
            self.assertIn("Subtype.val", str(indexed["operandChecks"][0]["actual"]))
            covered = {(n["operatorStart"], n["operatorEnd"]) for n in nodes}
            covered.update((b["start"], b["end"]) for n in nodes for b in n.get("bindingComponents", []))
            self.assertTrue(
                all((n["start"], n["end"]) in covered for n in operators.operator_candidates(row["syntax"]))
            )
        c = operators.chapter
        row, records = self.indexed_set_fixture(r"\bigcap_{n\ge1}G_n")
        term, context = c.translate(row["syntax"], row["variables"], records)
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook Set Topology\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n" + c.METRIC_POINT_ELAB
        proof = f"(show ∀ x : ℝ, x ∈ ({term}) ↔ ∀ n : Nat, 1 ≤ n → x ∈ G n from by intro x; change (x ∈ ⋂ i : {{n : Nat // 1 ≤ n}}, G i.val) ↔ _; rw [Set.mem_iInter]; exact ⟨fun h n hn => h ⟨n, hn⟩, fun h i => h i.val i.property⟩)"
        source += c.expression_definition({"lean": proof, "context": context}, records, "RestrictedIntersection")
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"restricted_intersection\\"}"\n'
        self.assertIn("restricted_intersection", c.export(source))
        original = c.translate

        def wrong_bound(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "set:indexed-intersection":
                    node["expectedImplicitArguments"][1]["candidate"] = "{n : Nat // 2 ≤ n}"
            return result

        with patch.object(c, "translate", side_effect=wrong_bound):
            changed = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(changed["targetStatus"], "matched")
        self.assertEqual(changed["implicitArgumentStatus"], "mismatch")
        self.assertEqual(changed["operandStatus"], "mismatch")

    def test_indexed_set_wrong_operation_is_rejected(self):
        row, records = self.indexed_set_fixture(r"\bigcap_n G_n")
        c = operators.chapter
        original = c.translate

        def wrong(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace("iInf (", "iSup ("), context

        with patch.object(c, "translate", side_effect=wrong):
            changed = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(changed["targetStatus"], "mismatch")
        self.assertTrue(all(r["status"] == "matched" for r in changed["operandChecks"]))
        self.assertEqual(changed["implicitArgumentStatus"], "mismatch")

    def test_source_baire_intersection_matches_original_theorem_family(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "baire-global-family")
        row = next(
            r
            for r in c.occurrences(text)
            if scope["start"] <= r["start"] < scope["end"] and r["book"] == r"\bigcap_n G_n"
        )
        records = c.evidence(c.source_declarations([scope]))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        self.assertTrue(all(v["status"] == "resolved" for v in variables))
        nodes = operators.inspect(tree, variables, records)
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        term, context = c.translate(tree, variables, records)
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook Set Topology\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n" + c.METRIC_POINT_ELAB
        for name, proof in [
            ("IntersectionIdentity", f"(show ({term}) = (⋂ n : ℕ, G n) from rfl)"),
            (
                "IntersectionDense",
                f"(show Dense ({term}) from (completely_metrizable_baire_space_book Y).baire_property G hGopen hGdense)",
            ),
        ]:
            source += c.expression_definition({"lean": proof, "context": context}, records, name)
        nonempty = next(
            r
            for r in c.occurrences(text)
            if scope["start"] <= r["start"] < scope["end"] and r["book"] == r"U\cap\bigcap_n G_n\ne\emptyset"
        )
        nonempty_tree, _ = c.located(c.syntax([nonempty["book"]])[0]["tree"])
        nonempty_vars, effects = c.leaves(nonempty_tree)
        nonempty_vars = c.resolve_variables(nonempty_vars, effects, nonempty, scopes, records)
        nonempty_term, nonempty_context = c.translate(nonempty_tree, nonempty_vars, records)
        nonempty_proof = f"(show ({nonempty_term}) from by change U ∩ (⋂ n, G n) ≠ ∅; rw [← hintersection]; exact (baire_open_intersection hY_complete hUopen ⟨x, hxU⟩ hHopen hHdense).ne_empty)"
        source += c.expression_definition(
            {"lean": nonempty_proof, "context": nonempty_context}, records, "IntersectionNonempty"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"baire_intersection\\"}"\n'
        self.assertIn("baire_intersection", c.export(source))

    def test_sequence_power_checks_alphabet_and_index(self):
        formula = r"\seqPower{\{0,1\}}{\omega}"
        nodes = inspect_formula(formula)
        self.assertEqual([n["rule"] for n in nodes], ["type:binary-alphabet", "binder:sequence-power"])
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        self.assertEqual(nodes[0]["elaborated"]["head"], "Bool")
        self.assertEqual(nodes[0]["lowering"]["zero"], "Bool.false")
        self.assertEqual(nodes[0]["lowering"]["one"], "Bool.true")
        self.assertEqual(nodes[-1]["operandChecks"][1]["actual"]["name"], "Nat")
        tree, _ = operators.chapter.located(operators.chapter.syntax([formula])[0]["tree"])
        covered = {(n["operatorStart"], n["operatorEnd"]) for n in nodes}
        self.assertTrue(all((n["start"], n["end"]) in covered for n in operators.operator_candidates(tree)))
        generic = inspect_formula(r"\seqPower{X}{I}", {"X": "Type", "I": "Type"})[-1]
        self.assertEqual(generic["operandStatus"], "matched")
        for bad in (r"\seqPower{\{0,2\}}{\omega}", r"\seqPower{\{0,1\}}{0}"):
            with self.assertRaises(ValueError):
                inspect_formula(bad)
        c = operators.chapter
        original = c.translate

        def wrong_index(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace(": ℕ)", ": ℤ)"), context

        with patch.object(c, "translate", side_effect=wrong_index):
            changed = inspect_formula(formula)[-1]
        self.assertEqual(changed["operandStatus"], "mismatch")

    def test_binary_sequence_power_matches_existing_real_embedding(self):
        c = operators.chapter
        formula = r"\seqPower{\{0,1\}}{\omega}"
        tree, _ = c.located(c.syntax([formula])[0]["tree"])
        term, _ = c.translate(tree, [], {})
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook\n"
        source += f"example : ({term}) = cantor_space := rfl\n"
        source += f"example (b : {term}) (n : ℕ) : bounded_binary_sequence b n = (if b n then (1 : ℝ) else 0) := rfl\n"
        source += f"example (b c : {term}) (h : b ≠ c) : dist (bounded_binary_sequence b) (bounded_binary_sequence c) = 1 := bounded_binary_sequence_dist h\n"
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"binary_sequence_identity\\"}"\n'
        self.assertIn("binary_sequence_identity", c.export(source))

    def test_function_composition_preserves_order_and_types(self):
        rows = inspect_formula(r"f\circ g", {"f": "ℝ → ℝ", "g": "ℕ → ℝ"})
        self.assertEqual(len(rows), 1)
        node = rows[0]
        self.assertEqual(node["elaborated"]["head"], "Function.comp")
        self.assertEqual(node["operandStatus"], "matched")
        self.assertEqual(node["implicitArgumentStatus"], "matched")
        self.assertEqual([a["actual"]["name"] for a in node["operandChecks"]], ["f", "g"])
        self.assertEqual(node["operatorStart"], 1)
        c = operators.chapter
        original = c.translate

        def reverse(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace("Function.comp («f») («g»)", "Function.comp («g») («f»)"), context

        with patch.object(c, "translate", side_effect=reverse):
            wrong = inspect_formula(r"f\circ g", {"f": "ℝ → ℝ", "g": "ℝ → ℝ"})[0]
        self.assertEqual(wrong["targetStatus"], "matched")
        self.assertEqual(wrong["operandStatus"], "mismatch")

        higher_order = inspect_formula(r"f\circ g", {"f": "(ℝ → ℝ) → ℝ", "g": "ℝ → ℝ → ℝ"})[0]
        self.assertEqual(higher_order["operandStatus"], "matched")
        self.assertEqual(higher_order["implicitArgumentStatus"], "matched")
        self.assertEqual(higher_order["lowering"]["kind"], "function-composition")

    def test_source_metric_composition_matches_original_bounded_distance(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        row = next(r for r in c.occurrences(text) if r["book"] == r"\hat d=\phi\circ d")
        relevant = [s for s in scopes if s["start"] <= row["start"] < s["end"]]
        records = c.evidence(c.source_declarations(relevant))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        term, context = c.translate(tree, variables, records)
        nodes = operators.inspect(tree, variables, records)
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        composition = next(n for n in nodes if n["rule"] == "operation:composition")
        self.assertEqual(composition["implicitArgumentStatus"], "matched")
        self.assertEqual(composition["lowering"]["inputAdapter"], "Function.uncurry")
        self.assertEqual(composition["lowering"]["outputAdapter"], "Function.curry")
        covered = {(n["operatorStart"], n["operatorEnd"]) for n in nodes}
        self.assertTrue(all((n["start"], n["end"]) in covered for n in operators.operator_candidates(tree)))
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook Set Topology\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n" + c.METRIC_POINT_ELAB
        source += c.expression_definition(
            {"lean": f"(show {term} from rfl)", "context": context}, records, "CompositionIdentity"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"composition_identity\\"}"\n'
        self.assertIn("composition_identity", c.export(source))

    def test_prose_list_traces_each_expression_without_tuple_lowering(self):
        row, records = self.metric_fixture("x_n,x", {"n": "ℕ"})
        # The fixture only registers standard names; register the genuine index.
        for variable in row["variables"]:
            if variable["symbol"] == "n":
                variable.update(
                    id="fixture/" + variable["symbol"], status="resolved", declaration="D", leanName="n", leanType="ℕ"
                )
        c = operators.chapter
        with patch.object(c, "SOURCE") as source:
            source.read_text.return_value = " " * row["bodyStart"] + "x_n,x"
            result = operators.inspect_formula_report(
                {
                    "formulas": [row],
                    "leanEvidence": records,
                    "source": "fixture.md",
                    "sourceHash": "fixture",
                },
                0,
                validated=True,
            )
        self.assertEqual(len(result["nodes"]), 1)
        self.assertEqual(result["nodes"][0]["rule"], "index:subscript")
        self.assertEqual(result["nodes"][0]["operandStatus"], "matched")
        self.assertEqual(result["unresolved"], [])
        self.assertEqual(result["untracedOperators"], [])
        self.assertEqual([p["inferredType"] for p in result["expressionFragments"]], ["ℝ", "ℝ"])

    def sequence_point_fixture(self, formula, explicit=True, family_type="ℕ → Type"):
        import json

        c = operators.chapter
        bindings = {
            "X": {"symbol": "X", "target": "D/Y"},
            "reference": {"symbol": "x^*", "target": "D/x0"},
            "sequence": {"symbol": "x", "occurrence": "superscript-base", "target": "D/u"},
            "limit": {"symbol": "x", "occurrence": "unsubscripted", "target": "D/x"},
            "coordinate": {"symbol": "x", "occurrence": "subscript-base", "target": "D/x"},
            "n": {"symbol": "n", "target": "D/n"},
            "k": {"symbol": "k", "target": "D/k"},
        }
        if not explicit:
            bindings = {"x": {"symbol": "x", "target": "D/u"}, "k": bindings["k"], "n": bindings["n"]}
        text = "<!-- chapter-correspondence " + json.dumps({"scope": "sequence", "bindings": bindings})
        text += " -->$" + formula + "$<!-- chapter-correspondence-end: sequence -->"
        types = [
            ("Y", family_type),
            ("u", "ℕ → (n : ℕ) → Y n"),
            ("v", "ℕ → (n : ℕ) → Y n"),
            ("x", "(n : ℕ) → Y n"),
            ("x0", "(n : ℕ) → Y n"),
            ("k", "ℕ"),
            ("n", "ℕ"),
        ]
        records = {"D": {"binders": [{"name": n, "type": t, "instance": False} for n, t in types]}}
        return c.report(text, c.scopes(text), records, trusted=False)["formulas"][0], records

    def test_batch_failure_isolation_retains_successful_formulas(self):
        row, records = self.sequence_point_fixture("x_n")
        probe = (row["syntax"], row["variables"], records)

        def check_batch(requests):
            if any(r is bad for r in requests):
                raise ValueError("bad expression")
            return [[{"verified": True}] for _ in requests]

        bad = (probe[0], probe[1], probe[2])
        with patch.object(operators, "inspect_many", side_effect=check_batch):
            results = operators.inspect_many_isolated([probe, bad, probe])
        self.assertEqual(results[0], [{"verified": True}])
        self.assertIsInstance(results[1], ValueError)
        self.assertEqual(results[2], [{"verified": True}])
        with (
            patch.object(operators, "inspect_many", side_effect=RuntimeError("missing dependency")),
            self.assertRaisesRegex(RuntimeError, "missing dependency"),
        ):
            operators.inspect_many_isolated([probe])

    def test_batched_operator_checks_match_individual_evidence(self):
        probes = []
        fixtures = []
        for formula in ("x_n", "x^k_n", r"\prod X_n"):
            row, records = self.sequence_point_fixture(formula)
            probes.append((row["syntax"], row["variables"], records))
            fixtures.append((row, formula, records))
        separate = [operators.inspect(*p) for p in probes]
        with patch.object(operators.chapter, "export", wraps=operators.chapter.export) as export:
            combined = operators.inspect_many(probes)
            self.assertEqual(export.call_count, 1)

        def stable(value):
            if isinstance(value, dict):
                return {k: stable(v) for k, v in value.items() if k != "id"}
            if isinstance(value, list):
                return [stable(v) for v in value]
            return value

        # Kernel fvar IDs are allocation details; every semantic field agrees.
        self.assertEqual(stable(combined), stable(separate))
        self.assertEqual(operators.inspect_many([]), [])
        for (row, formula, records), evidence in zip(fixtures, combined, strict=True):
            with (
                patch.object(operators.chapter, "SOURCE") as source,
                patch.object(operators, "inspect", side_effect=AssertionError("cached probe was repeated")),
            ):
                source.read_text.return_value = " " * row["bodyStart"] + formula
                report = operators.inspect_formula_report(
                    {"formulas": [row], "leanEvidence": records, "source": "fixture.md", "sourceHash": "fixture"},
                    0,
                    validated=True,
                    root_evidence=evidence,
                )
            self.assertEqual(report["unresolved"], [])
            self.assertEqual(report["untracedOperators"], [])
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in report["nodes"]))

    def test_implicit_product_binds_only_its_family_index(self):
        formula = r"x^* \in \prod X_n"
        row, records = self.sequence_point_fixture(formula)
        index = next(v for v in row["variables"] if v["symbol"] == "n")
        self.assertTrue(index["localBinder"])
        self.assertNotEqual(index["leanName"], "n")
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        products = [r for r in rows if r["rule"] == "binder:product"]
        self.assertTrue(products)
        self.assertTrue(all(r["elaborated"]["kernel"]["kind"] == "forall" for r in products))
        self.assertTrue(all(formula[r["operatorStart"] : r["operatorEnd"]] == r"\prod" for r in products))
        self.assertTrue(all(len(r["operandChecks"]) == 2 for r in products))
        # A same-spelled outer index stays free outside the product.
        row, records = self.sequence_point_fixture(r"n, \prod X_n")
        indices = [v for v in row["variables"] if v["symbol"] == "n"]
        self.assertEqual(indices[0]["leanName"], "n")
        self.assertFalse(indices[0].get("localBinder", False))
        self.assertTrue(indices[1]["localBinder"])
        # Reject unsupported domains and non-type-valued families at resolution.
        for family_type in ("ℕ → ℝ", "ℤ → Type", "ℤ → Set ℝ"):
            row, records = self.sequence_point_fixture(r"\prod X_n", family_type=family_type)
            index = next(v for v in row["variables"] if v["symbol"] == "n")
            self.assertEqual(index["status"], "unresolved")
            with self.assertRaises(ValueError):
                operators.inspect(row["syntax"], row["variables"], records)

    def test_products_of_sets_trace_the_subtype_predicate_and_ambient_type(self):
        for formula in (r"\prod X_n", r"\prod_n X_n", r"\prod_{n} X_n", r"\prod_{n \in \omega} X_n"):
            with self.subTest(formula=formula):
                row, records = self.sequence_point_fixture(formula, family_type="ℕ → Set ℝ")
                self.assertTrue(all(v["status"] == "resolved" for v in row["variables"]))
                nodes = operators.inspect(row["syntax"], row["variables"], records)
                self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
                subtype = next(n for n in nodes if n["rule"] == "type:subspace-carrier")
                self.assertEqual(subtype["lowering"]["kind"], "set-as-subspace-carrier")
                self.assertEqual(subtype["expectedImplicitArguments"][0]["argumentPosition"], 0)
                self.assertEqual(len(subtype["operandChecks"]), 1)
                covered = {(n["operatorStart"], n["operatorEnd"]) for n in nodes}
                covered.update((x["start"], x["end"]) for n in nodes for x in n.get("bindingComponents", []))
                for candidate in operators.operator_candidates(row["syntax"]):
                    self.assertIn((candidate["start"], candidate["end"]), covered)

    def test_subspace_product_rejects_wrong_ambient_type_and_predicate(self):
        c = operators.chapter
        original = c.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "type:subspace-carrier":
                    node["expectedImplicitArguments"][0]["candidate"] = "Nat"
                    node["expectedOperands"][0]["candidate"] = "(Set.univ : Set ℝ)"
            return result

        row, records = self.sequence_point_fixture(r"\prod_n X_n", family_type="ℕ → Set ℝ")
        with patch.object(c, "translate", side_effect=wrong):
            nodes = operators.inspect(row["syntax"], row["variables"], records)
        subtype = next(n for n in nodes if n["rule"] == "type:subspace-carrier")
        self.assertEqual(subtype["targetStatus"], "matched")
        self.assertEqual(subtype["operandChecks"][0]["status"], "mismatch")
        self.assertEqual(subtype["implicitArgumentStatus"], "mismatch")

    def test_alexandrov_subspace_product_is_original_diagonal_codomain(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "alexandrov-forward")
        records = c.evidence(
            c.source_declarations([s for s in scopes if scope["start"] <= s["start"] and s["end"] <= scope["end"]])
        )
        rows = [
            r
            for r in c.occurrences(text)
            if scope["start"] <= r["start"] < scope["end"] and r["book"] == r"\prod_n U_n"
        ]
        self.assertEqual(len(rows), 2)
        source = operators.HEADER
        for i, row in enumerate(rows):
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            self.assertTrue(all(v["status"] == "resolved" for v in variables))
            nodes = operators.inspect(tree, variables, records)
            for node in nodes:
                self.assertEqual(node["targetStatus"], "matched")
                self.assertEqual(node["operandStatus"], "matched")
                checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or j in checked for j, a in enumerate(node["elaborated"].get("arguments", []))
                    )
                )
            term, context = c.translate(tree, variables, records)
            source += c.expression_definition(
                {"lean": f"(show ({term}) = ((n : ℕ) → U n) from rfl)", "context": context},
                records,
                f"AlexandrovProduct{i}",
            )
            source += c.expression_definition(
                {"lean": f"(show s → ({term}) from diag)", "context": context}, records, f"AlexandrovMap{i}"
            )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"alexandrov_product\\"}"\n'
        self.assertIn("alexandrov_product", c.export(source))

    def test_alexandrov_limit_coordinates_keep_the_original_points(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        outer = next(s for s in scopes if s["scope"] == "alexandrov-closed-sequence")
        selected = [s for s in scopes if outer["start"] <= s["start"] and s["end"] <= outer["end"]]
        records = c.evidence(c.source_declarations(selected))
        proofs = {
            r"\iota(a^k)=\Tuple{a^k,a^k,\ldots}": lambda t: f"(show ({t}) from by funext n; simp only [ite_self]; rfl)",
            r"a^k \to b_n": lambda t: (
                f"(show ({t}) from (tendsto_pi_nhds.1 hyb n).congr' "
                "(Filter.Eventually.of_forall (fun k => congrArg (fun z => z n) (ha k).symm)))"
            ),
            r"\Sequence{b_n}{n\in\omega}": lambda t: f"(show ({t}) = b from rfl)",
            "b_n": lambda t: f"(show (({t}) : X) = x from hb n)",
            "x": lambda t: f"(show ({t}) = ((b 0 : U 0) : X) from rfl)",
            r"x \in A": lambda t: f"(show ({t}) from hx)",
            r"x=b_n \in U_n": lambda t: f"(show ({t}) from ⟨(hb n).symm, (b n).property⟩)",
            r"\Sequence{b_n}{n\in\omega} = \iota(x) \in \iota(A)": lambda t: (
                f"(show ({t}) from ⟨funext (fun n => Subtype.ext (hb n)), ⟨xA, rfl⟩⟩)"
            ),
        }
        source = operators.HEADER
        seen = []
        for row in c.occurrences(text):
            if not outer["start"] <= row["start"] < outer["end"] or row["book"] not in proofs:
                continue
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            self.assertTrue(all(v["status"] == "resolved" for v in variables), row["book"])
            nodes = operators.inspect(tree, variables, records)
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes), row["book"])
            for node in nodes:
                checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or j in checked for j, a in enumerate(node["elaborated"].get("arguments", []))
                    )
                )
            for node in nodes:
                if node["rule"] == "application:subtype-argument" and r"\iota(x)" in row["book"]:
                    self.assertEqual(node["requirementStatus"], "proved")
                    requirement = node["semanticRequirements"][0]
                    self.assertEqual(requirement["kind"], "subtype-membership")
                    self.assertTrue(requirement["kernelChecked"])
                    self.assertEqual(requirement["proof"]["name"], "hx")
                if node["rule"] == "relation:sequence-limit":
                    self.assertEqual(node["requirementStatus"], "proved")
                    requirement = node["semanticRequirements"][0]
                    self.assertEqual(requirement["kind"], "convergence-subspace-inclusion")
                    self.assertTrue(requirement["kernelChecked"])
                    self.assertIn("x ∈ s", requirement["proposition"])
                    self.assertIn("x ∈ U n", requirement["proposition"])
            term, context = c.translate(tree, variables, records)
            source += c.expression_definition(
                {"lean": proofs[row["book"]](term), "context": context}, records, f"AlexandrovLimit{len(seen)}"
            )
            seen.append(row["book"])
        self.assertEqual(set(seen), set(proofs))
        sequence_context = c.context_reference(outer["context"])
        source += c.expression_definition(
            {"lean": "(show diag (a k) = y k from ha k)", "context": sequence_context},
            records,
            "AlexandrovChosenPreimage",
        )
        limit_scope = next(s for s in selected if s["scope"] == "alexandrov-common-limit")
        context = c.context_reference(limit_scope["context"])
        source += c.expression_definition(
            {"lean": "(show (xA : X) = x from rfl)", "context": context}, records, "AlexandrovLimitSubtype"
        )
        source += c.expression_definition(
            {"lean": "(show b = diag xA from funext fun n => Subtype.ext (hb n))", "context": context},
            records,
            "AlexandrovLimitImage",
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"alexandrov_limits\\"}"\n'
        self.assertIn("alexandrov_limits", c.export(source))

    def test_explicit_natural_product_records_range_and_body(self):
        formula = r"\prod_{n \in \omega} X_n"
        row, records = self.sequence_point_fixture(formula)
        indices = [v for v in row["variables"] if v["symbol"] == "n"]
        self.assertEqual(len(indices), 2)
        self.assertTrue(all(v["localBinder"] for v in indices))
        self.assertEqual(indices[0]["leanName"], indices[1]["leanName"])
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        covered = {(r["operatorStart"], r["operatorEnd"]) for r in rows}
        covered.update((c["start"], c["end"]) for r in rows for c in r.get("bindingComponents", []))
        for candidate in operators.operator_candidates(row["syntax"]):
            self.assertIn((candidate["start"], candidate["end"]), covered)
        for formula in (r"\prod_{m \in \omega} X_n", r"\prod_{n<2} X_n", r"\prod_m X_n", r"\prod_{m} X_n"):
            row, records = self.sequence_point_fixture(formula)
            with self.assertRaises(ValueError):
                operators.inspect(row["syntax"], row["variables"], records)

    def test_source_disjoint_union_carrier_is_original_sigma(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        formula = r"\ExternalDisjointUnion_{n \in \omega} X_n"
        row = next(r for r in c.occurrences(text) if r["book"] == formula)
        scope = next(s for s in scopes if s["scope"] == "disjoint-union-metric-definition")
        records = c.evidence({b["target"].rsplit("/", 1)[0] for b in scope["bindings"].values()})
        tree, _ = c.located(c.syntax([formula])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        term, context = c.translate(tree, variables, records)
        rows = operators.inspect(tree, variables, records)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        proof = "(show (" + term + ") = Sigma Y from rfl)"
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook Set Topology\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n"
        source += c.expression_definition({"lean": proof, "context": context}, records, "DisjointCarrierIdentity")
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"sigma_identity\\"}"\n'
        self.assertIn("sigma_identity", c.export(source))

    def test_source_disjoint_tagged_pairs_preserve_dependent_fibers(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "disjoint-union-metric-definition")
        records = c.evidence({b["target"].rsplit("/", 1)[0] for b in scope["bindings"].values()})
        row = next(
            r for r in c.occurrences(text) if scope["start"] <= r["start"] < scope["end"] and "cases" in r["book"]
        )
        proofs = []
        for formula, tag, point in ((r"\Pair{n}{x}", "i", "x"), (r"\Pair{m}{y}", "j", "y")):
            # Preserve the actual source position when extracting each pair.
            offset = row["book"].index(formula)
            fragment = dict(row, bodyStart=row["bodyStart"] + offset)
            tree, _ = c.located(c.syntax([formula])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, fragment, scopes, records)
            term, context = c.translate(tree, variables, records)
            rows = operators.inspect(tree, variables, records)
            pair = next(r for r in rows if r["rule"] == "constructor:sigma-pair")
            self.assertEqual(pair["targetStatus"], "matched")
            self.assertEqual(pair["operandStatus"], "matched")
            self.assertEqual([r["status"] for r in pair["implicitArgumentChecks"]], ["matched", "matched"])
            proofs.append(f"(show ({term}) = (Sigma.mk {tag} {point} : Sigma Y) from rfl)")
            if tag == "i":
                original_translate = c.translate

                def wrong_implicit(*args, original_translate=original_translate, **kwargs):
                    result = original_translate(*args, **kwargs)
                    for node in kwargs.get("trace") or []:
                        if node["rule"] == "constructor:sigma-pair":
                            node["expectedImplicitArguments"][0]["candidate"] = "Int"
                            node["expectedImplicitArguments"][1]["candidate"] = "(fun n : Nat => Y (n + 1))"
                    return result

                with patch.object(c, "translate", side_effect=wrong_implicit):
                    incorrect = operators.inspect(tree, variables, records)
                incorrect_pair = next(r for r in incorrect if r["rule"] == "constructor:sigma-pair")
                self.assertEqual(
                    [r["status"] for r in incorrect_pair["implicitArgumentChecks"]], ["mismatch", "mismatch"]
                )

            wrong = copy.deepcopy(variables)
            next(v for v in wrong if v["symbol"] in {"n", "m"})["leanName"] = "j" if tag == "i" else "i"
            with self.assertRaises(ValueError):
                operators.inspect(tree, wrong, records)
        formula = row["book"].split(r"\;=", 1)[0].strip()
        tree, _ = c.located(c.syntax([formula])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        term, context = c.translate(tree, variables, records)
        rows = operators.inspect(tree, variables, records)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        application = next(r for r in rows if r["rule"] == "application:function")
        self.assertEqual(application["expectedVariable"], "dSigma")
        proofs.append(f"(show ({term}) = dSigma ⟨i, x⟩ ⟨j, y⟩ from rfl)")
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook Set Topology\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n"
        for i, proof in enumerate(proofs):
            source += c.expression_definition({"lean": proof, "context": context}, records, f"TaggedPairIdentity{i}")
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"tagged_pairs\\"}"\n'
        self.assertIn("tagged_pairs", c.export(source))

    def test_source_disjoint_metric_cases_match_original_definition(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "disjoint-union-metric-definition")
        records = c.evidence({b["target"].rsplit("/", 1)[0] for b in scope["bindings"].values()})
        source_row = next(
            r for r in c.occurrences(text) if scope["start"] <= r["start"] < scope["end"] and "cases" in r["book"]
        )

        def resolve(formula):
            tree, _ = c.located(c.syntax([formula])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, source_row, scopes, records)
            return tree, variables

        tree, variables = resolve(source_row["book"])
        term, context = c.translate(tree, variables, records)
        native = c.semantic_translation(
            tree,
            variables,
            [binder["name"] for record in records.values() for binder in record.get("binders", [])],
            records=records,
        )
        self.assertTrue(native["supported"], native)
        self.assertEqual(native["rendering"]["ordinary"], term)
        rows = operators.inspect(tree, variables, records)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        cases = next(r for r in rows if r["rule"] == "cases:real")
        self.assertEqual(cases["elaborated"]["head"], "dite")
        self.assertEqual(len(cases["operandChecks"]), 3)
        self.assertEqual([r["status"] for r in cases["implicitArgumentChecks"]], ["matched", "matched"])
        original_translate = c.translate

        def wrong_decision(*args, **kwargs):
            result = original_translate(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "cases:real":
                    node["expectedImplicitArguments"][1]["candidate"] = "Classical.propDecidable False"
            return result

        with patch.object(c, "translate", side_effect=wrong_decision):
            incorrect = operators.inspect(tree, variables, records)
        incorrect_case = next(r for r in incorrect if r["rule"] == "cases:real")
        self.assertEqual(incorrect_case["targetStatus"], "matched")
        self.assertEqual(incorrect_case["implicitArgumentChecks"][1]["typeStatus"], "mismatch")
        self.assertEqual(incorrect_case["operandStatus"], "mismatch")
        metric = next(r for r in rows if r["rule"] == "application:metric")
        self.assertEqual(metric["lowering"]["operation"], "Eq.mp")
        transported = metric["operandChecks"][1]["actual"]
        self.assertEqual(transported["function"]["name"], "Eq.mp")
        self.assertEqual(transported["arguments"][-1]["name"], "y")
        proof = transported["arguments"][-2]
        self.assertEqual(proof["function"]["name"], "congrArg")
        self.assertEqual(proof["arguments"][-1]["arguments"][-1]["name"], metric["lowering"]["branchProof"])
        covered = {(r["operatorStart"], r["operatorEnd"]) for r in rows}
        for candidate in operators.operator_candidates(tree):
            self.assertIn((candidate["start"], candidate["end"]), covered)
        prefix = "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook Set Topology\n"
        prefix += "set_option autoImplicit false\nset_option linter.unusedVariables false\n" + c.METRIC_POINT_ELAB

        def prove(value):
            source = prefix + c.expression_definition(
                {"lean": "(show " + value + " from by rfl)", "context": context}, records, "MetricCasesIdentity"
            )
            source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"metric_cases\\"}"\n'
            return c.export(source)

        self.assertIn("metric_cases", prove(term))
        # A different cross-component distance still typechecks, but is not the
        # original definition: the kernel identity check must reject it.
        wrong_tree, wrong_vars = resolve(source_row["book"].replace("1, &", "2, &"))
        wrong_term, _ = c.translate(wrong_tree, wrong_vars, records)
        with self.assertRaises(ValueError):
            prove(wrong_term)
        # The second condition must be the logical complement of the first.
        wrong_tree, wrong_vars = resolve(source_row["book"].replace(r"n \ne m", "n = m"))
        with self.assertRaises(ValueError):
            operators.inspect(wrong_tree, wrong_vars, records)
        # A branch equality cannot transport a point in the reverse direction
        # without a matching equality proof.
        wrong_tree, wrong_vars = resolve(source_row["book"].replace("d_n(x, y)", "d_m(x, y)"))
        with self.assertRaises(ValueError):
            operators.inspect(wrong_tree, wrong_vars, records)

    def test_source_disjoint_triangle_chains_and_named_points(self):
        o = operators
        c = o.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        selected = [s for s in scopes if s["scope"].startswith("disjoint-triangle")]
        r = c.evidence({b["target"].rsplit("/", 1)[0] for s in selected for b in s["bindings"].values()})
        unresolved = []
        outer = next(s for s in selected if s["scope"] == "disjoint-triangle")
        rows = [x for x in c.occurrences(text) if outer["start"] <= x["start"] < outer["end"]]
        proofs = {
            "disjoint-triangle-same": "by simp only [p, q_book_34, r_book_31, dSigma, dite_eq_left rfl, cast_eq]; exact ⟨by trivial, dist_triangle x y_book_33 z_book_30, by trivial⟩",
            "disjoint-triangle-return": "by simp only [p, q, r_book_31, dSigma, dite_eq_left rfl, dite_eq_right hij, dite_eq_right hji, cast_eq]; exact ⟨by trivial, hY_bound i x z_book_30, by norm_num, by trivial⟩",
            "disjoint-triangle-distinct": """by
          change dSigma p r = (1 : ℝ) ∧ (1 : ℝ) ≤ dSigma p q + dSigma q r
          constructor
          · simp only [p, r, dSigma, dite_eq_right hik]
          · by_cases hij : i = j
            · have hjk : j ≠ k := fun h => hik (hij.trans h)
              rw [show dSigma q r = 1 by simp only [q, r, dSigma, dite_eq_right hjk]]
              exact le_add_of_nonneg_left (dSigma_nonneg p q)
            · rw [show dSigma p q = 1 by simp only [p, q, dSigma, dite_eq_right hij]]
              exact le_add_of_nonneg_right (dSigma_nonneg q r)""",
        }
        source = (
            "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook Set Topology\nset_option autoImplicit false\nset_option linter.unusedVariables false\n"
            + c.METRIC_POINT_ELAB
        )
        requests = []
        for i, row in enumerate(rows):
            t, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            t = c.resolve_numeric_domain(t, row, scopes)
            v, e = c.leaves(t)
            v = c.resolve_variables(v, e, row, scopes, r)
            try:
                term, ctx = c.translate(t, v, r)
            except c.Unsupported as ex:
                unresolved.append((row["book"], str(ex)))
                continue
            requests.append((t, v, r))
            inner = next(
                (s["scope"] for s in selected if s is not outer and s["start"] <= row["start"] < s["end"]), None
            )
            proof = proofs.get(inner)
            if row["book"].startswith(("p=", "q=", "r=")):
                proof = "by rfl"
            if proof:
                source += c.expression_definition(
                    {"lean": "(show " + term + " from " + proof + ")", "context": ctx}, r, "TriangleIdentity" + str(i)
                )

        self.assertEqual(unresolved, [])
        self.assertEqual(len(rows), len(requests) + len(unresolved))
        for start in range(0, len(requests), 4):
            for nodes in o.inspect_many(requests[start : start + 4]):
                self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
                for node in nodes:
                    checked = {a["argumentPosition"] for a in node.get("expectedImplicitArguments", [])}
                    for position, argument in enumerate(node.get("elaborated", {}).get("arguments", [])):
                        if argument["implicit"]:
                            self.assertIn(position, checked, (node["rule"], position))
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"triangle_identities\\"}"\n'
        self.assertIn("triangle_identities", c.export(source))
        # Swapping p for q preserves the ambient Sigma type, but not the
        # source definition; the kernel must reject that correspondence.
        self.assertIn("(«p»)", source)
        with self.assertRaises(ValueError):
            c.export(source.replace("(«p»)", "(«q»)", 1))

    def test_source_numeric_comparison_operands_keep_domain_and_spans(self):
        c = operators.chapter
        formula = r"1\le 12+1=13"
        tree, _ = c.located(c.syntax([formula])[0]["tree"])
        tree["numericContext"] = {"type": "Real", "target": "D/d", "binding": "metric"}
        records = {"D": {"binders": [{"name": "d", "type": "ℝ → ℝ", "instance": False}]}}
        nodes = operators.inspect(tree, [], records)
        for node in nodes:
            self.assertEqual(node["operandStatus"], "matched")
            self.assertEqual(node["implicitArgumentStatus"], "matched")
            if node["rule"] == "literal:numeral":
                self.assertIn(formula[node["operatorStart"] : node["operatorEnd"]], {"1", "12", "13"})
        self.assertTrue(any(formula[n["operatorStart"] : n["operatorEnd"]] == "12" for n in nodes))
        wrong = copy.deepcopy(records)
        wrong["D"]["binders"][0]["type"] = "ℕ → ℕ"
        with self.assertRaisesRegex(ValueError, "Numeral domain does not match"):
            operators.inspect(tree, [], wrong)

    def test_source_dimension_levels_use_all_three_bound_apis(self):
        c = operators.chapter
        rows = [r for r in c.occurrences(c.SOURCE.read_text()) if r["book"] == r"\NonnegativeDimensionLevel{0}"]
        self.assertEqual(len(rows), 4)
        terms = []
        for row in rows:
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            nodes = operators.inspect(tree, [], {})
            self.assertEqual(len(nodes), 1)
            node = nodes[0]
            self.assertEqual(node["rule"], "literal:dimension-level")
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            self.assertEqual(node["implicitArgumentStatus"], "matched")
            self.assertEqual({a["argumentPosition"] for a in node["expectedImplicitArguments"]}, {0, 2})
            term, context = c.translate(tree, [], {})
            self.assertIsNone(context)
            terms.append(term)
        a, b, d, n = terms
        source = (
            "import PolishSpaceBook.DimensionExamples\n"
            + operators.HEADER
            + f"""
open TopologicalSpace
example (X : Type) [TopologicalSpace X] :
    smallInductiveDimension X ≤ ({a} : ℕ) ↔ IsZeroDimensional X :=
  (smallInductiveDimension_le_iff (X := X) (n := {a})).trans
    (zero_dimensional_iff_small_inductive X).symm
example (X : Type) [MetricSpace X] [SeparableSpace X] :
    largeInductiveDimension X ≤ (({b} : ℕ) : ℤ) ↔ IsZeroDimensional X :=
  ((largeInductiveDimension_le_iff X ({b})).trans (largeInductiveDimensionBound_one_iff X)).trans
    (zero_dimensional_iff_big_inductive X).symm
example (X : Type) [MetricSpace X] [SeparableSpace X] :
    coveringDimension X ≤ (({d} : ℕ) : ℤ) ↔ IsZeroDimensional X :=
  ((coveringDimension_le_iff X ({d})).trans (coveringDimensionBound_zero_iff X)).trans
    (zero_dimensional_iff_lebesgue_covering_dimension X).symm
example (X : Type) [MetricSpace X] [SeparableSpace X] [Nonempty X] (h : IsZeroDimensional X) :
    smallInductiveDimension X = (({n} : ℕ) : ℕ∞) ∧
      largeInductiveDimension X = (({n} : ℕ) : ℤ) ∧ coveringDimension X = (({n} : ℕ) : ℤ) :=
  dimensions_zero_of_clopen_basis X h
"""
        )
        source += 'run_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"dimension_levels_source\\"}"\n'
        self.assertIn("dimension_levels_source", c.export(source))
        original = c.translate

        def wrong_level(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "literal:dimension-level":
                    node["expectedOperands"][0]["candidate"] = "(1 : Nat)"
            return result

        with patch.object(c, "translate", side_effect=wrong_level):
            wrong = inspect_formula(r"\NonnegativeDimensionLevel{0}")
        self.assertEqual(wrong[0]["operandStatus"], "mismatch")
        for value in ("-1", "1/2", r"\infty"):
            with self.subTest(value=value), self.assertRaises(c.Unsupported):
                inspect_formula(r"\NonnegativeDimensionLevel{" + value + "}")
        with self.assertRaises(c.Unsupported):
            inspect_formula("0")

    def test_source_homeomorphism_tracks_spaces_topologies_and_external_input(self):
        c = operators.chapter
        row = next(
            r for r in c.occurrences(c.SOURCE.read_text()) if r["book"] == r"\Homeomorphic{\RealSequenceSpace}{\ell^2}"
        )
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        nodes = operators.inspect(tree, [], {})
        self.assertEqual(
            {n["rule"] for n in nodes},
            {"literal:ennreal-numeral", "space:real-lp", "type:homeomorphism", "relation:homeomorphic"},
        )
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or i in checked for i, a in enumerate(node["elaborated"].get("arguments", [])))
            )
            if checked:
                self.assertEqual(node["implicitArgumentStatus"], "matched")
        term, context = c.translate(tree, [], {})
        self.assertIsNone(context)
        theorem = "PolishSpaceBook.banach_homeomorphic_real_sequences_of_anderson_kadec"
        source = (
            operators.HEADER
            + f"""
example (anderson : {term}) :
    Nonempty (PolishSpaceBook.real_sequence_space ≃ₜ lp (fun _ : ℕ => ℝ) (2 : ENNReal)) := anderson
example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (h : ¬ FiniteDimensional ℝ E) (anderson : {term})
    (anderson_kadec : ¬ FiniteDimensional ℝ E → Nonempty (E ≃ₜ lp (fun _ : ℕ => ℝ) (2 : ENNReal))) :
    Nonempty (E ≃ₜ PolishSpaceBook.real_sequence_space) :=
  {theorem} E h anderson anderson_kadec
"""
        )
        source += 'run_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"homeomorphism_source\\"}"\n'
        self.assertIn("homeomorphism_source", c.export(source))
        original = c.translate

        def wrong_topology(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "type:homeomorphism":
                    node["expectedImplicitArguments"][1]["candidate"] = (
                        "(⊥ : TopologicalSpace (lp (fun _ : ℕ => ℝ) (2 : ENNReal)))"
                    )
            return result

        with patch.object(c, "translate", side_effect=wrong_topology):
            wrong = operators.inspect(tree, [], {})
        self.assertEqual(
            next(n for n in wrong if n["rule"] == "type:homeomorphism")["implicitArgumentStatus"], "mismatch"
        )

    def test_source_two_point_space_is_the_cantor_coordinate_type(self):
        c = operators.chapter
        rows = [r for r in c.occurrences(c.SOURCE.read_text()) if r["book"] == r"\TwoPointSpace"]
        self.assertEqual(len(rows), 2)
        for row in rows:
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            self.assertEqual(c.leaves(tree)[0], [])
            nodes = operators.inspect(tree, [], {})
            self.assertEqual(len(nodes), 1)
            node = nodes[0]
            self.assertEqual(node["rule"], "type:binary-alphabet")
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            self.assertEqual(node["elaborated"]["arguments"], [])
            self.assertEqual(node["operatorStart"], 0)
            self.assertEqual(node["operatorEnd"], len(row["book"]))
            term, context = c.translate(tree, [], {})
            self.assertIsNone(context)
        source = (
            operators.HEADER
            + f"""
example : DiscreteTopology ({term}) := inferInstance
example : PolishSpace ({term}) := PolishSpaceBook.bool_polish
example : CompactSpace ({term}) := inferInstance
example : Fintype.card ({term}) = 2 := rfl
example : PolishSpaceBook.cantor_space = (ℕ → ({term})) := rfl
example (n : ℕ) : PolishSpaceBook.bounded_binary_sequence (fun _ => false) n = 0 := by
  simp [PolishSpaceBook.bounded_binary_sequence]
example (n : ℕ) : PolishSpaceBook.bounded_binary_sequence (fun _ => true) n = 1 := by
  simp [PolishSpaceBook.bounded_binary_sequence]
"""
        )
        source += 'run_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"two_point_source\\"}"\n'
        self.assertIn("two_point_source", c.export(source))
        with self.assertRaises(c.Unsupported):
            inspect_formula("2")
        power = inspect_formula(r"\seqPower{\TwoPointSpace}{\omega}")
        self.assertEqual({n["rule"] for n in power}, {"type:binary-alphabet", "binder:sequence-power"})
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in power))

    def test_source_finite_lp_space_and_range_use_the_proved_polish_example(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "polish-examples")
        records = c.evidence(c.source_declarations([scope]))
        rows = [r for r in c.occurrences(text) if r["book"] in {r"\ell^p", r"1\le p<\infty"}]
        self.assertEqual(len(rows), 2)
        source = operators.HEADER
        for row in rows:
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            self.assertTrue(all(v["status"] == "resolved" for v in variables))
            nodes = operators.inspect(tree, variables, records)
            for node in nodes:
                self.assertEqual(node["targetStatus"], "matched")
                self.assertEqual(node["operandStatus"], "matched")
                self.assertEqual(node["implicitArgumentStatus"], "matched")
                checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or i in checked for i, a in enumerate(node["elaborated"].get("arguments", []))
                    )
                )
            term, context = c.translate(tree, variables, records)
            if row["book"] == r"\ell^p":
                proof = f"(show PolishSpace ({term}) from PolishSpaceBook.real_lp_polish «p» «hp»)"
            else:
                proof = f"(show {term} from ⟨Fact.out, «hp»⟩)"
            source += c.expression_definition(
                {"lean": proof, "context": context}, records, "FiniteLp" + str(row["index"])
            )
        source += 'run_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"finite_lp_source\\"}"\n'
        self.assertIn("finite_lp_source", c.export(source))

    def test_ennreal_range_uses_the_source_operand_type(self):
        for formula in (r"1\le p<\infty", r"p<\infty", r"0\le p"):
            with self.subTest(formula=formula):
                nodes = inspect_formula(formula, {"p": "ENNReal"})
                self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        with self.assertRaises(operators.chapter.Unsupported):
            inspect_formula(r"p<\infty", {"p": "ℝ"})
        original = operators.chapter.translate

        def wrong_lower_bound(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "infix:≤":
                    node["expectedOperands"][0]["candidate"] = "(0 : ENNReal)"
            return result

        with patch.object(operators.chapter, "translate", side_effect=wrong_lower_bound):
            wrong = inspect_formula(r"1\le p<\infty", {"p": "ENNReal"})
        self.assertEqual(next(n for n in wrong if n["rule"] == "infix:≤")["operandStatus"], "mismatch")

    def test_real_lp_exponents_preserve_natural_values_and_require_ennreal_variables(self):
        for exponent in ("0", "2", "12", "p"):
            with self.subTest(exponent=exponent):
                nodes = inspect_formula(r"\ell^{" + exponent + "}", {"p": "ENNReal"})
                for node in nodes:
                    self.assertEqual(node["targetStatus"], "matched")
                    self.assertEqual(node["operandStatus"], "matched")
                    self.assertEqual(node["implicitArgumentStatus"], "matched")
                space = next(n for n in nodes if n["rule"] == "space:real-lp")
                self.assertEqual(space["lowering"]["index"], "Nat")
                self.assertEqual(space["lowering"]["scalar"], "Real")
        for domain in ("ℝ", "ℕ", "ℤ", "Set ℝ"):
            with self.subTest(rejected_domain=domain), self.assertRaises(operators.chapter.Unsupported):
                inspect_formula(r"\ell^p", {"p": domain})

    def test_source_ell_infinity_tracks_exponent_and_real_coordinates(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        row = next(r for r in c.occurrences(text) if r["book"] == r"\ell^\infty")
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        nodes = operators.inspect(tree, [], {})
        self.assertEqual({n["rule"] for n in nodes}, {"space:real-lp", "literal:ennreal-top"})
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            self.assertEqual(node["implicitArgumentStatus"], "matched")
            checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or i in checked for i, a in enumerate(node["elaborated"].get("arguments", [])))
            )
        term, context = c.translate(tree, [], {})
        self.assertIsNone(context)
        source = (
            operators.HEADER
            + f"""
example : ({term}) = PolishSpaceBook.ell_infty := rfl
example : PolishSpaceBook.IsMetricComplete ({term}) := PolishSpaceBook.ell_infty_real_sequences_complete
example : ¬ TopologicalSpace.SeparableSpace ({term}) := PolishSpaceBook.ell_infty_real_sequences_not_separable
"""
        )
        source += 'run_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"ell_infty_source\\"}"\n'
        self.assertIn("ell_infty_source", c.export(source))
        original = c.translate

        def wrong_exponent(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "space:real-lp":
                    next(a for a in node["expectedOperands"] if a["sourceOperand"] == 0)["candidate"] = "(2 : ENNReal)"
            return result

        with patch.object(c, "translate", side_effect=wrong_exponent):
            wrong = operators.inspect(tree, [], {})
        self.assertEqual(next(n for n in wrong if n["rule"] == "space:real-lp")["operandStatus"], "mismatch")

    def test_source_continuous_interval_space_retains_interval_and_real_codomain(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "polish-examples")
        row = next(r for r in c.occurrences(text) if r["book"] == r"C(\ClosedInterval{0}{1})")
        records = c.evidence(c.source_declarations([scope]))
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        nodes = operators.inspect(tree, variables, records)
        self.assertEqual({n["rule"] for n in nodes}, {"macro:ClosedInterval", "application:function"})
        for node in nodes:
            self.assertEqual(node["targetStatus"], "matched")
            self.assertEqual(node["operandStatus"], "matched")
            checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
            self.assertTrue(
                all(not a["implicit"] or i in checked for i, a in enumerate(node["elaborated"].get("arguments", [])))
            )
            if checked:
                self.assertEqual(node["implicitArgumentStatus"], "matched")
        term, context = c.translate(tree, variables, records)
        self.assertIsNone(context)
        source = (
            operators.HEADER
            + f"""
example : ({term}) = ContinuousMap PolishSpaceBook.closed_unit_interval ℝ := rfl
example : PolishSpace ({term}) := PolishSpaceBook.continuous_unit_interval_polish
"""
        )
        source += 'run_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"continuous_interval_source\\"}"\n'
        self.assertIn("continuous_interval_source", c.export(source))
        original = c.translate

        def wrong_interval(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "application:function":
                    node["expectedOperands"][0]["candidate"] = "Set.Icc (0 : ℝ) 2"
            return result

        with patch.object(c, "translate", side_effect=wrong_interval):
            wrong = operators.inspect(tree, variables, records)
        application = next(n for n in wrong if n["rule"] == "application:function")
        self.assertEqual(application["operandStatus"], "mismatch")

    def test_standard_real_metric_and_isolated_singleton_match_original_definitions(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        selected = [s for s in scopes if s["scope"] in {"polish-examples", "sequence-spaces"}]
        records = c.evidence(c.source_declarations(selected))
        rows = [r for r in c.occurrences(text) if r["index"] in {9, 398, 399}]
        self.assertEqual(len(rows), 3)
        source = operators.HEADER
        for row in rows:
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            self.assertTrue(all(v["status"] == "resolved" for v in variables))
            nodes = operators.inspect(tree, variables, records)
            for node in nodes:
                self.assertEqual(node["targetStatus"], "matched")
                self.assertEqual(node["operandStatus"], "matched")
                checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or i in checked for i, a in enumerate(node["elaborated"].get("arguments", []))
                    )
                )
                if checked:
                    self.assertEqual(node["implicitArgumentStatus"], "matched")
            term, context = c.translate(tree, variables, records)
            if row["index"] == 9:
                self.assertEqual(row["book"], r"d(x, y) = \Abs{x - y}")
                proof = f"(show ({term}) from Real.dist_eq x y)"
            elif row["index"] == 398:
                self.assertEqual(row["book"], "x")
                proof = f"(show ({term}) = x from rfl)"
            else:
                self.assertEqual(row["book"], r"\{x\}")
                self.assertEqual(len(nodes), 1)
                self.assertEqual(nodes[0]["rule"], "set:singleton")
                proof = f"(show PolishSpaceBook.IsIsolatedPointByOpenSingleton x ↔ IsOpen ({term}) from Iff.rfl)"
            source += c.expression_definition(
                {"lean": proof, "context": context}, records, f"ExampleDefinition{row['index']}"
            )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"example_definitions\\"}"\n'
        self.assertIn("example_definitions", c.export(source))

    def test_singleton_requires_a_point_and_checks_its_carrier(self):
        c = operators.chapter
        original = c.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            trace = kwargs.get("trace")
            if trace:
                node = next(n for n in trace if n["rule"] == "set:singleton")
                node["expectedImplicitArguments"][0]["candidate"] = "Nat"
            return result

        with patch.object(c, "translate", side_effect=wrong):
            nodes = inspect_formula(r"\{x\}", {"x": "ℝ"})
        self.assertEqual(nodes[0]["implicitArgumentStatus"], "mismatch")
        for formula in (r"\{x,y\}", r"\{\}"):
            with self.subTest(formula=formula), self.assertRaises(ValueError):
                inspect_formula(formula)

    def test_alexandrov_prose_indices_match_the_original_natural_binder(self):
        from proof_contexts import inspection_source

        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "alexandrov-converse-metrics")
        found = c.export(inspection_source("PolishSpaceBook.polish_subspace_isGdelta", "hA_subset_V"))
        inclusion_context = next(k for k in found if "@" in k)
        records = c.evidence(c.source_declarations([scope]) | {inclusion_context})
        expected = {
            303: r"n \in \omega",
            309: "V_n",
            318: r"A \IncludedIn V_n",
            319: r"n \in \omega",
            325: "V_n",
            368: "V_n",
        }
        source = operators.HEADER
        rows = [r for r in c.occurrences(text) if r["index"] in expected]
        self.assertEqual(len(rows), 6)
        for row in rows:
            self.assertEqual(row["book"], expected[row["index"]])
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            self.assertTrue(all(v["status"] == "resolved" for v in variables))
            index = next(v for v in variables if v["symbol"] == "n")
            self.assertEqual(index["leanType"], "ℕ")
            self.assertEqual(index["leanName"], "n")
            self.assertNotIn("indexOffset", index)
            self.assertNotIn("indexOrigin", index)
            nodes = operators.inspect(tree, variables, records)
            for node in nodes:
                self.assertEqual(node["targetStatus"], "matched")
                self.assertEqual(node["operandStatus"], "matched")
                checked = {a["argumentPosition"] for a in node["expectedImplicitArguments"]}
                self.assertTrue(
                    all(
                        not a["implicit"] or i in checked for i, a in enumerate(node["elaborated"].get("arguments", []))
                    )
                )
            term, context = c.translate(tree, variables, records)
            if row["book"] == "V_n":
                proof = f"(show ({term}) = V n from rfl)"
            elif row["index"] == 318:
                context = inclusion_context
                proof = f"(show (∀ n : ℕ, {term}) from by intro n x hx; exact Set.mem_iInter.mp (hA_subset_V hx) n)"
            else:
                proof = f"(show ({term}) from Set.mem_univ n)"
            source += c.expression_definition({"lean": proof, "context": context}, records, f"ProseIndex{row['index']}")
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"prose_indices\\"}"\n'
        self.assertIn("prose_indices", c.export(source))

    def test_standalone_distance_numbers_follow_their_source_witnesses(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        expected = {23: "1", 24: "1/3", 44: "0", 64: "1"}
        rows = [r for r in c.occurrences(text) if r["index"] in expected]
        selected = [s for s in scopes if any(s["start"] <= r["start"] < s["end"] for r in rows)]
        records = c.evidence(c.source_declarations(selected))
        source = operators.HEADER
        for row in rows:
            self.assertEqual(row["book"], expected[row["index"]])
            tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
            tree = c.resolve_numeric_domain(tree, row, scopes)
            nodes = operators.inspect(tree, [], records)
            for node in nodes:
                self.assertEqual(node["targetStatus"], "matched")
                self.assertEqual(node["operandStatus"], "matched")
                self.assertEqual(node["implicitArgumentStatus"], "matched")
            term, context = c.translate(tree, [], records)
            proof = f"(show ({term}) = ({row['book']} : ℝ) from rfl)"
            source += c.expression_definition(
                {"lean": proof, "context": context}, records, f"DistanceNumber{row['index']}"
            )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"source_distance_numbers\\"}"\n'
        self.assertIn("source_distance_numbers", c.export(source))

    def test_numeric_expression_uses_the_constant_witness_result_type(self):
        import json

        c = operators.chapter
        records = c.evidence({"Dist.dist", "Nat.succ"})
        for formula in ("1", "1/3", "(12+1)/3"):
            annotation = {
                "scope": "numbers",
                "bindings": {"distance": {"symbol": "d", "target": {"constant": "Dist.dist"}}},
                "numerals": {"type": "Real", "from": "distance"},
            }
            text = "<!-- chapter-correspondence " + json.dumps(annotation) + " -->$" + formula + "$"
            text += "<!-- chapter-correspondence-end: numbers -->"
            row = c.report(text, c.scopes(text), records)["formulas"][0]
            self.assertEqual(row["typeStatus"], "typechecked")
            self.assertEqual(row["inferredType"], "ℝ")
            nodes = operators.inspect(row["syntax"], row["variables"], records)
            self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
            self.assertTrue(all(n["implicitArgumentStatus"] == "matched" for n in nodes))
            numbers = [n for n in nodes if n["rule"] == "literal:numeral"]
            self.assertTrue(numbers)
            self.assertTrue(all(n["lowering"]["target"] == "Dist.dist/@constant" for n in numbers))
            term, context = c.translate(row["syntax"], row["variables"], records)
            self.assertIsNone(context)
            proof = operators.HEADER + f"\nexample : ({term}) = ({formula} : ℝ) := rfl\n"
            proof += 'run_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"numeric_expression\\"}"\n'
            self.assertIn("numeric_expression", c.export(proof))
            invalid = copy.deepcopy(row["syntax"])
            key = "numericDomain" if "numericDomain" in invalid else "numericContext"
            invalid[key]["target"] = "Nat.succ/@constant"
            with self.assertRaises(ValueError):
                operators.inspect(invalid, row["variables"], records)

    def test_source_owned_numeral_domain_survives_report_serialization(self):
        import json

        c = operators.chapter
        annotation = {
            "scope": "numbers",
            "bindings": {"metric": {"symbol": "d", "target": "D/d"}},
            "numerals": {"type": "Real", "from": "metric"},
        }
        text = (
            "<!-- chapter-correspondence "
            + json.dumps(annotation)
            + " -->$ 12 $<!-- chapter-correspondence-end: numbers -->"
        )
        records = {"D": {"binders": [{"name": "d", "type": "ℝ → ℝ → ℝ", "instance": False}]}}
        report = c.report(text, c.scopes(text), records)
        row = json.loads(json.dumps(report))["formulas"][0]
        self.assertEqual(row["typeStatus"], "typechecked")
        self.assertEqual(row["inferredType"], "ℝ")
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(len(rows), 1)
        numeral = rows[0]
        self.assertEqual(numeral["rule"], "literal:numeral")
        self.assertEqual(numeral["operandStatus"], "matched")
        self.assertEqual(numeral["implicitArgumentStatus"], "matched")
        self.assertEqual(row["book"][numeral["operatorStart"] : numeral["operatorEnd"]], "12")
        self.assertEqual(numeral["lowering"]["target"], "D/d")
        with patch.object(c, "SOURCE") as source:
            source.read_text.return_value = text
            result = operators.inspect_formula_report(report, 0, validated=True, root_evidence=rows)
        self.assertEqual(result["nodes"][0]["sourceOperator"], "12")
        self.assertEqual(result["unresolved"], [])
        self.assertEqual(result["untracedOperators"], [])
        # A declared type must agree with the actual Lean witness, not merely
        # supply an annotation that makes the numeral elaborate.
        wrong_records = copy.deepcopy(records)
        wrong_records["D"]["binders"][0]["type"] = "ℕ → ℕ"
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], wrong_records)
        # Checks of the literal value and its implicit type remain independent.
        original = c.translate

        def wrong_expectations(*args, **kwargs):
            term, context = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "literal:numeral":
                    node["expectedOperands"][0]["candidate"] = "(13 : Nat)"
                    node["expectedImplicitArguments"][0]["candidate"] = "Nat"
            return term, context

        with patch.object(c, "translate", side_effect=wrong_expectations):
            wrong = operators.inspect(row["syntax"], row["variables"], records)[0]
        self.assertEqual(wrong["operandChecks"][0]["status"], "mismatch")
        self.assertEqual(wrong["implicitArgumentChecks"][0]["status"], "mismatch")
        annotation.pop("numerals")
        text = (
            "<!-- chapter-correspondence "
            + json.dumps(annotation)
            + " -->$12$<!-- chapter-correspondence-end: numbers -->"
        )
        untyped = c.report(text, c.scopes(text), records)["formulas"][0]
        self.assertEqual(untyped["typeStatus"], "unresolved")
        self.assertIn("ambient number type", untyped["typeReason"])

    def test_source_disjoint_completeness_and_dense_union_contexts(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        names = {
            "disjoint-topology",
            "disjoint-completeness",
            "disjoint-completeness-tail",
            "disjoint-separability",
            "disjoint-separability-dense-union",
        }
        selected = {s["scope"]: s for s in scopes if s["scope"] in names}
        records = c.evidence(c.source_declarations(selected.values()))
        contexts = {name: c.context_reference(scope["context"]) for name, scope in selected.items()}
        for name in ("disjoint-completeness", "disjoint-separability", "disjoint-separability-dense-union"):
            self.assertEqual(selected[name]["bindings"], {})
            self.assertIn(contexts[name], records)
        self.assertEqual(records[contexts["disjoint-completeness"]]["binders"][-1]["name"], "h_complete")
        self.assertEqual(records[contexts["disjoint-separability"]]["binders"][-1]["name"], "h_separable")
        prose_scope = selected["disjoint-separability"]
        begin = text.rfind("<!-- chapter-correspondence", 0, prose_scope["start"])
        end = text.index("-->", prose_scope["end"]) + 3
        prose = text[begin:end]
        proof_report = c.report(prose, c.scopes(prose), records, trusted=False)
        self.assertEqual(proof_report["formulas"], [])
        self.assertEqual(len(proof_report["scopeContexts"]), 2)
        self.assertTrue(all(s["status"] == "matched" for s in proof_report["scopeContexts"]))
        missing = {k: v for k, v in records.items() if k != contexts["disjoint-separability"]}
        missing_report = c.report(prose, c.scopes(prose), missing, trusted=False)
        self.assertEqual(missing_report["scopeContexts"][0]["status"], "unresolved")
        scope = selected["disjoint-completeness-tail"]
        row = next(r for r in c.occurrences(text) if scope["start"] <= r["start"] < scope["end"])
        self.assertEqual(row["book"], "d_n")
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        term, context = c.translate(tree, variables, records)
        self.assertEqual(context, contexts["disjoint-completeness-tail"])
        rows = operators.inspect(tree, variables, records)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        proofs = [
            ("disjoint-completeness", "(show @IsMetricComplete (Sigma Y) sigmaMetric from h_complete)"),
            ("disjoint-completeness-tail", f"(show ({term}) = boundedMetricOn i from rfl)"),
            ("disjoint-completeness-tail", "(show @IsMetricComplete (Y i) (boundedMetricOn i) from hY_complete i)"),
            ("disjoint-completeness-tail", "(show ∀ n, N ≤ n → (u n).fst = i from h_eventually_i)"),
            ("disjoint-completeness-tail", "(show ∀ n (hn : N ≤ n), u n = Sigma.mk i (v n) from hv_spec)"),
            ("disjoint-completeness-tail", "(show CauchySeq v from hv_cauchy)"),
            (
                "disjoint-completeness-tail",
                "(show ∃ x : Y i, Tendsto v Filter.atTop (nhds x) from hY_complete i v hv_cauchy)",
            ),
            ("disjoint-separability", "(show TopologicalSpace.SeparableSpace (Sigma Y) from h_separable)"),
            ("disjoint-separability-dense-union", "(show Dsigma = ⋃ i : ℕ, Sigma.mk i '' D i from rfl)"),
        ]
        topology_scope = selected["disjoint-topology"]
        metric_row = next(
            r
            for r in c.occurrences(text)
            if topology_scope["start"] <= r["start"] < topology_scope["end"] and r["book"] == "d"
        )
        metric_tree, _ = c.located(c.syntax([metric_row["book"]])[0]["tree"])
        metric_variables, metric_effects = c.leaves(metric_tree)
        metric_variables = c.resolve_variables(metric_variables, metric_effects, metric_row, scopes, records)
        metric_term, metric_context = c.translate(metric_tree, metric_variables, records)
        self.assertEqual(metric_context, contexts["disjoint-topology"])
        proofs.append(("disjoint-topology", f"(show ({metric_term}) = sigmaMetric from rfl)"))
        topology_context = records[contexts["disjoint-topology"]]
        original_topology = next(
            b["name"] for b in topology_context["binders"] if b["type"] == "(n : ℕ) → TopologicalSpace (Y n)"
        )
        proofs.extend(
            [
                (
                    "disjoint-topology",
                    f"(show sigmaMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = @instTopologicalSpaceSigma ℕ Y «{original_topology}» from rfl)",
                ),
                (
                    "disjoint-topology",
                    "(show ∀ p q : Sigma Y, @dist (Sigma Y) sigmaMetric.toDist p q = dSigma p q from sigmaMetric_dist)",
                ),
            ]
        )
        dense_context = records[contexts["disjoint-separability-dense-union"]]
        family_spec = next(
            b["name"] for b in dense_context["binders"] if b["type"] == "∀ (i : ℕ), (D i).Countable ∧ Dense (D i)"
        )
        proofs.append(
            (
                "disjoint-separability-dense-union",
                f"(show Dsigma.Countable from countable_iUnion fun i => ((«{family_spec}» i).1).image _)",
            )
        )
        proofs.append(
            (
                "disjoint-separability-dense-union",
                f"""(show Dense Dsigma from by
          rw [dense_iff_inter_open]
          intro O hO hOne
          rcases hOne with ⟨⟨i, x⟩, hxO⟩
          have hopen : IsOpen {{y : Y i | Sigma.mk i y ∈ O}} := isOpen_sigma_iff.1 hO i
          have hnonempty : ({{y : Y i | Sigma.mk i y ∈ O}} : Set (Y i)).Nonempty := ⟨x, hxO⟩
          rcases ((«{family_spec}» i).2).inter_open_nonempty
              {{y : Y i | Sigma.mk i y ∈ O}} hopen hnonempty with ⟨y, hyO, hyD⟩
          exact ⟨⟨i, y⟩, hyO, mem_iUnion.2 ⟨i, mem_image_of_mem (Sigma.mk i) hyD⟩⟩)""",
            )
        )
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook Set Topology Filter\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n" + c.METRIC_POINT_ELAB
        for i, (name, proof) in enumerate(proofs):
            source += c.expression_definition({"lean": proof, "context": contexts[name]}, records, f"DisjointFinal{i}")
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"disjoint_final\\"}"\n'
        self.assertIn("disjoint_final", c.export(source))

    def test_source_radius_predicate_and_same_component_ball(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "disjoint-topology")
        records = c.evidence(c.source_declarations([scope]))
        row = next(
            r for r in c.occurrences(text) if scope["start"] <= r["start"] < scope["end"] and r["book"].startswith("<")
        )
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        with self.assertRaises(ValueError):
            c.translate(tree, [], records)
        for unsupported in ("< 1 2", "< 1.5", "> 1", "< x"):
            invalid, _ = c.located(c.syntax([unsupported])[0]["tree"])
            self.assertNotIn(
                "prefixPredicate", c.resolve_prefix_predicate(invalid, dict(row, book=unsupported), scopes)
            )
        tree = c.resolve_prefix_predicate(tree, row, scopes)
        term, context = c.translate(tree, [], records)
        nodes = operators.inspect(tree, [], records)
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        relation = next(n for n in nodes if n["rule"] == "predicate:<")
        self.assertEqual([r["status"] for r in relation["implicitArgumentChecks"]], ["matched", "matched"])
        self.assertEqual(row["book"][relation["operatorStart"] : relation["operatorEnd"]], "<")
        binder = next(n for n in nodes if n["rule"] == "binder:radius")
        self.assertEqual(len(binder["operandChecks"]), 2)
        self.assertEqual(binder["elaborated"]["kernel"]["domain"]["name"], "Real")
        proofs = [
            f"(show ({term}) = (fun radius : ℝ => radius < 1) from rfl)",
            f"""(show
          ∀ radius : ℝ, ({term}) radius → ∀ a b : Sigma Y,
            @dist (Sigma Y) sigmaMetric.toDist b a < radius → b.fst = a.fst from by
          intro radius hr a b hd
          rcases a with ⟨i, x⟩
          rcases b with ⟨j, y⟩
          change j = i
          by_contra hji
          have hdist : dSigma (⟨j, y⟩ : Sigma Y) ⟨i, x⟩ < radius := by
            simpa only [sigmaMetric_dist] using hd
          have hone : (1 : ℝ) < radius := by simpa only [dSigma, dite_eq_right hji] using hdist
          exact (lt_irrefl (1 : ℝ)) (hone.trans hr))""",
        ]
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook Set Topology\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n" + c.METRIC_POINT_ELAB
        for i, proof in enumerate(proofs):
            source += c.expression_definition({"lean": proof, "context": context}, records, f"RadiusClaim{i}")
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"radius_claim\\"}"\n'
        self.assertIn("radius_claim", c.export(source))
        wrong = copy.deepcopy(tree)
        wrong["prefixPredicate"]["bound"]["numericDomain"]["target"] = context + "/sigmaMetric"
        with self.assertRaises(ValueError):
            operators.inspect(wrong, [], records)

    def test_arithmetic_types_and_instances_come_from_source_operands(self):
        with self.assertRaisesRegex(ValueError, "no reviewed ambient number type"):
            inspect_formula("1+1")
        for formula, types in (
            ("x+1", {"x": "ℝ"}),
            ("1+x", {"x": "ℝ"}),
            ("x-y", {"x": "ℝ", "y": "ℝ"}),
            ("x*y", {"x": "ℝ", "y": "ℝ"}),
            ("x/2", {"x": "ℝ"}),
            ("n+1", {"n": "ℕ"}),
        ):
            with self.subTest(formula=formula):
                arithmetic = inspect_formula(formula, types)[-1]
                self.assertEqual(arithmetic["implicitArgumentStatus"], "matched")
                self.assertEqual(len(arithmetic["implicitArgumentChecks"]), 4)
        c = operators.chapter
        original = c.translate

        def wrong_type_and_instance(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "infix:+":
                    node["expectedImplicitArguments"][0]["candidate"] = "Nat"
                    node["expectedImplicitArguments"][3]["candidate"] = "(⟨fun a b : ℝ => a - b⟩ : HAdd ℝ ℝ ℝ)"
            return result

        with patch.object(c, "translate", side_effect=wrong_type_and_instance):
            wrong = inspect_formula("x+y", {"x": "ℝ", "y": "ℝ"})[-1]
        self.assertEqual(wrong["targetStatus"], "matched")
        self.assertTrue(all(check["status"] == "matched" for check in wrong["operandChecks"]))
        self.assertEqual(
            [check["status"] for check in wrong["implicitArgumentChecks"]],
            ["mismatch", "matched", "matched", "mismatch"],
        )
        self.assertEqual(wrong["operandStatus"], "mismatch")

    def test_comparison_types_and_instances_come_from_source_operands(self):
        for formula, types in (
            ("x<1", {"x": "ℝ"}),
            ("1<x", {"x": "ℝ"}),
            (r"n\le 1", {"n": "ℕ"}),
            ("x=y", {"x": "ℝ", "y": "ℝ"}),
        ):
            rows = inspect_formula(formula, types)
            relation = rows[-1]
            self.assertEqual(relation["implicitArgumentStatus"], "matched")
            self.assertEqual(relation["expectedImplicitArguments"][0]["role"], "source-operand-type")
        c = operators.chapter
        original = c.translate

        def wrong_type_and_order(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "infix:<":
                    node["expectedImplicitArguments"][0]["candidate"] = "Nat"
                    node["expectedImplicitArguments"][1]["candidate"] = "(⟨fun a b : ℝ => b < a⟩ : LT ℝ)"
            return result

        with patch.object(c, "translate", side_effect=wrong_type_and_order):
            wrong = inspect_formula("x<y", {"x": "ℝ", "y": "ℝ"})[-1]
        self.assertEqual(wrong["targetStatus"], "matched")
        self.assertTrue(all(check["status"] == "matched" for check in wrong["operandChecks"]))
        self.assertEqual([check["status"] for check in wrong["implicitArgumentChecks"]], ["mismatch", "mismatch"])
        self.assertEqual(wrong["operandStatus"], "mismatch")

    def test_natural_disjoint_union_checks_sigma_and_family(self):
        formula = r"\ExternalDisjointUnion_{n \in \omega} X_n"
        row, records = self.sequence_point_fixture(formula)
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        sigma = next(r for r in rows if r["rule"] == "type:dependent-sum")
        self.assertEqual(sigma["elaborated"]["head"], "Sigma")
        self.assertEqual(sigma["implicitArgumentStatus"], "matched")
        c = operators.chapter
        original_translate = c.translate

        def wrong_index(*args, **kwargs):
            result = original_translate(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "type:dependent-sum":
                    node["expectedImplicitArguments"][0]["candidate"] = "Int"
            return result

        with patch.object(c, "translate", side_effect=wrong_index):
            incorrect = operators.inspect(row["syntax"], row["variables"], records)
        incorrect_sigma = next(r for r in incorrect if r["rule"] == "type:dependent-sum")
        self.assertEqual(incorrect_sigma["targetStatus"], "matched")
        self.assertEqual(incorrect_sigma["implicitArgumentStatus"], "mismatch")
        self.assertTrue(all(r["status"] == "matched" for r in incorrect_sigma["operandChecks"]))
        family = next(r for r in rows if r["rule"] == "binder:mapsto")
        self.assertEqual(len(family["operandChecks"]), 2)
        covered = {(r["operatorStart"], r["operatorEnd"]) for r in rows}
        covered.update((c["start"], c["end"]) for r in rows for c in r.get("bindingComponents", []))
        for candidate in operators.operator_candidates(row["syntax"]):
            self.assertIn((candidate["start"], candidate["end"]), covered)
        for bad in (r"\ExternalDisjointUnion_{m \in \omega} X_n", r"\ExternalDisjointUnion_{n<2} X_n"):
            row, records = self.sequence_point_fixture(bad)
            with self.assertRaises(ValueError):
                operators.inspect(row["syntax"], row["variables"], records)

    def test_disjoint_union_rejects_wrong_fiber_and_domain_evidence(self):
        import json

        row, records = self.sequence_point_fixture(r"\ExternalDisjointUnion_{n \in \omega} X_n")
        c = operators.chapter
        with patch.object(c, "export", wraps=c.export) as export:
            rows = operators.inspect(row["syntax"], row["variables"], records)
            source = export.call_args.args[0]
        family = next(r for r in rows if r["rule"] == "binder:mapsto")
        body = family["expectedOperands"][0]["candidate"]
        wrong_body = body.replace("«" + family["expectedBinderName"] + "»", "0")
        before = "(" + json.dumps(family["marker"]) + ", #[" + json.dumps(body, ensure_ascii=False) + ', "ℕ"]'
        after = "(" + json.dumps(family["marker"]) + ", #[" + json.dumps(wrong_body, ensure_ascii=False) + ', "ℤ"]'
        self.assertIn(before, source)
        observed = c.export(source.replace(before, after))
        with patch.object(c, "export", return_value=observed):
            wrong = operators.inspect(row["syntax"], row["variables"], records)
        family = next(r for r in wrong if r["rule"] == "binder:mapsto")
        self.assertEqual([check["status"] for check in family["operandChecks"]], ["mismatch", "mismatch"])

    def test_product_domain_and_fiber_are_independently_checked(self):
        import json

        row, records = self.sequence_point_fixture(r"\prod X_n")
        c = operators.chapter
        with patch.object(c, "export", wraps=c.export) as export:
            rows = operators.inspect(row["syntax"], row["variables"], records)
            source = export.call_args.args[0]
        product = next(r for r in rows if r["rule"] == "binder:product")
        binder = product["expectedBinderName"]
        body = product["expectedOperands"][0]["candidate"]
        wrong_body = body.replace("«" + binder + "»", "(«" + binder + "» + 1)")
        before = "(" + json.dumps(product["marker"]) + ", #[" + json.dumps(body, ensure_ascii=False) + ', "ℕ"]'
        after = "(" + json.dumps(product["marker"]) + ", #[" + json.dumps(wrong_body, ensure_ascii=False) + ', "ℤ"]'
        self.assertIn(before, source)
        observed = c.export(source.replace(before, after))
        with patch.object(c, "export", return_value=observed):
            wrong = operators.inspect(row["syntax"], row["variables"], records)
        wrong_product = next(r for r in wrong if r["rule"] == "binder:product")
        self.assertEqual([c["status"] for c in wrong_product["operandChecks"]], ["mismatch", "mismatch"])
        self.assertEqual(wrong_product["operandStatus"], "mismatch")

    def test_starred_reference_requires_its_own_name(self):
        for formula in ("x^*", "x^{*}"):
            row, records = self.sequence_point_fixture(formula)
            rows = operators.inspect(row["syntax"], row["variables"], records)
            self.assertEqual(len(rows), 1)
            self.assertEqual(rows[0]["rule"], "name:star")
            self.assertEqual(rows[0]["expectedVariable"], "x0")
            self.assertEqual(rows[0]["targetStatus"], "matched")
            candidates = operators.operator_candidates(row["syntax"])
            self.assertEqual(candidates, [{"start": 1, "end": len(formula)}])
        row, records = self.sequence_point_fixture("x^*", explicit=False)
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)
        row, records = self.sequence_point_fixture("x^*")
        original = operators.chapter.translate

        def wrong_target(*args, **kwargs):
            term, context = original(*args, **kwargs)
            if kwargs.get("trace") is not None:
                term = term.replace("«x0»", "«x»")
            return term, context

        # Instrumentation may never change the original named reference.
        with patch.object(operators.chapter, "translate", side_effect=wrong_target), self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)

    def test_source_disjoint_union_bound_uses_specialized_original_metrics(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "disjoint-union-bounded-metrics")
        records = c.evidence({b["target"].rsplit("/", 1)[0] for b in scope["bindings"].values()})
        formulas = {r["book"]: r for r in c.occurrences(text) if scope["start"] <= r["start"] < scope["end"]}
        terms = {}
        probes = []
        for formula in (r"\Sequence{X_n}{n\in\omega}", r"d_n \le 1", "X_n"):
            tree, _ = c.located(c.syntax([formula])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, formulas[formula], scopes, records)
            terms[formula], context = c.translate(tree, variables, records)
            probes.append((tree, variables, records))
        for rows in operators.inspect_many(probes):
            self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        evidence = records[context]
        self.assertEqual(evidence["unfoldings"], ["PolishSpaceBook.countable_disjoint_union_polish"])
        self.assertNotIn("ι", [b["name"] for b in evidence["binders"]])
        self.assertEqual(next(b["type"] for b in evidence["binders"] if b["name"] == "i"), "ℕ")
        choices = [b for b in evidence["binders"] if b["type"].count("∧") == 3]
        self.assertEqual(len(choices), 1)
        bound_proof = "(«" + choices[0]["name"] + "» i).2.2.2 a b"
        proofs = [
            "(show (" + terms[r"\Sequence{X_n}{n\in\omega}"] + ") = Y from rfl)",
            "(show (" + terms["X_n"] + ") = Y i from rfl)",
            (
                "(show (" + terms[r"d_n \le 1"] + ") from by intro a b; "
                "change @dist (Y i) (boundedMetricOn i).toDist a b ≤ 1; "
                "rw [metric_eq i]; exact " + bound_proof + ")"
            ),
        ]
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook Set Topology\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n" + c.METRIC_POINT_ELAB
        for i, proof in enumerate(proofs):
            source += c.expression_definition({"lean": proof, "context": context}, records, f"DisjointBoundIdentity{i}")
        source += r"""
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.logInfo "SORT_PILOT {\"declaration\":\"disjoint_bound_verified\"}"
"""
        self.assertIn("disjoint_bound_verified", c.export(source))

    def test_source_product_separability_dense_family_and_reference(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "product-separability")
        records = c.evidence({b["target"].rsplit("/", 1)[0] for b in scope["bindings"].values()})
        formulas = {r["book"]: r for r in c.occurrences(text) if scope["start"] <= r["start"] < scope["end"]}
        terms = {}
        for formula in (r"D_n \IncludedIn X_n", "x^*", "D_n", r"x^* \in \prod X_n"):
            tree, _ = c.located(c.syntax([formula])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, formulas[formula], scopes, records)
            terms[formula], context = c.translate(tree, variables, records)
            rows = operators.inspect(tree, variables, records)
            self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        dense = terms["D_n"]
        proofs = [
            "(show (" + terms[r"D_n \IncludedIn X_n"] + ") from Set.subset_univ _)",
            "(show (" + terms[r"x^* \in \prod X_n"] + ") from Set.mem_univ _)",
            f"(show ({dense}).Countable from countable_range _)",
            f"(show Dense ({dense}) from TopologicalSpace.denseRange_denseSeq (α := Y n))",
            "(show (" + terms["x^*"] + ") = Classical.choice hprod from rfl)",
            (
                "(show Dprod = {y | Set.Finite {n | y n ≠ x0 n} ∧ "
                "∀ n, y n ≠ x0 n → y n ∈ coordinateDense n} from Dprod_description)"
            ),
            (
                "(show ({y | Set.Finite {n | y n ≠ x0 n} ∧ "
                "∀ n, y n ≠ x0 n → y n ∈ coordinateDense n} : Set ((n : ℕ) → Y n)).Countable "
                "from by rw [← Dprod_description]; exact countable_range _)"
            ),
        ]
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\nopen PolishSpaceBook Set Topology\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n" + c.METRIC_POINT_ELAB
        for i, proof in enumerate(proofs):
            source += c.expression_definition({"lean": proof, "context": context}, records, f"ProductDenseIdentity{i}")
        source += 'run_cmd Lean.Elab.Command.liftTermElabM do\n  Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"dense_verified\\"}"\n'
        self.assertIn("dense_verified", c.export(source))

    def test_type_family_copies_are_all_checked_and_merged(self):
        row, records = self.sequence_point_fixture(r"x_n \in X_n")
        c = operators.chapter
        with patch.object(c, "export", wraps=c.export) as export:
            rows = operators.inspect(row["syntax"], row["variables"], records)
            source = export.call_args.args[0]
        family = [r for r in rows if r.get("expectedVariable") == "Y"]
        self.assertGreater(len(family), 1)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        grouped = {}
        for mapping in rows:
            operators.merge_operator_call(grouped, mapping)
        key = (family[0]["operatorStart"], family[0]["operatorEnd"], family[0]["rule"])
        self.assertEqual(len(grouped[key]["calls"]), len(family))
        # Each mapping owns its spans; offsetting one call must not move another.
        other_span = copy.deepcopy(family[1]["operandSpans"])
        family[0]["operandSpans"][0]["start"] += 100
        self.assertEqual(family[1]["operandSpans"], other_span)
        # Re-elaborate a wrong expected index: every copied application must fail.
        wrong_source = source
        marker = family[0]["marker"]
        wrong_source = wrong_source.replace('("' + marker + '", #["«n»"]', '("' + marker + '", #["«k»"]')
        self.assertNotEqual(wrong_source, source)
        observed = c.export(wrong_source)
        with patch.object(c, "export", return_value=observed):
            wrong = operators.inspect(row["syntax"], row["variables"], records)
        family_wrong = [r for r in wrong if r.get("expectedVariable") == "Y"]
        self.assertTrue(all(r["operandStatus"] == "mismatch" for r in family_wrong))
        grouped = {}
        for mapping in wrong:
            operators.merge_operator_call(grouped, mapping)
        self.assertEqual(grouped[key]["operandStatus"], "mismatch")
        # Fanout is allowed only for the explicit type-position marker.
        missing = copy.deepcopy(observed)
        missing["operators"]["nodes"] = [n for n in missing["operators"]["nodes"] if n["marker"] != marker]
        with patch.object(c, "export", return_value=missing), self.assertRaisesRegex(ValueError, "0 occurrences"):
            operators.inspect(row["syntax"], row["variables"], records)
        duplicated = copy.deepcopy(observed)
        value_marker = next(r["marker"] for r in rows if r.get("expectedVariable") == "x")
        duplicated["operators"]["nodes"].append(
            copy.deepcopy(next(n for n in duplicated["operators"]["nodes"] if n["marker"] == value_marker))
        )
        with patch.object(c, "export", return_value=duplicated), self.assertRaisesRegex(ValueError, "2 occurrences"):
            operators.inspect(row["syntax"], row["variables"], records)

    def test_sequence_superscript_and_coordinate_preserve_both_arguments(self):
        formula = "x^k_n"
        row, records = self.sequence_point_fixture(formula)
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual([r["rule"] for r in rows], ["index:superscript", "index:subscript"])
        self.assertEqual([formula[r["operatorStart"] : r["operatorEnd"]] for r in rows], ["^", "_"])
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        self.assertEqual(rows[-1]["calleeCheck"]["status"], "matched")
        original = operators.chapter.translate

        def wrong_function(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace("«u»", "«v»"), context

        with patch.object(operators.chapter, "translate", side_effect=wrong_function):
            rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(r["targetStatus"] == "mismatch" for r in rows))

        def wrong_index(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace("(«k»)", "(«n»)"), context

        with patch.object(operators.chapter, "translate", side_effect=wrong_index):
            rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[0]["operandStatus"], "mismatch")
        self.assertEqual(rows[1]["calleeCheck"]["status"], "mismatch")
        row, records = self.sequence_point_fixture("x^k", explicit=False)
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)

    def test_sequence_superscript_preserves_limit_and_lexical_sequence_index(self):
        row, records = self.sequence_point_fixture(r"\Sequence{x^k_n}{k\in\omega}")
        self.assertTrue(all(v.get("localBinder") for v in row["variables"] if v["symbol"] == "k"))
        self.assertTrue(
            all(
                r["targetStatus"] == r["operandStatus"] == "matched"
                for r in operators.inspect(row["syntax"], row["variables"], records)
            )
        )
        row, records = self.sequence_point_fixture("x_n")
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[0]["expectedVariable"], "x")
        self.assertEqual(rows[0]["targetStatus"], "matched")

    def test_numeric_power_checks_integer_exponent_and_real_instance(self):
        formula = r"2^{-n}"
        rows = inspect_formula(formula, {"n": "ℕ"})
        self.assertEqual([r["rule"] for r in rows], ["unary:-", "power:real-integer"])
        self.assertEqual([formula[r["operatorStart"] : r["operatorEnd"]] for r in rows], ["-", "^"])
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        self.assertTrue(all(r["implicitArgumentStatus"] == "matched" for r in rows))
        original = operators.chapter.translate

        def wrong(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace("(2 : ℝ)", "(3 : ℝ)"), context

        with patch.object(operators.chapter, "translate", side_effect=wrong):
            rows = inspect_formula(formula, {"n": "ℕ"})
        self.assertEqual(rows[-1]["targetStatus"], "matched")
        self.assertEqual(rows[-1]["operandStatus"], "mismatch")
        with self.assertRaises(ValueError):
            inspect_formula(formula, {"n": "ℝ"})
        with self.assertRaises(ValueError):
            inspect_formula("x^n", {"x": "ℝ", "n": "ℕ"})

    def test_numeric_power_preserves_multidigit_bases_and_parenthesized_exponents(self):
        formula = r"12^{-(n+10)}"
        rows = inspect_formula(formula, {"n": "ℕ"})
        self.assertEqual([r["rule"] for r in rows], ["infix:+", "unary:-", "power:real-integer"])
        self.assertEqual(rows[-1]["expectedOperands"][0]["candidate"], "(12 : ℝ)")
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        # The source power is equal to the weight used by the book's Lean proof.
        row, records = self.dependent_metric_fixture(r"2^{-n}")
        term, _ = operators.chapter.translate(row["syntax"], row["variables"], records)
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\nexample (n : ℕ) : "
        source += term + " = (1 / (2 : ℝ)) ^ n := by simp [zpow_neg, zpow_natCast, one_div, inv_pow]\n"
        row, records = self.dependent_metric_fixture(r"2^{-(n-1)}")
        term, _ = operators.chapter.translate(row["syntax"], row["variables"], records)
        source += "example : (fun n : ℕ => " + term + ") 0 = 2 := by norm_num\n"
        source += "run_cmd Lean.Elab.Command.liftTermElabM do\n"
        source += r'  Lean.logInfo "SORT_PILOT {\"declaration\":\"weight_identity\",\"verified\":true}"' + "\n"
        self.assertTrue(operators.chapter.export(source)["weight_identity"]["verified"])

    def test_weighted_metric_juxtaposition_has_an_explicit_boundary(self):
        formula = r"2^{-n}d_n(x_n,y_n)"
        row, records = self.dependent_metric_fixture(formula)
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[-1]["rule"], "infix:implicit-multiply")
        self.assertEqual(rows[-1]["lowering"], "juxtaposition")
        self.assertEqual(rows[-1]["operatorStart"], len(r"2^{-n}"))
        self.assertEqual(rows[-1]["operatorEnd"], rows[-1]["operatorStart"])
        self.assertIn(
            {"start": len(r"2^{-n}"), "end": len(r"2^{-n}"), "notation": "juxtaposition"},
            operators.operator_candidates(row["syntax"]),
        )
        self.assertEqual(rows[-1]["implicitArgumentStatus"], "matched")
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        self.assertEqual(
            [formula[o["start"] : o["end"]] for o in rows[-1]["operandSpans"]], [r"2^{-n}", "d_n(x_n,y_n)"]
        )
        row, records = self.dependent_metric_fixture(r"2^{-n} d_n (x_n,y_n)")
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        original = operators.chapter.translate

        def wrong(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace(" * ", " + ", 1), context

        with patch.object(operators.chapter, "translate", side_effect=wrong):
            changed = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(changed["elaborated"]["head"], "HAdd.hAdd")
        self.assertEqual(changed["expectedHead"], "HMul.hMul")
        self.assertEqual(changed["targetStatus"], "mismatch")
        self.assertEqual(changed["implicitArgumentStatus"], "mismatch")
        self.assertEqual(changed["implicitArgumentChecks"][-1]["typeStatus"], "mismatch")
        self.assertEqual(changed["operandStatus"], "mismatch")

    def test_natural_sums_keep_scope_bounds_and_summability_separate(self):
        row, records = self.dependent_metric_fixture(r"\sum_{n\in\omega}2^{-n}")
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[-1]["rule"], "sum:infinite")
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        self.assertEqual(rows[-1]["implicitArgumentStatus"], "matched")
        self.assertEqual(rows[-1]["requirementStatus"], "proved")
        self.assertTrue(rows[-1]["semanticRequirements"][0]["kernelChecked"])
        row, records = self.dependent_metric_fixture(r"\sum_{n\in\omega}1")
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[-1]["requirementStatus"], "unresolved")
        row, records = self.dependent_metric_fixture(r"\sum_{n<n}2^{-n}")
        variables = [v for v in row["variables"] if v["symbol"] == "n"]
        self.assertEqual([v.get("localBinder", False) for v in variables], [True, False, True])
        self.assertEqual(variables[0]["leanName"], variables[2]["leanName"])
        self.assertNotEqual(variables[0]["leanName"], variables[1]["leanName"])
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[-1]["rule"], "sum:finite")
        self.assertEqual(rows[-1]["operandStatus"], "matched")
        self.assertEqual(rows[-1]["implicitArgumentStatus"], "matched")
        row, _ = self.dependent_metric_fixture(r"\sum_{n<m}2^{-n}+n")
        variables = [v for v in row["variables"] if v["symbol"] == "n"]
        self.assertEqual([v.get("localBinder", False) for v in variables], [True, True, False])

    def test_weighted_sum_preserves_dependent_point_arguments(self):
        row, records = self.dependent_metric_fixture(r"\sum_{n\in\omega}2^{-n}d_n(x_n,y_n)")
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[-1]["rule"], "sum:infinite")
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        # Arbitrary metrics and points do not imply a summable distance sequence.
        self.assertEqual(rows[-1]["requirementStatus"], "unresolved")

    def test_unreviewed_set_comprehension_does_not_capture_outer_points(self):
        row, records = self.dependent_metric_fixture(r"\left\{x,y:\sum_{n<m}2^{-n}d_n(x_n,y_n)<1\right\}")
        self.assertTrue(any(e["command"] == "unreviewed-set-builder" for e in row["bindingEffects"]))
        self.assertTrue(all(v["status"] == "unresolved" for v in row["variables"]))
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)

    def test_predicate_set_binds_generator_and_checks_domain_and_predicate(self):
        formula = r"\left\{y:d(x,y)<1\right\}"
        row, records = self.metric_fixture(formula)
        self.assertTrue(all(v.get("localBinder") for v in row["variables"] if v["symbol"] == "y"))
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[-1]["expectedHead"], "Set.ofPred")
        self.assertEqual(rows[-1]["implicitArgumentStatus"], "matched")
        self.assertTrue(all(r["operandStatus"] == r["targetStatus"] == "matched" for r in rows))
        self.assertEqual(formula[rows[-1]["operatorStart"] : rows[-1]["operatorEnd"]], r"\{")
        original = operators.chapter.translate

        def wrong(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace(" < ", " ≤ "), context

        with patch.object(operators.chapter, "translate", side_effect=wrong):
            rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[-1]["operandStatus"], "mismatch")
        changed_order = next(r for r in rows if r["rule"] == "infix:<")
        self.assertEqual(changed_order["implicitArgumentChecks"][1]["typeStatus"], "mismatch")

        row, records = self.metric_fixture(r"\{z:d(x,z)<1\}")
        self.assertTrue(all(v["status"] == "unresolved" for v in row["variables"] if v["symbol"] == "z"))
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)
        row, _ = self.metric_fixture(r"\{y:d(x,y)<1\},y")
        points = [v for v in row["variables"] if v["symbol"] == "y"]
        self.assertEqual([v.get("localBinder", False) for v in points], [True, True, False])
        row, records = self.metric_fixture(r"\{y:y\in\{y:y>0\}\}")
        names = [v["leanName"] for v in row["variables"]]
        self.assertEqual(names[0], names[1])
        self.assertEqual(names[2], names[3])
        self.assertNotEqual(names[0], names[2])
        self.assertTrue(
            all(r["operandStatus"] == "matched" for r in operators.inspect(row["syntax"], row["variables"], records))
        )

    def test_tail_sum_preserves_lower_bound_and_shadowing(self):
        row, records = self.dependent_metric_fixture(r"\sum_{n\ge m}2^{-n}")
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[-1]["rule"], "sum:tail")
        self.assertEqual(rows[-1]["requirementStatus"], "proved")
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        self.assertEqual(rows[-1]["implicitArgumentStatus"], "matched")
        self.assertEqual(rows[-1]["semanticRequirements"][0]["sourceOperand"], 1)
        original = operators.chapter.translate

        def wrong(*args, **kwargs):
            term, context = original(*args, **kwargs)
            changed = term.replace("+ («m» : ℕ)", "+ («m» + 1 : ℕ)")
            return changed, context

        with patch.object(operators.chapter, "translate", side_effect=wrong):
            rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[-1]["operandStatus"], "mismatch")
        row, _ = self.dependent_metric_fixture(r"\sum_{n\ge n}2^{-n}+n")
        variables = [v for v in row["variables"] if v["symbol"] == "n"]
        self.assertEqual([v.get("localBinder", False) for v in variables], [True, False, True, False])
        row, records = self.dependent_metric_fixture(r"\sum_{n\ge m}1")
        self.assertEqual(
            operators.inspect(row["syntax"], row["variables"], records)[-1]["requirementStatus"], "unresolved"
        )

    def test_tail_sum_reindexing_is_valid_for_arbitrary_real_functions(self):
        source = r"""import PolishSpaceBook.PolishSpaces
import Lean
example (M : ℕ) (f : ℕ → ℝ) : (∑' k, f (k + M)) = ∑' n : {n : ℕ // M ≤ n}, f n := by
  let e : ℕ ≃ {n : ℕ // M ≤ n} := {
    toFun := fun k => ⟨k + M, by omega⟩
    invFun := fun n => n.val - M
    left_inv := by intro k; dsimp; omega
    right_inv := by intro n; apply Subtype.ext; dsimp; omega }
  exact e.tsum_eq (fun n => f n)
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.logInfo "SORT_PILOT {\"declaration\":\"tail_reindex\",\"verified\":true}"
"""
        self.assertTrue(operators.chapter.export(source)["tail_reindex"]["verified"])

    def test_finite_sum_rejects_changed_upper_bound(self):
        row, records = self.dependent_metric_fixture(r"\sum_{n<m}2^{-n}")
        original = operators.chapter.translate

        def wrong(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace("Finset.range («m» : ℕ)", "Finset.range («m» + 1 : ℕ)"), context

        with patch.object(operators.chapter, "translate", side_effect=wrong):
            rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[-1]["targetStatus"], "matched")
        self.assertEqual(rows[-1]["operandStatus"], "mismatch")

    def test_report_rejects_code_changed_since_loading(self):
        operators.assert_current_code()
        with (
            patch.object(operators, "LOADED_EXTRACTOR_HASH", "stale"),
            self.assertRaisesRegex(ValueError, "changed during inspection"),
        ):
            operators.assert_current_code()

    def test_source_product_weight_equals_original_proof_local_term(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "product-metric-construction")
        names = {b["target"].rsplit("/", 1)[0] for b in scope["bindings"].values()}
        records = c.evidence(names)
        row = next(
            r
            for r in c.occurrences(text)
            if scope["start"] <= r["start"] < scope["end"] and r["book"] == r"2^{-n}d_n(x_n,y_n)"
        )
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        term, context = c.translate(tree, variables, records)
        self.assertIn("term", {b["name"] for b in records[context]["binders"]})
        proof = f"(show ({term}) = term x y n from by "
        proof += "simp only [term, weight, zpow_neg, Int.ofNat_eq_natCast, zpow_natCast, one_div, inv_pow])"
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n"
        source += "open PolishSpaceBook Set Topology\n" + c.METRIC_POINT_ELAB
        source += c.expression_definition({"lean": proof, "context": context}, records, "ProductWeightIdentity")
        source += "run_cmd Lean.Elab.Command.liftTermElabM do\n"
        source += r'  Lean.logInfo "SORT_PILOT {\"declaration\":\"source_weight_identity\",\"verified\":true}"' + "\n"
        self.assertTrue(c.export(source)["source_weight_identity"]["verified"])

        definition = next(
            r
            for r in c.occurrences(text)
            if scope["start"] <= r["start"] < scope["end"] and r"\sum_{n \in \omega}" in r["book"]
        )
        tree, _ = c.located(c.syntax([definition["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, definition, scopes, records)
        rows = operators.inspect(tree, variables, records)
        self.assertEqual(len(rows), 14)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        summation = next(r for r in rows if r["rule"] == "sum:infinite")
        self.assertEqual(summation["requirementStatus"], "proved")
        self.assertTrue(summation["semanticRequirements"][0]["kernelChecked"])
        proposition, context = c.translate(tree, variables, records)
        proof = f"(show ({proposition}) from by "
        proof += "simp only [dPi, term, weight, zpow_neg, Int.ofNat_eq_natCast, zpow_natCast, one_div, inv_pow])"
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n"
        source += "open PolishSpaceBook Set Topology\n" + c.METRIC_POINT_ELAB
        source += c.expression_definition({"lean": proof, "context": context}, records, "ProductSumIdentity")
        source += "run_cmd Lean.Elab.Command.liftTermElabM do\n"
        source += r'  Lean.logInfo "SORT_PILOT {\"declaration\":\"source_sum_identity\",\"verified\":true}"' + "\n"
        self.assertTrue(c.export(source)["source_sum_identity"]["verified"])

    def test_source_product_completeness_uses_the_chosen_limit_and_original_sequence(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "product-completeness")
        records = c.evidence({b["target"].rsplit("/", 1)[0] for b in scope["bindings"].values()})
        formulas = {r["book"]: r for r in c.occurrences(text) if scope["start"] <= r["start"] < scope["end"]}
        terms = {}
        context = None
        for formula in [
            r"\Sequence{x^k}{k\in\omega}",
            r"\Sequence{x^k_n}{k\in\omega}",
            r"x_n \in X_n",
            r"x=\Sequence{x_n}{n\in\omega}",
        ]:
            row = formulas[formula]
            tree, _ = c.located(c.syntax([formula])[0]["tree"])
            variables, effects = c.leaves(tree)
            variables = c.resolve_variables(variables, effects, row, scopes, records)
            term, current = c.translate(tree, variables, records)
            if context is not None:
                self.assertEqual(context, current)
            context = current
            terms[formula] = term
            if formula in {r"\Sequence{x^k_n}{k\in\omega}", r"x_n \in X_n"}:
                rows = operators.inspect(tree, variables, records)
                self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        sequence = terms[r"\Sequence{x^k}{k\in\omega}"]
        coordinates = terms[r"\Sequence{x^k_n}{k\in\omega}"]
        membership = terms[r"x_n \in X_n"]
        limit = terms[r"x=\Sequence{x_n}{n\in\omega}"]
        proofs = [
            f"(show ({sequence}) = u from rfl)",
            f"(show CauchySeq ({coordinates}) from hcoord_cauchy n)",
            f"(show Filter.Tendsto ({coordinates}) Filter.atTop (nhds (x n)) from hx n)",
            f"(show ({membership}) from Set.mem_univ _)",
            f"(show ({limit}) from rfl)",
        ]
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n"
        source += "open PolishSpaceBook Set Topology\n" + c.METRIC_POINT_ELAB
        for i, proof in enumerate(proofs):
            source += c.expression_definition({"lean": proof, "context": context}, records, f"ProductLimitIdentity{i}")
        source += "run_cmd Lean.Elab.Command.liftTermElabM do\n"
        source += r'  Lean.logInfo "SORT_PILOT {\"declaration\":\"product_limit\",\"verified\":true}"' + "\n"
        self.assertTrue(c.export(source)["product_limit"]["verified"])

    def test_source_product_topology_sum_bound_matches_original_proof(self):
        c = operators.chapter
        text = c.SOURCE.read_text()
        scopes = c.scopes(text)
        scope = next(s for s in scopes if s["scope"] == "product-topology-neighborhood")
        names = {b["target"].rsplit("/", 1)[0] for b in scope["bindings"].values()}
        records = c.evidence(names)
        row = next(
            r
            for r in c.occurrences(text)
            if scope["start"] <= r["start"] < scope["end"] and r["book"].startswith(r"d(x,y)\le\sum")
        )
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        rows = operators.inspect(tree, variables, records)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        self.assertEqual(sum(r["rule"] == "sum:tail" for r in rows), 2)
        self.assertTrue(all(r["requirementStatus"] == "proved" for r in rows if r["rule"] == "sum:tail"))
        proposition, context = c.translate(tree, variables, records)
        proof = (
            f"(show ({proposition}) from by "
            + r"""
          have hsum : dPi x y ≤ (∑ n ∈ Finset.range M, term x y n) + (∑' n, weight (n+M)) := by
            change (∑' n, term x y n) ≤ _
            rw [← (term_summable x y).sum_add_tsum_nat_add M]
            exact add_le_add le_rfl htail
          have hbound : (∑ n ∈ Finset.range M, term x y n) + (∑' n, weight (n+M)) < ε := by
            linarith [hpartial, hM]
          simpa only [term, weight, zpow_neg, Int.ofNat_eq_natCast, zpow_natCast, one_div, inv_pow]
            using And.intro hsum hbound)
"""
        )
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n"
        source += "open PolishSpaceBook Set Topology\n" + c.METRIC_POINT_ELAB
        source += c.expression_definition({"lean": proof, "context": context}, records, "ProductTopologyBound")
        source += "run_cmd Lean.Elab.Command.liftTermElabM do\n"
        source += r'  Lean.logInfo "SORT_PILOT {\"declaration\":\"topology_bound\",\"verified\":true}"' + "\n"
        self.assertTrue(c.export(source)["topology_bound"]["verified"])

        row = next(
            r
            for r in c.occurrences(text)
            if scope["start"] <= r["start"] < scope["end"] and r["book"].startswith(r"V=\left\{")
        )
        tree, _ = c.located(c.syntax([row["book"]])[0]["tree"])
        variables, effects = c.leaves(tree)
        variables = c.resolve_variables(variables, effects, row, scopes, records)
        rows = operators.inspect(tree, variables, records)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        generator = next(r for r in rows if r["rule"] == "binder:predicate-set")
        self.assertEqual(generator["implicitArgumentStatus"], "matched")
        self.assertTrue(all(v.get("localBinder") for v in variables if v["symbol"] == "y"))
        proposition, context = c.translate(tree, variables, records)
        proof = f"(show ({proposition}) from by "
        proof += "simp only [V, term, weight, zpow_neg, Int.ofNat_eq_natCast, zpow_natCast, one_div, inv_pow])"
        source = "import PolishSpaceBook.PolishSpaces\nimport Lean\n"
        source += "set_option autoImplicit false\nset_option linter.unusedVariables false\n"
        source += "open PolishSpaceBook Set Topology\n" + c.METRIC_POINT_ELAB
        source += c.expression_definition({"lean": proof, "context": context}, records, "ProductNeighborhoodIdentity")
        source += "run_cmd Lean.Elab.Command.liftTermElabM do\n"
        source += r'  Lean.logInfo "SORT_PILOT {\"declaration\":\"neighborhood_identity\",\"verified\":true}"' + "\n"
        self.assertTrue(c.export(source)["neighborhood_identity"]["verified"])

    def metric_fixture(self, formula, overrides=None):
        import json

        c = operators.chapter
        types = {
            "d": "MetricSpace ℝ",
            "e": "MetricSpace ℝ",
            "x": "ℝ",
            "y": "ℝ",
            "C": "Set ℝ",
            "D": "Set ℝ",
            "u": "ℕ → ℝ",
        }
        types.update(overrides or {})
        bindings = {n: {"symbol": n, "target": "D/" + n} for n in types if n != "u"}
        bindings["x"]["occurrence"] = "unsubscripted"
        bindings["sequence-x"] = {"symbol": "x", "occurrence": "subscript-base", "target": "D/u"}
        data = {"scope": "metric", "bindings": bindings}
        text = (
            "<!-- chapter-correspondence "
            + json.dumps(data)
            + " -->$"
            + formula
            + "$<!-- chapter-correspondence-end: metric -->"
        )
        records = {"D": {"binders": [{"name": n, "type": ty, "instance": False} for n, ty in types.items()]}}
        row = c.report(text, c.scopes(text), records, trusted=False)["formulas"][0]
        return row, records

    def test_distance_to_set_checks_metric_and_set_arguments(self):
        formula = r"d(x,\, \SetDifference{\R}{C})"
        row, records = self.metric_fixture(formula)
        rows = operators.inspect(row["syntax"], row["variables"], records)
        metric = rows[-1]
        self.assertEqual(metric["elaborated"]["head"], "Metric.infDist")
        self.assertEqual(metric["rule"], "application:distance-to-set")
        self.assertEqual(metric["implicitArgumentStatus"], "matched")
        self.assertEqual(metric["operandStatus"], "matched")
        self.assertEqual(metric["requirementStatus"], "unresolved")
        self.assertEqual([r["role"] for r in metric["expectedImplicitArguments"]], ["metric-domain", "metric-instance"])
        self.assertEqual(
            formula[metric["operandSpans"][1]["start"] : metric["operandSpans"][1]["end"]], r"\SetDifference{\R}{C}"
        )

    def test_distance_to_comprehension_keeps_its_set_role_and_nonemptiness_obligation(self):
        formula = r"d(x,\{s:P(s)\})"
        row, records = self.metric_fixture(formula, {"s": "ℝ", "P": "ℝ → Prop"})
        c = operators.chapter
        with legacy_oracle(c):
            legacy, context = c.translate(row["syntax"], row["variables"], records)
        with self.assertRaises(ValueError):
            c.export(
                operators.HEADER
                + c.expression_definition({"lean": legacy, "context": context}, records, "LegacyConstructedSetPoint")
            )
        nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(nodes[-1]["rule"], "application:distance-to-set")
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        self.assertEqual(nodes[-1]["requirementStatus"], "unresolved")
        records["D"]["binders"].append({"name": "hP", "type": "(Set.ofPred P).Nonempty", "instance": False})
        checked = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(checked["requirementStatus"], "proved")
        self.assertTrue(checked["semanticRequirements"][0]["kernelChecked"])

    def test_bounded_infimum_binds_only_its_generator(self):
        formula = r"d(x,C):=\inf\{d(x,s):s\in C\}"
        row, records = self.metric_fixture(formula)
        records["D"]["binders"].append({"name": "hC", "type": "C.Nonempty", "instance": False})
        self.assertTrue(all(v["status"] == "resolved" for v in row["variables"]))
        bound = [v for v in row["variables"] if v["symbol"] == "s"]
        self.assertTrue(all(v["localBinder"] and v["leanType"] == "ℝ" for v in bound))
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        self.assertEqual(rows[-1]["rule"], "definition:=")
        self.assertEqual(rows[-1]["requirementStatus"], "proved")
        self.assertTrue(rows[-1]["semanticRequirements"][0]["kernelChecked"])
        infimum = next(r for r in rows if r["rule"] == "operation:infimum")
        self.assertEqual(infimum["requirementStatus"], "proved")
        for node in rows:
            self.assertEqual(node["implicitArgumentStatus"], "matched")
        self.assertEqual(
            {r["rule"] for r in rows},
            {
                "definition:=",
                "operation:infimum",
                "binder:image-set",
                "application:metric",
                "application:distance-to-set",
            },
        )

    def test_infimum_image_and_definition_reject_wrong_implicit_arguments(self):
        row, records = self.metric_fixture(r"d(x,C):=\inf\{d(x,s):s\in C\}")
        records["D"]["binders"].append({"name": "hC", "type": "C.Nonempty", "instance": False})
        c = operators.chapter
        original = c.translate

        def wrong(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] in {"binder:image-set", "definition:="}:
                    node["expectedImplicitArguments"][0]["candidate"] = "Nat"
                if node["rule"] == "binder:image-set":
                    node["expectedImplicitArguments"][1]["candidate"] = "Nat"
                if node["rule"] == "operation:infimum":
                    node["expectedImplicitArguments"][1]["candidate"] = "(⟨fun _ => 0⟩ : InfSet ℝ)"
            return result

        with patch.object(c, "translate", side_effect=wrong):
            nodes = operators.inspect(row["syntax"], row["variables"], records)
        for node in nodes:
            if node["rule"] in {"binder:image-set", "definition:=", "operation:infimum"}:
                self.assertEqual(node["targetStatus"], "matched")
                self.assertTrue(all(r["status"] == "matched" for r in node["operandChecks"]))
                self.assertEqual(node["implicitArgumentStatus"], "mismatch")
                self.assertEqual(node["operandStatus"], "mismatch")

    def test_mapsto_uses_mapped_domain_and_checks_it_independently(self):
        row, records = self.metric_fixture(r"x\mapsto x")
        self.assertTrue(all(v["localBinder"] and v["leanType"] == "ℝ" for v in row["variables"]))
        mapping = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(mapping["rule"], "binder:mapsto")
        self.assertEqual(mapping["operandStatus"], "matched")
        self.assertEqual(mapping["targetStatus"], "matched")
        original = operators.chapter.translate

        def wrong(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace(" : ℝ =>", " : ℤ =>"), context

        with patch.object(operators.chapter, "translate", side_effect=wrong):
            mapping = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(mapping["operandStatus"], "mismatch")
        row, _ = self.metric_fixture(r"z\mapsto d(z,C)")
        self.assertTrue(all(v["status"] == "unresolved" for v in row["variables"] if v["symbol"] == "z"))

    def test_membership_projects_points_without_changing_set_or_instance(self):
        row, records = self.metric_fixture(r"x\in C", {"x": "{p : ℝ // p > 0}"})
        mapping = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(mapping["targetStatus"], "matched")
        self.assertEqual(mapping["operandStatus"], "matched")
        self.assertIn("Subtype.val", str(mapping["operandChecks"][1]["actual"]))
        row, records = self.metric_fixture(r"x\in \SetDifference{\R}{C}", {"x": "{p : ℝ // p > 0}"})
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(sum(r["rule"] == "macro:SetDifference" for r in rows), 1)
        self.assertTrue(all(r["operandStatus"] == "matched" for r in rows))

    def dependent_metric_fixture(self, formula):
        import json

        c = operators.chapter
        types = [
            ("Y", "ℕ → Type"),
            ("d", "(n : ℕ) → MetricSpace (Y n)"),
            ("e", "(n : ℕ) → MetricSpace (Y n)"),
            ("x", "(n : ℕ) → Y n"),
            ("y", "(n : ℕ) → Y n"),
            ("n", "ℕ"),
            ("m", "ℕ"),
        ]
        bindings = {name: {"symbol": name, "target": "D/" + name} for name, _ in types}
        text = "<!-- chapter-correspondence " + json.dumps({"scope": "dependent", "bindings": bindings})
        text += " -->$" + formula + "$<!-- chapter-correspondence-end: dependent -->"
        records = {"D": {"binders": [{"name": n, "type": t, "instance": False} for n, t in types]}}
        row = c.report(text, c.scopes(text), records, trusted=False)["formulas"][0]
        return row, records

    def test_indexed_metric_uses_actual_dependent_domain_and_instance(self):
        row, records = self.dependent_metric_fixture("d_n(x_n,y_n)")
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual([r["rule"] for r in rows], ["index:subscript"] * 3 + ["application:metric"])
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        self.assertEqual(rows[-1]["implicitArgumentStatus"], "matched")
        original = operators.chapter.translate

        def wrong(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace("«d»", "«e»"), context

        with patch.object(operators.chapter, "translate", side_effect=wrong):
            wrong_rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(wrong_rows[-1]["implicitArgumentStatus"], "mismatch")
        self.assertEqual(wrong_rows[-1]["operandStatus"], "mismatch")
        row, records = self.dependent_metric_fixture("d_n(x_n,y_m)")
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)

    def test_indexed_metric_bound_does_not_leave_discarded_markers(self):
        row, records = self.dependent_metric_fixture(r"d_n\le 1")
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual([r["rule"] for r in rows], ["index:subscript", "relation:metric-le"])
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        self.assertEqual(rows[-1]["implicitArgumentStatus"], "matched")
        row, records = self.dependent_metric_fixture(r"d_n(x_n,y_n)\le 1")
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(rows[-1]["rule"], "infix:≤")
        self.assertTrue(all(r["operandStatus"] == "matched" for r in rows))

    def test_pointwise_metric_bound_uses_the_subtype_domain(self):
        domain = "{p : ℝ // p > 0}"
        row, records = self.metric_fixture(r"d\le f", {"f": f"{domain} → {domain} → ℝ"})
        mapping = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(mapping["rule"], "relation:metric-le")
        self.assertEqual(mapping["targetStatus"], "matched")
        self.assertEqual(mapping["operandStatus"], "matched")
        self.assertEqual(mapping["implicitArgumentStatus"], "matched")
        self.assertIn("Subtype.val", str(mapping["operandChecks"][0]["actual"]))
        row, records = self.metric_fixture(r"d\le 1")
        mapping = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(mapping["operandStatus"], "matched")

    def test_metric_restriction_records_product_and_uncurrying(self):
        row, records = self.metric_fixture(r"\restrict{d}{C\times D}")
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual([r["rule"] for r in rows], ["set:product", "operation:restrict"])
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        restriction = rows[-1]
        self.assertEqual(restriction["implicitArgumentStatus"], "matched")
        self.assertEqual([r["sourceOperand"] for r in restriction["expectedOperands"]], [1, 0])
        self.assertIn("Function.uncurry", str(restriction["operandChecks"][1]["actual"]))
        original = operators.chapter.translate

        def wrong(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace("Set.prod («C») («D»)", "Set.prod («D») («C»)"), context

        with patch.object(operators.chapter, "translate", side_effect=wrong):
            rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(r["targetStatus"] == "matched" for r in rows))
        self.assertTrue(all(r["operandStatus"] == "mismatch" for r in rows))

    def test_infimum_rejects_missing_domain_and_does_not_capture_outer_symbol(self):
        row, _ = self.metric_fixture(r"s:=\inf\{d(x,s):s\in C\}")
        variables = [v for v in row["variables"] if v["symbol"] == "s"]
        self.assertEqual(variables[0]["status"], "unresolved")
        self.assertTrue(all(v["localBinder"] for v in variables[1:]))
        row, _ = self.metric_fixture(r"\inf\{d(x,s):s\in C\}", {"C": "ℝ"})
        self.assertTrue(all(v["status"] == "unresolved" for v in row["variables"] if v["symbol"] == "s"))
        row, records = self.metric_fixture(r"\inf\{d(x,s):s\in C\}")
        original = operators.chapter.translate

        def wrong(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace("«C»", "«D»"), context

        with patch.object(operators.chapter, "translate", side_effect=wrong):
            rows = operators.inspect(row["syntax"], row["variables"], records)
        image = next(r for r in rows if r["rule"] == "binder:image-set")
        self.assertEqual(image["targetStatus"], "matched")
        self.assertEqual(image["operandStatus"], "mismatch")

    def test_defining_equality_requires_a_proof(self):
        row = inspect_formula("x:=y")[-1]
        self.assertEqual(row["operandStatus"], "matched")
        self.assertEqual(row["requirementStatus"], "unresolved")
        row = inspect_formula("x:=x")[-1]
        self.assertEqual(row["requirementStatus"], "proved")

    def test_batched_requirements_do_not_require_a_first_probe_declaration(self):
        empty, empty_records = self.metric_fixture("x")
        row, records = self.metric_fixture("d(x,C)")
        records["D"]["binders"].append({"name": "hC", "type": "C.Nonempty", "instance": False})
        equality, equality_records = self.metric_fixture("x:=x")
        results = operators.inspect_many(
            [
                (empty["syntax"], empty["variables"], empty_records),
                (row["syntax"], row["variables"], records),
                (equality["syntax"], equality["variables"], equality_records),
            ]
        )
        self.assertEqual(results[0], [])
        for nodes in results[1:]:
            self.assertEqual(nodes[-1]["requirementStatus"], "proved")
            self.assertTrue(nodes[-1]["semanticRequirements"][0]["kernelChecked"])

    def test_distance_nonempty_requirement_is_proved_only_with_evidence(self):
        row, records = self.metric_fixture("d(x,C)")
        records["D"]["binders"].append({"name": "hC", "type": "C.Nonempty", "instance": False})
        metric = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(metric["requirementStatus"], "proved")
        self.assertTrue(metric["semanticRequirements"][0]["kernelChecked"])
        row, records = self.metric_fixture(r"d(x,\SetDifference{\R}{C})")
        records["D"]["binders"].append({"name": "hC", "type": "Cᶜ.Nonempty", "instance": False})
        metric = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(metric["requirementStatus"], "proved")
        self.assertTrue(metric["semanticRequirements"][0]["kernelChecked"])
        row, records = self.metric_fixture(r"d(x,\SetDifference{\R}{\R})")
        metric = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(metric["requirementStatus"], "unresolved")

    def test_set_equality_to_carrier_uses_univ_without_changing_type_equality(self):
        for formula, rule in [(r"C=\R", "set:="), (r"C\ne\R", "set:≠")]:
            row = inspect_formula(formula, {"C": "Set ℝ"})[0]
            self.assertEqual(row["rule"], rule)
            self.assertEqual(row["operandStatus"], "matched")
            self.assertIn("Set.univ", str(row["operandChecks"][1]["actual"]))
        self.assertEqual(inspect_formula(r"\R=\R")[0]["rule"], "infix:=")

    def test_ambient_metric_projects_subtype_points(self):
        row, records = self.metric_fixture("d(x,C)")
        for binder in records["D"]["binders"]:
            if binder["name"] == "x":
                binder["type"] = "{p : ℝ // p > 0}"
        for variable in row["variables"]:
            if variable["symbol"] == "x":
                variable["leanType"] = "{p : ℝ // p > 0}"
        metric = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(metric["operandStatus"], "matched")
        self.assertEqual(metric["implicitArgumentStatus"], "matched")
        self.assertIn("Subtype.val", str(metric["operandChecks"][0]["actual"]))

        for binder in records["D"]["binders"]:
            if binder["name"] == "x":
                binder["type"] = "{p : Bool // p = true}"
        with self.assertRaisesRegex(ValueError, "Metric point does not belong"):
            operators.inspect(row["syntax"], row["variables"], records)

    def test_changing_metric_is_detected_even_with_matching_head_and_points(self):
        c = operators.chapter
        original = c.translate
        for formula in ("d(x,C)", "d(x,y)"):
            row, records = self.metric_fixture(formula)

            def wrong(*args, **kwargs):
                term, context = original(*args, **kwargs)
                return term.replace("«d»", "«e»"), context

            with patch.object(c, "translate", side_effect=wrong):
                metric = operators.inspect(row["syntax"], row["variables"], records)[-1]
            self.assertEqual(metric["targetStatus"], "matched")
            self.assertTrue(all(o["status"] == "matched" for o in metric["operandChecks"]))
            self.assertEqual(metric["implicitArgumentChecks"][0]["status"], "matched")
            self.assertEqual(metric["implicitArgumentChecks"][1]["status"], "mismatch")
            self.assertEqual(metric["operandStatus"], "mismatch")

    def test_reciprocal_distance_convergence_preserves_long_arrow_and_period(self):
        formula = r"\frac{1}{d(x_n, C)}\longrightarrow\frac{1}{d(x,C)}."
        row, records = self.metric_fixture(formula)
        rows = operators.inspect(row["syntax"], row["variables"], records)
        limit = rows[-1]
        self.assertEqual(limit["rule"], "relation:sequence-limit")
        self.assertEqual(formula[limit["operatorStart"] : limit["operatorEnd"]], r"\longrightarrow")
        self.assertEqual(
            formula[limit["operandSpans"][1]["start"] : limit["operandSpans"][1]["end"]], r"\frac{1}{d(x,C)}"
        )
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        for node in rows:
            checked = {a["argumentPosition"] for a in node.get("expectedImplicitArguments", [])}
            for position, argument in enumerate(node.get("elaborated", {}).get("arguments", [])):
                if argument["implicit"]:
                    self.assertIn(position, checked, (node["rule"], position))
                    self.assertEqual(node["implicitArgumentStatus"], "matched")

    def test_primed_functions_are_distinct_and_keep_their_full_span(self):
        formula = "d'(x,y)+d(x,y)"
        rows = inspect_formula(formula, {"d'": "ℝ → ℝ → ℝ", "d": "ℝ → ℝ → ℝ"})
        calls = [r for r in rows if r["rule"] == "application:function"]
        self.assertEqual([r["expectedVariable"] for r in calls], ["d'", "d"])
        self.assertEqual([formula[r["operatorStart"] : r["operatorEnd"]] for r in calls], ["d'", "d"])
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))

        original = operators.chapter.translate

        def unprimed(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace("«d'»", "«d»"), context

        with patch.object(operators.chapter, "translate", side_effect=unprimed):
            wrong = inspect_formula(formula, {"d'": "ℝ → ℝ → ℝ", "d": "ℝ → ℝ → ℝ"})
        wrong_calls = [r for r in wrong if r["rule"] == "application:function"]
        self.assertEqual([r["targetStatus"] for r in wrong_calls], ["mismatch", "matched"])

    def convergence_fixture(self, formula, domain="ℕ", selector="subscript-base", codomain="ℝ"):
        import json

        c = operators.chapter
        bindings = {
            "sequence": {"symbol": "x", "occurrence": selector, "target": "D/u"},
            "point": {"symbol": "x", "occurrence": "unsubscripted", "target": "D/a"},
            "function": {"symbol": "f", "target": "D/f"},
            "index": {"symbol": "n", "target": "D/n"},
        }
        data = {"scope": "convergence", "bindings": bindings}
        text = "<!-- chapter-correspondence " + json.dumps(data) + " -->$" + formula + "$"
        text += "<!-- chapter-correspondence-end: convergence -->"
        records = {
            "D": {
                "binders": [
                    {"name": name, "type": ty, "instance": False}
                    for name, ty in [
                        ("u", domain + " → " + codomain),
                        ("a", codomain),
                        ("b", codomain),
                        ("f", codomain + " → " + codomain),
                        ("n", "ℤ"),
                    ]
                ]
            }
        }
        row = c.report(text, c.scopes(text), records, trusted=False)["formulas"][0]
        return row, records

    def test_superscript_convergence_requires_explicit_sequence_selector(self):
        row, records = self.convergence_fixture(r"x^n\to x", selector="superscript-base")
        nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual([n["rule"] for n in nodes], ["index:superscript", "relation:sequence-limit"])
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        row, records = self.convergence_fixture(r"x^n\to x")
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)

    def test_numeric_sequence_limit_infers_codomain_and_rejects_bool(self):
        for codomain in ["ℝ", "ℕ", "ENNReal"]:
            with self.subTest(codomain=codomain):
                row, records = self.convergence_fixture(r"x_n\to 0", codomain=codomain)
                nodes = operators.inspect(row["syntax"], row["variables"], records)
                self.assertEqual(
                    [n["rule"] for n in nodes], ["index:subscript", "literal:sequence-limit", "relation:sequence-limit"]
                )
                self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
                self.assertEqual(nodes[1]["implicitArgumentStatus"], "matched")
                term, context = operators.chapter.translate(row["syntax"], row["variables"], records)
                intended = f"Filter.Tendsto u Filter.atTop (nhds (0 : {codomain}))"
                source = operators.HEADER + operators.chapter.expression_definition(
                    {"lean": f"(show ({term}) = ({intended}) from rfl)", "context": context}, records, "NumericLimit"
                )
                source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"numeric_limit\\"}"\n'
                self.assertIn("numeric_limit", operators.chapter.export(source))
        row, records = self.convergence_fixture(r"x_n\to 0", codomain="Bool")
        with self.assertRaises(ValueError):
            operators.inspect(row["syntax"], row["variables"], records)

    def test_sequence_limit_tracks_function_filters_and_lexical_index(self):
        formula = r"f(x_n)\to f(x)"
        row, records = self.convergence_fixture(formula)
        index = next(v for v in row["variables"] if v["symbol"] == "n")
        self.assertTrue(index["localBinder"])
        self.assertEqual(index["leanType"], "ℕ")
        component = row["bindingEffects"][0]["binder"]["components"][0]
        self.assertEqual(component["start"], index["start"])
        self.assertEqual(component["end"], index["end"])
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual(
            [r["rule"] for r in rows],
            ["index:subscript", "application:function", "application:function", "relation:sequence-limit"],
        )
        self.assertTrue(all(r["targetStatus"] == r["operandStatus"] == "matched" for r in rows))
        limit = rows[-1]
        self.assertEqual(formula[limit["operatorStart"] : limit["operatorEnd"]], r"\to")
        self.assertEqual(limit["elaborated"]["head"], "Filter.Tendsto")
        self.assertEqual(
            [o["target"] for o in limit["expectedOperands"]], ["sequence", "source-filter", "target-filter"]
        )
        self.assertIsNone(limit["expectedOperands"][1]["sourceOperand"])
        self.assertEqual(limit["implicitArgumentStatus"], "matched")
        c = operators.chapter
        original = c.translate

        def wrong_types(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "relation:sequence-limit":
                    node["expectedImplicitArguments"][0]["candidate"] = "Int"
                    node["expectedImplicitArguments"][1]["candidate"] = "Nat"
            return result

        with patch.object(c, "translate", side_effect=wrong_types):
            changed = operators.inspect(row["syntax"], row["variables"], records)[-1]
        self.assertEqual(changed["targetStatus"], "matched")
        self.assertTrue(all(r["status"] == "matched" for r in changed["operandChecks"]))
        self.assertEqual([r["status"] for r in changed["implicitArgumentChecks"]], ["mismatch", "mismatch"])
        self.assertEqual(changed["operandStatus"], "mismatch")

    def test_convergence_witness_preserves_source_names_inside_coordinate_limits(self):
        import json

        c = operators.chapter
        bindings = {
            "sequence": {"symbol": "x", "occurrence": "subscript-base", "target": "D/u"},
            "index": {"symbol": "n", "target": "D/n"},
            "carrier": {"symbol": "X", "target": "D/book_power_index"},
            "indices": {"symbol": "I", "target": "D/I"},
        }
        text = "<!-- chapter-correspondence " + json.dumps({"scope": "limit", "bindings": bindings}) + " -->"
        text += r"$x_n\to\seqPower{X}{I}$<!-- chapter-correspondence-end: limit -->"
        records = {
            "D": {
                "binders": [
                    {"name": name, "type": ty, "instance": instance}
                    for name, ty, instance in [
                        ("book_power_index", "Type", False),
                        ("I", "Type", False),
                        ("topology", "TopologicalSpace (Type)", True),
                        ("u", "ℕ → Type", False),
                        ("n", "Int", False),
                    ]
                ]
            }
        }
        row = c.report(text, c.scopes(text), records, trusted=False)["formulas"][0]
        nodes = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(n["targetStatus"] == n["operandStatus"] == "matched" for n in nodes))
        term, context = c.translate(row["syntax"], row["variables"], records)
        intended = "Filter.Tendsto u Filter.atTop (nhds (I → book_power_index))"
        source = operators.HEADER + c.expression_definition(
            {"lean": f"(show ({term}) = ({intended}) from rfl)", "context": context}, records, "CoordinateLimit"
        )
        source += '\nrun_cmd Lean.logInfo "SORT_PILOT {\\"declaration\\":\\"coordinate_limit\\"}"\n'
        self.assertIn("coordinate_limit", c.export(source))

    def test_sequence_limit_rejects_wrong_domain_or_ambiguous_index(self):
        for formula, domain, reason in [
            (r"x_n\to x", "ℤ", "natural-number"),
            (r"x_n\to x_n", "ℕ", "bound.*index"),
            (r"x_n+x_m\to x", "ℕ", "unreviewed binding effect"),
            (r"x_{n+1}\to x", "ℕ", "unreviewed binding effect"),
            (r"x_n\to[z]x", "ℕ", "No Markdown-owned declaration"),
        ]:
            row, records = self.convergence_fixture(formula, domain)
            if domain == "ℤ":
                self.assertTrue(all(v["status"] == "unresolved" for v in row["variables"] if v["symbol"] == "n"))
            with self.assertRaisesRegex(operators.chapter.Unsupported, reason):
                operators.inspect(row["syntax"], row["variables"], records)

    def test_sequence_limit_detects_changed_limit_and_source_filter(self):
        row, records = self.convergence_fixture(r"x_n\to x")
        c = operators.chapter
        original = c.translate
        for before, after, changed in [
            ("nhds («a»)", "nhds («b»)", 2),
            ("Filter.atTop", "(Filter.principal (Set.univ : Set ℕ))", 1),
        ]:

            def wrong(*args, before=before, after=after, **kwargs):
                term, context = original(*args, **kwargs)
                return term.replace(before, after), context

            with patch.object(c, "translate", side_effect=wrong):
                limit = operators.inspect(row["syntax"], row["variables"], records)[-1]
            self.assertEqual(limit["targetStatus"], "matched")
            self.assertEqual(limit["operandStatus"], "mismatch")
            self.assertEqual(limit["operandChecks"][changed]["status"], "mismatch")

    def test_chapter_retains_unresolved_and_empty_formulas(self):
        report = {"source": "chapter.md", "sourceHash": "hash", "formulas": [{}, {}, {}]}
        rows = [
            {"nodes": [{"targetStatus": "mismatch", "rule": "macro:frac"}], "untracedOperators": [], "unresolved": []},
            {"nodes": [], "untracedOperators": [{"sourceOperator": "^"}], "unresolved": [{"reason": "unsupported"}]},
            {"nodes": [], "untracedOperators": [], "unresolved": []},
        ]
        progress = []
        with (
            patch.object(operators, "validate_inventory") as validate,
            patch.object(operators, "inspect_formula_report", side_effect=rows) as inspect,
        ):
            result = operators.inspect_chapter_report(report, lambda n, total: progress.append((n, total)))
        validate.assert_called_once_with(report)
        self.assertEqual(result["formulas"], rows)
        self.assertEqual(result["summary"]["formulas"], 3)
        self.assertEqual(result["summary"]["targetStatuses"], {"mismatch": 1})
        self.assertEqual(result["summary"]["untracedKnownOperators"], 1)
        self.assertEqual(result["summary"]["unresolvedSubexpressions"], 1)
        self.assertEqual(progress, [(1, 3), (2, 3), (3, 3)])
        self.assertEqual([call.args[1] for call in inspect.call_args_list], [0, 1, 2])
        self.assertTrue(all(call.kwargs == {"validated": True} for call in inspect.call_args_list))

    def test_variable_list_comparison_preserves_each_call(self):
        rows = inspect_formula(r"a,b\ge 0")
        self.assertEqual(len(rows), 2)
        self.assertEqual([r["lowering"] for r in rows], ["variable-list-conjunction"] * 2)
        self.assertTrue(all(r["operandStatus"] == "matched" for r in rows))
        self.assertEqual([r["elaborated"]["arguments"][-2]["value"] for r in rows], ["a", "b"])
        evidence = {}
        for row in rows:
            operators.merge_operator_call(evidence, row)
        self.assertEqual(len(evidence), 1)
        node = next(iter(evidence.values()))
        self.assertEqual(len(node["calls"]), 2)
        self.assertNotEqual(node["calls"][0]["operandSpans"][0], node["calls"][1]["operandSpans"][0])
        with self.assertRaisesRegex(operators.chapter.Unsupported, "variable-list"):
            inspect_formula("a,b=0")
        with self.assertRaisesRegex(operators.chapter.Unsupported, "Comma syntax"):
            inspect_formula("a,b<0<y")

    def test_repeated_source_operator_does_not_hide_a_mismatch(self):
        rows = inspect_formula(r"a,b\ge 0")
        rows[0]["operandStatus"] = "mismatch"
        rows[0]["requirementStatus"] = "unresolved"
        rows[1]["requirementStatus"] = "proved"
        evidence = {}
        for row in rows:
            operators.merge_operator_call(evidence, row)
        node = next(iter(evidence.values()))
        self.assertEqual(node["operandStatus"], "mismatch")
        self.assertEqual(node["requirementStatus"], "unresolved")
        self.assertEqual(node["calls"][0]["operandStatus"], "mismatch")
        self.assertEqual(node["calls"][1]["operandStatus"], "matched")

    def test_nested_macro_spans_and_real_division_instance(self):
        formula = r"\Abs{\frac{x}{y}}"
        rows = inspect_formula(formula)
        self.assertEqual([r["rule"] for r in rows], ["macro:frac", "macro:Abs"])
        self.assertEqual(formula[rows[0]["start"] : rows[0]["end"]], r"\frac{x}{y}")
        self.assertEqual(formula[rows[0]["operatorStart"] : rows[0]["operatorEnd"]], r"\frac")
        self.assertEqual(formula[rows[1]["start"] : rows[1]["end"]], formula)
        division = rows[0]["elaborated"]
        self.assertEqual(division["head"], "HDiv.hDiv")
        self.assertEqual(division["type"], "ℝ")
        self.assertEqual([a["value"] for a in division["arguments"] if not a["implicit"]], ["x", "y"])
        self.assertTrue(any(a["instance"] and "ℝ" in a["type"] for a in division["arguments"]))
        self.assertEqual(rows[1]["elaborated"]["head"], "abs")
        self.assertTrue(all(r["implicitArgumentStatus"] == "matched" for r in rows))

    def test_macro_instances_are_checked_independently(self):
        c = operators.chapter
        original = c.translate
        cases = [
            (r"\frac{x}{y}", "macro:frac", 3, "(⟨fun a b : ℝ => b / a⟩ : HDiv ℝ ℝ ℝ)"),
            (r"\Abs{x}", "macro:Abs", 1, "(inferInstance : Lattice (OrderDual ℝ))"),
            (r"\ClosedInterval{x}{y}", "macro:ClosedInterval", 1, "(inferInstance : Preorder (OrderDual ℝ))"),
            (r"\OpenInterval{x}{y}", "macro:OpenInterval", 1, "(inferInstance : Preorder (OrderDual ℝ))"),
            (r"\LeftClosedInterval{x}{y}", "macro:LeftClosedInterval", 1, "(inferInstance : Preorder (OrderDual ℝ))"),
            (r"\Closure{C}", "macro:Closure", 1, "(⊥ : TopologicalSpace ℝ)"),
        ]
        for formula, rule, position, candidate in cases:
            with self.subTest(formula=formula):
                types = {"x": "ℝ", "y": "ℝ", "C": "Set ℝ"}
                normal = inspect_formula(formula, types)[-1]
                self.assertEqual(normal["implicitArgumentStatus"], "matched")

                def wrong(*args, rule=rule, position=position, candidate=candidate, **kwargs):
                    result = original(*args, **kwargs)
                    for node in kwargs.get("trace") or []:
                        if node["rule"] == rule:
                            node["expectedImplicitArguments"][position]["candidate"] = candidate
                    return result

                with patch.object(c, "translate", side_effect=wrong):
                    changed = inspect_formula(formula, types)[-1]
                self.assertEqual(changed["targetStatus"], "matched")
                self.assertTrue(all(r["status"] == "matched" for r in changed["operandChecks"]))
                self.assertEqual(changed["implicitArgumentChecks"][position]["typeStatus"], "matched")
                self.assertEqual(changed["implicitArgumentChecks"][position]["status"], "mismatch")
                self.assertEqual(changed["operandStatus"], "mismatch")

    def test_same_type_wrong_operation_has_different_elaborated_head(self):
        chapter = operators.chapter
        with corrupt_native_terms(chapter, lambda term: term.replace(" / ", " * ")):
            row = inspect_formula(r"\frac{x}{y}")[0]
        self.assertEqual(row["elaborated"]["type"], "ℝ")
        self.assertEqual(row["elaborated"]["head"], "HMul.hMul")
        self.assertNotEqual(row["elaborated"]["head"], "HDiv.hDiv")
        self.assertEqual(row["headStatus"], "mismatch")

    def test_same_head_swapped_arguments_are_rejected(self):
        chapter = operators.chapter
        with corrupt_native_terms(chapter, lambda term: term.replace("((«x») / («y»))", "((«y») / («x»))")):
            row = inspect_formula(r"\frac{x}{y}")[0]
        self.assertEqual(row["operandStatus"], "mismatch")
        self.assertEqual([o["status"] for o in row["operandChecks"]], ["mismatch", "mismatch"])
        call = row["elaborated"]
        self.assertEqual(call["head"], "HDiv.hDiv")
        self.assertEqual([a["value"] for a in call["arguments"] if not a["implicit"]], ["y", "x"])
        instance = next(a for a in call["arguments"] if a["instance"])
        self.assertEqual(instance["kernel"]["kind"], "application")

    def test_source_operands_match_reversed_order_relations(self):
        for formula in (r"x>y", r"x\ge y", r"x\in C"):
            types = {"x": "ℝ", "y": "ℝ", "C": "Set ℝ"}
            row = inspect_formula(formula, types)[0]
            self.assertEqual(row["operandStatus"], "matched", formula)
            self.assertEqual(
                [o["sourceOperand"] for o in row["expectedOperands"]],
                [1, 0] if formula == r"x\in C" else [0, 1],
            )
            self.assertEqual(row["targetStatus"], "matched")

    def test_nested_operands_and_expected_numeric_type(self):
        rows = inspect_formula(r"\frac{x}{1+x}")
        self.assertTrue(all(row["operandStatus"] == "matched" for row in rows))
        addition = next(row for row in rows if row["rule"] == "infix:+")
        self.assertEqual(addition["elaborated"]["arguments"][-2]["type"], "ℝ")

    def test_comparison_chain_tracks_each_relation_and_repeated_middle_operand(self):
        formula = r"x\le y+x\le y"
        rows = inspect_formula(formula)
        comparisons = [row for row in rows if row["rule"] == "infix:≤"]
        self.assertEqual(len(comparisons), 2)
        self.assertEqual([row["operatorStart"] for row in comparisons], [1, 8])
        self.assertTrue(all(row["operandStatus"] == "matched" for row in rows))
        self.assertEqual(len({row["marker"] for row in rows}), len(rows))

    def test_unbounded_real_intervals_trace_endpoint_and_order(self):
        for macro, head in [("OpenInterval", "Set.Ioi"), ("LeftClosedInterval", "Set.Ici")]:
            with self.subTest(macro=macro):
                formula = "\\" + macro + r"{0}{\infty}"
                nodes = inspect_formula(formula)
                self.assertEqual(len(nodes), 1)
                node = nodes[0]
                self.assertEqual(node["expectedConstant"], head)
                self.assertEqual(node["rule"], "set:real-upper-ray")
                self.assertEqual(node["targetStatus"], "matched")
                self.assertEqual(node["operandStatus"], "matched")
                self.assertEqual(node["implicitArgumentStatus"], "matched")
                self.assertEqual(len(node["operandSpans"]), 2)
                self.assertEqual(node["lowering"]["upperEndpoint"], "unbounded")
                self.assertEqual(node["expectedOperands"], [{"sourceOperand": 0, "candidate": "(0 : Real)"}])

    def test_unbounded_real_interval_rejects_wrong_endpoint(self):
        c = operators.chapter
        original = c.translate

        def wrong_endpoint(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace", []):
                if node["rule"] == "set:real-upper-ray":
                    node["expectedOperands"][0]["candidate"] = "(1 : Real)"
            return result

        with patch.object(c, "translate", side_effect=wrong_endpoint):
            node = inspect_formula(r"\LeftClosedInterval{0}{\infty}")[0]
        self.assertEqual(node["targetStatus"], "matched")
        self.assertEqual(node["operandStatus"], "mismatch")

    def test_interval_operand_coercion_is_checked(self):
        row = inspect_formula(r"\ClosedInterval{x}{y}", {"x": "ℕ", "y": "ℝ"})[0]
        self.assertEqual(row["operandStatus"], "matched")
        converted = row["operandChecks"][0]
        self.assertEqual(converted["actual"]["kind"], "application")
        self.assertEqual(converted["expected"]["kind"], "application")
        chapter = operators.chapter
        with corrupt_native_terms(chapter, lambda term: term.replace("(«x» : ℝ)", "((«x» : ℝ) + 1)")):
            wrong = inspect_formula(r"\ClosedInterval{x}{y}", {"x": "ℕ", "y": "ℝ"})[0]
        self.assertEqual(wrong["targetStatus"], "matched")
        self.assertEqual(wrong["operandStatus"], "mismatch")

    def test_closure_exposes_set_and_topology_arguments(self):
        row = inspect_formula(r"\Closure{C}", {"C": "Set ℝ"})[0]
        call = row["elaborated"]
        self.assertEqual(call["head"], "closure")
        self.assertEqual(call["type"], "Set ℝ")
        self.assertTrue(any(a["instance"] and "TopologicalSpace" in a["type"] for a in call["arguments"]))
        self.assertEqual([a["value"] for a in call["arguments"] if not a["implicit"]], ["C"])

    def test_infix_precedence_positions_and_comparison(self):
        formula = r"x+y*x\le y"
        rows = inspect_formula(formula)
        self.assertEqual([r["rule"] for r in rows], ["infix:*", "infix:+", "infix:≤"])
        self.assertEqual([formula[r["operatorStart"] : r["operatorEnd"]] for r in rows], ["*", "+", r"\le"])
        self.assertTrue(all(r["headStatus"] == "matched" for r in rows))
        self.assertEqual(formula[rows[0]["start"] : rows[0]["end"]], "y*x")
        self.assertEqual(rows[-1]["elaborated"]["type"], "Prop")
        tree, _ = operators.chapter.located(operators.chapter.syntax([formula])[0]["tree"])
        candidates = operators.operator_candidates(tree)
        self.assertEqual(
            {(r["operatorStart"], r["operatorEnd"]) for r in rows}, {(c["start"], c["end"]) for c in candidates}
        )

    def test_parentheses_and_left_associativity(self):
        rows = inspect_formula("(x+y)*x")
        self.assertEqual([r["rule"] for r in rows], ["infix:+", "infix:*"])
        rows = inspect_formula("x-y-x")
        self.assertEqual([r["rule"] for r in rows], ["infix:-", "infix:-"])
        self.assertEqual(rows[0]["start"], 0)
        self.assertEqual(rows[0]["end"], 3)

    def test_metric_application_uses_the_original_metric_instance(self):
        c = operators.chapter
        text = r"d(x,y)"
        tree, _ = c.located(c.syntax([text])[0]["tree"])
        variables, _ = c.leaves(tree)
        types = {"d": "MetricSpace ℝ", "x": "ℝ", "y": "ℝ"}
        for v in variables:
            v.update(
                id="fixture/" + v["symbol"],
                status="resolved",
                declaration="D",
                leanName=v["symbol"],
                leanType=types[v["symbol"]],
                formulaOffset=v["start"],
            )
        records = {"D": {"binders": [{"name": n, "type": ty, "instance": n == "d"} for n, ty in types.items()]}}
        row = operators.inspect(tree, variables, records)[0]
        self.assertEqual(row["rule"], "application:metric")
        self.assertEqual(row["headStatus"], "matched")
        self.assertEqual(row["elaborated"]["head"], "Dist.dist")
        instance = next(a for a in row["elaborated"]["arguments"] if a["instance"])
        self.assertIn("d", str(instance["kernel"]))

    def test_set_operators_and_ambient_carrier_are_traced(self):
        rows = inspect_formula(r"\SetDifference{\R}{C}\cap D\IncludedIn\R", {"C": "Set ℝ", "D": "Set ℝ"})
        self.assertEqual([r["rule"] for r in rows], ["macro:SetDifference", "set:cap", "set:IncludedIn"])
        self.assertTrue(all(r["implicitArgumentStatus"] == "matched" for r in rows))
        self.assertTrue(
            all(r["targetStatus"] == "matched" for r in rows), [(r["rule"], r["elaborated"]["head"]) for r in rows]
        )
        self.assertTrue(any(a["instance"] and "LE (Set ℝ)" in a["type"] for a in rows[-1]["elaborated"]["arguments"]))
        row = inspect_formula(r"x\in C", {"x": "ℝ", "C": "Set ℝ"})[0]
        self.assertEqual(row["targetStatus"], "matched")
        self.assertEqual(row["elaborated"]["head"], "Membership.mem")
        self.assertEqual(row["implicitArgumentStatus"], "matched")

    def test_set_membership_and_product_check_independent_domains(self):
        row = inspect_formula(r"C\times D", {"C": "Set ℝ", "D": "Set ℕ"})[-1]
        self.assertEqual(row["implicitArgumentStatus"], "matched")
        self.assertEqual(len(row["implicitArgumentChecks"]), 2)
        c = operators.chapter
        original = c.translate

        def wrong_membership(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "set:in":
                    node["expectedImplicitArguments"][0]["candidate"] = "Nat"
                    node["expectedImplicitArguments"][2]["candidate"] = "(⟨fun A x => x ∉ A⟩ : Membership ℝ (Set ℝ))"
                elif node["rule"] == "set:product":
                    node["expectedImplicitArguments"][1]["candidate"] = "Real"
            return result

        with patch.object(c, "translate", side_effect=wrong_membership):
            wrong = inspect_formula(r"x\in C", {"x": "ℝ", "C": "Set ℝ"})[-1]
            product = inspect_formula(r"C\times D", {"C": "Set ℝ", "D": "Set ℕ"})[-1]
        self.assertEqual(wrong["targetStatus"], "matched")
        self.assertTrue(all(check["status"] == "matched" for check in wrong["operandChecks"]))
        self.assertEqual(
            [check["status"] for check in wrong["implicitArgumentChecks"]], ["mismatch", "matched", "mismatch"]
        )
        self.assertEqual(wrong["operandStatus"], "mismatch")
        self.assertEqual(product["implicitArgumentStatus"], "mismatch")

    def test_set_types_and_instances_reject_same_signature_substitutions(self):
        types = {"C": "Set ℝ", "D": "Set ℝ"}
        for formula in (r"C\cup D", r"C\cap D", r"C\IncludedIn D", r"\SetDifference{C}{D}", "C=D"):
            with self.subTest(formula=formula):
                row = inspect_formula(formula, types)[-1]
                self.assertEqual(row["implicitArgumentStatus"], "matched")
        c = operators.chapter
        original = c.translate

        def wrong_union(*args, **kwargs):
            result = original(*args, **kwargs)
            for node in kwargs.get("trace") or []:
                if node["rule"] == "set:cup":
                    node["expectedImplicitArguments"][0]["candidate"] = "Set Nat"
                    node["expectedImplicitArguments"][1]["candidate"] = "(⟨fun A B : Set ℝ => A ∩ B⟩ : Union (Set ℝ))"
            return result

        with patch.object(c, "translate", side_effect=wrong_union):
            wrong = inspect_formula(r"C\cup D", types)[-1]
        self.assertEqual(wrong["targetStatus"], "matched")
        self.assertTrue(all(check["status"] == "matched" for check in wrong["operandChecks"]))
        self.assertEqual([check["status"] for check in wrong["implicitArgumentChecks"]], ["mismatch", "mismatch"])
        self.assertEqual(wrong["operandStatus"], "mismatch")

    def test_sequence_lambda_and_index_share_the_scoped_binder(self):
        c = operators.chapter
        import json

        data = {"scope": "seq", "bindings": {"x": {"symbol": "x", "target": "D/x"}}}
        text = "<!-- chapter-correspondence " + json.dumps(data) + " -->" + r"$\Sequence{x_n}{n\in\omega}$"
        text += "<!-- chapter-correspondence-end: seq -->"
        records = {"D": {"binders": [{"name": "x", "type": "ℕ → ℝ", "instance": False}]}}
        row = c.report(text, c.scopes(text), records)["formulas"][0]
        rows = operators.inspect(row["syntax"], row["variables"], records)
        self.assertEqual([r["rule"] for r in rows], ["index:subscript", "binder:Sequence"])
        self.assertTrue(all(r["targetStatus"] == "matched" for r in rows))
        self.assertTrue(all(r["operandStatus"] == "matched" for r in rows))
        self.assertEqual([o["target"] for o in rows[1]["expectedOperands"]], ["lambda.body", "lambda.domain"])
        self.assertEqual(rows[1]["operandChecks"][1]["actual"]["name"], "Nat")
        self.assertEqual(len(rows[1]["bindingComponents"]), 3)
        original = c.translate

        def shifted(*args, **kwargs):
            term, context = original(*args, **kwargs)
            term = re.sub(r"\(«(seq_index_\d+)»\)", r"(«\1» + 1)", term)
            return term, context

        with patch.object(c, "translate", side_effect=shifted):
            wrong = operators.inspect(row["syntax"], row["variables"], records)
        self.assertTrue(all(r["targetStatus"] == "matched" for r in wrong))
        self.assertTrue(all(r["operandStatus"] == "mismatch" for r in wrong))
        self.assertEqual(wrong[1]["operandChecks"][1]["status"], "matched")
        index = rows[0]["elaborated"]["arguments"][0]["kernel"]
        binder = rows[1]["elaborated"]["kernel"]
        self.assertEqual(index["name"], binder["name"])
        self.assertEqual(binder["domain"]["name"], "Nat")
        self.assertEqual(rows[0]["elaborated"]["kernel"]["function"]["name"], "x")

    def test_nested_sequences_keep_distinct_shadowed_binders(self):
        c = operators.chapter
        text = r"$\Sequence{\Sequence{n}{n\in\omega}}{n\in\omega}$"
        row = c.report(text, [], {})["formulas"][0]
        rows = operators.inspect(row["syntax"], row["variables"], {})
        self.assertEqual(len(rows), 2)
        self.assertNotEqual(rows[0]["expectedBinderName"], rows[1]["expectedBinderName"])
        self.assertTrue(all(r["operandStatus"] == "matched" for r in rows))
        self.assertEqual(rows[0]["operandChecks"][0]["actual"]["name"], rows[0]["expectedBinderName"])

    def test_sequence_domain_change_is_rejected(self):
        c = operators.chapter
        text = r"$\Sequence{n}{n\in\omega}$"
        row = c.report(text, [], {})["formulas"][0]
        original = c.translate

        def integers(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace(": ℕ =>", ": ℤ =>"), context

        with patch.object(c, "translate", side_effect=integers):
            wrong = operators.inspect(row["syntax"], row["variables"], {})[0]
        self.assertEqual(wrong["targetStatus"], "mismatch")
        self.assertEqual(wrong["operandStatus"], "mismatch")
        self.assertEqual(wrong["operandChecks"][1]["status"], "mismatch")

    def test_named_function_target_uses_the_actual_constant_head(self):
        import json

        c = operators.chapter
        name = "PolishSpaceBook.boundedMetricTransform"
        records = c.evidence({name})
        records["D"] = {"binders": [{"name": "e", "type": "ℝ", "instance": False}]}
        data = {
            "scope": "constant",
            "bindings": {
                "phi": {"symbol": r"\phi", "target": {"constant": name}},
                "epsilon": {"symbol": r"\epsilon", "target": "D/e"},
            },
        }
        text = "<!-- chapter-correspondence " + json.dumps(data) + " -->" + r"$\phi(\epsilon)$"
        text += "<!-- chapter-correspondence-end: constant -->"
        row = c.report(text, c.scopes(text), records, trusted=False)["formulas"][0]
        evidence = operators.inspect(row["syntax"], row["variables"], records)[0]
        self.assertEqual(evidence["elaborated"]["head"], name)
        self.assertEqual(evidence["targetStatus"], "matched")
        self.assertEqual(evidence["operandStatus"], "matched")
        self.assertEqual(evidence["elaborated"]["arguments"][0]["value"], "e")
        original = c.translate

        def wrong_function(*args, **kwargs):
            term, context = original(*args, **kwargs)
            return term.replace(name, "Real.sin"), context

        with patch.object(c, "translate", side_effect=wrong_function):
            wrong = operators.inspect(row["syntax"], row["variables"], records)[0]
        self.assertEqual(wrong["elaborated"]["type"], "ℝ")
        self.assertEqual(wrong["targetStatus"], "mismatch")

    def test_function_application_checks_the_scoped_callee(self):
        rows = inspect_formula("f(x)", {"f": "ℝ → ℝ", "x": "ℝ"})
        self.assertEqual(rows[0]["rule"], "application:function")
        self.assertEqual(rows[0]["expectedVariable"], "f")
        self.assertEqual(rows[0]["targetStatus"], "matched")

    def test_sized_parentheses_preserve_operator_and_operand_positions(self):
        formula = r"f\bigl(x+y\bigr)"
        rows = inspect_formula(formula, {"f": "ℝ → ℝ"})
        call = next(r for r in rows if r["rule"] == "application:function")
        addition = next(r for r in rows if r["rule"] == "infix:+")
        self.assertEqual(formula[call["operatorStart"] : call["operatorEnd"]], "f")
        self.assertEqual(formula[addition["operatorStart"] : addition["operatorEnd"]], "+")
        self.assertTrue(all(r["targetStatus"] == "matched" and r["operandStatus"] == "matched" for r in rows))
        for formula in (r"f\bigl[x+y\bigr]", r"f\bigl x"):
            with self.assertRaisesRegex(operators.chapter.Unsupported, "Delimiter sizing"):
                inspect_formula(formula, {"f": "ℝ → ℝ"})

    def test_final_relational_comma_is_not_an_operand(self):
        formula = "x<y,\n"
        row = inspect_formula(formula)[0]
        self.assertEqual(row["operandStatus"], "matched")
        self.assertEqual(row["elaborated"]["arguments"][-1]["value"], "y")
        with self.assertRaisesRegex(operators.chapter.Unsupported, "Comma syntax"):
            inspect_formula("x,y,")


if __name__ == "__main__":
    unittest.main()
