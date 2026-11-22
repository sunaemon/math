"""Independent regressions for syntax, scope, inventory and Lean rejection."""

import hashlib
import importlib.util
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("chapter_correspondence", ROOT / "tools/chapter-correspondence/check.py")
chapter = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(chapter)


def scope(name, bindings, body):
    data = {"scope": name, "bindings": bindings}
    return (
        "<!-- chapter-correspondence "
        + json.dumps(data)
        + " -->"
        + body
        + "<!-- chapter-correspondence-end: "
        + name
        + " -->"
    )


class ChapterCorrespondenceTests(unittest.TestCase):
    def test_rational_singleton_union_retains_domain_and_element_spans(self):
        row = next(r for r in chapter.occurrences(chapter.SOURCE.read_text()) if r"\QQ = \bigcup" in r["book"])
        formula = row["book"]
        tree, _ = chapter.located(chapter.syntax([formula])[0]["tree"])
        (shape,) = chapter.indexed_singleton_shapes(tree)
        expected = {
            "marker": r"\bigcup",
            "binder": "q",
            "domainRelation": r"\in",
            "domain": r"\QQ",
            "subscript": "_",
            "opening": r"\{",
            "value": "q",
            "closing": r"\}",
        }
        for component, text in expected.items():
            span = shape[component]
            self.assertEqual(formula[span["start"] : span["end"]], text)
        self.assertEqual(shape["indexType"], "ℚ")
        self.assertFalse(shape["whole"])
        variables, effects = chapter.leaves(tree)
        candidate = next(e for e in effects if "candidateSingletonFamily" in e)
        self.assertEqual(candidate["candidateSingletonFamily"], shape)
        self.assertNotIn("binder", candidate)
        self.assertIn("ambient carrier", candidate["reason"])
        variables = chapter.resolve_variables(variables, effects, row, chapter.scopes(chapter.SOURCE.read_text()), {})
        self.assertTrue(all(v["status"] == "unresolved" for v in variables))
        with self.assertRaises(chapter.Unsupported):
            chapter.translate(tree, variables, {})

    def test_japanese_rational_ambient_keeps_its_own_source_offsets(self):
        text = (ROOT / "polish-space-ja/src/polish-space-book/polish-spaces.md").read_text()
        scopes = chapter.scopes(text)
        row = next(r for r in chapter.occurrences(text) if r"\QQ = \bigcup" in r["book"])
        tree, _ = chapter.located(chapter.syntax([row["book"]])[0]["tree"])
        tree = chapter.resolve_rational_ambient(tree, row, scopes)
        ambient = tree["rationalAmbient"]
        self.assertEqual(ambient["type"], "Real")
        self.assertIn(row["book"], text[ambient["start"] : ambient["end"]])
        variables, effects = chapter.leaves(tree)
        variables = chapter.resolve_variables(variables, effects, row, scopes, {})
        self.assertTrue(all(v["status"] == "resolved" and v["leanType"] == "ℚ" for v in variables))

    def test_rational_ambient_requires_explicit_supported_scope_metadata(self):
        formula = r"\QQ = \bigcup_{q \in \QQ} \{q\}"
        for ambient in ({"ambient": "Rat"}, {"ambient": "Real", "extra": True}, "Real", None):
            data = {"scope": "rationals", "bindings": {}, "rationalSingletons": ambient}
            text = "<!-- chapter-correspondence " + json.dumps(data) + " -->$" + formula + "$"
            text += "<!-- chapter-correspondence-end: rationals -->"
            with self.subTest(ambient=ambient), self.assertRaises(ValueError):
                chapter.scopes(text)
        text = scope("outer", {"q": {"symbol": "q", "target": "D/q"}}, "$" + formula + "$")
        row = chapter.occurrences(text)[0]
        tree, _ = chapter.located(chapter.syntax([formula])[0]["tree"])
        tree = chapter.resolve_rational_ambient(tree, row, chapter.scopes(text))
        self.assertNotIn("rationalAmbient", tree)
        variables, effects = chapter.leaves(tree)
        records = {"D": {"binders": [{"name": "q", "type": "ℝ", "instance": False}]}}
        variables = chapter.resolve_variables(variables, effects, row, chapter.scopes(text), records)
        self.assertTrue(all(v["status"] == "unresolved" for v in variables))

    def test_singleton_union_candidates_require_exact_typed_identity_family(self):
        valid = [r"\bigcup_{q \in \QQ} \{q\}", r"\bigcup_{x \in \R} \{x\}", r"\bigcup_{n \in \omega} \{n\}"]
        invalid = [
            r"\bigcup_q \{q\}",
            r"\bigcup_{q \in X} \{q\}",
            r"\bigcup_{q > 0} \{q\}",
            r"\bigcup_{q \in \QQ} \{x\}",
            r"\bigcup_{q \in \QQ} \{q,0\}",
            r"\bigcup_{q \in \QQ} \{q+1\}",
            r"\bigcap_{q \in \QQ} \{q\}",
            r"\bigcup_{q \in \QQ^2} \{q\}",
        ]
        for formula in valid + invalid:
            with self.subTest(formula=formula):
                tree, _ = chapter.located(chapter.syntax([formula])[0]["tree"])
                shapes = chapter.indexed_singleton_shapes(tree)
                self.assertEqual(bool(shapes), formula in valid)
                if shapes:
                    self.assertTrue(shapes[0]["whole"])

    def test_ball_restriction_requires_marked_prose_and_the_same_metric_trace(self):
        text = chapter.SOURCE.read_text()
        scopes = chapter.scopes(text)
        row = next(r for r in chapter.occurrences(text) if r"V_n \;=\; \bigcup" in r["book"])
        tree, _ = chapter.located(chapter.syntax([row["book"]])[0]["tree"])
        resolved = chapter.resolve_generator_restrictions(tree, row, scopes)
        (restriction,) = resolved["generatorRestrictions"]
        source = restriction["source"]
        self.assertEqual(text[source["start"] : source["end"]], source["text"])
        self.assertGreaterEqual(source["start"], row["end"])
        self.assertEqual(restriction["metric"]["id"], "alexandrov-ball-union/rho")
        self.assertEqual(restriction["subset"]["id"], "alexandrov-ball-union/A")
        _, effects = chapter.leaves(resolved)
        effect = next(e for e in effects if "sourceRestriction" in e)
        self.assertEqual(effect["sourceRestriction"], restriction)
        self.assertIn(effect["command"], {"ball-generator-point", "ball-generator-radius"})
        self.assertIn("binder", effect)
        begin = "<!-- chapter-correspondence-premise: alexandrov-bounded-traces -->"
        end = "<!-- chapter-correspondence-premise-end: alexandrov-bounded-traces -->"
        for invalid in (
            text.replace(begin, ""),
            text.replace(end, ""),
            text.replace(begin, begin + begin),
            text.replace(source["text"], " "),
        ):
            with self.assertRaises(ValueError):
                chapter.scopes(invalid)
        for formula in (
            row["book"].replace(r"\cap A", r"\cap X"),
            row["book"].replace(r"\MetricDiameter{\rho}", r"\MetricDiameter{d}"),
            row["book"].replace(r"\MetricBall{d}{x}{\delta} \cap", r"\MetricBall{d}{x}{1} \cap"),
        ):
            changed, _ = chapter.located(chapter.syntax([formula])[0]["tree"])
            self.assertNotIn("generatorRestrictions", chapter.resolve_generator_restrictions(changed, row, scopes))

    def test_ball_family_retains_all_source_conditions_without_approving_them(self):
        row = next(r for r in chapter.occurrences(chapter.SOURCE.read_text()) if r"V_n \;=\; \bigcup" in r["book"])
        formula = row["book"]
        tree, _ = chapter.located(chapter.syntax([formula])[0]["tree"])
        shapes = chapter.ball_family_chunks(tree)
        self.assertEqual(len(shapes), 1)
        shape = shapes[0]
        span = lambda nodes: formula[nodes[0]["start"] : nodes[-1]["end"]]
        self.assertEqual(span(shape["pointDomain"]), r"x \in X")
        self.assertEqual(span(shape["radiusCondition"]), r"\delta > 0")
        self.assertEqual(
            span(shape["traceCondition"]), r"\MetricDiameter{\rho}{\MetricBall{d}{x}{\delta} \cap A} < 1/(n+1)"
        )
        self.assertEqual(span([shape["value"]]), r"\MetricBall{d}{x}{\delta}")
        self.assertEqual(len(shape["separators"]), 2)
        _variables, effects = chapter.leaves(tree)
        candidate = next(e for e in effects if "candidateGenerator" in e)
        self.assertNotIn("binder", candidate)
        self.assertEqual(candidate["candidateGenerator"], shape)
        self.assertTrue(any(e["command"] == "bigcup" and "binder" not in e for e in effects))
        types = {
            "V": "ℕ → Set X",
            "n": "ℕ",
            "d": "MetricSpace X",
            "x": "X",
            "delta": "ℝ",
            "rho": "MetricSpace ↑A",
            "A": "Set X",
            "X": "Type",
        }
        bindings = {
            name: {"symbol": "\\" + name if name in {"delta", "rho"} else name, "target": "D/" + name} for name in types
        }
        text = scope("candidate", bindings, "$" + formula + "$")
        candidate_row = chapter.occurrences(text)[0]
        records = {"D": {"binders": [{"name": name, "type": ty, "instance": False} for name, ty in types.items()]}}
        variables = chapter.resolve_variables(_variables, effects, candidate_row, chapter.scopes(text), records)
        self.assertTrue(all(v["status"] == "unresolved" for v in variables))
        with self.assertRaises(chapter.Unsupported):
            chapter.translate(tree, variables, records)
        for changed in (
            formula.replace(r"x \in X", r"y \in X"),
            formula.replace(r"\delta > 0", r"\delta \ge 0"),
            formula.replace(r"\delta > 0", r"x > 0"),
            formula.replace(r"< 1/(n+1)", r"< 1/(n+1), x=x"),
            formula.replace(r"\},", ""),
        ):
            tree, _ = chapter.located(chapter.syntax([changed])[0]["tree"])
            self.assertEqual(chapter.ball_family_chunks(tree), [])

    def test_subtype_projection_requires_a_named_subset_binder(self):
        binding = {"symbol": "a", "target": "D/a", "projection": "Subtype.val"}
        text = scope("s", {"a": binding}, "$a$")
        for ty, status in [("↑A", "resolved"), ("ℝ", "unresolved")]:
            records = {
                "D": {
                    "binders": [
                        {"name": "A", "type": "Set ℝ", "instance": False},
                        {"name": "a", "type": ty, "instance": False},
                    ]
                }
            }
            row = chapter.report(text, chapter.scopes(text), records, trusted=False)["formulas"][0]
            var = row["variables"][0]
            self.assertEqual(var["status"], status)
            if status == "resolved":
                self.assertEqual(var["sourceLeanType"], "↑A")
                self.assertEqual(var["leanType"], "ℝ")
                self.assertEqual(chapter.translate(row["syntax"], row["variables"], records)[0], "(Subtype.val «a»)")
        for changed in [{"projection": "arbitrary"}, {"indexOrigin": 1}, {"indexOffset": 1}]:
            with self.assertRaises(ValueError):
                chapter.scopes(scope("s", {"a": {**binding, **changed}}, "$a$"))

    def test_index_offset_rejects_invalid_metadata_and_constants(self):
        for offset in [0, -1, True, "1", 1.5]:
            with self.subTest(offset=offset), self.assertRaises(ValueError):
                chapter.scopes(scope("s", {"n": {"symbol": "n", "target": "D/n", "indexOffset": offset}}, "$n$"))
        binding = {"symbol": "n", "target": "D/n", "indexOffset": 1, "indexOrigin": 1}
        with self.assertRaises(ValueError):
            chapter.scopes(scope("s", {"n": binding}, "$n$"))
        binding = {"symbol": "n", "target": "D/@constant", "indexOffset": 1}
        text = scope("s", {"n": binding}, "$n$")
        result = chapter.report(text, chapter.scopes(text), {"D": {"declarationType": "Nat"}})
        variable = result["formulas"][0]["variables"][0]
        self.assertEqual(variable["status"], "unresolved")
        self.assertIn("natural-number binder", variable["reason"])

    def test_prose_list_keeps_independent_types_and_offsets(self):
        text = scope(
            "list",
            {
                "x": {"symbol": "x", "target": "D/u", "occurrence": "subscript-base"},
                "point": {"symbol": "x", "target": "D/x", "occurrence": "unsubscripted"},
                "n": {"symbol": "n", "target": "D/n"},
            },
            "$x_n,x$",
        )
        records = {
            "D": {
                "binders": [
                    {"name": "u", "type": "ℕ → ℝ", "instance": False},
                    {"name": "x", "type": "ℤ", "instance": False},
                    {"name": "n", "type": "ℕ", "instance": False},
                ]
            }
        }
        row = chapter.report(text, chapter.scopes(text), records)["formulas"][0]
        self.assertEqual(row["expressionKind"], "expression-list")
        self.assertEqual(row["typeStatus"], "typechecked")
        self.assertEqual(row["inferredTypes"], ["ℝ", "ℤ"])
        self.assertNotIn("inferredType", row)
        self.assertNotIn("lean", row)
        parts = row["expressionFragments"]
        self.assertEqual([text[p["start"] : p["end"]] for p in parts], ["x_n", "x"])
        self.assertEqual([p["inferredType"] for p in parts], ["ℝ", "ℤ"])
        stale = chapter.report(text, chapter.scopes(text), records, trusted=False)["formulas"][0]
        self.assertTrue(all(p["typeStatus"] == "unresolved" for p in stale["expressionFragments"]))
        self.assertEqual(stale["typeStatus"], "unresolved")

        def one_failed(candidate, records):
            if candidate["lean"] != "«x»":
                candidate.update(typeStatus="typechecked", inferredType="ℝ")

        partial = chapter.report(text, chapter.scopes(text), records, check=one_failed)["formulas"][0]
        self.assertEqual(partial["typeStatus"], "unresolved")
        self.assertEqual([p["typeStatus"] for p in partial["expressionFragments"]], ["typechecked", "unresolved"])
        self.assertNotIn("inferredTypes", partial)
        for formula in ["(x,y)", "f(x,y)", "x,y>0", r"x,y\mapsto x", "x,,y", "x,", "x+y,z"]:
            node, _ = chapter.located(chapter.syntax([formula])[0]["tree"])
            self.assertIsNone(chapter.expression_list(node), formula)

    def test_prime_decorations_do_not_capture_the_unprimed_binding(self):
        text = scope("primes", {"d": {"symbol": "d", "target": "D/d"}}, "$d+d'+d''$")
        records = {"D": {"binders": [{"name": "d", "type": "ℝ", "instance": False}]}}
        row = chapter.report(text, chapter.scopes(text), records, trusted=False)["formulas"][0]
        self.assertEqual([v["symbol"] for v in row["variables"]], ["d", "d'", "d''"])
        self.assertEqual([v["status"] for v in row["variables"]], ["resolved", "unresolved", "unresolved"])
        self.assertEqual([text[v["start"] : v["end"]] for v in row["variables"]], ["d", "d'", "d''"])

    def test_prime_before_and_after_script_have_different_positions(self):
        for source, expected in [("x'_n", ["x'", "n"]), ("x_n'", ["x", "n"]), (r"\phi'", [r"\phi'"])]:
            tree, _ = chapter.located(chapter.syntax([source])[0]["tree"])
            variables, _ = chapter.leaves(tree)
            self.assertEqual([v["symbol"] for v in variables], expected)
            self.assertEqual([source[v["start"] : v["end"]] for v in variables], expected)

    def test_all_occurrences_include_heading_and_skips(self):
        text = "# Heading $X$\n<!-- formalization: skip-begin -->\n$x$ and $$y$$\n<!-- formalization: skip-end -->"
        self.assertEqual([r["book"] for r in chapter.occurrences(text)], ["X", "x", "y"])
        self.assertEqual(chapter.occurrences(text)[2]["start"], text.index("$$y"))

    def test_comments_escaped_dollars_and_missing_formula(self):
        text = r"<!-- $hidden$ --> \$literal $X$" + "\n\n$unclosed\n\nnext"
        rows = chapter.occurrences(text)
        self.assertEqual([r["book"] for r in rows], ["X", "unclosed"])
        self.assertFalse(rows[-1]["closed"])
        changed = chapter.report("$X$ $Y$", [], {}, trusted=False)
        self.assertEqual(changed["expressionTypes"], {"total": 2, "typechecked": 0, "unresolved": 2})

    def test_parser_nested_arguments_and_exact_offsets(self):
        formula = r"\Pair{x}{\Pair{y}{z}}"
        parsed = chapter.syntax([formula])[0]
        self.assertTrue(parsed["roundtrip"])
        tree, end = chapter.located(parsed["tree"])
        self.assertEqual(end, len(formula))
        variables, _ = chapter.leaves(tree)
        self.assertEqual([formula[v["start"] : v["end"]] for v in variables], ["x", "y", "z"])
        with self.assertRaisesRegex(chapter.Unsupported, "[Pp]air"):
            chapter.translate(tree, [])

    def test_shadowing_and_collision(self):
        binding = lambda name: {"symbol": "x", "target": "D/" + name}
        text = scope("outer", {"x": binding("a")}, "$x$" + scope("inner", {"x": binding("b")}, "$x$"))
        records = {"D": {"binders": [{"name": "a", "type": "Nat"}, {"name": "b", "type": "Nat"}]}}
        result = chapter.report(text, chapter.scopes(text), records, check=lambda *_: None)
        self.assertEqual([r["variables"][0]["id"] for r in result["formulas"]], ["outer/x", "inner/x"])
        self.assertEqual(result["formulas"][1]["variables"][0]["argumentPosition"], 1)
        collision = scope("bad", {"a": binding("a"), "b": binding("b")}, "$x$")
        with self.assertRaisesRegex(ValueError, "Colliding"):
            chapter.scopes(collision)

    def test_sequence_base_and_limit_have_distinct_source_identities(self):
        bindings = {
            "sequence": {"symbol": "x", "occurrence": "subscript-base", "target": "D/u"},
            "limit": {"symbol": "x", "occurrence": "unsubscripted", "target": "D/a"},
            "index": {"symbol": "n", "target": "D/n"},
        }
        records = {
            "D": {
                "binders": [
                    {"name": "u", "type": "ℕ → ℝ", "instance": False},
                    {"name": "a", "type": "ℝ", "instance": False},
                    {"name": "n", "type": "ℕ", "instance": False},
                ]
            }
        }
        text = scope("limits", bindings, r"$x_n-x$ $\Sequence{x_n-x}{n\in\omega}$")
        rows = chapter.report(text, chapter.scopes(text), records)["formulas"]
        self.assertTrue(all(r["typeStatus"] == "typechecked" for r in rows))
        for row in rows:
            xs = [v for v in row["variables"] if v["symbol"] == "x"]
            self.assertEqual([v["id"] for v in xs], ["limits/sequence", "limits/limit"])
            self.assertEqual([v["leanName"] for v in xs], ["u", "a"])
            self.assertTrue(all(text[v["start"] : v["end"]] == "x" for v in xs))
        self.assertEqual(rows[0]["inferredType"], "ℝ")
        self.assertEqual(rows[1]["inferredType"], "ℕ → ℝ")
        swapped = {k: dict(v) for k, v in bindings.items()}
        swapped["sequence"]["target"] = "D/a"
        bad = scope("bad", swapped, "$x_n-x$")
        rejected = chapter.report(bad, chapter.scopes(bad), records)["formulas"][0]
        self.assertEqual(rejected["typeStatus"], "unresolved")
        self.assertIn("scalar or point", rejected["variables"][0]["reason"])

    def test_occurrence_selectors_reject_overlap_and_preserve_outer_family(self):
        family = {"symbol": "x", "occurrence": "subscript-base", "target": "D/u"}
        plain = {"symbol": "x", "occurrence": "unsubscripted", "target": "D/a"}
        text = scope("outer", {"family": family}, scope("inner", {"point": plain}, "$x_n-x$"))
        records = {"D": {"binders": [{"name": "u", "type": "ℕ → ℝ"}, {"name": "a", "type": "ℝ"}]}}
        row = chapter.report(text, chapter.scopes(text), records, trusted=False)["formulas"][0]
        self.assertEqual([v.get("id") for v in row["variables"] if v["symbol"] == "x"], ["outer/family", "inner/point"])
        for duplicate in (family, {"symbol": "x", "target": "D/a"}):
            with self.assertRaisesRegex(ValueError, "Colliding"):
                chapter.scopes(scope("bad", {"family": family, "duplicate": duplicate}, "$x$"))
        with self.assertRaisesRegex(ValueError, "Unknown occurrence"):
            chapter.scopes(scope("bad", {"x": dict(plain, occurrence="typo")}, "$x$"))

    def test_elided_local_definition_is_not_reconstructed_with_placeholders(self):
        records = {
            "D": {"binders": [{"name": "metric", "type": "MetricSpace ℝ", "value": "MetricSpace.ofDistTopology d ⋯"}]}
        }
        with self.assertRaisesRegex(ValueError, "Elided proof context"):
            chapter.expression_definition({"lean": "metric", "context": "D"}, records, "Probe")

    def test_structured_targets_keep_exact_context_paths(self):
        target = {"declaration": "D", "path": ["root.body", "arg.body"], "binder": "u"}
        text = scope("structured", {"x": {"symbol": "x", "target": target}}, "$x$")
        parsed = chapter.scopes(text)
        self.assertEqual(parsed[0]["bindings"]["x"]["target"], "D@root.body.arg.body/u")
        records = {"D@root.body.arg.body": {"binders": [{"name": "u", "type": "ℕ → ℝ"}]}}
        row = chapter.report(text, parsed, records, trusted=False)["formulas"][0]
        self.assertEqual(row["variables"][0]["leanName"], "u")
        for bad in (dict(target, path=[]), {"declaration": "D", "binder": "u"}):
            with self.assertRaises(ValueError):
                chapter.scopes(scope("bad", {"x": {"symbol": "x", "target": bad}}, "$x$"))

    def test_sequence_binder_shadows_a_constant_target(self):
        text = scope("outer", {"n": {"symbol": "n", "target": {"constant": "Nat.succ"}}}, r"$\Sequence{n}{n\in\omega}$")
        records = {"Nat.succ": {"binders": [], "declarationType": "ℕ → ℕ"}}
        row = chapter.report(text, chapter.scopes(text), records)["formulas"][0]
        self.assertEqual(row["inferredType"], "ℕ → ℕ")
        self.assertTrue(all("constantDeclaration" not in v for v in row["variables"]))
        self.assertTrue(all(v["localBinder"] for v in row["variables"]))

    def test_local_binder_does_not_capture_outer_identity(self):
        text = scope("outer", {"n": {"symbol": "n", "target": "D/n"}}, r"$\Sequence{x_n}{n\in\omega}$")
        records = {"D": {"binders": [{"name": "n", "type": "Nat"}]}}
        result = chapter.report(text, chapter.scopes(text), records, check=lambda *_: None)
        variables = result["formulas"][0]["variables"]
        indices = [v for v in variables if v["symbol"] == "n"]
        self.assertTrue(all(v["status"] == "resolved" and v.get("localBinder") for v in indices))
        self.assertTrue(all(v["declaration"] is None for v in indices))
        self.assertEqual(len({v["id"] for v in indices}), 1)
        self.assertEqual(result["formulas"][0]["typeStatus"], "unresolved")
        self.assertTrue(result["formulas"][0]["bindingEffects"])

    def test_same_type_retarget_is_not_blessed_by_types(self):
        text = scope("scope", {"x": {"symbol": "x", "target": "D/b"}}, "$x$")
        records = {
            "D": {
                "binders": [{"name": "a", "type": "Nat"}, {"name": "b", "type": "Nat"}],
                "signature": "a b : Nat",
                "body": "Nat",
            }
        }
        reviewed_text = text.replace("D/b", "D/a")
        review = {
            "sourceHash": hashlib.sha256(reviewed_text.encode()).hexdigest(),
            "rulesHash": chapter.rules_hash(),
            "leanFingerprints": {"D": hashlib.sha256(b"a b : Nat\nNat").hexdigest()},
        }
        self.assertTrue(chapter.review_matches(review, reviewed_text, records))
        self.assertFalse(chapter.review_matches(review, text, records))
        result = chapter.report(
            text, chapter.scopes(text), records, trusted=chapter.review_matches(review, text, records)
        )
        self.assertEqual(result["reviewStatus"], "stale")
        self.assertEqual(result["expressionTypes"]["typechecked"], 0)

    def test_unsupported_macro_and_invalid_lean_term_remain_unresolved(self):
        malformed = chapter.report("$x}$", [], {})
        self.assertEqual(malformed["parsing"]["unsupported"], 1)
        result = chapter.report(r"$\Unknown{x}$", [], {})
        self.assertEqual(result["expressionTypes"]["unresolved"], 1)
        row = {"lean": "Nat.succ True", "context": None, "typeStatus": "unresolved"}
        chapter.batch_check([row], {})
        self.assertEqual(row["typeStatus"], "unresolved")
        self.assertIn("Lean rejected", row["typeReason"])
        self.assertIn("diagnostic", row)

    def test_rational_carrier_embedding_and_infinite_endpoints(self):
        formulas = [r"\QQ", r"\SetDifference{\R}{\QQ}", r"\OpenInterval{0}{\infty}", r"\LeftClosedInterval{0}{\infty}"]
        rows = []
        for parsed in chapter.syntax(formulas):
            tree, _ = chapter.located(parsed["tree"])
            term, context = chapter.translate(tree, [])
            rows.append({"lean": term, "context": context})
        self.assertEqual(rows[0]["lean"], "ℚ")
        self.assertIn("Set.range", rows[1]["lean"])
        self.assertEqual(rows[2]["lean"], "Set.Ioi (0 : ℝ)")
        self.assertEqual(rows[3]["lean"], "Set.Ici (0 : ℝ)")
        chapter.batch_check(rows, {})
        self.assertTrue(all(r["typeStatus"] == "typechecked" for r in rows))

    def test_typed_application_and_metric_projection(self):
        binders = [
            {"name": "X", "type": "Type", "instance": False},
            {"name": "d", "type": "MetricSpace X", "instance": True},
            {"name": "x", "type": "X", "instance": False},
            {"name": "y", "type": "X", "instance": False},
            {"name": "f", "type": "X → X → X", "instance": False},
        ]
        bindings = {b["name"]: {"symbol": b["name"], "target": "D/" + b["name"]} for b in binders}
        text = scope("application", bindings, "$d(x,y)$ $f(x,y)$ $x(y)$")
        result = chapter.report(text, chapter.scopes(text), {"D": {"binders": binders}})
        rows = result["formulas"]
        self.assertEqual([r["typeStatus"] for r in rows], ["typechecked", "typechecked", "unresolved"])
        self.assertIn("@dist", rows[0]["lean"])
        self.assertEqual(rows[0]["inferredType"], "ℝ")
        self.assertIn("function binder", rows[2]["typeReason"])

    def test_subscripts_preserve_application_and_source_positions(self):
        binders = [
            {"name": "x", "type": "ℕ → ℝ", "instance": False},
            {"name": "y", "type": "ℕ → ℝ", "instance": False},
            {"name": "n", "type": "ℕ", "instance": False},
            {"name": "f", "type": "ℝ → ℝ → ℝ", "instance": False},
        ]
        bindings = {b["name"]: {"symbol": b["name"], "target": "D/" + b["name"]} for b in binders}
        text = scope("indices", bindings, "$x_n$ $f(x_n,y_n)$ $n_n$ $x^n$")
        result = chapter.report(text, chapter.scopes(text), {"D": {"binders": binders}})
        rows = result["formulas"]
        self.assertEqual([r["typeStatus"] for r in rows], ["typechecked", "typechecked", "unresolved", "unresolved"])
        self.assertEqual(rows[1]["inferredType"], "ℝ")
        self.assertEqual([text[v["start"] : v["end"]] for v in rows[1]["variables"]], ["f", "x", "n", "y", "n"])
        self.assertIn("Source binding is unresolved", rows[2]["typeReason"])
        self.assertEqual(rows[2]["variables"][0]["status"], "unresolved")
        self.assertIn("explicit source selector", rows[3]["typeReason"])

    def test_proof_local_definition_is_replayed_not_assumed(self):
        target = "PolishSpaceBook.complete_compatible_metric_bounded_by_one@root.body.body.body.body"
        records = chapter.evidence({target})
        row = {
            "context": target,
            "lean": "(rfl : boundedDist = fun x y => dist x y / (1 + dist x y))",
        }
        definition = chapter.expression_definition(row, records, "testContext")
        self.assertIn("getConstInfo", definition)
        chapter.batch_check([row], records)
        self.assertEqual(row["typeStatus"], "typechecked")
        family = {"context": target, "lean": "boundedDist"}
        chapter.batch_check([family], records)
        self.assertEqual(family["inferredType"], "Y → Y → ℝ")
        text = scope("bounded", {"bounded": {"symbol": r"\hat d", "target": target + "/boundedDist"}}, r"$\hat d$")
        result = chapter.report(text, chapter.scopes(text), records)
        self.assertEqual(result["formulas"][0]["inferredType"], "Y → Y → ℝ")
        self.assertEqual(result["formulas"][0]["variables"][0]["leanName"], "boundedDist")
        root = target.split("@", 1)[0]
        self.assertNotEqual(records[root]["body"], "none")

    def test_large_local_context_uses_original_expression(self):
        root = "PolishSpaceBook.complete_compatible_metric_bounded_by_one"
        path = "root" + ".body" * 9 + ".value.body"
        target = root + "@" + path
        records = chapter.evidence({target})
        metric = next(b for b in records[target]["binders"] if b["name"] == "boundedMetric")
        self.assertIn("⋯", metric["value"])
        row = {"context": target, "lean": "u"}
        chapter.batch_check([row], records)
        self.assertEqual(row.get("typeStatus"), "typechecked", row.get("diagnostic"))
        self.assertEqual(row["inferredType"], "ℕ → Y")
        incomplete = {"context": target, "lean": "(by sorry : ℕ)"}
        chapter.batch_check([incomplete], records)
        self.assertIn("Incomplete context term", incomplete["diagnostic"])

    def test_context_bridge_rejects_siblings_and_changed_let_values(self):
        binder = {"name": "x", "type": "ℝ", "instance": False, "value": None}
        records = {
            "D": {"binders": []},
            "D@root.body": {"binders": [binder]},
            "D@root.body.body": {"binders": [binder, dict(binder, name="y")]},
            "D@root.arg": {"binders": [binder]},
        }
        self.assertEqual(chapter.shared_context({"D", "D@root.body", "D@root.body.body"}, records), "D@root.body.body")
        with self.assertRaises(chapter.Unsupported):
            chapter.shared_context({"D@root.body", "D@root.arg"}, records)
        records["D@root.body.body"]["binders"][0] = dict(binder, value="0")
        with self.assertRaises(chapter.Unsupported):
            chapter.shared_context({"D@root.body", "D@root.body.body"}, records)

    def test_context_bridge_preserves_original_hygienic_identity(self):
        original = {"name": "inst._hyg.3", "type": "TopologicalSpace X", "instance": True}
        local = dict(original, name="book_hyg_1", originalName=original["name"])
        records = {
            "D": {"binders": [original]},
            "D@root.body": {"binders": [local, {"name": "x", "type": "X"}]},
        }
        self.assertEqual(chapter.shared_context(set(records), records), "D@root.body")
        for change in ({"originalName": "inst._hyg.4"}, {"type": "TopologicalSpace Y"}, {"value": "other"}):
            records["D@root.body"]["binders"][0] = dict(local, **change)
            with self.assertRaises(chapter.Unsupported):
                chapter.shared_context(set(records), records)

    def test_bounded_metric_application_in_its_actual_point_context(self):
        root = "PolishSpaceBook.complete_compatible_metric_bounded_by_one"
        path = "root.body.body.body.body.body.value.body"
        local = root + "@" + path
        records = chapter.evidence({root, local})
        data = {
            "scope": "points",
            "context": {"declaration": root, "path": path},
            "bindings": {
                "d": {"symbol": "d", "target": root + "/originalMetric"},
                "hat": {"symbol": r"\hat d", "target": "boundedDist"},
                "x": {"symbol": "x", "target": "x"},
                "y": {"symbol": "y", "target": "y"},
            },
        }
        text = "<!-- chapter-correspondence " + json.dumps(data) + " -->" + r"$\hat d(x,y)\le d(x,y)$"
        text += "<!-- chapter-correspondence-end: points -->"
        result = chapter.report(text, chapter.scopes(text), records)
        row = result["formulas"][0]
        self.assertEqual(row["typeStatus"], "typechecked", row.get("diagnostic", row.get("typeReason")))
        self.assertEqual(row["inferredType"], "Prop")
        self.assertEqual(row["context"], local)

    def test_topological_class_names_are_polymorphic_predicates(self):
        result = chapter.report(r"$\Gdelta$ $\Fsigma$", [], {})
        self.assertEqual(result["expressionTypes"]["typechecked"], 2)
        for row in result["formulas"]:
            self.assertIn("TopologicalSpace", row["inferredType"])
            self.assertIn("Set", row["inferredType"])
            self.assertIn("Prop", row["inferredType"])
            self.assertIsNone(row["context"])
        self.assertEqual(result["formulas"][0]["lean"], "(@IsGδ)")
        self.assertEqual(result["formulas"][1]["lean"], "(@PolishSpaceBook.IsFsigma)")

    def test_comparison_chain_keeps_every_adjacent_relation(self):
        bindings = {n: {"symbol": n, "target": "D/" + n} for n in "abc"}
        records = {"D": {"binders": [{"name": n, "type": "ℝ", "instance": False} for n in "abc"]}}
        text = scope("chain", bindings, r"$0<a<1$ $a=b\le c$ $a<<b$")
        result = chapter.report(text, chapter.scopes(text), records)
        rows = result["formulas"]
        self.assertEqual([r["typeStatus"] for r in rows], ["typechecked", "typechecked", "unresolved"])
        self.assertEqual(rows[0]["inferredType"], "Prop")
        self.assertEqual(rows[1]["lean"].count("∧"), 1)
        self.assertIn("((«a») = («b»))", rows[1]["lean"])
        self.assertIn("((«b») ≤ («c»))", rows[1]["lean"])
        self.assertIn("Empty expression operand", rows[2]["typeReason"])

    def test_sequence_binders_shadow_outer_names_and_check_index_types(self):
        bindings = {n: {"symbol": n, "target": "D/" + n} for n in "xn"}
        records = {
            "D": {
                "binders": [
                    {"name": "x", "type": "ℕ → ℝ", "instance": False},
                    {"name": "n", "type": "ℝ", "instance": False},
                ]
            }
        }
        text = scope(
            "seq",
            bindings,
            r"$\Sequence{x_n}{n\in\omega}$ $\Sequence{\Sequence{x_n}{n\in\omega}}{n\in\omega}$ $\Sequence{x_n}{n\ge1}$",
        )
        result = chapter.report(text, chapter.scopes(text), records)
        rows = result["formulas"]
        self.assertEqual([r["typeStatus"] for r in rows], ["typechecked"] * 3)
        self.assertTrue(
            all(v.get("indexOffset") == 1 and v["localBinder"] for v in rows[2]["variables"] if v["symbol"] == "n")
        )
        self.assertEqual(rows[0]["inferredType"], "ℕ → ℝ")
        offset = rows[0]["bindingEffects"][0]["binder"]["declarationOffset"]
        self.assertEqual(text[offset], "n")
        self.assertEqual(rows[1]["inferredType"], "ℕ → ℕ → ℝ")
        ids = [v["id"] for v in rows[1]["variables"] if v["symbol"] == "n"]
        self.assertEqual(len(set(ids)), 2)
        self.assertEqual(ids[0], ids[1])
        self.assertNotEqual(ids[1], ids[2])
        records["D"]["binders"][0]["type"] = "Bool → ℝ"
        bad = chapter.report(text, chapter.scopes(text), records)
        self.assertEqual(bad["formulas"][0]["typeStatus"], "unresolved")
        self.assertIn("diagnostic", bad["formulas"][0])

    def test_carrier_set_convention_preserves_ambient_types(self):
        binders = [
            {"name": "X", "type": "Type", "instance": False},
            {"name": "Y", "type": "Type", "instance": False},
            {"name": "C", "type": "Set X", "instance": False},
            {"name": "D", "type": "Set X", "instance": False},
            {"name": "x", "type": "X", "instance": False},
        ]
        bindings = {b["name"]: {"symbol": b["name"], "target": "D/" + b["name"]} for b in binders}
        text = scope(
            "sets",
            bindings,
            r"$C \IncludedIn X$ $\SetDifference{X}{C}$ $C\cap D\IncludedIn X$ $x\in X$ $C\IncludedIn Y$",
        )
        result = chapter.report(text, chapter.scopes(text), {"D": {"binders": binders}})
        rows = result["formulas"]
        self.assertEqual([r["typeStatus"] for r in rows], ["typechecked"] * 4 + ["unresolved"])
        self.assertIn("Set.univ", rows[0]["lean"])
        self.assertEqual(rows[1]["inferredType"], "Set X")
        self.assertEqual(rows[3]["inferredType"], "Prop")
        rational = chapter.report(r"$\QQ \IncludedIn \R$", [], {})["formulas"][0]
        self.assertEqual(rational["typeStatus"], "typechecked")
        self.assertIn("Set.range", rational["lean"])

    def test_metric_bounds_are_pointwise(self):
        binders = [
            {"name": "X", "type": "Type", "instance": False},
            {"name": "d", "type": "MetricSpace X", "instance": True},
            {"name": "bounded", "type": "X → X → ℝ", "instance": False},
        ]
        bindings = {"d": {"symbol": "d", "target": "D/d"}, "bounded": {"symbol": r"\hat d", "target": "D/bounded"}}
        text = scope("metric", bindings, r"$d\le 1$ $\hat d\le d$")
        result = chapter.report(text, chapter.scopes(text), {"D": {"binders": binders}})
        self.assertEqual(result["expressionTypes"]["typechecked"], 2)
        for row in result["formulas"]:
            self.assertEqual(row["inferredType"], "Prop")
        expected = ["∀ x y : X, @dist X d.toDist x y ≤ 1", "∀ x y : X, bounded x y ≤ @dist X d.toDist x y"]
        proofs = [
            {"lean": f"(show ({row['lean']}) = ({proposition}) from rfl)", "context": "D"}
            for row, proposition in zip(result["formulas"], expected, strict=True)
        ]
        chapter.batch_check(proofs, {"D": {"binders": binders}})
        self.assertTrue(all(row["typeStatus"] == "typechecked" for row in proofs))

    def test_real_lean_expression_checks(self):
        rows = [{"lean": "ℝ", "context": None}, {"lean": "Set.Icc (0 : ℝ) (1 : ℝ)", "context": None}]
        chapter.batch_check(rows, {})
        self.assertTrue(all(r["typeStatus"] == "typechecked" for r in rows))


if __name__ == "__main__":
    unittest.main()
