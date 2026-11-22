"""Native lowering rejects malformed inputs and preserves exact source spans."""

import json
import subprocess
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

from correspondence_oracle import legacy_oracle

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools/chapter-correspondence"))
import native
from validate import chapter


def syntax(formulas):
    result = subprocess.run(
        [str(ROOT / "build/book-filter"), "math-syntax-located"],
        input=json.dumps(formulas),
        text=True,
        capture_output=True,
        check=True,
    )
    return json.loads(result.stdout)


class NativeCorrespondenceTests(unittest.TestCase):
    def test_unicode_offsets_are_character_offsets(self):
        source = r"😀α+\frac{日_x}{β^{12}}"
        row = syntax([source])[0]
        self.assertTrue(row["roundtrip"])
        tree = row["tree"]
        self.assertEqual((tree["start"], tree["end"]), (0, len(source)))
        macro = tree["items"][1]
        self.assertEqual((macro["start"], macro["end"]), (3, len(source)))
        numerator, denominator = macro["args"]
        self.assertEqual(source[numerator["start"] : numerator["end"]], "日_x")
        self.assertEqual(source[denominator["start"] : denominator["end"]], "β^{12}")
        argument = denominator["items"][0]["argument"]
        self.assertEqual(source[argument["start"] : argument["end"]], "{12}")

    def test_unicode_decimal_indices_keep_their_numeric_value(self):
        source = r"\Sequence{x_n}{n\ge １２}"
        node = syntax([source])[0]["tree"]["items"][0]
        self.assertEqual(chapter.sequence_binder(node)["indexOffset"], 12)
        power = syntax(["١٢^n"])[0]["tree"]["items"][0]
        self.assertTrue(chapter.numeric_power(power))

    def test_native_recognition_does_not_approve_interpretations(self):
        node = syntax([r"\Sequence{x_n}{n\in\omega}"])[0]["tree"]["items"][0]
        result = native.structural("sequenceBinder", node)
        self.assertEqual(result["indexOffset"], 0)
        self.assertNotIn("reviewed", result)
        basis = {"sourceHash": "source", "rulesHash": "rules", "leanFingerprints": {"D": "body"}}
        self.assertTrue(native.request({"action": "reviewMatches", "recorded": basis, "current": basis})["matched"])
        for changed in (
            dict(basis, sourceHash="other"),
            dict(basis, rulesHash="other"),
            dict(basis, leanFingerprints={"D": "different body"}),
            dict(basis, leanFingerprints={}),
        ):
            self.assertFalse(
                native.request({"action": "reviewMatches", "recorded": basis, "current": changed})["matched"]
            )

    def test_cached_recognition_does_not_share_mutable_nodes(self):
        node = syntax(["α+β"])[0]["tree"]["items"][0]
        first = native.structural("expressionTokens", node)
        first[0]["text"] = "changed"
        self.assertEqual(native.structural("expressionTokens", node)[0]["text"], "α")

    def test_empty_script_base_fails_without_worker_loss(self):
        node = {
            "kind": "script",
            "marker": "_",
            "start": 0,
            "end": 2,
            "base": {"kind": "text", "text": "", "start": 0, "end": 0},
            "argument": {"kind": "text", "text": "n", "start": 1, "end": 2},
        }
        with self.assertRaisesRegex(ValueError, "Empty script base"):
            native.structural("expressionTokens", node)
        self.assertEqual(native.lower_macro("Abs", ["x"]), "|x|")

    def test_natural_lower_bound_requires_contiguous_digits(self):
        source = r"n\ge 12"
        tree = syntax([source])[0]["tree"]
        result = native.structural("naturalLowerBound", tree)
        self.assertEqual(result["lowerBound"], "12")
        span = result["components"][-1]
        self.assertEqual(source[span["start"] : span["end"]], "12")
        for bad in (r"n\ge 1 2", r"n\ge -1"):
            self.assertIsNone(native.structural("naturalLowerBound", syntax([bad])[0]["tree"]))

    def test_integer_exponent_normalization_keeps_groups_and_unicode_offsets(self):
        source = "-(α+12)"
        tree = syntax([source])[0]["tree"]
        result = native.structural("integerExpression", tree)
        self.assertEqual(result["kind"], "integer-expression")
        tokens = result["body"]["items"][0]["items"]
        self.assertEqual([p["text"] for p in tokens], ["-", "(", "α", "+", "12", ")"])
        self.assertEqual(
            [p["kind"] for p in tokens], ["text", "text", "integer-variable", "text", "integer-literal", "text"]
        )
        self.assertTrue(all(source[p["start"] : p["end"]] == p["text"] for p in tokens))
        for bad in ("x/2", r"\Abs{x}", "x=2"):
            with self.assertRaisesRegex(ValueError, "integer|Integer"):
                native.structural("integerExpression", syntax([bad])[0]["tree"])

    def test_cases_normalization_keeps_branch_spans_and_avoids_context_names(self):
        source = r"f=\begin{cases}x & x=0,\\y & x\ne 0.\end{cases}"
        tree = syntax([source])[0]["tree"]
        payload = {"tree": tree, "occupied": ["book_case_2_0"]}
        result = native.structural("casesNode", payload)
        grouped = next(t for t in result["items"] if t["kind"] == "real-cases")
        self.assertEqual([b["proofName"] for b in grouped["branches"]], ["book_case_2_0_", "book_case_2_1"])
        self.assertEqual([b["equality"] for b in grouped["branches"]], [True, False])
        for branch, value, condition in zip(grouped["branches"], ["x", "y"], ["x=0", r"x\ne 0"], strict=True):
            self.assertEqual(source[branch["body"]["start"] : branch["body"]["end"]], value)
            self.assertEqual(source[branch["condition"]["start"] : branch["condition"]["end"]], condition)
        self.assertIsNone(native.structural("casesNode", {"tree": syntax(["x+y"])[0]["tree"]}))
        for bad, message in (
            (r"\begin{cases}x & x=0\end{cases}", "two complementary"),
            (r"\begin{cases}x & x=0\\y & x>0", "one unnested"),
            (r"\begin{cases}x & & x=0\\y & x>0\end{cases}", "one value and condition"),
        ):
            with self.assertRaisesRegex(ValueError, message):
                native.structural("casesNode", {"tree": syntax([bad])[0]["tree"]})

    def test_summation_scope_ends_before_addition(self):
        for domain, mode in ((r"n<k", "finite"), (r"n\in\omega", "infinite"), (r"n\ge k", "tail")):
            source = r"\sum_{" + domain + "} x_n+y"
            chunks = native.structural("summationChunks", syntax([source])[0]["tree"])
            self.assertEqual(len(chunks), 1)
            self.assertEqual(chunks[0]["mode"], mode)
            body = chunks[0]["body"]
            self.assertEqual(source[body["start"] : body["end"]], "x_n")

    def test_predicate_set_preserves_domain_and_sized_delimiters(self):
        source = r"\left\{x\in A:x>0\right\}"
        shapes = native.structural("predicateSets", syntax([source])[0]["tree"])
        self.assertEqual(len(shapes), 1)
        shape = shapes[0]
        self.assertEqual(shape["binder"]["text"], "x")
        self.assertEqual(shape["domain"]["text"], "A")
        body = shape["body"]
        self.assertEqual(source[body["start"] : body["end"]], "x>0")
        self.assertEqual(shape["first"], 0)
        bad = r"\left\{x:x>0\}"
        self.assertEqual(native.structural("predicateSets", syntax([bad])[0]["tree"]), [])

    def test_indexed_singleton_requires_identity_and_retains_index_carrier(self):
        for carrier, index_type in (("QQ", "ℚ"), ("R", "ℝ"), ("omega", "ℕ")):
            source = r"\bigcup_{q\in" + chr(92) + carrier + r"}\{q\}"
            shapes = native.structural("indexedSingletons", syntax([source])[0]["tree"])
            self.assertEqual(len(shapes), 1)
            self.assertEqual(shapes[0]["indexType"], index_type)
            self.assertTrue(shapes[0]["whole"])
            self.assertNotIn("ambient", shapes[0])
        bad = r"\bigcup_{q\in\QQ}\{r\}"
        self.assertEqual(native.structural("indexedSingletons", syntax([bad])[0]["tree"]), [])

    def test_natural_family_retains_lower_bound_and_each_family_reference(self):
        source = r"\bigcap_{n\ge 2}(U_n\cap V_n)"
        shapes = native.structural("naturalFamilies", syntax([source])[0]["tree"])
        self.assertEqual(len(shapes), 1)
        binder = shapes[0]["binder"]
        self.assertEqual(binder["lowerBound"], "2")
        self.assertEqual(binder["familyOffsets"], [source.index("U_n"), source.index("V_n")])
        self.assertTrue(all(component["target"].startswith("lambda.") for component in binder["components"]))
        for bad in (
            r"\bigcap U_n",
            r"\bigcap_{m\in\omega}U_n",
        ):
            self.assertEqual(native.structural("naturalFamilies", syntax([bad])[0]["tree"]), [])
        nested = r"\bigcap_{n\in\omega}(U_n\cap\bigcup_{m\in\omega}V_m)"
        inner = native.structural("naturalFamilies", syntax([nested])[0]["tree"])
        self.assertEqual([shape["marker"]["name"] for shape in inner], ["bigcup"])
        self.assertTrue(all(not shape["whole"] for shape in inner))
        product = r"\prod_{n\in\omega}X_n"
        self.assertIsNotNone(native.structural("naturalFamily", syntax([product])[0]["tree"]))
        self.assertIsNone(native.structural("naturalFamily", syntax([source])[0]["tree"]))

    def test_native_lexical_walk_retains_decorations_and_skips_prose(self):
        source = r"\hat d+x_1+A^*+\text{ignored}"
        result = native.structural("lexicalWalk", syntax([source])[0]["tree"])
        variables = result["variables"]
        self.assertEqual([v["symbol"] for v in variables], [r"\hat d", "x", "A^*"])
        self.assertTrue(variables[1]["subscriptBase"])
        self.assertEqual(variables[1]["numericSubscriptName"]["symbol"], "x_1")
        self.assertEqual(result["effects"], [])
        prime = r"\phi'+\text{ignored}"
        primed = native.structural("lexicalWalk", syntax([prime])[0]["tree"])["variables"]
        self.assertEqual([v["symbol"] for v in primed], [r"\phi'"])
        builder = r"\{x:x>0\}"
        guard = native.structural("lexicalWalk", syntax([builder])[0]["tree"])["effects"]
        self.assertEqual(len(guard), 1)
        self.assertEqual(guard[0]["command"], "unreviewed-set-builder")
        self.assertNotIn("binder", guard[0])

    def test_native_binding_registration_preserves_scope_and_exact_domain(self):
        source = r"\sum_{n<k}x_n+y_n"
        result = native.structural("extractBindings", syntax([source])[0]["tree"])
        effect = next(e for e in result["effects"] if e["command"] == "natural-sum")
        self.assertEqual(effect["binder"]["symbol"], "n")
        self.assertEqual(source[effect["binder"]["bodyStart"] : effect["end"]], "x_n")
        self.assertLess(effect["end"], source.index("y_n"))
        self.assertNotIn("reason", effect)
        source = r"\{x\in A:x>0\}"
        result = native.structural("extractBindings", syntax([source])[0]["tree"])
        self.assertEqual([e["command"] for e in result["effects"]], ["predicate-set"])
        binder = result["effects"][0]["binder"]
        self.assertEqual(binder["domainOffset"], source.index("A"))
        self.assertEqual(binder["symbol"], "x")

    def test_optional_argument_and_literal_interval(self):
        for source in (r"\foo[α]{β}", r"f\to[0,\infty)"):
            row = syntax([source])[0]
            self.assertTrue(row["roundtrip"])
            self.assertEqual(row["tree"]["end"], len(source))
        command = syntax([r"\foo[α]{β}"])[0]["tree"]["items"][0]
        self.assertEqual((command["optional"]["start"], command["optional"]["end"]), (5, 6))

    def test_malformed_grouping_is_not_accepted(self):
        for row in syntax([r"\frac{x}{y", "{x", "x}"]):
            self.assertTrue(row["problems"])

    def test_native_macro_operands_are_not_reordered(self):
        expected = {
            "SetDifference": "(left \\ right)",
            "frac": "((left) / (right))",
            "Abs": "|left|",
            "Closure": "closure (left)",
            "AmbientClosure": "@closure (left) inferInstance (right)",
            "Ball": "Metric.ball (left) (right : ℝ)",
            "ClosedInterval": "Set.Icc (left : ℝ) (right : ℝ)",
            "OpenInterval": "Set.Ioo (left : ℝ) (right : ℝ)",
            "LeftClosedInterval": "Set.Ico (left : ℝ) (right : ℝ)",
        }
        macros = native.NativeMacros()
        self.assertEqual(set(macros), set(expected))
        for name, result in expected.items():
            arity, lower = macros[name]
            self.assertEqual(lower(["left", "right"][:arity]), result)

    def test_invalid_rule_and_arity_fail_without_restarting_worker(self):
        native.request({"action": "macros"})
        process = native._process
        for name, args in (("frac", ["x"]), ("Abs", ["x", "y"]), ("invented", ["x"])):
            with self.assertRaises(ValueError):
                native.lower_macro(name, args)
        with self.assertRaises(ValueError):
            native.request({"action": "invented"})
        self.assertEqual(native.lower_macro("frac", ["x", "y"]), "((x) / (y))")
        self.assertIs(native._process, process)


class NativeSemanticTranslationTests(unittest.TestCase):
    def test_chapter_preparation_and_translation_use_one_source_transaction(self):
        metadata = {
            "scope": "batch",
            "bindings": {name: {"symbol": name, "target": "D/" + name} for name in ("x", "y")},
        }
        source = "<!-- chapter-correspondence " + json.dumps(metadata) + " -->$x+y$ and $x,y$"
        source += "<!-- chapter-correspondence-end: batch -->"
        scopes = chapter.scopes(source)
        records = {
            "D": {
                "binders": [{"name": name, "type": "Real", "instance": False} for name in ("x", "y")],
                "body": "DECLARATION_BODY_MUST_NOT_CROSS_THE_PREPARATION_BOUNDARY",
            }
        }
        native._analyze_chapter.cache_clear()

        def checked(row, _records):
            row.update(typeStatus="typechecked", inferredType="transport fixture")

        with (
            patch.object(native, "request", wraps=native.request) as requests,
            patch.object(chapter, "leaves", side_effect=AssertionError("fine-grained walk")),
            patch.object(chapter, "resolve_variables", side_effect=AssertionError("fine-grained resolution")),
            patch.object(chapter, "resolve_numeric_domain", side_effect=AssertionError("fine-grained normalization")),
        ):
            report = chapter.report(source, scopes, records, check=checked)
        self.assertEqual([call.args[0]["action"] for call in requests.call_args_list], ["analyzeChapter"])
        self.assertNotIn("DECLARATION_BODY_MUST_NOT_CROSS", json.dumps([call.args for call in requests.call_args_list]))
        self.assertEqual([row["typeStatus"] for row in report["formulas"]], ["typechecked", "typechecked"])
        self.assertEqual(len(report["formulas"][1]["expressionFragments"]), 2)
        invalid = chapter.syntax(["x"])
        invalid[0]["tree"]["end"] = 2
        with self.assertRaisesRegex(ValueError, "positions did not consume"):
            native.prepare_chapter("$x$", [], {}, parsed=invalid)

    def test_chapter_batch_shares_signatures_and_resolves_contexts_per_expression(self):
        tree, variables = self.expression("x+y")
        for variable in variables:
            variable["declaration"] = "D@root" if variable["symbol"] == "x" else "D@root.body"
        binder = {"name": "x", "originalName": "source_x", "type": "Real", "instance": False}
        records = {
            "D@root": {"binders": [dict(binder)]},
            "D@root.body": {"binders": [dict(binder), {"name": "y", "type": "Real", "instance": False}]},
        }
        numeric, _ = self.expression("1+2")
        jobs = [{"tree": tree, "variables": variables}, {"tree": numeric, "variables": []}]
        results = native.semantic_translation_batch(jobs, ["md_operator_0"], records=records)
        self.assertEqual([result["supported"] for result in results], [True, False])
        self.assertEqual(results[0]["context"], "D@root.body")
        self.assertEqual(results[0]["rendering"]["mappings"][0]["marker"], "md_operator_0_")
        self.assertIn("no reviewed ambient number type", results[1]["reason"])
        individual = native.semantic_translation(tree, variables, ["md_operator_0"], records=records)
        self.assertEqual(results[0]["rendering"], individual["rendering"])
        # Cached reports must not share mutable response dictionaries.
        results[0]["rendering"]["ordinary"] = "corrupted"
        fresh = native.semantic_translation_batch(jobs, ["md_operator_0"], records=records)
        self.assertEqual(fresh[0]["rendering"], individual["rendering"])
        records["D@root"]["binders"][0]["value"] = "0"
        rejected = native.semantic_translation_batch(jobs, [], records=records)
        self.assertFalse(rejected[0]["supported"])
        self.assertIn("prefix changed", rejected[0]["reason"])

    def test_shared_membership_singletons_and_variable_lists_keep_source_evidence(self):
        for source, types in (
            (r"x,y\in X", {"x": "X", "y": "X", "X": "Type"}),
            (r"x,y\in A", {"x": "Real", "y": "Real", "A": "Set Real"}),
            (r"x=y\in A", {"x": "Real", "y": "↑A", "A": "Set Real"}),
            (r"A\hookrightarrow B", {"A": "Set Real", "B": "Set Real"}),
            (r"x,y\ge 0", {"x": "Real", "y": "Real"}),
            (r"\{x\}", {"x": "Real"}),
        ):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    name = variable["symbol"]
                    variable.update(
                        id="s/" + name,
                        declaration="D",
                        leanName=name,
                        leanType=types[name],
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                invalid = [dict(variable, status="unresolved") for variable in variables]
                self.assertFalse(native.semantic_translation(tree, invalid, [])["supported"])

        for source in (r"\{x,y\}", r"\{\}", "x,y=0", r"x,y\in z"):
            tree, variables = self.expression(source)
            self.assertFalse(native.semantic_translation(tree, variables, [])["supported"], source)

    def test_comparisons_use_original_types_without_a_scalar_type_whitelist(self):
        for source, types in (
            ("x<y", {"x": "X", "y": "X"}),
            ("f(x)<f(y)", {"x": "X", "y": "X", "f": "X → Y"}),
            (r"f(x)\le1", {"x": "Real", "f": "Real → Real"}),
        ):
            tree = syntax([source])[0]["tree"]
            variables, _ = chapter.leaves(tree)
            for variable in variables:
                name = variable["symbol"]
                variable.update(
                    id="s/" + name,
                    declaration="D",
                    leanName=name,
                    leanType=types[name],
                    status="resolved",
                    formulaOffset=variable["start"],
                )
            with legacy_oracle(chapter):
                plain, context = chapter.translate(tree, variables)
                mappings = []
                instrumented, _ = chapter.translate(tree, variables, trace=mappings)
            result = native.semantic_translation(tree, variables, [])
            self.assertTrue(result["supported"], result)
            self.assertEqual(result["contexts"], [context])
            self.assertEqual(
                result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
            )

    def test_source_numeric_domains_cover_literals_arithmetic_and_comparison_chains(self):
        for source in (" 12 ", "1/3", "(12+1)/3", r"1\le12+1=13", "\x1c12\x1f"):
            for constant in (False, True):
                with self.subTest(source=source, constant=constant):
                    target = {"constant": "Dist.dist"} if constant else "D/d"
                    annotation = {
                        "scope": "numbers",
                        "bindings": {"distance": {"symbol": "d", "target": target}},
                        "numerals": {"type": "Real", "from": "distance"},
                    }
                    text = "<!-- chapter-correspondence " + json.dumps(annotation) + " -->$" + source
                    text += "$<!-- chapter-correspondence-end: numbers -->"
                    records = {
                        "D": {"binders": [{"name": "d", "type": "ℝ → ℝ", "instance": False}]},
                        "Dist.dist": {"binders": []},
                    }
                    row = chapter.report(text, chapter.scopes(text), records, trusted=False)["formulas"][0]
                    tree = row["syntax"]
                    with legacy_oracle(chapter):
                        plain, context = chapter.translate(tree, [], records)
                        mappings = []
                        instrumented, _ = chapter.translate(tree, [], records, trace=mappings)
                    result = native.semantic_translation(tree, [], [], records=records)
                    self.assertTrue(result["supported"], result)
                    self.assertEqual(chapter.shared_context(result["contexts"], records), context)
                    self.assertEqual(
                        result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                    )
                    self.assertFalse(native.semantic_translation(tree, [], [], records={})["supported"])
                    self.assertFalse(
                        native.semantic_translation(dict(tree, inventedAnnotation=True), [], [], records=records)[
                            "supported"
                        ]
                    )
                    if "numericDomain" in tree:
                        altered = json.loads(json.dumps(tree))
                        altered["numericEnd"] += 1
                        self.assertFalse(native.semantic_translation(altered, [], [], records=records)["supported"])
                        altered = json.loads(json.dumps(tree))
                        altered["numeral"] = "99"
                        self.assertFalse(native.semantic_translation(altered, [], [], records=records)["supported"])

    def test_prefix_radius_predicate_keeps_bound_source_type_and_hygienic_name(self):
        tree = syntax(["<12"])[0]["tree"]
        tree = native.request(
            {
                "action": "normalizeSource",
                "stage": "prefix",
                "tree": tree,
                "row": {"start": 1},
                "scopes": [
                    {
                        "scope": "s",
                        "start": 0,
                        "end": 100,
                        "context": {"declaration": "D", "path": "root"},
                        "predicates": {"type": "Real", "witness": "d"},
                    }
                ],
            }
        )["tree"]
        records = {
            "D@root": {
                "binders": [
                    {"name": "d", "type": "ℝ → ℝ", "instance": False},
                    {"name": "book_radius", "type": "Nat", "instance": False},
                ]
            }
        }
        with legacy_oracle(chapter):
            plain, context = chapter.translate(tree, [], records)
            mappings = []
            instrumented, _ = chapter.translate(tree, [], records, trace=mappings)
        result = native.semantic_translation(tree, [], ["d", "book_radius"], records=records)
        self.assertTrue(result["supported"], result)
        self.assertEqual(chapter.shared_context(result["contexts"], records), context)
        self.assertEqual(result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings})
        self.assertEqual(mappings[-1]["expectedBinderName"], "book_radius_")
        self.assertFalse(native.semantic_translation(tree, [], [])["supported"])
        altered = json.loads(json.dumps(tree))
        altered["prefixPredicate"]["bound"]["numeral"] = "13"
        altered["prefixPredicate"]["bound"]["items"][-1]["text"] = "3"
        self.assertFalse(native.semantic_translation(altered, [], [], records=records)["supported"])

    def test_contextual_literal_interpretations_keep_distinct_constants_and_consumers(self):
        source = (
            "<!-- chapter-correspondence "
            + json.dumps(
                {
                    "scope": "zero",
                    "bindings": {},
                    "literalInterpretations": [
                        {
                            "id": identity,
                            "constant": constant,
                            "consumer": {"declaration": declaration, "callee": "F", "argumentPosition": 1},
                        }
                        for identity, constant, declaration in [
                            ("cantor", "Bool.false", "C"),
                            ("baire", "Nat.zero", "B"),
                        ]
                    ],
                }
            )
            + " -->$0$<!-- chapter-correspondence-end: zero -->"
        )
        records = {name: {"binders": []} for name in ["Bool.false", "Nat.zero", "C", "B", "F"]}
        row = chapter.report(source, chapter.scopes(source), records, trusted=False)["formulas"][0]
        for tree in chapter.expression_list(row["syntax"]):
            with legacy_oracle(chapter):
                plain, context = chapter.translate(tree, [], records)
                mappings = []
                instrumented, _ = chapter.translate(tree, [], records, trace=mappings)
            result = native.semantic_translation(tree, [], [], records=records)
            self.assertTrue(result["supported"], result)
            self.assertEqual(chapter.shared_context(result["contexts"], records), context)
            self.assertEqual(
                result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
            )
            self.assertFalse(native.semantic_translation(tree, [], [], records={"F": {"binders": []}})["supported"])
            for name in (tree["expectedConstant"], tree["consumer"]["declaration"], tree["consumer"]["callee"]):
                incomplete = {key: record for key, record in records.items() if key != name}
                self.assertFalse(native.semantic_translation(tree, [], [], records=incomplete)["supported"])

    def test_real_cases_and_sigma_pairs_preserve_scoped_equality_transport(self):
        case = r"\begin{cases}d_n(x,y), & n=m,\\1, & n\ne m.\end{cases}"
        for source in (
            r"\Pair{n}{x}",
            case,
            r"d(\Pair{n}{x},\Pair{m}{y})=" + case,
            case.replace("d_n(x,y)", r"\MetricDiameter{d_n}{\MetricBall{d_n}{y}{1}}"),
        ):
            with self.subTest(source=source):
                types = {
                    "Y": "ℕ → Type",
                    "metrics": "(i : ℕ) → MetricSpace (Y i)",
                    "distance": "Sigma Y → Sigma Y → ℝ",
                    "i": "ℕ",
                    "j": "ℕ",
                    "x": "Y i",
                    "y": "Y j",
                }
                bindings = {
                    "family": {"symbol": "d", "occurrence": "subscript-base", "target": "D/metrics"},
                    "distance": {"symbol": "d", "occurrence": "unsubscripted", "target": "D/distance"},
                    "first": {"symbol": "n", "target": "D/i"},
                    "second": {"symbol": "m", "target": "D/j"},
                    "x": {"symbol": "x", "target": "D/x"},
                    "y": {"symbol": "y", "target": "D/y"},
                }
                text = (
                    "<!-- chapter-correspondence "
                    + json.dumps({"scope": "cases", "bindings": bindings})
                    + " -->$"
                    + source
                )
                text += "$<!-- chapter-correspondence-end: cases -->"
                occupied = list(types)
                if r"\begin" in source:
                    begin = source.index(r"\begin")
                    occupied += [f"book_case_{begin}_0", f"book_case_{begin}_0_", f"book_case_{begin}_1"]
                records = {
                    "D": {
                        "binders": [
                            {"name": name, "type": types.get(name, "ℕ"), "instance": False} for name in occupied
                        ]
                    }
                }
                row = chapter.report(text, chapter.scopes(text), records, trusted=False)["formulas"][0]
                tree, variables = row["syntax"], row["variables"]
                self.assertTrue(all(v["status"] == "resolved" for v in variables), variables)
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables, records)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, records, trace=mappings)
                result = native.semantic_translation(tree, variables, occupied, records=records)
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                if r"\begin" in source:
                    metric = next((m for m in mappings if m["rule"] == "application:metric"), None)
                    if metric is not None:
                        self.assertEqual(metric["lowering"]["operation"], "Eq.mp")
                        self.assertTrue(metric["lowering"]["branchProof"].endswith("__"))
                    else:
                        ball = next(m for m in mappings if m["rule"] == "macro:MetricBall")
                        self.assertIn("bookEqualMetricPoint%", ball["expectedOperands"][0]["candidate"])
                if r"\Pair" in source:
                    self.assertFalse(native.semantic_translation(tree, variables, occupied)["supported"])
                    changed = {
                        "D": {
                            "binders": [
                                dict(b, type="Int → Type") if b["name"] == "Y" else b for b in records["D"]["binders"]
                            ]
                        }
                    }
                    self.assertFalse(
                        native.semantic_translation(tree, variables, occupied, records=changed)["supported"]
                    )

    def test_set_comprehensions_and_infimum_images_keep_source_owned_domains(self):
        for source in (
            r"\{s:s>0\}",
            r"\left\{s:s>0\right\}",
            r"\{s:P(s)\}",
            r"\{s\in X:P(s)\}",
            r"x\in\{s:s>0\}",
            r"d(x,\{s:s>0\})",
            r"\{s:s\in\{t:t>0\}\}",
            r"\{s:\sum_{n<m}2^{-n}<s\}",
            r"\bigcap_{n\in\omega}\{s\in X:P(s)\}",
            r"\inf\{d(x,s):s\in C\}",
            r"d(x,C):=\inf\{d(x,s):s\in C\}",
            r"\inf\{s:s\in C\}",
        ):
            with self.subTest(source=source):
                types = {
                    "s": "Int" if r"\inf" in source else "ℝ",
                    "t": "ℝ",
                    "x": "ℝ",
                    "C": "Set ℝ",
                    "d": "MetricSpace ℝ",
                    "P": "X → Prop" if r"\in X" in source else "ℝ → Prop",
                    "X": "Type",
                    "n": "ℕ",
                    "m": "ℕ",
                }
                bindings = {name: {"symbol": name, "target": "D/" + name} for name in types}
                text = (
                    "<!-- chapter-correspondence "
                    + json.dumps({"scope": "builder", "bindings": bindings})
                    + " -->$"
                    + source
                )
                text += "$<!-- chapter-correspondence-end: builder -->"
                records = {
                    "D": {"binders": [{"name": name, "type": ty, "instance": False} for name, ty in types.items()]}
                }
                row = chapter.report(text, chapter.scopes(text), records, trusted=False)["formulas"][0]
                tree, variables = row["syntax"], row["variables"]
                self.assertTrue(all(v["status"] == "resolved" for v in variables), variables)
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables, records)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, records, trace=mappings)
                result = native.semantic_translation(tree, variables, list(types), constants=chapter.CONSTANTS)
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                if source == r"d(x,\{s:s>0\})":
                    # The legacy interpreter classified a constructed set as a
                    # point and Lean rejected it. The semantic AST knows its role.
                    self.assertIn("@dist", plain)
                    self.assertIn("Metric.infDist", result["rendering"]["ordinary"])
                    self.assertEqual(result["rendering"]["mappings"][-1]["rule"], "application:distance-to-set")
                else:
                    self.assertEqual(
                        result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                    )
                altered = [dict(v, localBinder=False) if v.get("localBinder") else v for v in variables]
                self.assertFalse(
                    native.semantic_translation(tree, altered, list(types), constants=chapter.CONSTANTS)["supported"]
                )

    def test_sentence_punctuation_belongs_only_to_the_root_comparison(self):
        for source in ("x<y.", " x<1, "):
            tree, variables = self.expression(source)
            with legacy_oracle(chapter):
                plain, _ = chapter.translate(tree, variables)
                mappings = []
                instrumented, _ = chapter.translate(tree, variables, trace=mappings)
            result = native.semantic_translation(tree, variables, [])
            self.assertTrue(result["supported"], result)
            self.assertEqual(
                result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
            )
            self.assertFalse(native.semantic_translation(tree, variables, [], root=False)["supported"])

    def test_metric_set_operations_restrictions_and_composition_preserve_adapters(self):
        for source in (
            r"\AmbientClosure{\R}{A}",
            r"\MetricBall{d}{x}{r+1}",
            r"\MetricBall{d_n}{x}{\epsilon}",
            r"\MetricDiameter{d}{A}",
            r"\MetricDiameter{d}{A}<1/n.",
            r"\MetricDiameter{d}{A}\le2^{-n}",
            r"\MetricDiameter{d}{A_n}\to r/2",
            r"d(x,x)<1/n",
            r"\MetricDiameter{d_n}{\Closure{A}}",
            r"\restrict{d}{A\times A}",
            r"\restrict{d_n}{A\times A}",
            r"\restrict{f}{A}",
            r"\phi\circ d",
            r"\phi\circ d_n",
            r"f\circ g",
            r"\phi\circ k",
            r"h\circ k",
            r"d\le1",
            r"d_n\le1",
            r"d_n\le d_n",
            r"\hat d\le d",
            r"d\le d'",
            r"d\le j",
            r"\restrict{\hat d}{A\times A}",
            r"\phi\circ\hat d",
            r"d(x,A')",
        ):
            with self.subTest(source=source):
                types = {
                    "d": "ℕ → MetricSpace ℝ" if "d_n" in source else "MetricSpace ℝ",
                    "A": "ℕ → Set ℝ" if "A_n" in source else "Set ℝ",
                    "x": "ℝ",
                    "r": "Nat",
                    "n": "Nat",
                    "f": "ℝ → ℝ",
                    "g": "ℤ → ℝ",
                    "k": "ℝ → ℝ → ℝ",
                    "h": "(ℝ → ℝ) → ℝ",
                    "phi": "ℝ → ℝ",
                    "epsilon": "ℝ",
                    "bounded": "ℝ → ℝ → ℝ",
                    "dPrime": "MetricSpace ℝ",
                    "j": "{z : ℝ // z > 0} → {z : ℝ // z > 0} → ℝ",
                    "aPrime": "Set ℝ",
                }
                bindings = {
                    name: {"symbol": "\\" + name if name in {"phi", "epsilon"} else name, "target": "D/" + name}
                    for name in types
                }
                bindings["bounded"]["symbol"] = r"\hat d"
                bindings["dPrime"]["symbol"] = "d'"
                bindings["aPrime"]["symbol"] = "A'"
                text = (
                    "<!-- chapter-correspondence "
                    + json.dumps({"scope": "metric", "bindings": bindings})
                    + " -->$"
                    + source
                )
                text += "$<!-- chapter-correspondence-end: metric -->"
                records = {"D": {"binders": [{"name": n, "type": ty, "instance": False} for n, ty in types.items()]}}
                occupied = [*types, "book_point_a", "book_point_b"]
                records["D"]["binders"].extend({"name": name, "type": "ℝ", "instance": False} for name in occupied[-2:])
                row = chapter.report(text, chapter.scopes(text), records, trusted=False)["formulas"][0]
                tree, variables = row["syntax"], row["variables"]
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables, records)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, records, trace=mappings)
                result = native.semantic_translation(tree, variables, occupied, constants=chapter.CONSTANTS)
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                if any(v["symbol"] in {r"\hat d", "d'", "A'"} for v in variables):
                    altered = [
                        dict(v, indexOrigin=1) if v["symbol"] in {r"\hat d", "d'", "A'"} else v for v in variables
                    ]
                    self.assertFalse(
                        native.semantic_translation(tree, altered, list(types), constants=chapter.CONSTANTS)[
                            "supported"
                        ]
                    )

    def test_natural_sums_preserve_bounds_scope_and_weighted_metric_operands(self):
        for source in (
            r"\sum_{n\in\omega}2^{-n}",
            r"\sum_{n\in\omega}1",
            r"\sum_{n<m}2^{-n}+n",
            r"\sum_{n<n}2^{-n}",
            r"\sum_{n\ge m}2^{-n}",
            r"\sum_{n\ge n}2^{-n}+n",
            r"\sum_{n<m}2^{-n}+\sum_{n<m}1",
            r"\sum_{n\in\omega}2^{-n}d_n(x_n,y_n)",
        ):
            with self.subTest(source=source):
                types = {
                    "X": "ℕ → Type",
                    "x": "(n : ℕ) → X n",
                    "y": "(n : ℕ) → X n",
                    "d": "(n : ℕ) → MetricSpace (X n)",
                    "n": "ℕ",
                    "m": "ℕ",
                }
                bindings = {name: {"symbol": name, "target": "D/" + name} for name in types}
                text = (
                    "<!-- chapter-correspondence "
                    + json.dumps({"scope": "sum", "bindings": bindings})
                    + " -->$"
                    + source
                )
                text += "$<!-- chapter-correspondence-end: sum -->"
                records = {"D": {"binders": [{"name": n, "type": ty, "instance": False} for n, ty in types.items()]}}
                row = chapter.report(text, chapter.scopes(text), records, trusted=False)["formulas"][0]
                tree, variables = row["syntax"], row["variables"]
                self.assertTrue(all(v["status"] == "resolved" for v in variables), variables)
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables, records)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, records, trace=mappings)
                result = native.semantic_translation(tree, variables, list(types))
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [] if context is None else [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                altered = [dict(v, localBinder=False) if v.get("localBinder") else v for v in variables]
                self.assertFalse(native.semantic_translation(tree, altered, [])["supported"])

    def test_convergence_preserves_filters_index_origin_and_source_typed_numeric_limit(self):
        for source, codomain, origin in (
            (r"x_n\to x", "ℝ", None),
            (r" f(x_n)\longrightarrow f(x). ", "ℝ", None),
            (r"x^n\to x", "ℝ", None),
            (r"x_n\to 0", "ℝ", None),
            (r"x_n\to 0", "ℕ", None),
            (r"x_n\to 0", "ENNReal", None),
            (r"x_n\to 12", "ℝ", None),
            (r"x_n\to {0}", "ℝ", None),
            (r"x_n\to x", "ℝ", 2),
            (r"x_n\to\seqPower{X}{I}", "Type", None),
        ):
            with self.subTest(source=source, codomain=codomain, origin=origin):
                bindings = {
                    "family": {
                        "symbol": "x",
                        "occurrence": "superscript-base" if "^" in source else "subscript-base",
                        "target": "D/u",
                    },
                    "point": {"symbol": "x", "occurrence": "unsubscripted", "target": "D/a"},
                    "function": {"symbol": "f", "target": "D/f"},
                    "index": {"symbol": "n", "target": "D/n"},
                    "carrier": {"symbol": "X", "target": "D/book_power_index"},
                    "indices": {"symbol": "I", "target": "D/I"},
                }
                if origin is not None:
                    bindings["family"]["indexOrigin"] = origin
                text = (
                    "<!-- chapter-correspondence "
                    + json.dumps({"scope": "limit", "bindings": bindings})
                    + " -->$"
                    + source
                )
                text += "$<!-- chapter-correspondence-end: limit -->"
                records = {
                    "D": {
                        "binders": [
                            {"name": n, "type": ty, "instance": False}
                            for n, ty in [
                                ("u", "ℕ → " + codomain),
                                ("a", codomain),
                                ("f", codomain + " → " + codomain),
                                ("n", "Int"),
                                ("book_power_index", "Type"),
                                ("I", "Type"),
                            ]
                        ]
                    }
                }
                row = chapter.report(text, chapter.scopes(text), records, trusted=False)["formulas"][0]
                tree, variables = row["syntax"], row["variables"]
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables, records)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, records, trace=mappings)
                result = native.semantic_translation(
                    tree, variables, ["u", "a", "f", "n", "book_power_index", "I"], constants=chapter.CONSTANTS
                )
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                altered = [dict(v, localBinder=False) if v["symbol"] == "n" else v for v in variables]
                self.assertFalse(native.semantic_translation(tree, altered, [])["supported"])
                self.assertFalse(native.semantic_translation(tree, variables, [], root=False)["supported"])

    def test_natural_type_and_set_families_preserve_lexical_binders_and_evidence(self):
        for source, family_types in (
            (r"\prod_n X_n", {"X": "ℕ → Type"}),
            (r" \prod_{n\in\omega} X_n ", {"X": "ℕ → Type"}),
            (r"\prod_n U_n", {"U": "ℕ → Set ℝ"}),
            (r"x\in\prod_n X_n", {"X": "ℕ → Type", "x": "(n : ℕ) → X n"}),
            (r"\ExternalDisjointUnion_{n\in\omega}X_n", {"X": "ℕ → Type"}),
            (r"\bigcap_n G_n", {"G": "ℕ → Set ℝ"}),
            (r"x\in\bigcap_n G_n", {"G": "ℕ → Set ℝ", "x": "Real"}),
            (r"\bigcup_{n\in\omega}G_n", {"G": "ℕ → Set ℝ"}),
            (r"\bigcap_{n\ge1}G_n", {"G": "ℕ → Set ℝ"}),
            (r"\bigcap_{n\ge01}G_n", {"G": "ℕ → Set ℝ"}),
            (r"\bigcup_{n\ge0}(G_n\cap H_n)", {"G": "ℕ → Set ℝ", "H": "ℕ → Set ℝ"}),
            (
                r"f:A\to\prod_n U_n, f(x)=\Tuple{x,x,\ldots}",
                {"A": "Set ℝ", "U": "ℕ → Set ℝ", "f": "↑A → (n : ℕ) → ↑(U n)", "x": "Int"},
            ),
        ):
            with self.subTest(source=source):
                types = {**family_types, "n": "Int"}
                metadata = {"scope": "family", "bindings": {n: {"symbol": n, "target": "D/" + n} for n in types}}
                text = "<!-- chapter-correspondence " + json.dumps(metadata) + " -->$" + source
                text += "$<!-- chapter-correspondence-end: family -->"
                records = {"D": {"binders": [{"name": n, "type": ty, "instance": False} for n, ty in types.items()]}}
                row = chapter.report(text, chapter.scopes(text), records, trusted=False)["formulas"][0]
                tree, variables = row["syntax"], row["variables"]
                self.assertTrue(all(v["status"] == "resolved" for v in variables), variables)
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables, records)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, records, trace=mappings)
                result = native.semantic_translation(tree, variables, list(types), constants=chapter.CONSTANTS)
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                altered = [dict(v, localBinder=False) if v["symbol"] == "n" else v for v in variables]
                self.assertFalse(native.semantic_translation(tree, altered, list(types))["supported"])

    def test_typed_map_preserves_subspace_signature_and_source_owned_binder(self):
        for source in (
            r"f:A\to\R, f(x)=x",
            r" f : A \to \R,\qquad f(x)=x+1 ",
        ):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    name = variable["symbol"]
                    variable.update(
                        id="s/" + name,
                        declaration="D",
                        leanName=name,
                        leanType={"f": "↑A → ℝ", "A": "Set ℝ", "x": "Subtype «A»"}[name],
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                    if name == "x":
                        variable.update(localBinder=True, binderContext="D")
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [], constants=chapter.CONSTANTS)
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                self.assertEqual(sum(m["rule"] == "type:subspace-carrier" for m in mappings), 1)
                self.assertEqual(mappings[-1]["rule"], "binder:typed-map")
                for changes in ({"localBinder": False}, {"binderContext": None}):
                    altered = [dict(v, **changes) if v["symbol"] == "x" else v for v in variables]
                    self.assertFalse(
                        native.semantic_translation(tree, altered, [], constants=chapter.CONSTANTS)["supported"]
                    )

    def test_mixed_membership_chain_has_its_own_equality_rule(self):
        for source, supported in ((r"x=y", True), (r"x=y\in A", True), (r"x=y\IncludedIn A", False)):
            tree = syntax([source])[0]["tree"]
            variables, _ = chapter.leaves(tree)
            for variable in variables:
                name = variable["symbol"]
                variable.update(
                    id="s/" + name,
                    declaration="D",
                    leanName=name,
                    leanType="Set Real" if name == "A" else "Real",
                    status="resolved",
                    formulaOffset=variable["start"],
                )
            result = native.semantic_translation(tree, variables, [])
            self.assertEqual(result["supported"], supported, source)
            if source == r"x=y\in A":
                self.assertEqual(
                    [mapping["rule"] for mapping in result["rendering"]["mappings"]],
                    ["relation:membership-chain-equality", "set:in"],
                )

    def test_coordinate_spaces_preserve_index_dimension_and_binary_embedding_convention(self):
        for source in (
            r"X^n",
            r"\R^0",
            r"\QQ^{12}",
            r"\seqPower{X}{I}",
            r"\seqPower{\R}{\omega}",
            r"\seqPower{\{0,1\}}{\omega}",
            r"\Homeomorphic{\seqPower{\R}{\omega}}{\R}",
        ):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    name = variable["symbol"]
                    variable.update(
                        id="s/" + name,
                        declaration="D",
                        leanName=name,
                        leanType="Nat" if name == "n" else "Type",
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(
                    tree, variables, [], constants=chapter.CONSTANTS, conventions=chapter.CONVENTIONS
                )
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context] if context is not None else [])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
        for source in (r"\seqPower{\{0,2\}}{\omega}", r"\seqPower{\R}{0}"):
            self.assertFalse(
                native.semantic_translation(syntax([source])[0]["tree"], [], [], constants=chapter.CONSTANTS)[
                    "supported"
                ]
            )

    def test_coordinate_binders_avoid_original_context_names(self):
        source = r"\seqPower{X}{I}"
        tree = syntax([source])[0]["tree"]
        variables, _ = chapter.leaves(tree)
        for variable in variables:
            name = variable["symbol"]
            variable.update(
                id="s/" + name,
                declaration="D",
                leanName="book_power_index" if name == "X" else "I",
                leanType="Type",
                status="resolved",
                formulaOffset=variable["start"],
            )
        records = {"D": {"binders": [{"name": "book_power_index"}, {"name": "I"}]}}
        with legacy_oracle(chapter):
            plain, _ = chapter.translate(tree, variables, records)
            mappings = []
            instrumented, _ = chapter.translate(tree, variables, records, trace=mappings)
        result = native.semantic_translation(tree, variables, ["book_power_index", "I"])
        self.assertTrue(result["supported"], result)
        self.assertEqual(result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings})
        self.assertEqual(mappings[-1]["expectedBinderName"], "book_power_index_")

    def test_function_declarations_and_homeomorphic_types_keep_domains_and_topologies(self):
        for source in (r"f:X\to Y", r" f : \R \to \R ", r"\Homeomorphic{X}{Y}", r"\Homeomorphic{\ell^2}{\R}"):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    name = variable["symbol"]
                    variable.update(
                        id="s/" + name,
                        declaration="D",
                        leanName=name,
                        leanType="X → Y" if name == "f" else "Type u",
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [], constants=chapter.CONSTANTS)
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context] if context is not None else [])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                if "Homeomorphic" in source:
                    homeomorphism = next(m for m in mappings if m["rule"] == "type:homeomorphism")
                    self.assertEqual(
                        [a["argumentPosition"] for a in homeomorphism["expectedImplicitArguments"]], [2, 3]
                    )
                    self.assertEqual(mappings[-1]["rule"], "relation:homeomorphic")
                else:
                    self.assertEqual(
                        [m["rule"] for m in mappings], ["type:function-arrow", "declaration:function-type"]
                    )
                    self.assertEqual(
                        [a["target"] for a in mappings[0]["expectedOperands"]], ["forall.body", "forall.domain"]
                    )
        tree = syntax([r"f:X\to Y"])[0]["tree"]
        variables, _ = chapter.leaves(tree)
        for variable in variables:
            name = variable["symbol"]
            variable.update(
                id="s/" + name,
                declaration="D",
                leanName=name,
                leanType={"f": "X → Y", "X": "Set Real", "Y": "Type"}[name],
                status="resolved",
                formulaOffset=variable["start"],
            )
        self.assertFalse(native.semantic_translation(tree, variables, [])["supported"])

    def test_extended_comparison_literals_take_their_domain_from_source_operands(self):
        for source in (r"1\le p<\infty", r"p\ge 2", r"p\ge 12", r"p+1<\infty", r"p<1<q"):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    name = variable["symbol"]
                    variable.update(
                        id="s/" + name,
                        declaration="D",
                        leanName=name,
                        leanType="ENNReal",
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                for variable in variables:
                    variable["leanType"] = "Nat"
                if "infty" in source:
                    self.assertFalse(native.semantic_translation(tree, variables, [])["supported"])

    def test_real_sequence_spaces_keep_extended_exponents_and_coordinate_evidence(self):
        for source in (
            r"\ell^2",
            r"\ell^{12}",
            r"\ell^{ 12 }",
            r"\ell^\infty",
            r"\ell^{\infty}",
            r"\ell^p",
            r"\ell^{ p }",
        ):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    variable.update(
                        id="s/p",
                        declaration="D",
                        leanName="p",
                        leanType="ENNReal",
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context] if context is not None else [])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                self.assertEqual(mappings[-1]["rule"], "space:real-lp")
                self.assertEqual(mappings[-1]["expectedOperands"][0]["sourceOperand"], None)
                self.assertEqual(
                    [a["role"] for a in mappings[-1]["expectedImplicitArguments"]],
                    ["sequence-index", "coordinate-normed-group"],
                )
        tree = syntax([r"\ell^p"])[0]["tree"]
        variables, _ = chapter.leaves(tree)
        for variable in variables:
            variable.update(
                id="s/p",
                declaration="D",
                leanName="p",
                leanType="Nat",
                status="resolved",
                formulaOffset=variable["start"],
            )
        self.assertFalse(native.semantic_translation(tree, variables, [])["supported"])
        self.assertFalse(native.semantic_translation(syntax([r"\ell^{-1}"])[0]["tree"], [], [])["supported"])

    def test_explicit_levels_unbounded_intervals_and_integer_powers_preserve_evidence(self):
        for source in (
            r"\NonnegativeDimensionLevel{0}",
            r"\NonnegativeDimensionLevel{ 12 }",
            r"\OpenInterval{x}{\infty}",
            r"\LeftClosedInterval{x+y}{\infty}",
            r"2^{-n}",
            r"12^{-(n+10)}",
            r"10^{n-m}",
            r"x+12^{n-1}",
        ):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    name = variable["symbol"]
                    variable.update(
                        id="s/" + name,
                        declaration="D",
                        leanName=name,
                        leanType={"n": "Nat", "m": "Int"}.get(name, "Real"),
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [], constants=chapter.CONSTANTS)
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context] if context is not None else [])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                self.assertTrue(
                    all(
                        "md_operator_" not in a["candidate"]
                        for mapping in mappings
                        for a in mapping["expectedOperands"]
                    )
                )

    def test_integer_power_and_level_grammar_rejects_missing_source_types_and_noninteger_operations(self):
        for source in (
            r"2^{n/2}",
            r"2^{\Abs{n}}",
            r"x^n",
            r"\NonnegativeDimensionLevel{-1}",
            r"\NonnegativeDimensionLevel{n}",
            r"\NonnegativeDimensionLevel{1 2}",
        ):
            tree, variables = self.expression(source)
            self.assertFalse(native.semantic_translation(tree, variables, [])["supported"], source)
        tree = syntax([r"2^{-n}"])[0]["tree"]
        variables, _ = chapter.leaves(tree)
        for variable in variables:
            variable.update(
                id="s/n",
                declaration="D",
                leanName="n",
                leanType="Real",
                status="resolved",
                formulaOffset=variable["start"],
            )
        self.assertFalse(native.semantic_translation(tree, variables, [])["supported"])

    def test_empty_set_preserves_ambient_witness_and_emits_no_extra_operand_trace(self):
        for source in (
            r"A=\emptyset",
            r"\emptyset\ne A",
            r"A\cap\emptyset",
            r"\SetDifference{ \emptyset }{ A }",
            r"X_n\cap\emptyset",
        ):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    name = variable["symbol"]
                    variable.update(
                        id="s/" + name,
                        declaration="D",
                        leanName=name,
                        leanType={"X": "Nat → Type u", "n": "Nat"}.get(name, "Set X"),
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                empty = next(m for m in mappings if m["rule"] == "set:empty")
                self.assertEqual(empty["operandSpans"], [])
                self.assertEqual(empty["expectedOperands"], [])
                self.assertTrue(all("md_operator_" not in a["candidate"] for a in empty["expectedImplicitArguments"]))
        for source in (r"\emptyset", r"\emptyset=\emptyset"):
            self.assertFalse(native.semantic_translation(syntax([source])[0]["tree"], [], [])["supported"])

    def test_defining_equality_retains_full_source_span_and_independent_value_type(self):
        for source in ("x:=y+1", " x := y.", r"x:=\Abs{y}"):
            with self.subTest(source=source):
                tree, variables = self.expression(source)
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                definition = mappings[-1]
                self.assertEqual(definition["rule"], "definition:=")
                self.assertEqual((definition["start"], definition["end"]), (0, len(source)))
                self.assertEqual(definition["expectedImplicitArguments"][0]["role"], "defined-value-type")
        for source in ("x:=", ":=x", "x:=y:=z", "x: =y"):
            tree, variables = self.expression(source)
            self.assertFalse(native.semantic_translation(tree, variables, [])["supported"], source)

    def test_mapsto_lambda_keeps_source_domain_context_and_lexical_identity(self):
        for source in (r"x\mapsto x", r" x \mapsto x+1 ", r"x\mapsto f(x)", r"x\mapsto x+y"):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    name = variable["symbol"]
                    variable.update(
                        id="s/" + name,
                        declaration=None if name == "x" else "D",
                        leanName="source_point" if name == "x" else name,
                        leanType="Real → Real" if name == "f" else "Real",
                        status="resolved",
                        formulaOffset=variable["start"],
                        localBinder=name == "x",
                    )
                    if name == "x":
                        variable["binderContext"] = "D"
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [], constants=chapter.CONSTANTS)
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                binder = mappings[-1]
                self.assertEqual(binder["rule"], "binder:mapsto")
                self.assertEqual(binder["expectedBinderName"], "source_point")
                self.assertEqual(
                    binder["expectedOperands"][1],
                    {"sourceOperand": None, "target": "lambda.domain", "candidate": "Real"},
                )
                self.assertFalse(
                    native.semantic_translation(tree, variables, [], constants=chapter.CONSTANTS, root=False)[
                        "supported"
                    ]
                )
                for variable in variables:
                    if variable["symbol"] == "x":
                        variable.pop("binderContext", None)
                self.assertFalse(
                    native.semantic_translation(tree, variables, [], constants=chapter.CONSTANTS)["supported"]
                )

    def test_sequence_lambda_retains_lexical_identity_domain_spans_and_index_origin(self):
        for source, origin in (
            (r"\Sequence{x_n}{n\in\omega}", 0),
            (r"\Sequence{n+1}{n\in\omega}", 0),
            (r"\Sequence{x_n}{n\ge 2}", 2),
        ):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    name = variable["symbol"]
                    variable.update(
                        id="s/" + name,
                        declaration=None if name == "n" else "D",
                        leanName="book_n" if name == "n" else name,
                        leanType="Nat" if name == "n" else "Nat → Real",
                        status="resolved",
                        formulaOffset=variable["start"],
                        localBinder=name == "n",
                    )
                    if name == "n" and origin:
                        variable["indexOffset"] = origin
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [], constants=chapter.CONSTANTS)
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context] if context is not None else [])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                binder = mappings[-1]
                self.assertEqual(binder["expectedBinderName"], "book_n")
                self.assertEqual(
                    binder["expectedOperands"][1], {"sourceOperand": 1, "target": "lambda.domain", "candidate": "Nat"}
                )
                self.assertEqual(binder.get("lowering", {}).get("sourceOrigin", 0), origin)
                for variable in variables:
                    if variable["symbol"] == "n":
                        variable["localBinder"] = False
                self.assertFalse(
                    native.semantic_translation(tree, variables, [], constants=chapter.CONSTANTS)["supported"]
                )

    def test_registered_constants_and_real_rational_embedding_preserve_both_forms(self):
        for source in (
            r"\R",
            r"\QQ",
            r"\omega",
            r"\Gdelta",
            r"\TwoPointSpace",
            r"\SetDifference{\R}{\QQ}",
            r"\SetDifference{ \R}{\QQ}",
            r"\SetDifference{\QQ}{\R}",
            r"\QQ\cap\R",
            r"A\IncludedIn\R",
            r"x\in\R",
        ):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    name = variable["symbol"]
                    variable.update(
                        id="s/" + name,
                        declaration="D",
                        leanName=name,
                        leanType="Set ℝ" if name == "A" else "ℝ",
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [], constants=chapter.CONSTANTS)
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context] if context is not None else [])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )

    def test_constant_registry_is_explicit_and_part_of_the_worker_cache_identity(self):
        tree = syntax([r"\R"])[0]["tree"]
        self.assertFalse(native.semantic_translation(tree, [], [])["supported"])
        self.assertEqual(native.semantic_translation(tree, [], [], constants={"R": "ℝ"})["rendering"]["ordinary"], "ℝ")
        self.assertEqual(
            native.semantic_translation(tree, [], [], constants={"R": "Nat"})["rendering"]["ordinary"], "Nat"
        )
        self.assertFalse(native.semantic_translation(tree, [], [])["supported"])
        complement = syntax([r"\SetDifference{\R}{\QQ}"])[0]["tree"]
        self.assertFalse(
            native.semantic_translation(complement, [], [], constants={"R": "Nat", "QQ": "Int"})["supported"]
        )

    def test_set_operations_preserve_coercions_precedence_and_ordered_expectations(self):
        for source in (
            r"A\cap B",
            r"A\cup B\cap C",
            r"(A\cap B)\cup C",
            r"A\IncludedIn X",
            r"x\in A",
            r"x\in X",
            r"\SetDifference{A}{B}",
            r"\SetDifference{X}{A}",
            r"A\times B",
            r"A\times X",
            "A=X",
            r"A\ne X",
            "A=B",
            r"X_n\cap A",
            r"x\in X_n",
        ):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    name = variable["symbol"]
                    ty = (
                        "Nat → Type u"
                        if name == "X" and "X_n" in source
                        else {"X": "Type u", "x": "X", "n": "Nat"}.get(name, "Set X")
                    )
                    variable.update(
                        id="s/" + name,
                        declaration="D",
                        leanName=name,
                        leanType=ty,
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                if "in " in source:
                    self.assertEqual([a["sourceOperand"] for a in mappings[-1]["expectedOperands"]], [1, 0])
                if "X_n" in source:
                    self.assertTrue(next(m for m in mappings if m["rule"] == "index:subscript")["allowMultipleCalls"])

    def test_set_grammar_rejects_unsupported_chains_and_ungrouped_products(self):
        for source in (r"x\in A\IncludedIn B", r"A\times B\times C", r"X\times Y", r"A\cap"):
            tree = syntax([source])[0]["tree"]
            variables, _ = chapter.leaves(tree)
            for variable in variables:
                name = variable["symbol"]
                variable.update(
                    id="s/" + name,
                    declaration="D",
                    leanName=name,
                    leanType="Type" if name in {"X", "Y"} else "Set X",
                    status="resolved",
                    formulaOffset=variable["start"],
                )
            self.assertFalse(native.semantic_translation(tree, variables, [])["supported"], source)

    def test_subtype_range_matches_the_entire_source_domain_and_keeps_operand_order(self):
        for source, ty, rule in (
            ("f(A)", "↑A → Real", "application:subtype-range"),
            ("f(A)", "↑A -> Real", "application:subtype-range"),
            ("f(B)", "↑A → Real", "application:subtype-argument"),
        ):
            with self.subTest(source=source, ty=ty):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    variable.update(
                        id="s/" + variable["symbol"],
                        declaration="D",
                        leanName=variable["symbol"],
                        leanType=ty if variable["symbol"] == "f" else "Set X",
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                self.assertEqual(mappings[0]["rule"], rule)
                if rule == "application:subtype-range":
                    self.assertEqual(mappings[0]["expectedConstant"], "Set.range")
                    self.assertEqual(mappings[0]["lowering"]["domainSet"], "A")
                    self.assertEqual(mappings[0]["expectedOperands"], [{"sourceOperand": 0, "candidate": "«f»"}])

    def test_decorated_subtype_range_has_no_discarded_callee_marker(self):
        source = "f^*(A)"
        tree = syntax([source])[0]["tree"]
        variables, _ = chapter.leaves(tree)
        for variable in variables:
            name = "f" if variable["start"] == 0 else "A"
            variable.update(
                id="s/" + name,
                declaration="D",
                leanName=name,
                leanType="↑A → Real" if name == "f" else "Set X",
                status="resolved",
                formulaOffset=variable["start"],
            )
        result = native.semantic_translation(tree, variables, [])
        self.assertTrue(result["supported"], result)
        rendering = result["rendering"]
        self.assertEqual([m["rule"] for m in rendering["mappings"]], ["name:star", "application:subtype-range"])
        for mapping in rendering["mappings"]:
            self.assertIn("let " + mapping["marker"] + " :=", rendering["instrumented"])
        self.assertNotIn("md_operator_", rendering["mappings"][-1]["expectedOperands"][0]["candidate"])

    def test_subtype_point_application_keeps_source_argument_and_membership_adapter(self):
        source = "f(x)"
        tree = syntax([source])[0]["tree"]
        variables, _ = chapter.leaves(tree)
        for variable in variables:
            variable.update(
                id="s/" + variable["symbol"],
                declaration="D",
                leanName=variable["symbol"],
                leanType="↑A → Real" if variable["symbol"] == "f" else "X",
                status="resolved",
                formulaOffset=variable["start"],
            )
        with legacy_oracle(chapter):
            plain, context = chapter.translate(tree, variables)
            mappings = []
            instrumented, _ = chapter.translate(tree, variables, trace=mappings)
        result = native.semantic_translation(tree, variables, [])
        self.assertTrue(result["supported"], result)
        self.assertEqual(result["contexts"], [context])
        self.assertEqual(result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings})
        mapping = mappings[0]
        self.assertEqual(mapping["lowering"]["kind"], "subtype-argument-from-local-membership")
        self.assertEqual(mapping["expectedOperands"][0]["candidate"], "(bookSubtypeArgument% («f»), («x»))")
        variables[1]["leanType"] = "Set X"
        alternate = native.semantic_translation(tree, variables, [])
        self.assertTrue(alternate["supported"])
        self.assertEqual(alternate["rendering"]["mappings"][0]["rule"], "application:subtype-argument")

    def test_metric_applications_keep_domain_instance_and_independent_point_adapters(self):
        for source, types in (
            ("d(x,y)", {"d": "MetricSpace X"}),
            ("d(f(x),y)", {"d": "MetricSpace X", "f": "X → X"}),
            ("d_n(x_n,y_n)", {"d": "Nat → MetricSpace X", "x": "Nat → X", "y": "Nat → X", "n": "Nat"}),
            (r"\rho(x,y)", {r"\rho": "MetricSpace X"}),
        ):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    variable.update(
                        id="s/" + variable["symbol"],
                        declaration="D",
                        leanName=variable["symbol"].removeprefix(chr(92)),
                        leanType=types.get(variable["symbol"], "X"),
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                metric = mappings[-1]
                self.assertEqual(metric["rule"], "application:metric")
                self.assertEqual(
                    [a["role"] for a in metric["expectedImplicitArguments"]], ["metric-domain", "metric-instance"]
                )
                self.assertTrue(
                    all(
                        "bookMetricPoint%" in a["candidate"] and "md_operator_" not in a["candidate"]
                        for a in metric["expectedOperands"]
                    )
                )

    def test_metric_set_argument_keeps_the_distance_to_set_obligation(self):
        for source, ty in (
            ("d(x,A)", "Set X"),
            ("d(x,A_n)", "Nat → Set X"),
            ("d(x,A_n)", "Nat -> Set X"),
            (r"d(x,\Closure{A})", "Set X"),
        ):
            tree = syntax([source])[0]["tree"]
            variables, _ = chapter.leaves(tree)
            for variable in variables:
                variable.update(
                    id="s/" + variable["symbol"],
                    declaration="D",
                    leanName=variable["symbol"],
                    leanType={"d": "MetricSpace X", "A": ty, "n": "Nat"}.get(variable["symbol"], "X"),
                    status="resolved",
                    formulaOffset=variable["start"],
                )
            with legacy_oracle(chapter):
                plain, context = chapter.translate(tree, variables)
                mappings = []
                instrumented, _ = chapter.translate(tree, variables, trace=mappings)
            result = native.semantic_translation(tree, variables, [])
            self.assertTrue(result["supported"], result)
            self.assertEqual(result["contexts"], [context])
            self.assertEqual(
                result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
            )
            mapping = mappings[-1]
            self.assertEqual(mapping["rule"], "application:distance-to-set")
            self.assertNotIn("bookMetricPoint%", mapping["expectedOperands"][1]["candidate"])
            self.assertIn("toPseudoMetricSpace", mapping["expectedImplicitArguments"][1]["candidate"])

    def test_function_applications_preserve_callee_arguments_and_nested_traces(self):
        for source, types in (
            ("f(x)", {"f": "Real → Real"}),
            ("f(x,y)", {"f": "Real → Real → Real"}),
            ("f(x)+f(y)", {"f": "Real → Real"}),
            ("f(g(x))", {"f": "Real → Real", "g": "Real → Real"}),
            ("f(g(x,y),z)", {"f": "Real → Real → Real", "g": "Real → Real → Real"}),
            ("f_n(x)", {"f": "Nat → Real → Real", "n": "Nat"}),
            (r"\phi(\epsilon)", {r"\phi": "Real → Real"}),
        ):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variables, _ = chapter.leaves(tree)
                for variable in variables:
                    variable.update(
                        id="s/" + variable["symbol"],
                        declaration="D",
                        leanName=variable["symbol"].removeprefix(chr(92)),
                        leanType=types.get(variable["symbol"], "Real"),
                        status="resolved",
                        formulaOffset=variable["start"],
                    )
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                for call in (m for m in mappings if m["rule"] == "application:function"):
                    self.assertEqual(
                        call["expectedVariable"],
                        "phi" if source.startswith(chr(92)) else ("g" if source[call["operatorStart"]] == "g" else "f"),
                    )
                    self.assertTrue(all("md_operator_" not in a["candidate"] for a in call["expectedOperands"]))

    def test_application_rejects_ambiguous_syntax_and_preserves_special_adapters(self):
        for source, ty in (
            ("f()", "Real → Real"),
            ("f(x,)", "Real → Real"),
            ("f (x)", "Real → Real"),
            ("f(x)", "Real"),
            ("f_n(x)", "Nat → MetricSpace X"),
        ):
            tree = syntax([source])[0]["tree"]
            variables, _ = chapter.leaves(tree)
            for variable in variables:
                variable.update(
                    id="s/" + variable["symbol"],
                    declaration="D",
                    leanName=variable["symbol"],
                    leanType=ty if variable["symbol"] == "f" else "Real",
                    status="resolved",
                    formulaOffset=variable["start"],
                )
            self.assertFalse(native.semantic_translation(tree, variables, [])["supported"], source)

    def expression(self, source=r"\frac{\Abs{x}}{1+y}"):
        tree = syntax([source])[0]["tree"]
        variables = [
            {
                "id": "example/" + name,
                "symbol": name,
                "declaration": "D",
                "leanName": name,
                "leanType": "Real",
                "status": "resolved",
                "formulaOffset": offset,
                "start": offset,
                "end": offset + 1,
            }
            for offset, name in enumerate(source)
            if name in {"x", "y", "z"}
        ]
        return tree, variables

    def test_one_ast_produces_both_forms_and_independent_operands(self):
        tree, variables = self.expression()
        records = {"D": {"binders": [{"name": "md_operator_0"}]}}
        # The frozen test-only interpreter is an independent migration oracle.
        with legacy_oracle(chapter):
            plain, context = chapter.translate(tree, variables, records)
            mappings = []
            traced, traced_context = chapter.translate(tree, variables, records, trace=mappings)
        result = native.semantic_translation(tree, variables, ["md_operator_0"])
        self.assertTrue(result["supported"])
        self.assertEqual(result["contexts"], [context])
        self.assertEqual(context, traced_context)
        self.assertEqual(result["rendering"], {"ordinary": plain, "instrumented": traced, "mappings": mappings})
        self.assertEqual(mappings[0]["marker"], "md_operator_0_")
        self.assertIn("md_operator_0_", mappings[-1]["candidate"])
        self.assertTrue(all("md_operator_" not in operand["candidate"] for operand in mappings[-1]["expectedOperands"]))
        self.assertEqual(mappings[-1]["expectedOperands"][0]["candidate"], "|«x»|")

    def test_precedence_parentheses_and_source_spans_match(self):
        for source in (
            "x+y*z",
            "x-y-z",
            "(x+y)/y",
            "x - (y*x)",
            "x  +  y",
            "( x )",
            r"\frac{x+y}{1+x}",
            r"\frac{  x  }{y}",
            r"\Abs{(x-y)/(x+y)}",
            r"\Ball{x}{y}",
            r"\ClosedInterval{x}{y}",
            r"\Closure{x}",
            "-x",
            "-(x+y)/z",
            "x=-y",
            r"0<x\le y+z",
            r"x\ne y",
            "(x+y)>z",
            r"\bigl(x+y\bigr)>z",
            r"x+\bigl(y*z\bigr)",
        ):
            with self.subTest(source=source):
                tree, variables = self.expression(source)
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    traced, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["rendering"], {"ordinary": plain, "instrumented": traced, "mappings": mappings})
                self.assertEqual(result["contexts"], [context])

    def test_comparisons_keep_repeated_operand_traces_and_source_order(self):
        source = r"x+1<\Abs{y}\le z"
        tree, variables = self.expression(source)
        result = native.semantic_translation(tree, variables, [])
        self.assertTrue(result["supported"], result)
        traces = result["rendering"]["mappings"]
        self.assertEqual([t["rule"] for t in traces], ["infix:+", "macro:Abs", "infix:<", "macro:Abs", "infix:≤"])
        comparisons = [t for t in traces if t["rule"] in {"infix:<", "infix:≤"}]
        self.assertEqual([source[t["operatorStart"] : t["operatorEnd"]] for t in comparisons], ["<", r"\le"])
        self.assertEqual(comparisons[0]["expectedOperands"][1]["candidate"], "|«y»|")
        self.assertEqual(comparisons[1]["expectedOperands"][0]["candidate"], "|«y»|")
        self.assertTrue(
            all("md_operator_" not in a["candidate"] for t in comparisons for a in t["expectedImplicitArguments"])
        )
        # Rendering preserves the source type; Lean checks whether its operations exist.
        variables[0]["leanType"] = "MetricSpace X"
        self.assertTrue(native.semantic_translation(tree, variables, [])["supported"])

    def test_normal_numeric_gate_remains_in_force(self):
        tree = syntax(["1+2"])[0]["tree"]
        self.assertTrue(native.semantic_translation(tree, [], [])["supported"])
        with self.assertRaisesRegex(chapter.Unsupported, "no reviewed ambient number type"):
            chapter.translate(tree, [])

    def test_existing_translate_uses_the_native_renderer(self):
        tree, variables = self.expression()
        with patch.object(chapter, "semantic_translation", wraps=native.semantic_translation) as invoke:
            plain, _ = chapter.translate(tree, variables)
            trace = []
            instrumented, _ = chapter.translate(tree, variables, trace=trace)
        self.assertEqual(invoke.call_count, 2)
        self.assertNotEqual(plain, instrumented)
        self.assertEqual(len(trace), 3)

    def test_unknown_annotations_and_unresolved_bindings_do_not_get_erased(self):
        tree, variables = self.expression()
        for altered_tree, altered_vars in (
            (dict(tree, numericContext={"type": "Real"}), variables),
            (dict(tree, start=-1), variables),
            (tree, [dict(variables[0], status="unresolved"), *variables[1:]]),
            (tree, [dict(variables[0], projection="unknown"), *variables[1:]]),
            (tree, [*variables, variables[0]]),
        ):
            result = native.semantic_translation(altered_tree, altered_vars, [])
            self.assertFalse(result["supported"])
            self.assertNotIn("rendering", result)

    def test_adapted_references_preserve_context_and_source_identity(self):
        tree, variables = self.expression("x+y")
        for changes in ({"projection": "Subtype.val"}, {"indexOffset": 2, "leanType": "Nat"}, {"indexLowerBound": 1}):
            with self.subTest(changes=changes):
                adapted = [dict(variables[0], **changes), variables[1]]
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, adapted)
                    mappings = []
                    traced, _ = chapter.translate(tree, adapted, trace=mappings)
                result = native.semantic_translation(tree, adapted, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(result["rendering"], {"ordinary": plain, "instrumented": traced, "mappings": mappings})
        for changes in (
            {"indexOffset": 2},
            {"indexOrigin": 1},
            {"constantDeclaration": "D", "projection": "Subtype.val"},
        ):
            self.assertFalse(
                native.semantic_translation(tree, [dict(variables[0], **changes), variables[1]], [])["supported"]
            )

    def test_index_application_keeps_callee_identity_and_independent_argument(self):
        for source in ("x_n", "x_n+y", "y+x_{n+1}", "x_n_m", r"\rho_n"):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                names = [(offset, name) for offset, name in enumerate(source) if name in {"x", "y", "n", "m"}]
                if source.startswith(chr(92)):
                    names = [(0, "rho"), (source.index("n"), "n")]
                variables = [
                    {
                        "id": "s/" + name,
                        "symbol": chr(92) + name if name == "rho" else name,
                        "declaration": "D",
                        "leanName": name,
                        "leanType": ("Nat → Nat → Real" if source == "x_n_m" else "Nat → Real")
                        if name in {"x", "rho"}
                        else ("Real" if name == "y" else "Nat"),
                        "status": "resolved",
                        "formulaOffset": offset,
                        "start": offset,
                        "end": offset + (4 if name == "rho" else 1),
                    }
                    for offset, name in names
                ]
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    traced, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(result["rendering"], {"ordinary": plain, "instrumented": traced, "mappings": mappings})
                indices = [t for t in mappings if t["rule"] == "index:subscript"]
                self.assertEqual(indices[0]["expectedVariable"], "rho" if source.startswith(chr(92)) else "x")
                self.assertEqual([o["sourceOperand"] for o in indices[0]["expectedOperands"]], [1])
                if len(indices) == 2:
                    self.assertEqual(indices[1]["expectedCallee"], "((«x») («n»))")

    def test_index_source_binding_cannot_be_reinterpreted_as_named_or_shifted_family(self):
        tree, variables = self.expression("x_y")
        variables[0]["leanType"] = "Nat → Real"
        for changes in ({"namedSubscript": True}, {"indexOrigin": 1}, {"leanType": "Real"}):
            self.assertFalse(
                native.semantic_translation(tree, [dict(variables[0], **changes), variables[1]], [])["supported"]
            )

    def test_index_origins_and_superscript_selectors_preserve_source_operands(self):
        for source, family, index in (
            ("x_2", {"indexOrigin": 1}, {}),
            ("x_n", {"indexOrigin": 1}, {"indexOffset": 1}),
            ("x_n", {"indexOrigin": 2}, {"indexLowerBound": 2}),
            ("x^n", {"occurrenceSelector": "superscript-base"}, {}),
            ("x^n", {"occurrenceSelector": "superscript-base", "indexOrigin": 1}, {"indexOffset": 2}),
        ):
            with self.subTest(source=source, family=family, index=index):
                tree = syntax([source])[0]["tree"]
                variables = [
                    dict(
                        {
                            "id": "s/" + name,
                            "symbol": name,
                            "leanName": name,
                            "declaration": "D",
                            "leanType": "Nat → Real" if name == "x" else "Nat",
                            "status": "resolved",
                            "formulaOffset": offset,
                            "start": offset,
                            "end": offset + 1,
                        },
                        **(family if name == "x" else index),
                    )
                    for offset, name in enumerate(source)
                    if name in {"x", "n"}
                ]
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, variables)
                    mappings = []
                    instrumented, _ = chapter.translate(tree, variables, trace=mappings)
                result = native.semantic_translation(tree, variables, [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                mapping = mappings[-1]
                self.assertEqual(
                    source[mapping["operandSpans"][1]["start"] : mapping["operandSpans"][1]["end"]], source[2:]
                )
                if "indexOrigin" in family:
                    self.assertEqual(mapping["lowering"]["sourceOrigin"], family["indexOrigin"])

    def test_shifted_family_rejects_missing_or_insufficient_source_lower_bound(self):
        tree, variables = self.expression("x_y")
        variables[0].update(leanType="Nat → Real", indexOrigin=2)
        for changes in ({"leanType": "Nat"}, {"leanType": "Nat", "indexOffset": 1}):
            altered = [variables[0], dict(variables[1], **changes)]
            self.assertFalse(native.semantic_translation(tree, altered, [])["supported"])
        superscript, variables = self.expression("x^y")
        variables[0]["leanType"] = "Nat → Real"
        self.assertFalse(native.semantic_translation(superscript, variables, [])["supported"])

    def test_decorated_names_use_the_explicit_whole_symbol_binding(self):
        for source, symbol, named in (
            ("x_1", "x_1", True),
            ("x_{12}", "x_12", True),
            ("x^*", "x^*", False),
            ("x^{*}", "x^*", False),
        ):
            with self.subTest(source=source):
                tree = syntax([source])[0]["tree"]
                variable = {
                    "id": "s/name",
                    "symbol": symbol,
                    "declaration": "D",
                    "leanName": "chosen",
                    "leanType": "Real",
                    "status": "resolved",
                    "formulaOffset": 0,
                    "start": 0,
                    "end": len(source),
                    "namedSubscript": named,
                }
                with legacy_oracle(chapter):
                    plain, context = chapter.translate(tree, [variable])
                    mappings = []
                    instrumented, _ = chapter.translate(tree, [variable], trace=mappings)
                result = native.semantic_translation(tree, [variable], [])
                self.assertTrue(result["supported"], result)
                self.assertEqual(result["contexts"], [context])
                self.assertEqual(
                    result["rendering"], {"ordinary": plain, "instrumented": instrumented, "mappings": mappings}
                )
                self.assertEqual(mappings[0]["expectedVariable"], "chosen")
                self.assertEqual(mappings[0]["expectedOperands"], [])
                self.assertFalse(native.semantic_translation(tree, [dict(variable, symbol="x")], [])["supported"])

    def test_batch_marker_offsets_and_unicode_positions(self):
        source = r"\Closure{α}"
        tree = syntax([source])[0]["tree"]
        offset = source.index("α")
        variables = [
            {
                "id": "scope/alpha",
                "declaration": "D",
                "leanName": "α",
                "leanType": "Set Real",
                "formulaOffset": offset,
                "status": "resolved",
            }
        ]
        jobs = [
            {
                "tree": tree,
                "variables": variables,
                "firstMarker": first,
                "occupied": ["md_operator_5", "md_operator_5_"],
            }
            for first in (0, 5)
        ]
        results = native.request({"action": "translateBatch", "expressions": jobs})["results"]
        self.assertTrue(all(result["supported"] for result in results))
        self.assertEqual(results[1]["rendering"]["mappings"][0]["marker"], "md_operator_5__")
        self.assertEqual(results[0]["rendering"]["mappings"][0]["operandSpans"], [{"start": offset, "end": offset + 1}])

    def test_native_errors_and_unsupported_results_never_select_a_python_interpreter(self):
        tree, variables = self.expression()
        with (
            patch.object(chapter, "semantic_translation", side_effect=RuntimeError("worker failed")),
            self.assertRaisesRegex(RuntimeError, "worker failed"),
        ):
            chapter.translate(tree, variables)
        with (
            patch.object(chapter, "semantic_translation", return_value={"supported": False, "reason": "unknown rule"}),
            self.assertRaisesRegex(chapter.Unsupported, "unknown rule"),
        ):
            chapter.translate(tree, variables)


class NativeVariableResolutionTests(unittest.TestCase):
    def resolve(self, binding, record):
        scope = {
            "scope": "scope",
            "start": 0,
            "end": 100,
            "bindings": {"x": {"id": "scope/x", "symbol": "x", **binding}},
        }
        return native.request(
            {
                "action": "resolveOuter",
                "variables": [{"symbol": "x", "start": 0, "end": 1}],
                "scopes": [scope],
                "row": {"start": 0, "bodyStart": 10},
                "records": {"D": record},
            }
        )["variables"][0]

    def test_explicit_target_and_ambiguous_lean_binder(self):
        binder = {"name": "x", "type": "Nat"}
        good = self.resolve({"target": "D/x"}, {"binders": [binder]})
        self.assertEqual(
            (good["status"], good["leanName"], good["start"], good["formulaOffset"]), ("resolved", "x", 10, 0)
        )
        bad = self.resolve({"target": "D/x"}, {"binders": [binder, binder]})
        self.assertEqual(bad["status"], "unresolved")
        self.assertIn("ambiguous", bad["reason"])
        bad = self.resolve({"target": "D/@constant", "indexOffset": 1}, {"declarationType": "Nat"})
        self.assertEqual(bad["status"], "unresolved")

    def test_lexical_override_updates_effects_and_avoids_capture(self):
        variables = [
            {
                "symbol": "x",
                "formulaOffset": offset,
                "start": 100 + offset,
                "end": 101 + offset,
                "status": "resolved",
                "declaration": "D",
                "leanName": "x",
                "leanType": "Real",
                "argumentPosition": 0,
            }
            for offset in (0, 5)
        ]
        effect = {"command": "mapsto", "start": 0, "end": 10, "binder": {"symbol": "x", "declarationOffset": 0}}
        records = {"D": {"binders": [{"name": "seq_index_100"}, {"name": "seq_index_100_"}]}}
        result = native.request(
            {
                "action": "resolveLexical",
                "variables": variables,
                "effects": [effect],
                "row": {"bodyStart": 100, "index": 2},
                "records": records,
            }
        )
        self.assertEqual(result["effects"][0]["binder"]["sourceContext"], "D")
        self.assertTrue(all(v["leanName"] == "seq_index_100__" and v["localBinder"] for v in result["variables"]))
        self.assertTrue(all(v["binderContext"] == "D" and v["declaration"] is None for v in result["variables"]))
        self.assertTrue(all("argumentPosition" not in v for v in result["variables"]))
        effect.pop("binder")
        result = native.request(
            {
                "action": "resolveLexical",
                "variables": variables,
                "effects": [effect],
                "row": {"bodyStart": 100},
                "records": records,
            }
        )
        self.assertTrue(all(v["status"] == "unresolved" and "localBinder" not in v for v in result["variables"]))

    def test_subtype_projection_uses_original_named_subset(self):
        good = self.resolve(
            {"target": "D/x", "projection": "Subtype.val"},
            {"binders": [{"name": "x", "type": "↑A"}, {"name": "A", "type": "Set Real"}]},
        )
        self.assertEqual((good["status"], good["leanType"], good["sourceLeanType"]), ("resolved", "Real", "↑A"))
        bad = self.resolve({"target": "D/x", "projection": "Subtype.val"}, {"binders": [{"name": "x", "type": "Real"}]})
        self.assertEqual(bad["status"], "unresolved")

    def test_domain_checks_require_the_declared_family_kind(self):
        effect = {
            "command": "natural-set-family",
            "start": 0,
            "binder": {"familyOffset": 0, "familyOffsets": [0], "lowerBound": "2"},
        }
        for ty, valid in (
            ("Nat → Set Real", True),
            ("Nat -> Set Real", True),
            ("Int → Set Real", False),
            ("Nat → Type", False),
            ("Nat → Set Real\n", False),
        ):
            with self.subTest(type=ty):
                variables = [
                    {"formulaOffset": 0, "status": "resolved", "leanType": ty},
                    {
                        "formulaOffset": 3,
                        "status": "resolved",
                        "leanType": "unresolved",
                        "localBinder": True,
                        "scopeStart": 100,
                    },
                ]
                result = native.request(
                    {"action": "resolveDomains", "variables": variables, "effects": [effect], "row": {"bodyStart": 100}}
                )["variables"][-1]
                self.assertEqual(result["status"] == "resolved", valid)
                if valid:
                    self.assertEqual((result["leanType"], result["indexLowerBound"]), ("ℕ", "2"))

    def test_convergence_uses_source_family_index_origin(self):
        effect = {"command": "sequence-limit", "start": 0, "binder": {"familyOffsets": [0]}}
        variables = [
            {"formulaOffset": 0, "status": "resolved", "leanType": "Nat → Real", "indexOrigin": 2},
            {"formulaOffset": 3, "status": "resolved", "leanType": "ℕ", "localBinder": True, "scopeStart": 100},
        ]
        payload = {"action": "resolveDomains", "variables": variables, "effects": [effect], "row": {"bodyStart": 100}}
        self.assertEqual(native.request(payload)["variables"][-1]["indexOffset"], 2)
        variables[0]["leanType"] = "Int → Real"
        self.assertEqual(native.request(payload)["variables"][-1]["status"], "unresolved")


class NativeSourceScopeTests(unittest.TestCase):
    def test_short_and_structured_targets_share_exact_context(self):
        context = {"declaration": "D", "path": ["root", "body"]}
        scope = {
            "scope": "s",
            "context": context,
            "bindings": {
                "x": {"symbol": "x", "target": "x"},
                "y": {"symbol": "y", "target": {"declaration": "D", "path": "root.body", "binder": "y"}},
                "c": {"symbol": "c", "target": {"constant": "C"}},
            },
        }
        result = native.request({"action": "scopeBindings", "scope": scope})["scope"]
        self.assertEqual(result["bindings"]["x"]["target"], "D@root.body/x")
        self.assertEqual(result["bindings"]["y"]["target"], "D@root.body/y")
        self.assertEqual(result["bindings"]["c"]["target"], "C/@constant")
        self.assertEqual(
            set(native.request({"action": "scopeDeclarations", "scopes": [result]})["declarations"]),
            {"D@root.body", "C"},
        )
        scope["bindings"]["z"] = {"symbol": "x", "target": "z"}
        with self.assertRaisesRegex(ValueError, "Colliding symbols"):
            native.request({"action": "scopeBindings", "scope": scope})
        for path in ("root.root", ["root", ""], "body"):
            with self.assertRaises(ValueError):
                native.request({"action": "contextReference", "context": {"declaration": "D", "path": path}})

    def test_premise_metadata_keeps_unicode_spans_and_rejects_empty_or_duplicate(self):
        opening = "<!-- chapter-correspondence-premise: p -->"
        closing = "<!-- chapter-correspondence-premise-end: p -->"
        text = "α" + opening + " x < 1 " + closing + "ω"
        scope = {
            "scope": "s",
            "start": 0,
            "end": len(text),
            "bindings": {"d": {"target": "D/d"}, "A": {"target": "D/A"}},
            "restrictions": [{"kind": "bounded-trace", "premise": "p", "metric": "d", "subset": "A"}],
        }
        result = native.request({"action": "scopeMetadata", "scopes": [scope], "text": text})["scopes"][0]
        source = result["restrictions"][0]["source"]
        self.assertEqual(text[source["start"] : source["end"]], " x < 1 ")
        self.assertEqual(source["start"], 1 + len(opening))
        for bad in (text.replace(" x < 1 ", " \n "), text + opening):
            with self.assertRaisesRegex(ValueError, "premise"):
                native.request({"action": "scopeMetadata", "scopes": [scope], "text": bad})
        crossed = [
            {"scope": "a", "bindings": {}, "start": 0, "end": 10},
            {"scope": "b", "bindings": {}, "start": 5, "end": 15},
        ]
        with self.assertRaisesRegex(ValueError, "Crossing scopes"):
            native.request({"action": "scopeMetadata", "scopes": crossed, "text": ""})

    def test_raw_scope_decoder_keeps_integer_tokens_and_duplicate_keys_strict(self):
        def source(raw):
            return "α<!-- chapter-correspondence" + raw + " -->$n$<!-- chapter-correspondence-end: s -->ω"

        template = '{"scope":"s","bindings":{"n":{"symbol":"n","target":"D/n","indexOffset":TOKEN,"unused":1.5}}}'
        text = source(template.replace("TOKEN", "1"))
        result = native.request({"action": "sourceScopes", "text": text})["scopes"][0]
        self.assertEqual(result["start"], text.index("$n$"))
        self.assertEqual(result["end"], text.index("<!-- chapter-correspondence-end"))
        self.assertEqual(result["bindings"]["n"]["unused"], 1.5)
        for token in ("1.0", "1e0", "2E1", "true", "-1", "0", '"1"'):
            with self.subTest(token=token), self.assertRaises(ValueError):
                native.request({"action": "sourceScopes", "text": source(template.replace("TOKEN", token))})
        interpretations = [
            {"id": identity, "constant": "C", "consumer": {"declaration": "D", "callee": "F", "argumentPosition": 1.0}}
            for identity in ("a", "b")
        ]
        raw = json.dumps({"scope": "s", "bindings": {}, "literalInterpretations": interpretations})
        with self.assertRaisesRegex(ValueError, "integer JSON token"):
            native.request({"action": "sourceScopes", "text": source(raw)})
        duplicate = r'{"scope":"s","bindings":{"n":{"symbol":"n","target":"D/n","\u0074arget":"D/m"}}}'
        with self.assertRaisesRegex(ValueError, "Duplicate source identity/key"):
            native.request({"action": "sourceScopes", "text": source(duplicate)})


class NativeSourceNormalizationTests(unittest.TestCase):
    def test_comparison_numerals_require_explicit_domain_and_keep_contiguous_spans(self):
        tokens = [{"kind": "text", "text": value, "start": i, "end": i + 1} for i, value in enumerate(" 12+3 ")]
        domain = {"type": "Real", "binding": "s/x", "target": "D/x"}
        payload = {"action": "comparisonOperand", "tokens": tokens, "domain": domain}
        parts = native.request(payload)["tree"]["items"]
        self.assertEqual(
            [(p["numeral"], p["start"], p["end"]) for p in parts if "numeral" in p], [("12", 1, 3), ("3", 4, 5)]
        )
        self.assertEqual(parts[0]["numericDomain"], domain)
        payload["domain"] = None
        self.assertTrue(all(p["kind"] == "text" for p in native.request(payload)["tree"]["items"]))
        payload["tokens"] = tokens[:1]
        with self.assertRaisesRegex(ValueError, "Empty expression operand"):
            native.request(payload)

    def test_real_scalar_coercions_use_source_types_and_reject_other_carriers(self):
        tree = syntax(["x+12"])[0]["tree"]
        payload = {
            "action": "scalarOperands",
            "stage": "real",
            "tree": tree,
            "variables": [{"formulaOffset": 0, "leanType": "Nat"}],
        }
        parts = native.request(payload)["tree"]["items"]
        self.assertEqual([p["body"]["text"] for p in parts if p["kind"] == "real-scalar-atom"], ["x", "12"])
        payload["variables"][0]["leanType"] = "Bool"
        self.assertIsNone(native.request(payload)["tree"])

    def test_ennreal_literals_require_resolved_source_operand(self):
        operands = [syntax([source])[0]["tree"] for source in ("x", r"\infty")]
        variable = {"formulaOffset": 0, "leanType": "ENNReal", "status": "unresolved"}
        payload = {"action": "scalarOperands", "stage": "ennreal", "operands": operands, "variables": [variable]}
        self.assertEqual(native.request(payload)["operands"], operands)
        variable["status"] = "resolved"
        self.assertEqual(native.request(payload)["operands"][1]["kind"], "ennreal-top")

    def test_numeric_domain_uses_innermost_explicit_witness_and_literal_span(self):
        source = " \t12 "
        tree = syntax([source])[0]["tree"]
        scopes = [
            {
                "scope": name,
                "start": begin,
                "end": end,
                "numerals": {"type": "Real", "from": "v"},
                "bindings": {"v": {"target": "D/" + name, "id": name + "/v"}},
            }
            for name, begin, end in (("outer", 0, 100), ("inner", 10, 30))
        ]
        result = native.request(
            {
                "action": "normalizeSource",
                "stage": "numeric",
                "tree": tree,
                "row": {"start": 20, "book": source},
                "scopes": scopes,
            }
        )["tree"]
        self.assertEqual(result["numericDomain"]["binding"], "inner/v")
        self.assertEqual((result["numeral"], result["numericStart"], result["numericEnd"]), ("12", 2, 4))

    def test_prefix_predicate_rejects_noncontiguous_digits(self):
        scope = {
            "scope": "s",
            "start": 0,
            "end": 100,
            "context": {"declaration": "D", "path": "root"},
            "predicates": {"type": "Real", "witness": "d"},
        }
        for source, supported in (("<12", True), ("<1 2", False), ("<-1", False)):
            tree = syntax([source])[0]["tree"]
            result = native.request(
                {"action": "normalizeSource", "stage": "prefix", "tree": tree, "row": {"start": 1}, "scopes": [scope]}
            )["tree"]
            self.assertEqual("prefixPredicate" in result, supported)
            if supported:
                self.assertEqual(result["prefixPredicate"]["domain"]["target"], "D@root/d")
            else:
                self.assertEqual(result, tree)

    def test_generator_restriction_requires_one_explicit_forward_premise(self):
        source = r"\bigcup\{\MetricBall{d}{x}{\delta}:x\in X,\delta>0,\MetricDiameter{\rho}{\MetricBall{d}{x}{\delta}\cap A}<1\}"
        tree = syntax([source])[0]["tree"]
        scope = {
            "scope": "s",
            "start": 0,
            "end": 1000,
            "bindings": {
                "rho": {"symbol": r"\rho", "id": "s/rho", "target": "D/rho"},
                "A": {"symbol": "A", "id": "s/A", "target": "D/A"},
            },
            "restrictions": [
                {
                    "kind": "bounded-trace",
                    "premise": "p",
                    "metric": "rho",
                    "subset": "A",
                    "source": {"start": 500, "end": 600, "text": "premise"},
                }
            ],
        }
        payload = {
            "action": "normalizeSource",
            "stage": "restrictions",
            "tree": tree,
            "row": {"start": 0, "end": len(source)},
            "scopes": [scope],
        }
        result = native.request(payload)["tree"]
        self.assertEqual(result["generatorRestrictions"][0]["metric"]["target"], "D/rho")
        scope["restrictions"].append(dict(scope["restrictions"][0], premise="q"))
        with self.assertRaisesRegex(ValueError, "Ambiguous bounded-trace"):
            native.request(payload)
        scope["restrictions"] = [dict(scope["restrictions"][0], source={"start": 0})]
        self.assertNotIn("generatorRestrictions", native.request(payload)["tree"])


class NativeContextTests(unittest.TestCase):
    def test_context_bridge_does_not_treat_null_identity_as_an_alias(self):
        root = {"name": "x", "type": "Nat", "instance": False}
        child = dict(root, originalName=None)
        records = {
            "D": {"binders": [root]},
            "D@root.body": {"binders": [child, {"name": "y", "type": "Nat", "instance": False}]},
        }
        with self.assertRaises(ValueError):
            native.request({"action": "contextBridge", "names": list(records), "records": records})
        child["originalName"] = "x"
        result = native.request({"action": "contextBridge", "names": list(records), "records": records})
        self.assertEqual(result["context"], "D@root.body")

    def test_local_definition_and_later_instance_remain_in_body(self):
        binders = [
            {"name": "α", "type": "Type u_1", "instance": False},
            {"name": "x", "type": "α", "instance": False},
            {"name": "saved", "type": "α", "instance": False, "value": "x"},
            {"name": "inst", "type": "Inhabited α", "instance": True},
        ]
        result = native.expression_definition({"context": "D", "lean": "saved"}, {"D": {"binders": binders}}, "Probe")
        self.assertEqual(
            result,
            "noncomputable abbrev Probe («α» : Type) («x» : α) :=\n  let «saved» : α := x;\n  fun [«inst» : Inhabited α] =>\n  saved\n",
        )

    def test_shadowing_elision_and_invalid_paths_are_rejected(self):
        for binders in (
            [{"name": "x", "type": "Nat", "instance": False}] * 2,
            [{"name": "x", "type": "⋯", "instance": False}],
            [{"name": "x", "type": "Nat", "instance": False, "value": "⋯"}],
        ):
            with self.assertRaises(ValueError):
                native.expression_definition({"context": "D", "lean": "x"}, {"D": {"binders": binders}}, "Probe")
        for path in ("root.root", "root.", "body", "root.inject", "root.body; run_cmd"):
            with self.assertRaises(ValueError):
                native.request(
                    {
                        "action": "contextExpression",
                        "declaration": "D",
                        "path": path,
                        "term": "x",
                        "name": "Probe",
                        "helper": native.helper_name("Probe"),
                    }
                )

    def test_placeholder_words_in_terms_are_not_substituted(self):
        term = '"ROOT TERM HELPER UNFOLD FRESH"'
        result = native.request(
            {
                "action": "contextExpression",
                "declaration": "D",
                "path": "root.body",
                "term": term,
                "name": "Probe",
                "helper": native.helper_name("Probe"),
            }
        )["source"]
        self.assertIn(json.dumps(term, ensure_ascii=False), result)
        self.assertIn('let info ← getConstInfo "D".toName', result)
        self.assertIn('["body"] #[] body', result)


class NativeEvidenceTests(unittest.TestCase):
    def test_missing_nullable_evidence_is_an_error(self):
        with self.assertRaises(ValueError):
            native.request(
                {
                    "action": "checkOperatorProbe",
                    "heads": {},
                    "consumers": {},
                    "mappings": [{"marker": "m", "rule": "infix:+"}],
                    "nodes": [{"marker": "m", "elaborated": {}}],
                }
            )

    def test_empty_observed_telescope_does_not_accept_expected_implicit(self):
        result = native.request(
            {
                "action": "implicitCoverage",
                "elaborated": {"arguments": []},
                "expectations": [{"argumentPosition": 0}],
                "checks": [{"status": "matched"}],
            }
        )["coverage"]
        self.assertEqual(result["status"], "mismatch")
        self.assertEqual(result["unexpectedPositions"], [0])

    def test_missing_and_duplicate_markers_fail(self):
        for nodes in ([], [{"marker": "m"}, {"marker": "m"}]):
            with self.assertRaisesRegex(ValueError, "missing or duplicated"):
                native.request(
                    {
                        "action": "checkOperatorProbe",
                        "heads": {},
                        "consumers": {},
                        "mappings": [{"marker": "m", "rule": "infix:+"}],
                        "nodes": nodes,
                    }
                )


class NativeCallAggregationTests(unittest.TestCase):
    def test_later_success_cannot_hide_a_failed_call(self):
        mapping = {
            "headStatus": "matched",
            "targetStatus": "matched",
            "operandStatus": "mismatch",
            "implicitArgumentStatus": "matched",
            "requirementStatus": "unresolved",
        }
        first = native.request({"action": "mergeOperatorCall", "mapping": mapping, "existing": None})["node"]
        successful = dict(mapping, operandStatus="matched", requirementStatus="proved")
        merged = native.request({"action": "mergeOperatorCall", "mapping": successful, "existing": first})["node"]
        self.assertEqual(len(merged["calls"]), 2)
        self.assertEqual(merged["operandStatus"], "mismatch")
        self.assertEqual(merged["requirementStatus"], "unresolved")


if __name__ == "__main__":
    unittest.main()
