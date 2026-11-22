"""Viewer projection preserves validated evidence; inspection never approves it."""

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools/chapter-correspondence"))
from lean_locations import original_index
from native import request
from viewer import compact_operator, digest, latest_snapshot, viewer_report


class CorrespondenceViewerTests(unittest.TestCase):
    def test_original_lean_byte_positions_convert_unicode_to_utf16(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "tools").mkdir()
            (root / "tools/lean_source_ranges.lean").write_text("fixture")
            source = root / "A.lean"
            source.write_text("😀 x\nα")
            index = {"ranges": [{"startByte": 5, "endByte": 6}, {"startByte": 7, "endByte": 9}]}
            with patch("lean_locations.chapter.ROOT", root), patch("lean_locations.read_artifact", return_value=index):
                ranges = original_index(source, "A", {}, "fixture")
            self.assertEqual(
                [(row["startOffset"], row["endOffset"], row["startLine"]) for row in ranges], [(3, 4, 1), (5, 6, 2)]
            )

    def test_original_lean_ranges_require_full_arguments_and_local_context(self):
        kernel = {
            "kind": "application",
            "function": {"kind": "constant", "name": "f", "levels": "[]"},
            "arguments": [{"kind": "variable", "name": "x"}],
        }
        binder = {"name": "x", "type": "Nat", "value": None}
        target = {"formulaIndex": 3, "operatorStart": 12, "declaration": "A.f", "kernel": kernel, "binders": [binder]}
        original = {
            "declaration": "A.f",
            "kernel": kernel,
            "locals": [binder],
            "source": "A.lean",
            "startOffset": 4,
            "endOffset": 9,
            "startLine": 1,
        }

        def match(row):
            return request({"action": "leanSourceRanges", "targets": [target], "ranges": [row]})["ranges"]

        self.assertEqual(len(match(original)), 1)
        truncated = copy.deepcopy(original)
        truncated["kernel"] = {"kind": "truncated"}
        self.assertEqual(
            request(
                {
                    "action": "leanSourceRanges",
                    "targets": [dict(target, kernel=truncated["kernel"])],
                    "ranges": [truncated],
                }
            )["ranges"],
            [],
        )
        for kind in ("argument", "type", "value", "declaration", "shadow"):
            wrong = copy.deepcopy(original)
            if kind == "argument":
                wrong["kernel"]["arguments"][0]["name"] = "y"
            elif kind in ("type", "value"):
                wrong["locals"][0][kind] = "Int" if kind == "type" else "1"
            elif kind == "declaration":
                wrong["declaration"] = "B.f"
            else:
                wrong["locals"].append(binder)
            with self.subTest(kind=kind):
                self.assertEqual(match(wrong), [])

    def test_pdf_formula_identity_uses_source_positions_and_changes_with_source_content(self):
        text = "😀 $x$ <!-- $ignored$ -->\n```\n$opaque$\n```\n$$a+b$$"
        payload = {"action": "formulaAnchors", "source": "book/chapter.md", "text": text}
        first = request(payload)["formulas"]
        self.assertEqual(len(first), 2)
        self.assertEqual(first[0]["bodyStart"], text.index("x"))
        self.assertNotEqual(first[0]["pdfTag"], first[1]["pdfTag"])
        changed = request(dict(payload, text=text + " revised"))["formulas"]
        self.assertNotEqual(first[0]["pdfTag"], changed[0]["pdfTag"])
        self.assertEqual(first[0]["bodyStart"], changed[0]["bodyStart"])

    def test_stale_sources_rules_reviews_and_lean_never_get_a_current_ast(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            registry = root / "chapters"
            registry.mkdir()
            (registry / "fixture.json").write_text("{}")
            source = root / "chapter.md"
            source.write_text("$x$")
            review = root / "review.json"
            review.write_text("{}")
            config = SimpleNamespace(
                source=source, name="fixture", project=".", modules=(), review=review, fingerprint="config"
            )
            run = root / "build/validation/correspondence-fixture-1"
            run.mkdir(parents=True)
            report = {"passed": True, "configurationHash": "config", "reviewHash": digest(review)}
            formulas = {
                "source": "chapter.md",
                "sourceHash": digest(source),
                "interpretationRulesHash": "rules",
                "formulas": [],
                "offsetConvention": "codepoints",
            }
            operators = {"sourceHash": digest(source), "interpretationRulesHash": "rules", "formulas": []}
            for name, data in (
                ("report", report),
                ("formulas", formulas),
                ("operators", operators),
                ("dependencies", {"fingerprint": "lean"}),
            ):
                (run / (name + ".json")).write_text(json.dumps(data))
            with (
                patch("viewer.chapter.ROOT", root),
                patch("viewer.REGISTRY", registry),
                patch("viewer.load_chapter", return_value=config),
                patch("viewer.chapter.configure"),
                patch("viewer.chapter.request") as native,
                patch("viewer.chapter.rules_hash", return_value="changed"),
                patch("lean_probe_cache.Environment") as environment,
            ):
                environment.return_value.snapshot.return_value = {"fingerprint": "lean"}
                result = viewer_report("chapter.md")
                self.assertEqual(result["status"], "stale")
                self.assertIn("rules-changed", result["reasons"])
                native.assert_not_called()
                with patch("viewer.chapter.rules_hash", return_value="rules"):
                    for mutation, reason in (
                        ("source", "source-changed"),
                        ("review", "review-changed"),
                        ("lean", "lean-changed"),
                    ):
                        with self.subTest(mutation=mutation):
                            source.write_text("$y$" if mutation == "source" else "$x$")
                            review.write_text('{"changed":true}' if mutation == "review" else "{}")
                            environment.return_value.snapshot.return_value = {
                                "fingerprint": "different" if mutation == "lean" else "lean"
                            }
                            result = viewer_report("chapter.md")
                            self.assertEqual(result["status"], "stale")
                            self.assertIn(reason, result["reasons"])
                            native.assert_not_called()

    def test_semantic_ast_is_the_actual_native_expression_and_is_opt_in(self):
        from validate import chapter

        node = chapter.syntax(["1+2"])[0]["tree"]
        payload = {"action": "translateBatch", "expressions": [{"tree": node, "variables": []}]}
        ordinary = request(payload)["results"][0]
        self.assertNotIn("semanticAST", ordinary)
        inspected = request(dict(payload, environment={"includeAST": True}))["results"][0]
        self.assertEqual(inspected["rendering"], ordinary["rendering"])
        self.assertEqual(inspected["semanticAST"]["node"], "Scoped")
        scalar = inspected["semanticAST"]["arguments"][1]
        self.assertEqual(scalar["node"], "Scalar")
        self.assertEqual(scalar["arguments"][0], {"start": 0, "end": 3})
        self.assertEqual(scalar["arguments"][3]["arguments"][1]["node"], "Literal")

    def test_projection_keeps_all_lean_calls_and_implicit_argument_types(self):
        argument = {"value": "x", "type": "Real", "implicit": True, "instance": False, "parameter": "α"}
        calls = [{"elaborated": {"head": head, "arguments": [argument]}} for head in ("LT.lt", "LE.le")]
        projected = compact_operator({"rule": "comparison", "calls": calls})
        self.assertEqual([call["head"] for call in projected["calls"]], ["LT.lt", "LE.le"])
        self.assertEqual(projected["calls"][0]["arguments"], [argument])

    def test_snapshot_selection_does_not_hide_failed_or_partial_validation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            run = root / "build/validation/correspondence-fixture-1"
            run.mkdir(parents=True)
            self.assertIsNone(latest_snapshot(root, "chapter.md"))
            (run / "report.json").write_text(json.dumps({"passed": False}))
            (run / "formulas.json").write_text(json.dumps({"source": "chapter.md"}))
            selected = latest_snapshot(root, "chapter.md")
            self.assertFalse(selected[2]["passed"])
            self.assertIsNone(latest_snapshot(root, "other.md"))
