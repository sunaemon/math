"""Proof-local evidence must retain definitions and distinguish shadowing."""

import copy
import importlib.util
import subprocess
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("proof_contexts", ROOT / "tools/chapter-correspondence/proof_contexts.py")
contexts = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(contexts)


class ProofContextTests(unittest.TestCase):
    def test_relative_meager_context_keeps_subspace_and_ambient_sets_distinct(self):
        declaration = "PolishSpaceBook.nonempty_open_not_meagre_in_itself"
        records = contexts.export(contexts.inspection_source(declaration, "hxH"))
        local = [r for key, r in records.items() if "@" in key]
        self.assertEqual(len(local), 1)
        path = local[0]["declaration"].split("@", 1)[1]
        # Replay the mathematical claims in their original local context.
        # In particular closure (N n) is in U, whereas closure (G n) is in X.
        claims = [
            "(show (Set.univ : Set U) = ⋃ n, N n from hNcover)",
            "(show ∀ n, H n = (closure (N n))ᶜ from fun _ => rfl)",
            "(show ∀ n, G n = Subtype.val '' H n from fun _ => rfl)",
            "(show ∀ n, U ⊆ closure (G n) from hGdense)",
            "(show (⟨x, hxU⟩ : U) ∈ ⋂ n, H n from hxH)",
        ]
        source = contexts.LEAN
        for index, claim in enumerate(claims):
            source += contexts.expression_from_context(declaration, path, claim, f"RelativeMeager{index}")
        source += '\nrun_cmd logInfo "BOOK_LEAN_EXPORT {\\"declaration\\":\\"relative_meager\\",\\"checked\\":true}"\n'
        self.assertTrue(contexts.export(source)["relative_meager"]["checked"])

    @patch.dict("os.environ", {"BOOK_LEAN_EXPORT_BACKEND": "subprocess"})
    def test_missing_dependency_aborts_instead_of_becoming_an_unresolved_formula(self):
        missing = "error: object file '/tmp/M.olean' of module M does not exist"
        result = subprocess.CompletedProcess([], 1, stdout=missing, stderr="")
        with (
            patch("lean_export.subprocess.run", return_value=result),
            self.assertRaisesRegex(RuntimeError, "finish the Lake build"),
        ):
            contexts.export("import M")
        result = subprocess.CompletedProcess([], 1, stdout="error: type mismatch", stderr="")
        with patch("lean_export.subprocess.run", return_value=result), self.assertRaises(ValueError):
            contexts.export("def bad : Nat := True")

    def test_explicit_unfold_preserves_specialization_and_dependency_evidence(self):
        fixture = """
universe u
def genericContext (α : Type u) (f : α → α) (seed : α) : α :=
  let saved := f seed
  saved
def natContext (seed : Nat) : Nat := genericContext Nat (fun n => n + 1) seed
"""
        query = "root.body.unfold::saved"
        source = contexts.inspection_source("natContext", query)
        source = source.replace("run_cmd liftTermElabM do", fixture + "\nrun_cmd liftTermElabM do", 1)
        records = contexts.export(source)
        key = next(k for k in records if "@" in k)
        record = records[key]
        self.assertEqual([b["type"] for b in record["binders"]], ["ℕ", "ℕ"])
        self.assertIsNotNone(record["binders"][-1]["value"])
        self.assertEqual(record["unfoldings"], ["genericContext"])
        exact = contexts.inspection_source("natContext", key.split("@", 1)[1])
        exact = exact.replace("run_cmd liftTermElabM do", fixture + "\nrun_cmd liftTermElabM do", 1)
        self.assertEqual(contexts.export(exact), records)
        changed = contexts.export(source.replace("let saved := f seed", "let saved := f (f seed)"))
        self.assertEqual(records["natContext"]["body"], changed["natContext"]["body"])
        self.assertNotEqual(records["genericContext"]["body"], changed["genericContext"]["body"])
        spec = importlib.util.spec_from_file_location(
            "unfold_chapter_check", ROOT / "tools/chapter-correspondence/check.py"
        )
        chapter = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(chapter)
        fingerprints = []
        for evidence in (records, changed):
            with patch.object(
                chapter,
                "export",
                side_effect=[{"natContext": copy.deepcopy(evidence["natContext"])}, copy.deepcopy(evidence)],
            ):
                fingerprints.append(chapter.evidence({key})[key]["body"])
        self.assertNotEqual(*fingerprints)
        replay = contexts.LEAN + fixture
        replay += contexts.expression_from_context("natContext", key.split("@", 1)[1], "saved", "NatSaved")
        replay += r"""
example (n : Nat) : NatSaved n = n + 1 := rfl
run_cmd logInfo "BOOK_LEAN_EXPORT {\"declaration\":\"probe\",\"checked\":true}"
"""
        self.assertTrue(contexts.export(replay)["probe"]["checked"])
        # Plain name search must never unfold arbitrary referenced theorems.
        plain = contexts.inspection_source("natContext", "saved")
        plain = plain.replace("run_cmd liftTermElabM do", fixture + "\nrun_cmd liftTermElabM do", 1)
        self.assertEqual(set(contexts.export(plain)), {"natContext"})
        invalid = contexts.inspection_source("natContext", "root.unfold")
        invalid = invalid.replace("run_cmd liftTermElabM do", fixture + "\nrun_cmd liftTermElabM do", 1)
        with self.assertRaisesRegex(ValueError, "constant-headed application"):
            contexts.export(invalid)

    def test_batched_exact_paths_match_name_search_with_shadowing_and_lets(self):
        fixture = """
def batchFixture (x : Nat) : Nat := let y := x + 1; (fun y : Nat => y + 2) y
def otherFixture (x : Nat) : Nat := let y := x + 3; y
"""
        broad = contexts.inspection_source_many([("batchFixture", "y"), ("otherFixture", "y")])
        broad = broad.replace("run_cmd liftTermElabM do", fixture + "\nrun_cmd liftTermElabM do", 1)
        expected = contexts.export(broad)
        requests = [key.split("@", 1) for key in expected if "@" in key]
        self.assertEqual(len(requests), 3)
        exact = contexts.inspection_source_many(requests + requests[:1])
        exact = exact.replace("run_cmd liftTermElabM do", fixture + "\nrun_cmd liftTermElabM do", 1)
        self.assertEqual(contexts.export(exact), expected)

    def test_real_bounded_distance_retains_its_construction(self):
        name = "PolishSpaceBook.complete_compatible_metric_bounded_by_one"
        records = contexts.export(contexts.inspection_source(name, "boundedDist"))
        self.assertNotEqual(records[name]["body"], "none")
        locals_ = [r for key, r in records.items() if key != name]
        self.assertEqual(len(locals_), 1)
        binders = locals_[0]["binders"]
        self.assertEqual(binders[-1]["name"], "boundedDist")
        self.assertEqual(binders[-1]["type"], "Y → Y → ℝ")
        self.assertEqual(binders[-1]["value"], "fun x y => PolishSpaceBook.boundedMetricTransform (originalDist x y)")
        self.assertEqual(binders[-2]["name"], "originalDist")
        self.assertIsNotNone(binders[-2]["value"])

    def test_context_term_is_inserted_without_replacing_its_identifiers(self):
        source = contexts.LEAN + "\ndef contextFixture (x : Nat) : Nat := x + 1\n"
        source += contexts.expression_from_context(
            "contextFixture", "root", "let OUTPUT := x + 1; OUTPUT", "ContextProbe"
        )
        source += r"""
example (x : Nat) : ContextProbe x = x + 1 := rfl
run_cmd logInfo "BOOK_LEAN_EXPORT {\"declaration\":\"probe\",\"checked\":true}"
"""
        self.assertTrue(contexts.export(source)["probe"]["checked"])

    def test_generated_binder_name_does_not_capture_an_existing_name(self):
        fixture = """
def collisionFixture (x y_book_3 : Nat) : Nat :=
  let y := x + 1
  (fun y : Nat => y + y_book_3) y
"""
        source = contexts.inspection_source("collisionFixture", "y")
        source = source.replace("run_cmd liftTermElabM do", fixture + "\nrun_cmd liftTermElabM do")
        records = contexts.export(source)
        inner = next(row for row in records.values() if row.get("kind") == "lambda")
        self.assertEqual(inner["binders"][-1]["name"], "y_book_3_")
        replay = contexts.LEAN + fixture
        replay += contexts.expression_from_context(
            "collisionFixture", inner["declaration"].split("@", 1)[1], "(y, y_book_3_, y_book_3)", "CollisionProbe"
        )
        replay += r"""
example : CollisionProbe 3 20 9 = (4, 9, 20) := rfl
run_cmd logInfo "BOOK_LEAN_EXPORT {\"declaration\":\"probe\",\"checked\":true}"
"""
        self.assertTrue(contexts.export(replay)["probe"]["checked"])

    def test_shadowed_names_have_distinct_paths_and_binding_kinds(self):
        source = contexts.inspection_source("contextFixture", "y")
        source = source.replace(
            "run_cmd liftTermElabM do",
            """
def contextFixture (x : Nat) : Nat :=
  let y := x + 1
  (fun y : Nat => y + 2) y
run_cmd liftTermElabM do""",
        )
        records = contexts.export(source)
        locals_ = [r for key, r in records.items() if key != "contextFixture"]
        self.assertEqual(len(locals_), 2)
        self.assertEqual({r["kind"] for r in locals_}, {"lambda", "let"})
        self.assertNotEqual(locals_[0]["declaration"], locals_[1]["declaration"])
        for row in locals_:
            self.assertEqual(row["binders"][-1]["value"] is None, row["kind"] == "lambda")
            self.assertEqual(row["binders"][-1]["originalName"], "y")
            self.assertEqual(len({b["name"] for b in row["binders"]}), len(row["binders"]))
        inner = next(row for row in locals_ if row["kind"] == "lambda")
        self.assertEqual(inner["binders"][-1]["name"], "y_book_2")
        replay = contexts.LEAN + "\ndef contextFixture (x : Nat) : Nat := let y := x + 1; (fun y : Nat => y + 2) y\n"
        replay += contexts.expression_from_context(
            "contextFixture", inner["declaration"].split("@", 1)[1], "(y, y_book_2)", "ShadowProbe"
        )
        replay += r"""
example : ShadowProbe 3 9 = (4, 9) := rfl
run_cmd logInfo "BOOK_LEAN_EXPORT {\"declaration\":\"probe\",\"checked\":true}"
"""
        self.assertTrue(contexts.export(replay)["probe"]["checked"])


if __name__ == "__main__":
    unittest.main()
