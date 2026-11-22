"""Shared rules, candidate provenance and dependency-aware execution reuse."""

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools/chapter-correspondence"))
import chapter_config
import check as chapter
import notation_rules
import suggest
from lean_export import cache_active, cached_probes, export
from lean_probe_cache import Environment, ProbeCache


class DependencyCacheTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.lib = self.root / "book/.lake/build/lib/lean"
        self.lib.mkdir(parents=True)
        for name, imports in (("A", ["B"]), ("B", []), ("Other", [])):
            self.module(name, imports)
        self.environment = Environment(self.root / "book", self.root / "cache", roots=[self.lib])

    def module(self, name, imports):
        (self.lib / (name + ".olean")).write_text("compiled " + name)
        (self.lib / (name + ".ilean")).write_text(
            json.dumps({"directImports": [[i, False, False, False] for i in imports]})
        )

    def cache(self, *, force=False):
        return ProbeCache(self.root / "probes", self.environment.snapshot(["A"]), force=force)

    def test_only_changed_probe_is_executed(self):
        execute = Mock(return_value={"probe": {"checked": True}})
        cache = self.cache()
        for source in ("import A\nfirst", "import A\nsecond"):
            cache.run(source, execute)
        self.assertEqual(execute.call_count, 2)
        warm = self.cache()
        warm.run("import A\nfirst", execute)
        warm.run("import A\nchanged second", execute)
        self.assertEqual(warm.statistics()["reusedProbes"], 1)
        self.assertEqual(warm.statistics()["executedProbes"], 1)
        self.assertEqual(execute.call_count, 3)

    def test_transitive_change_invalidates_but_unrelated_module_does_not(self):
        execute = Mock(return_value={"probe": {"checked": True}})
        self.cache().run("import A\nprobe", execute)
        (self.lib / "Other.olean").write_text("unrelated change")
        self.cache().run("import A\nprobe", execute)
        self.assertEqual(execute.call_count, 1)
        (self.lib / "B.olean").write_text("new instance in a dependency")
        self.cache().run("import A\nprobe", execute)
        self.assertEqual(execute.call_count, 2)

    def test_private_artifact_and_import_graph_changes_invalidate(self):
        original = self.environment.snapshot(["A"])
        (self.lib / "B.olean.private").write_text("private theorem value")
        changed = self.environment.snapshot(["A"])
        self.assertNotEqual(original["fingerprint"], changed["fingerprint"])
        self.module("B", ["Other"])
        changed = self.environment.snapshot(["A"])
        self.assertIn("Other", changed["modules"])
        (self.lib / "Other.olean").unlink()
        with self.assertRaisesRegex(RuntimeError, "Missing compiled dependency"):
            self.environment.snapshot(["A"])

    def test_corrupt_import_inventory_is_rebuilt_instead_of_losing_dependencies(self):
        before = self.environment.snapshot(["A"])
        self.environment.memo[str(self.lib / "A.ilean")]["imports"] = []
        after = self.environment.snapshot(["A"])
        self.assertIn("B", after["modules"])
        self.assertEqual(before["fingerprint"], after["fingerprint"])

    def test_unbuilt_source_edits_and_deleted_sources_are_detected(self):
        source = self.root / "book/lean/B.lean"
        source.parent.mkdir()
        source.write_text("def value := 0")
        before = self.environment.snapshot(["A"])
        source.write_text("def value := 1")
        after = self.environment.snapshot(["A"])
        self.assertNotEqual(before["fingerprint"], after["fingerprint"])
        source.unlink()
        self.assertNotEqual(after["fingerprint"], self.environment.snapshot(["A"])["fingerprint"])

    def test_changed_transport_or_imports_cannot_reuse_evidence(self):
        execute = Mock(return_value={"probe": {"checked": True}})
        cache = self.cache()
        cache.run("import A\nprobe", execute)
        cache.implementation = "changed transport"
        cache.run("import A\nprobe", execute)
        self.assertEqual(execute.call_count, 2)
        with self.assertRaisesRegex(ValueError, "Probe imports differ"):
            cache.run("import Other\nprobe", execute)

    def test_failures_are_not_cached_and_full_mode_rechecks(self):
        execute = Mock(side_effect=ValueError("Lean rejected"))
        cache = self.cache()
        for _ in range(2):
            with self.assertRaises(ValueError):
                cache.run("import A\nprobe", execute)
        self.assertEqual(execute.call_count, 2)
        execute = Mock(return_value={"probe": {"checked": True}})
        cache.run("import A\nprobe", execute)
        self.cache(force=True).run("import A\nprobe", execute)
        self.assertEqual(execute.call_count, 2)

    def test_corrupt_cached_result_is_reexecuted(self):
        execute = Mock(return_value={"probe": {"checked": True}})
        self.cache().run("import A\nprobe", execute)
        path = next((self.root / "probes").rglob("*.json"))
        data = json.loads(path.read_text())
        data["result"]["probe"]["checked"] = False
        path.write_text(json.dumps(data))
        self.cache().run("import A\nprobe", execute)
        self.assertEqual(execute.call_count, 2)

    def test_cache_scope_does_not_leak_after_exception(self):
        self.assertFalse(cache_active())
        with self.assertRaises(ValueError), cached_probes(self.cache()):
            self.assertTrue(cache_active())
            raise ValueError("aborted")
        self.assertFalse(cache_active())


class LiveProbeCacheTests(unittest.TestCase):
    def test_actual_lean_reuses_unchanged_input_and_executes_changed_input(self):
        imports = (*chapter.CONFIG.modules, "Lean")

        def probe(value):
            return (
                chapter.CONFIG.imports()
                + f"""open Lean
run_cmd logInfo m!"BOOK_LEAN_EXPORT {{(Json.mkObj [
  ("declaration", toJson "cacheRegression"), ("value", toJson ({value} : Nat))]).compress}}"
"""
            )

        with tempfile.TemporaryDirectory() as directory:
            environment = Environment(ROOT / chapter.CONFIG.project, Path(directory) / "environment")
            snapshot = environment.snapshot(imports)
            cache = ProbeCache(Path(directory) / "probes", snapshot)
            with cached_probes(cache):
                self.assertEqual(export(probe(3))["cacheRegression"]["value"], 3)
                self.assertEqual(export(probe(3))["cacheRegression"]["value"], 3)
                self.assertEqual(export(probe(4))["cacheRegression"]["value"], 4)
            self.assertEqual(cache.statistics()["reusedProbes"], 1)
            self.assertEqual(cache.statistics()["executedProbes"], 2)
            self.assertEqual(environment.snapshot(imports)["fingerprint"], snapshot["fingerprint"])


class SharedRulesAndCandidateTests(unittest.TestCase):
    def test_chapter_selection_changes_source_imports_and_profiles_without_engine_edits(self):
        data = json.loads((chapter_config.REGISTRY / "polish-spaces.json").read_text())
        data.update(
            chapter="fixture",
            source="polish-space/src/polish-space-book/cantor-baire-space.md",
            leanModules=["PolishSpaceBook.PolishSpaces"],
            notationProfiles=["core"],
        )
        original = chapter.CONFIG.name
        try:
            with tempfile.TemporaryDirectory() as directory, patch.object(chapter_config, "REGISTRY", Path(directory)):
                (Path(directory) / "fixture.json").write_text(json.dumps(data))
                chapter.configure("fixture")
                self.assertTrue(str(chapter.SOURCE).endswith("cantor-baire-space.md"))
                self.assertNotIn("PartIScope", chapter.CONFIG.imports())
                self.assertNotIn("BaireSpace", chapter.CONSTANTS)
                self.assertIs(chapter.MACROS, notation_rules.MACROS)
                self.assertEqual(chapter.MACROS["frac"][1](["x", "y"]), "((x) / (y))")
        finally:
            chapter.configure(original)

    def test_unknown_duplicate_and_conflicting_profiles_fail(self):
        for profiles in (["unknown"], ["core", "core"]):
            with self.assertRaises(ValueError):
                notation_rules.select_profiles(profiles)
        with (
            patch.dict(
                notation_rules.PROFILES,
                {"collision": {"constants": {"R": "Nat"}, "declarations": [], "conventions": {}}},
            ),
            self.assertRaisesRegex(ValueError, "Conflicting"),
        ):
            notation_rules.select_profiles(["core", "collision"])

    def test_namespaces_and_ambiguous_declarations_are_retained(self):
        entry = {"lean": {"declName": "fact", "declLine": 11}}
        declarations = {"A.fact": [10, 0, 12, 0], "B.fact": [30, 0, 32, 0]}
        self.assertEqual(suggest.qualified_names(entry, declarations), ["A.fact"])
        declarations["B.fact"] = [10, 0, 12, 0]
        self.assertEqual(suggest.qualified_names(entry, declarations), ["A.fact", "B.fact"])
        self.assertEqual(suggest.qualified_names({"lean": {"declName": None, "declLine": 11}}, declarations), [])

    def test_binding_drafts_preserve_ambiguity_and_never_claim_review(self):
        variables = [{"symbol": "x"}, {"symbol": "y"}, {"symbol": "missing"}]
        binders = [{"name": name, "type": "Nat", "instance": False} for name in ("x", "y", "y")]
        draft, options = suggest.binding_draft(variables, "A.fact", {"binders": binders})
        self.assertEqual(list(draft.values()), [{"symbol": "x", "target": "A.fact/x"}])
        by_symbol = {row["symbol"]: row for row in options}
        self.assertEqual(by_symbol["y"]["status"], "unresolved")
        self.assertEqual(len(by_symbol["y"]["options"]), 2)
        self.assertEqual(by_symbol["missing"]["options"], [])
        self.assertEqual(by_symbol["x"]["status"], "candidate")


if __name__ == "__main__":
    unittest.main()
