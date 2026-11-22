"""Migration gates must reject partial, stale and cross-chapter evidence."""

import copy
import json
import subprocess
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools/chapter-correspondence"))
import chapter_config as config
import validate
from lean_export import parse_export_result


def reports():
    formulas = {
        "reviewStatus": "reviewed",
        "sourceHash": "source",
        "interpretationRulesHash": "rules",
        "scopeContexts": [{"status": "matched"}],
        "formulas": [{"index": 0, "syntaxStatus": "parsed", "typeStatus": "typechecked", "variables": []}],
    }
    evidence = {
        "sourceHash": "source",
        "interpretationRulesHash": "rules",
        "formulas": [
            {
                "formulaIndex": 0,
                "unresolved": [],
                "untracedOperators": [],
                "nodes": [
                    {
                        "operatorStart": 10,
                        "targetStatus": "matched",
                        "operandStatus": "matched",
                        "implicitArgumentStatus": "matched",
                        "requirementStatus": "proved",
                    }
                ],
            }
        ],
    }
    return formulas, evidence


class CorrespondenceMigrationTests(unittest.TestCase):
    def test_complete_evidence_passes(self):
        self.assertEqual(validate.coverage_findings(*reports()), [])

    def test_partial_evidence_cannot_hide_behind_successful_summary(self):
        for field, value in [
            ("targetStatus", "mismatch"),
            ("operandStatus", "unreviewed"),
            ("implicitArgumentStatus", "missing"),
            ("requirementStatus", "unresolved"),
        ]:
            with self.subTest(field=field):
                formulas, evidence = reports()
                evidence["summary"] = {"passed": True}
                evidence["formulas"][0]["nodes"][0][field] = value
                self.assertTrue(validate.coverage_findings(formulas, evidence))

    def test_missing_duplicate_and_wrong_formula_evidence_fail(self):
        for indices in ([], [0, 0], [1]):
            formulas, evidence = reports()
            row = evidence["formulas"][0]
            evidence["formulas"] = [dict(row, formulaIndex=i) for i in indices]
            self.assertTrue(validate.coverage_findings(formulas, evidence))

    def test_unresolved_source_and_fragments_fail(self):
        for change in (
            {"syntaxStatus": "unsupported"},
            {"typeStatus": "unresolved"},
            {"variables": [{"status": "unresolved"}]},
            {"expressionFragments": [{"typeStatus": "unresolved"}]},
        ):
            formulas, evidence = reports()
            formulas["formulas"][0].update(change)
            self.assertTrue(validate.coverage_findings(formulas, evidence))

    def test_untraced_operator_and_unresolved_subexpression_fail(self):
        for field in ("unresolved", "untracedOperators"):
            formulas, evidence = reports()
            evidence["formulas"][0][field] = [{"start": 10}]
            self.assertTrue(validate.coverage_findings(formulas, evidence))

    def test_stale_review_and_wrong_evidence_fail(self):
        formulas, evidence = reports()
        stale = copy.deepcopy(formulas)
        stale["reviewStatus"] = "stale"
        self.assertTrue(validate.coverage_findings(stale, evidence))
        evidence["sourceHash"] = "another-source"
        self.assertTrue(validate.coverage_findings(formulas, evidence))

    def test_unregistered_chapters_fail_instead_of_using_polish(self):
        for name in ("cantor-baire-space", "../polish-spaces", ""):
            with self.assertRaises(ValueError):
                config.load_chapter(name)

    def test_all_adapters_use_selected_imports(self):
        from dataclasses import replace

        chapter = validate.chapter
        selected = replace(chapter.CONFIG, modules=("Example.NewChapter",))
        with patch.object(chapter, "CONFIG", selected):
            self.assertIn("import Example.NewChapter", chapter.declaration_export({"Nat.zero"}))
        from proof_contexts import inspection_source

        source = inspection_source("Example.theorem", "x", imports=selected.imports())
        self.assertIn("import Example.NewChapter", source)
        self.assertNotIn("import PolishSpaceBook.PolishSpaces", source)

    def test_inventory_rejects_wrong_chapter_and_rules_before_export(self):
        operators = validate.operators
        chapter = operators.chapter
        good = {
            "chapter": chapter.CONFIG.name,
            "configurationHash": chapter.CONFIG.fingerprint,
            "interpretationRulesHash": chapter.rules_hash(),
        }
        for field in good:
            report = dict(good)
            report[field] = "other"
            with patch.object(chapter, "evidence") as export, self.assertRaises(ValueError):
                operators.validate_inventory(report)
            export.assert_not_called()

    def test_transport_accepts_neutral_and_legacy_protocol(self):
        for prefix in ("BOOK_LEAN_EXPORT", "SORT_PILOT"):
            result = subprocess.CompletedProcess([], 0, prefix + ' {"declaration":"probe","result":"Nat"}\n', "")
            self.assertEqual(parse_export_result(result)["probe"]["result"], "Nat")
        with self.assertRaises(ValueError):
            parse_export_result(subprocess.CompletedProcess([], 0, "warning: bad\n", ""))

    def test_chapter_does_not_import_legacy_sort_tooling(self):
        script = "import sys; sys.path.insert(0, 'tools/chapter-correspondence'); import validate; print(sorted(sys.modules))"
        output = subprocess.check_output([sys.executable, "-c", script], cwd=ROOT, text=True)
        for name in ("check_sort_pilot", "sort_coverage", "source_bindings", "formula_types"):
            self.assertNotIn("'" + name + "'", output)

    def test_proof_context_adapter_imports_in_isolation(self):
        script = """import importlib.util
spec = importlib.util.spec_from_file_location('isolated_contexts', 'tools/chapter-correspondence/proof_contexts.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
assert 'import PolishSpaceBook.PolishSpaces' in module.inspection_source('Nat.zero', 'root')
"""
        subprocess.run([sys.executable, "-c", script], cwd=ROOT, check=True)

    def test_registered_source_has_no_legacy_variable_declarations(self):
        self.assertNotRegex(config.load_chapter().source.read_text(), r"\\vars\s*\{")
        self.assertEqual(json.loads((config.REGISTRY / "polish-spaces.json").read_text())["chapter"], "polish-spaces")


if __name__ == "__main__":
    unittest.main()
