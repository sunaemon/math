"""Terminology regression checks, including false positives and PO locations."""

from __future__ import annotations

import copy
import json
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, os.fspath(REPO_ROOT / "tools"))

import check_translation_terms as checker
import check_translation_workflow as workflow
from project_translation_sourcemap import PoMessage

DATA = {
    "version": 1,
    "language": "ja",
    "terms": [
        {
            "id": "uniformization",
            "english": "uniformization",
            "japanese": "一意化",
            "status": "approved",
            "avoid": ["一様化"],
            "definition_keys": ["uniformization"],
        },
        {
            "id": "indicator",
            "english": "indicator function",
            "japanese": "指示関数",
            "status": "approved",
            "avoid": ["特性関数"],
            "source_terms": ["indicator", "indicators"],
            "definition_keys": ["indicator function"],
        },
    ],
    "spellings": [{"id": "query", "preferred": "問い合わせ", "avoid": ["問合せ"]}],
}


class TerminologyTest(unittest.TestCase):
    def setUp(self):
        self.glossary = checker.parse_glossary(DATA)

    def check(self, translated, source="A theorem."):
        return checker.check_message(PoMessage(source, translated), self.glossary)

    def test_detects_multiple_rules_and_wrapped_phrase(self):
        errors = self.check("一様\n化と問合せを用いる．")
        self.assertEqual(len(errors), 2)
        self.assertIn("一意化", errors[0])
        self.assertIn("問い合わせ", errors[1])

    def test_source_scope_preserves_distinct_mathematical_meaning(self):
        self.assertFalse(self.check("分布の特性関数", "The characteristic function of a distribution."))
        self.assertTrue(self.check("集合の特性関数", "An INDICATOR\nfunction."))
        self.assertTrue(self.check("集合の特性関数", "Indicators of sets."))
        self.assertFalse(self.check("特性関数", "A nonindicator."))

    def test_definition_checks_unknown_spelling_not_only_known_variants(self):
        self.assertTrue(self.check(r"\termdefineas{uniformization}{別の訳語}"))
        self.assertTrue(self.check(r"\termdefine{uniformization}"))
        self.assertFalse(self.check(r"\termdefineas{uniformization}{一意化}"))
        self.assertFalse(self.check(r"\termuseas{uniformization}{この構成}"))

    def test_alternate_definition_form_is_explicit(self):
        data = copy.deepcopy(DATA)
        data["terms"][0]["definition_forms"] = ["一意化", "一意化定理"]
        glossary = checker.parse_glossary(data)
        self.assertFalse(checker.check_message(PoMessage("", r"\termdefineas{uniformization}{一意化定理}"), glossary))

    def test_skips_nonrendered_content_and_code_but_checks_display(self):
        text = r"""---
metadata: 一様化
---
<!-- 一様化 -->
`一様化`
```tex
\termdefineas{uniformization}{一様化}
```
\termuseas{一様化}{一意化} \termref{一様化}
§{一様化} {#一様化} \label{一様化} [@一様化] [資料](https://example.invalid/一様化)
\href{https://example.invalid/一様化}{資料} \url{https://example.invalid/一様化}
10\%
\begin{mathmeta}\define{一様化}\end{mathmeta}
"""
        self.assertFalse(self.check(text))
        self.assertTrue(self.check(r"\termuseas{uniformization}{一様化}"))

    def test_percent_in_markdown_does_not_hide_terminology(self):
        self.assertTrue(self.check("50%の一様化を使う。"))
        self.assertTrue(self.check(r"\termuseas{key}{表示} % 一様化"))
        self.assertFalse(self.check("```{=latex}\n% 一様化\n```"))
        self.assertTrue(self.check("```{=latex}\n10\\% 一様化\n```"))
        with (
            patch.object(checker, "_content_text", return_value="short"),
            self.assertRaisesRegex(ValueError, "preserve source offsets"),
        ):
            self.check("longer message")

    def test_raw_tex_and_text_in_mathematics_remain_checked(self):
        self.assertTrue(self.check("```{=latex}\n一様化\n```"))
        self.assertTrue(self.check(r"$\text{問合せ}$"))
        self.assertTrue(self.check(r"10\% 一様化"))

    def test_excluded_spans_do_not_join_into_a_variant(self):
        self.assertFalse(self.check("一様`code`化"))
        self.assertFalse(self.check("一様<!-- comment -->化"))

    def test_distinct_concepts_are_not_globally_required(self):
        self.assertFalse(self.check("始切片，接頭辞，尺度，普遍集合，非痩集合"))

    def test_po_continuations_locations_headers_and_obsolete_messages(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "sample.po"
            path.write_text(
                'msgid ""\nmsgstr "一様化"\n\n'
                '#~ msgid "obsolete"\n#~ msgstr "一様化"\n\n'
                'msgid "source"\nmsgstr ""\n"一様"\n"化"\n',
                encoding="utf-8",
            )
            before = path.read_bytes()
            errors = checker.check_catalogs([path], self.glossary)
            self.assertEqual(len(errors), 1)
            self.assertTrue(errors[0].startswith(f"{path}:8:"))
            self.assertEqual(path.read_bytes(), before)

    def test_real_workflow_terminology_gate_rejects_before_generation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            po = root / "chapter.po"
            po.write_text('msgid "source"\nmsgstr "一様化"\n', encoding="utf-8")
            chapter = workflow.Chapter("chapter.md", root / "en.md", root / "ja.md", po, root / "chapter.pot", "")
            with (
                patch.object(checker, "load_glossary", return_value=self.glossary),
                self.assertRaisesRegex(workflow.TranslationCheckError, "uniformization"),
            ):
                workflow._check_terminology([chapter], root / "glossary.yaml")


class ContextualTerminologyTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.glossary = checker.parse_glossary(
            json.loads((Path(__file__).parent / "fixtures/contextual-glossary.json").read_text(encoding="utf-8"))
        )

    def check(self, source, translated):
        return checker.check_message(PoMessage(source, translated), self.glossary)

    def test_predecessor_is_distinct_from_ordinary_subtraction(self):
        self.assertTrue(self.check("Compose with predecessor.", "1を引く手続き"))
        self.assertFalse(self.check("Subtract one from an integer.", "1を引く手続き"))
        self.assertFalse(
            self.check("The predecessor returns zero at zero.", "直前の自然数を求める項は0に対して0を返す．")
        )

    def test_prefix_pairs_do_not_ban_order_initial_segments(self):
        self.assertTrue(self.check("Apply the test to prefixes.", "始切片の対を検査する．"))
        self.assertFalse(self.check("Compare initial segments of the orders.", "始切片の対を比較する．"))
        self.assertFalse(self.check("Prefixes and initial segments.", "接頭辞の対と順序の始切片"))

    def test_forcing_rules_keep_procedures_and_model_distinctions(self):
        self.assertTrue(self.check("A dense test set.", "稠密テスト集合"))
        self.assertFalse(self.check("A test and a decision set.", "有限検査の手続きと判定集合"))
        self.assertTrue(self.check("The model is externally countable.", "モデルは外部で可算である．"))
        self.assertFalse(
            self.check("Internal and external countability.", "内部で可算であることと外部から見て可算であること")
        )

    def test_schema_instances_and_bounded_formulas(self):
        self.assertTrue(self.check("A Separation instance.", "分出公理の例"))
        self.assertTrue(self.check("Bounded Separation.", "有界分出"))
        self.assertFalse(self.check("An application of Separation.", "分出公理の適用例"))
        self.assertFalse(self.check("Bounded Separation.", "有界論理式による分出公理図式の当該公理"))

    def test_randomness_tests_keep_statistics_out_of_scope(self):
        self.assertTrue(self.check("Martin-Löf randomness tests.", "ランダム性検定"))
        self.assertFalse(self.check("A statistical test.", "統計学の検定"))
        self.assertFalse(self.check("Randomness Tests and Null-Set Avoidance", "ランダム性テストと零集合の回避"))

    def test_forcing_terms_and_canonical_keys(self):
        self.assertTrue(self.check("A meager Borel set", "痩なBorel集合"))
        self.assertTrue(self.check("Use Separation", "Separationにより"))
        self.assertFalse(
            self.check(
                "Use Separation", r"\termdefineas{Separation in generic extensions}{ジェネリック拡大での分出公理}"
            )
        )
        self.assertFalse(self.check("Lebesgue differentiation and density theorems", "Lebesgueの微分定理と密度定理"))

    def test_sections_distinguish_fibres_from_right_inverses(self):
        self.assertTrue(self.check("For points in the same section of A.", "同じ切断の点"))
        self.assertFalse(self.check("For points in the same section of A.", "同じ切片の点"))
        self.assertFalse(self.check("Use the same section of the map.", "写像の同じ切断を使う．"))

    def test_valid_input_names_are_not_effectiveness(self):
        self.assertTrue(self.check("Determine a valid output prefix.", "有効な出力の先頭部分"))
        self.assertFalse(self.check("An effective output method.", "有効な出力の先頭部分"))
        self.assertTrue(self.check("On all valid input names.", "有効な入力名すべてについて"))
        self.assertFalse(self.check("On all valid input names.", "妥当な入力名すべてについて"))
        self.assertFalse(self.check("The method is effective.", "この方法は有効である．"))

    def test_splitting_keeps_partition_and_basis_concepts_distinct(self):
        self.assertTrue(self.check("The Silver splitting lemma.", "Silverの分割補題"))
        self.assertTrue(self.check("Generic-pair splitting.", "ジェネリックな対の分割"))
        self.assertFalse(self.check("A partition construction.", "分割構成"))
        self.assertTrue(self.check("The splitting argument.", "分割の議論"))
        self.assertFalse(self.check("The partition argument.", "分割の議論"))
        self.assertFalse(self.check("Splitting uses a partition.", "分裂には分割を用いる．"))
        self.assertFalse(self.check("A basic open set and a basis.", "基本開集合と開基"))
        self.assertTrue(self.check("HKL coherent finite refinement", "HKLの整合的な有限精密化"))
        self.assertFalse(self.check("Topology refinement", "位相の精密化"))

    def test_fusion_and_inequality_rules_preserve_other_senses(self):
        self.assertTrue(self.check("A strict inequality", "厳密な不等号"))
        self.assertFalse(self.check("A rigorous proof", "厳密な証明"))
        self.assertTrue(self.check("The common right limit", "共通の右極限"))
        self.assertFalse(self.check("A right-hand limit of a function", "関数の右極限"))
        self.assertTrue(self.check("Fusion witness requirements", "証拠要求"))
        self.assertFalse(self.check("Legal evidence requirements", "証拠要求"))
        self.assertTrue(self.check("Axiom schema instances", "公理図式の例"))
        self.assertFalse(self.check("An example of using an axiom", "公理の適用例"))


class GlossarySchemaTest(unittest.TestCase):
    def test_rejects_duplicate_ids_keys_and_conflicting_variants(self):
        mutations = [
            lambda d: d["terms"].append(copy.deepcopy(d["terms"][0])),
            lambda d: d["terms"][1].update(english="uniformization"),
            lambda d: d["terms"][1].update(definition_keys=["uniformization"]),
            lambda d: d["terms"][0].update(avoid=["一意化"]),
            lambda d: d["terms"][0].update(avoid=["指示関数"]),
            lambda d: d["terms"][0].update(avoids=["一様化"]),
            lambda d: d["terms"][0].update(avoid="一様化"),
            lambda d: d["terms"][0].update(source_terms=["source"], avoid=[]),
        ]
        for mutate in mutations:
            data = copy.deepcopy(DATA)
            mutate(data)
            with self.subTest(data=data), self.assertRaises(checker.TerminologyError):
                checker.parse_glossary(data)

    @unittest.skipUnless(
        shutil.which("pandoc") and (REPO_ROOT / "polish-space-ja/l10n/glossary-ja.yaml").is_file(),
        "repository glossary and Pandoc are required for this smoke test",
    )
    def test_loads_repository_glossary_with_existing_pandoc(self):
        glossary = checker.load_glossary(REPO_ROOT / "polish-space-ja/l10n/glossary-ja.yaml")
        self.assertTrue(glossary.rules)

    @unittest.skipUnless(shutil.which("pandoc"), "Pandoc is required for YAML integration")
    def test_yaml_reader_preserves_hyphens_and_apostrophes(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "glossary.yaml"
            data = copy.deepcopy(DATA)
            data["terms"][0]["definition_keys"] = ["Someone's--theorem"]
            # JSON is also valid YAML; Pandoc must not apply smart typography.
            path.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
            glossary = checker.load_glossary(path)
            self.assertEqual(glossary.rules[0].definition_keys, ("Someone's--theorem",))

    @unittest.skipUnless(shutil.which("pandoc"), "Pandoc is required for YAML integration")
    def test_missing_or_invalid_yaml_is_a_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "glossary.yaml"
            with self.assertRaises(OSError):
                checker.load_glossary(path)
            path.write_text("terms: [broken", encoding="utf-8")
            with self.assertRaises(checker.TerminologyError):
                checker.load_glossary(path)


if __name__ == "__main__":
    unittest.main()
