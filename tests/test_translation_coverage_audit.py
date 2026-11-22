"""Canonical gaps must survive coarse Japanese navigation projections."""

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))

import audit_translation_coverage as audit
import project_translation_sourcemap as projection


class TranslationCoverageAuditTest(unittest.TestCase):
    def check_chapter(self, source, target, covered):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.md"
            path.write_text(source)
            chapter = projection.ChapterProjection(
                path,
                Path(directory) / "ja.md",
                source,
                target,
                [projection.Segment(0, len(source), 0, len(target))],
            )
            entries = [{"match": {"status": "matched", "startOffset": a, "endOffset": b}} for a, b in covered]
            return audit.audit_chapter(chapter, entries)

    def test_partly_linked_proof_keeps_gap_even_when_po_band_covers_everything(self):
        source = "\\begin{proof}\nFirst deduction. Missing second deduction.\n\\end{proof}\n"
        target = "\\begin{proof}\n第1の推論と第2の推論．\n\\end{proof}\n"
        start = source.index("First")
        end = source.index("Missing")
        result = self.check_chapter(source, target, [(start, end)])
        unit = next(u for u in result["units"] if u["kind"] == "proof")
        self.assertEqual(unit["status"], "partial")
        self.assertTrue(any("Missing second deduction" in g["text"] for g in unit["gaps"]))
        self.assertEqual(unit["translation"]["endOffset"], len(target))
        self.assertEqual(result["alignmentIssues"], [])

    def test_ordinary_prose_retains_partial_gap_in_translation(self):
        source = "Definition. Such f induces an injection.\n"
        target = "定義．この写像は単射を誘導する．\n"
        result = self.check_chapter(source, target, [(0, len("Definition."))])
        self.assertEqual(len(result["units"]), 1)
        unit = result["units"][0]
        self.assertEqual(unit["kind"], "prose")
        self.assertEqual(unit["status"], "partial")
        self.assertIn("Such f", unit["gaps"][0]["text"])

    def test_unlinked_proof_remains_uncovered(self):
        source = "\\begin{proof}\nAn unlinked argument.\n\\end{proof}\n"
        result = self.check_chapter(source, source, [])
        unit = next(u for u in result["units"] if u["kind"] == "proof")
        self.assertEqual(unit["status"], "uncovered")
        self.assertTrue(unit["gaps"])

    def test_two_distinct_proofs_cannot_share_one_translation(self):
        source = "\\begin{proof}\nFirst proof.\n\\end{proof}\n\n\\begin{proof}\nSecond proof.\n\\end{proof}\n"
        target = "\\begin{proof}\n結合してしまった証明．\n\\end{proof}\n"
        result = self.check_chapter(source, target, [(0, len(source))])
        self.assertEqual(len(result["proofAlignment"]), 2)
        self.assertTrue(any("share" in i["reason"] for i in result["alignmentIssues"]))

    def test_target_range_crossing_two_proofs_is_reported(self):
        source = "\\begin{proof}\nOne proof.\n\\end{proof}\n"
        target = "\\begin{proof}\n証明1．\n\\end{proof}\n\n\\begin{proof}\n証明2．\n\\end{proof}\n"
        result = self.check_chapter(source, target, [(0, len(source))])
        self.assertTrue(any("exactly one" in i["reason"] for i in result["alignmentIssues"]))


if __name__ == "__main__":
    unittest.main()
