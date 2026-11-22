"""Tests for projecting canonical booklinks onto translated PO messages."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "tools"))

import project_translation_sourcemap as projection


class AtomicMapWriteTest(unittest.TestCase):
    def test_reader_keeps_previous_map_until_complete_replacement(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "map.json"
            path.write_text('{"previous": true}\n', encoding="utf-8")
            path.chmod(0o640)
            result = {"entries": [{"text": "日本語"}]}
            replace = Path.replace

            def check_before_replace(source, target):
                self.assertEqual(json.loads(path.read_text()), {"previous": True})
                self.assertEqual(json.loads(source.read_text()), result)
                return replace(source, target)

            with patch.object(Path, "replace", check_before_replace):
                projection.write_projected_map(path, result)
            self.assertEqual(json.loads(path.read_text()), result)
            self.assertEqual(path.stat().st_mode & 0o777, 0o640)
            self.assertEqual(list(path.parent.iterdir()), [path])

    def test_failed_replacement_preserves_map_and_cleans_temporary_file(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "map.json"
            previous = '{"previous": true}\n'
            path.write_text(previous, encoding="utf-8")
            with (
                patch.object(Path, "replace", side_effect=OSError("publication failed")),
                self.assertRaisesRegex(OSError, "publication failed"),
            ):
                projection.write_projected_map(path, {"entries": []})
            self.assertEqual(path.read_text(), previous)
            self.assertEqual(list(path.parent.iterdir()), [path])


class PoParserTest(unittest.TestCase):
    def test_reads_multiline_singular_messages_and_ignores_header(self):
        content = """msgid ""
msgstr ""
"Language: ja\\n"

msgid ""
"English line\\n"
"continued.\\n"
msgstr ""
"日本語の行\\n"
"続き。\\n"
"""
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "chapter.po"
            path.write_text(content, encoding="utf-8")
            messages = projection.read_po(path)
        self.assertEqual(
            messages,
            [projection.PoMessage("English line\ncontinued.\n", "日本語の行\n続き。\n")],
        )

    def test_fuzzy_messages_are_rejected_and_obsolete_fuzzy_entries_are_ignored(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "chapter.po"
            path.write_text('#, fuzzy\nmsgid "English"\nmsgstr "日本語"\n', encoding="utf-8")
            with self.assertRaisesRegex(projection.ProjectionError, "fuzzy PO entry"):
                projection.read_po(path)
            path.write_text('#~ #, fuzzy\n#~ msgid "Old"\n#~ msgstr "古い"\n\nmsgid "New"\nmsgstr "新しい"\n')
            self.assertEqual(projection.read_po(path), [projection.PoMessage("New", "新しい")])


class ManifestResolutionTest(unittest.TestCase):
    def test_chapters_resolve_from_manifests_outside_the_current_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            source_manifest = root / "english/src/book.json"
            target_manifest = root / "japanese/src/book.json"
            for language, text in (("english", "Same source."), ("japanese", "Same source.")):
                source = root / language / "src/chapter.md"
                source.parent.mkdir(parents=True)
                source.write_text(text)
                source.with_name("book.json").write_text(
                    json.dumps(
                        {
                            "source": f"{language}/src/book.md",
                            "chapters": [f"{language}/src/chapter.md"],
                        }
                    )
                )
            chapters = projection.load_projections(source_manifest, target_manifest, root / "po")
            chapter = chapters[(root / "english/src/chapter.md").resolve()]
            self.assertEqual(chapter.target.resolve(), (root / "japanese/src/chapter.md").resolve())
            self.assertIsNone(chapter.segments)


def chapter_projection(source: str, target: str) -> projection.ChapterProjection:
    segments = projection.po_segments(
        source, target, [projection.PoMessage(source.strip(), target.strip())], Path("chapter.po")
    )
    return projection.ChapterProjection(Path("source.md"), Path("target.md"), source, target, segments)


class MessageAlignmentTest(unittest.TestCase):
    def test_translated_math_prose_keeps_formula_anchors(self):
        source = r"Use $T\text{ is well-founded}$ in §{sec:trees}."
        target = r"§{sec:trees} で $T\text{ は整礎である}$ を用いる．"
        source += " Continue."
        target += "続ける．"
        matched = chapter_projection(source, target)
        self.assertEqual(matched.project_span(0, source.index(" Continue."))[2], "po-sentence")
        mismatched_source = source.replace("$T", "$S")
        mismatched = chapter_projection(mismatched_source, target)
        self.assertEqual(mismatched.project_span(0, mismatched_source.index(" Continue."))[2], "po-message")

    def test_list_indentation_does_not_prevent_alignment(self):
        source = "*   **Term.** English line\n    continued.\n"
        target = "*   **用語。** 日本語の行\n    続き。\n"
        messages = [
            projection.PoMessage(
                "**Term.** English line\ncontinued.\n",
                "**用語。** 日本語の行\n続き。\n",
            )
        ]
        segments = projection.po_segments(source, target, messages, Path("chapter.po"))
        self.assertEqual(len(segments), 1)
        segment = segments[0]
        self.assertEqual(source[segment.source_start : segment.source_end].split()[0], "**Term.**")
        self.assertEqual(target[segment.target_start : segment.target_end].split()[0], "**用語。**")

    def test_projected_span_expands_to_the_whole_translated_message(self):
        chapter = projection.ChapterProjection(
            Path("source.md"),
            Path("target.md"),
            "first sentence. second sentence.",
            "第一文。第二文。",
            [projection.Segment(0, 32, 0, 8)],
        )
        self.assertEqual(chapter.project_span(16, 32), (0, 8, "po-message"))


class StructuralRefinementTest(unittest.TestCase):
    def test_intro_metadata_and_statement_stay_separate_despite_sentence_counts(self):
        source = "Introduction. Another sentence.\n\\begin{mathmeta}\n\\define{X}\n\\end{mathmeta}\n\\begin{definition*}[Name]\nUse $X$.\n\\end{definition*}"
        target = "導入の一文．\n\\begin{mathmeta}\n\\define{X}\n\\end{mathmeta}\n\\begin{definition*}[名前]\n$X$ を用いる．\n\\end{definition*}"
        chapter = chapter_projection(source, target)
        a, b, kind = chapter.project_span(0, len("Introduction. Another sentence."))
        self.assertEqual((target[a:b], kind), ("導入の一文．", "po-structure"))
        start = source.index(r"\begin{definition*}")
        a, b, kind = chapter.project_span(start, len(source))
        self.assertEqual(target[a:b], target[target.index(r"\begin{definition*}") :])
        self.assertEqual(kind, "po-structure")

    def test_adjacent_statement_and_proof_do_not_share_a_projection_band(self):
        source = "\\begin{lemma*}[Name]\nUse $X$.\n\\end{lemma*}\n\\begin{proof}\nCheck $X$.\n\\end{proof}"
        target = "\\begin{lemma*}[名前]\n$X$ を用いる．\n\\end{lemma*}\n\\begin{proof}\n$X$ を確かめる．\n\\end{proof}"
        chapter = chapter_projection(source, target)
        chapter.source = chapter.source.resolve()
        chapter.target = chapter.target.resolve()
        boundary = source.index(r"\begin{proof}")
        original = {
            "entries": [
                {
                    "booklink": {"target": kind},
                    "match": {
                        "status": "matched",
                        "source": str(chapter.source),
                        "startOffset": start,
                        "endOffset": end,
                    },
                }
                for kind, start, end in [("statement", 0, boundary), ("proof", boundary, len(source))]
            ]
        }
        result = projection.project_map(
            original, {chapter.source: chapter}, chapter.source.parent, chapter.target.parent
        )
        statement, proof = [entry["match"] for entry in result["entries"]]
        self.assertLessEqual(statement["endOffset"], proof["startOffset"])
        self.assertEqual(target[proof["startOffset"] : proof["endOffset"]], target[target.index(r"\begin{proof}") :])

    def test_mismatched_structure_or_anchors_keeps_whole_message(self):
        source = "\\begin{lemma*}\nUse $X$. Continue.\n\\end{lemma*}"
        target = "\\begin{lemma*}\n$X$ を用いる．続ける．\n\\end{lemma*}"
        for changed in [target.replace("lemma*", "theorem*"), target.replace("$X$", "$Y$")]:
            with self.subTest(target=changed):
                chapter = chapter_projection(source, changed)
                self.assertEqual(
                    chapter.project_span(source.index("Use"), source.index(" Continue")),
                    (0, len(changed), "po-message"),
                )


class SentenceRefinementTest(unittest.TestCase):
    SOURCE = "The space $X$ is Polish. The set $Y \\IncludedIn X$ is closed.\n"
    TARGET = "空間 $X$ はポーランド空間である．集合 $Y \\IncludedIn X$ は閉である．\n"

    def _chapter(self, source: str, target: str) -> projection.ChapterProjection:
        return chapter_projection(source, target)

    def test_sentence_span_projects_to_the_aligned_target_sentence(self):
        chapter = self._chapter(self.SOURCE, self.TARGET)
        start = self.SOURCE.index("The set")
        end = self.SOURCE.index("closed.") + len("closed.")
        target_start, target_end, kind = chapter.project_span(start, end)
        self.assertEqual(kind, "po-sentence")
        self.assertEqual(self.TARGET[target_start:target_end], "集合 $Y \\IncludedIn X$ は閉である．")

    def test_first_sentence_projects_without_swallowing_the_rest(self):
        chapter = self._chapter(self.SOURCE, self.TARGET)
        target_start, target_end, kind = chapter.project_span(0, len("The space $X$ is Polish."))
        self.assertEqual(kind, "po-sentence")
        self.assertEqual(self.TARGET[target_start:target_end], "空間 $X$ はポーランド空間である．")

    def test_anchor_mismatch_falls_back_to_the_whole_message(self):
        source = "The space $X$ is Polish. The set $Y$ is closed.\n"
        target = "空間 $Y$ はポーランド空間である．集合 $X$ は閉である．\n"
        chapter = self._chapter(source, target)
        start = source.index("The set")
        target_start, target_end, kind = chapter.project_span(start, len(source.strip()))
        self.assertEqual(kind, "po-message")
        self.assertEqual(target[target_start:target_end], target.strip())

    def test_html_comment_is_its_own_segment(self):
        text = "First sentence. <!-- formalization: skip-end -->\nSecond sentence."
        chapter = chapter_projection(text, text)
        for piece in ["First sentence.", "<!-- formalization: skip-end -->", "Second sentence."]:
            start = text.index(piece)
            a, b, kind = chapter.project_span(start, start + len(piece))
            self.assertEqual((text[a:b], kind), (piece, "po-sentence"))

    def test_skip_region_ending_mid_paragraph_projects_to_the_comment_boundary(self):
        # A merged paragraph carries a skip region delimited by inline comments;
        # the projected end must stop at the closing comment, not swallow the
        # following (booklinked) sentence.
        source = (
            "<!-- formalization: skip-begin (remark) -->\n"
            "We skip this. <!-- formalization: skip-end -->\n"
            "The set $Y$ is closed.\n"
        )
        target = (
            "<!-- formalization: skip-begin (remark) -->\n"
            "これは省略する． <!-- formalization: skip-end -->\n"
            "集合 $Y$ は閉である．\n"
        )
        chapter = self._chapter(source, target)
        start = source.index("<!-- formalization: skip-begin")
        end = source.index("skip-end -->") + len("skip-end -->")
        target_start, target_end, kind = chapter.project_span(start, end)
        self.assertEqual(kind, "po-sentence")
        self.assertEqual(
            target[target_start:target_end],
            "<!-- formalization: skip-begin (remark) -->\nこれは省略する． <!-- formalization: skip-end -->",
        )

    def test_reordered_anchors_within_a_sentence_still_refine(self):
        # Natural Japanese word order permutes the formulas of a sentence; the
        # per-sentence anchor comparison is a multiset, so refinement holds.
        source = "The space $X$ is Polish. Tychonoff makes $\\CantorSpace$ compact because $2$ is compact.\n"
        target = "空間 $X$ はポーランド空間である．$2$ がコンパクトなので，チホノフの定理より $\\CantorSpace$ はコンパクトである．\n"
        chapter = self._chapter(source, target)
        start = source.index("Tychonoff")
        target_start, target_end, kind = chapter.project_span(start, len(source.strip()))
        self.assertEqual(kind, "po-sentence")
        self.assertEqual(
            target[target_start:target_end],
            "$2$ がコンパクトなので，チホノフの定理より $\\CantorSpace$ はコンパクトである．",
        )

    def test_sentence_count_mismatch_falls_back_to_the_whole_message(self):
        source = "The space $X$ is Polish. The set $Y$ is closed.\n"
        target = "空間 $X$ はポーランド空間であり，集合 $Y$ は閉である．\n"
        chapter = self._chapter(source, target)
        start = source.index("The set")
        target_start, target_end, kind = chapter.project_span(start, len(source.strip()))
        self.assertEqual(kind, "po-message")
        self.assertEqual(target[target_start:target_end], target.strip())

    def test_math_periods_and_abbreviations_do_not_split_sentences(self):
        text = "Take $d(x, y) = |x - y|$, i.e. the metric on $\\R$. Then $X$ is Polish."
        chapter = chapter_projection(text, text)
        start = text.index("metric")
        a, b, kind = chapter.project_span(start, start + len("metric"))
        self.assertEqual(kind, "po-sentence")
        self.assertEqual(text[a:b], "Take $d(x, y) = |x - y|$, i.e. the metric on $\\R$.")
        start = text.index("Then")
        a, b, kind = chapter.project_span(start, len(text))
        self.assertEqual((text[a:b], kind), ("Then $X$ is Polish.", "po-sentence"))


class SourceMapRewriteTest(unittest.TestCase):
    def _project_ranges(self, ranges, *, kinds=None, exact=False):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name).resolve()
        source = root / "english/src/chapter.md"
        target = root / "japanese/src/chapter.md"
        chapter = projection.ChapterProjection(
            source,
            target,
            "abcdefghijABCDEFGHIJ",
            "日本語。\n訳文。\n",
            None
            if exact
            else [
                projection.Segment(0, 10, 0, 4),
                projection.Segment(10, 20, 5, 8),
            ],
        )
        source_map = {
            "entries": [
                {
                    "lean": {"declName": f"decl{i}"},
                    "booklink": {"target": kinds[i] if kinds else "prose"},
                    "match": {"status": "matched", "source": str(source), "startOffset": start, "endOffset": end},
                }
                for i, (start, end) in enumerate(ranges)
            ]
        }
        result = projection.project_map(source_map, {source: chapter}, source.parent, target.parent)
        return source_map, result

    def test_disjoint_excerpts_widened_by_po_projection_share_one_injection_range(self):
        # The second English excerpt crosses a PO-message boundary. Projection
        # used to produce [0,4] and [0,8], which the injector must reject.
        original, result = self._project_ranges([(0, 5), (5, 15), (15, 20)])
        self.assertEqual([e["lean"]["declName"] for e in result["entries"]], ["decl0", "decl1", "decl2"])
        for entry in result["entries"]:
            match = entry["match"]
            self.assertEqual((match["startOffset"], match["endOffset"]), (0, 8))
            self.assertEqual((match["startLine"], match["endLine"], match["endColumn"]), (1, 2, 3))
            self.assertEqual(match["translationProjection"], "po-shared")
        self.assertEqual(original["entries"][0]["match"]["endOffset"], 5)

    def test_distinct_po_messages_remain_separate(self):
        _, result = self._project_ranges([(0, 10), (10, 20)])
        self.assertEqual(
            [(e["match"]["startOffset"], e["match"]["endOffset"]) for e in result["entries"]], [(0, 4), (5, 8)]
        )

    def test_exact_ranges_are_not_coalesced(self):
        _, result = self._project_ranges([(0, 6), (3, 8)], exact=True)
        self.assertEqual(
            [(e["match"]["startOffset"], e["match"]["endOffset"]) for e in result["entries"]], [(0, 6), (3, 8)]
        )

    def test_proof_and_prose_share_translation_without_losing_lean_targets(self):
        for ranges in [[(0, 5), (5, 9)], [(0, 5), (5, 15)]]:
            with self.subTest(ranges=ranges):
                original, result = self._project_ranges(ranges, kinds=["prose", "proof"])
                entries = result["entries"]
                self.assertEqual([e["booklink"]["target"] for e in entries], ["prose", "proof"])
                self.assertEqual([e["lean"]["declName"] for e in entries], ["decl0", "decl1"])
                self.assertEqual(
                    (entries[0]["match"]["startOffset"], entries[0]["match"]["endOffset"]),
                    (entries[1]["match"]["startOffset"], entries[1]["match"]["endOffset"]),
                )
                self.assertEqual(original["entries"][0]["match"]["endOffset"], 5)

    def test_statement_and_body_targets_are_not_silently_combined(self):
        for body in ["prose", "proof"]:
            with (
                self.subTest(body=body),
                self.assertRaisesRegex(projection.ProjectionError, "mix statements and prose"),
            ):
                self._project_ranges([(0, 5), (5, 15)], kinds=[body, "statement"])

    def test_rewrites_book_and_lean_paths_to_the_translation_project(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            source_project = root / "english"
            target_project = root / "japanese"
            source = source_project / "src" / "book" / "chapter.md"
            target = target_project / "src" / "book" / "chapter.md"
            source.parent.mkdir(parents=True)
            target.parent.mkdir(parents=True)
            source.write_text("English", encoding="utf-8")
            target.write_text("日本語", encoding="utf-8")
            chapter = projection.ChapterProjection(
                source, target, "English", "日本語", [projection.Segment(0, 7, 0, 3)]
            )
            source_map = {
                "root": str(source_project),
                "leanFile": str(source_project / "lean" / "Root.lean"),
                "leanFiles": [str(source_project / "lean" / "Root.lean")],
                "entries": [
                    {
                        "lean": {"source": str(source_project / "lean" / "Chapter.lean")},
                        "match": {"status": "matched", "source": str(source), "startOffset": 0, "endOffset": 7},
                    }
                ],
                "skips": [],
            }
            result = projection.project_map(
                source_map,
                {source.resolve(): chapter},
                source_project,
                target_project,
            )
        self.assertEqual(result["entries"][0]["match"]["source"], str(target.resolve()))
        self.assertTrue(result["entries"][0]["lean"]["source"].endswith("japanese/lean/Chapter.lean"))
        self.assertEqual(result["entries"][0]["match"]["translationProjection"], "po-message")
        self.assertEqual(result["entries"][0]["canonicalMatch"], source_map["entries"][0]["match"])
        self.assertNotIn("canonicalMatch", source_map["entries"][0])

    def test_weak_candidate_uses_japanese_coordinates_without_gaining_confidence(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            source = root / "english/src/chapter.md"
            target = root / "japanese/src/chapter.md"
            chapter = projection.ChapterProjection(
                source, target, "English.", "日本語。", [projection.Segment(0, 8, 0, 4)]
            )
            candidate = {
                "status": "weak",
                "score": 0.7,
                "source": "english/src/chapter.md",
                "startOffset": 0,
                "endOffset": 8,
            }
            result = projection.project_map(
                {"entries": [{"match": candidate}], "skips": []},
                {source.resolve(): chapter},
                root / "english",
                root / "japanese",
            )["entries"][0]
            self.assertEqual(result["match"]["status"], "weak")
            self.assertEqual(result["match"]["score"], 0.7)
            self.assertEqual(result["match"]["source"], str(target))
            self.assertEqual(result["match"]["endOffset"], 4)
            self.assertEqual(result["canonicalMatch"], candidate)


if __name__ == "__main__":
    unittest.main()
