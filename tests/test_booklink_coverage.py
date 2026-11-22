"""Tests for booklink_coverage: the formalization-scope mechanism.

These cover how units resolve to covered / uncovered / partial / exempt:
explicit scope for statement kinds, the author
`formalization:` annotations (single-unit skip/require and skip-begin/skip-end
regions), the rule that explicit skips cannot overlap links, and that
HTML-comment-only blocks (including the annotations themselves) are structural.
Run with `python -m unittest` (stdlib only, no pytest).
"""

import contextlib
import io
import json
import sys
import tempfile
import unittest
from itertools import pairwise
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "tools"))

import booklink_coverage as cov
import booklink_sourcemap as sourcemap
from booklink_fixtures import lean_booklink as _marker


def units(text: str, covered=()):
    """Run units_for_source over an in-memory book source with given covered spans."""
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / "chap.md"
        path.write_text(text, encoding="utf-8")
        return cov.units_for_source(path, list(covered))


def by_label(us, needle):
    return next(u for u in us if u.label and needle in u.label)


class CoveredSpansStatusTest(unittest.TestCase):
    """covered_spans_by_source must count only genuinely resolved booklink
    matches. A `statement` target attaches offsets even when its title resolved
    weakly or not at all; an `unresolved` match must never count as covered."""

    def _spans(self, entries):
        sm = {"entries": entries}
        with mock.patch.object(sourcemap, "build_combined_sourcemap", return_value=sm):
            return cov.covered_spans_by_source(Path("."), [])

    def test_matched_and_weak_count_unresolved_does_not(self):
        spans = self._spans(
            [
                {"match": {"status": "matched", "source": "a.md", "startOffset": 0, "endOffset": 10}},
                {"match": {"status": "weak", "source": "a.md", "startOffset": 20, "endOffset": 30}},
                # Has offsets but did not resolve — must be ignored.
                {"match": {"status": "unresolved", "source": "a.md", "startOffset": 40, "endOffset": 50}},
            ]
        )
        self.assertEqual(spans, {"a.md": [(0, 10), (20, 30)]})

    def test_unresolved_only_retains_source_with_zero_coverage(self):
        spans = self._spans(
            [
                {"match": {"status": "unresolved", "source": "a.md", "startOffset": 0, "endOffset": 9}},
            ]
        )
        self.assertEqual(spans, {"a.md": []})

    def test_cli_reports_a_chapter_when_all_statement_selectors_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "book/src/chap.md"
            source.parent.mkdir(parents=True)
            source.write_text("A real mathematical claim without a matching statement title.\n")
            lean = root / "book/lean/Main.lean"
            lean.parent.mkdir(parents=True)
            lean.write_text(
                "/-@ booklink:\n  source: chap.md\n  target: statement\n  title: Missing\n-/\n"
                "theorem proof : True := by trivial\n"
            )
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                code = cov.main(["coverage", str(lean), "--root", str(root), "--json", "--strict"])
            report = json.loads(output.getvalue())
            self.assertEqual(code, 1)
            self.assertEqual(len(report), 1)
            self.assertEqual(Path(report[0]["source"]).resolve(), source.resolve())
            self.assertEqual(report[0]["prose"]["uncovered"], 1)

    def test_statement_and_prose_in_one_block_are_disjoint_and_complete(self):
        text = "Introductory claim.\n\\begin{lemma*}[Lemma]\nA statement.\n\\end{lemma*}\nTrailing claim.\n"
        start, end = text.index("\\begin"), text.index("\\end{lemma*}") + len("\\end{lemma*}")
        result = units(text, [(start, end)])
        self.assertEqual([unit.kind for unit in result], ["prose", "statement", "prose"])
        self.assertEqual([unit.status for unit in result], ["uncovered", "covered", "uncovered"])
        self.assertTrue(all(first.end_offset <= second.start_offset for first, second in pairwise(result)))
        self.assertEqual(sum(unit.end_offset - unit.start_offset for unit in result), len(text))


# A statement whose unmatched body carries real content, so it counts as a gap.
FACT = (
    "\\begin{fact*}[Some background]\n"
    "This is a recalled background fact cited from the literature, stated here\n"
    "for reference.\n"
    "\\end{fact*}\n"
)
LEMMA = (
    "\\begin{lemma*}[Worth proving]\n"
    "Here is a genuine lemma whose statement and proof the chapter establishes\n"
    "and which later sections rely on, so it must be formalized.\n"
    "\\end{lemma*}\n"
)


class DefaultExemptKindTest(unittest.TestCase):
    def test_fact_requires_explicit_scope_decision(self):
        u = by_label(units(FACT), "fact")
        self.assertEqual(u.status, "uncovered")
        self.assertIsNone(u.exempt_reason)

    def test_lemma_is_not_exempt(self):
        u = by_label(units(LEMMA), "lemma")
        self.assertEqual(u.status, "uncovered")
        self.assertIsNone(u.exempt_reason)

    def test_booklink_anchor_outranks_exemption(self):
        # A fully covered fact* stays "covered", not "exempt".
        us = units(FACT, covered=[(0, len(FACT))])
        u = by_label(us, "fact")
        self.assertEqual(u.status, "covered")
        self.assertIsNone(u.exempt_reason)


class AnnotationTest(unittest.TestCase):
    def test_require_forces_default_exempt_kind_in_scope(self):
        text = "<!-- formalization: require -->\n" + FACT
        u = by_label(units(text), "fact")
        self.assertEqual(u.status, "uncovered")

    def test_skip_exempts_following_lemma(self):
        text = "<!-- formalization: skip (cited to Kechris) -->\n" + LEMMA
        u = by_label(units(text), "lemma")
        self.assertEqual(u.status, "exempt")
        self.assertEqual(u.exempt_reason, "cited to Kechris")

    def test_skip_only_attaches_to_immediately_following_unit(self):
        # A real paragraph sits between the annotation and the lemma, so the
        # skip does not reach the lemma.
        prose = "A substantive intervening paragraph that is itself a unit of prose here.\n"
        text = "<!-- formalization: skip -->\n\n" + prose + "\n" + LEMMA
        u = by_label(units(text), "lemma")
        self.assertEqual(u.status, "uncovered")

    def test_skip_leading_comment_in_same_block_exempts_prose(self):
        # The natural authoring form: the comment sits on the line directly above
        # the prose with no blank line, so they share one paragraph block. The
        # leading skip must still exempt that block.
        text = (
            "<!-- formalization: skip (motivation) -->\n"
            "This motivational paragraph is long enough to be a real prose unit on its own.\n"
        )
        us = units(text)
        prose = next(u for u in us if u.kind == "prose" and "motivational paragraph" in u.snippet)
        self.assertEqual(prose.status, "exempt")
        self.assertEqual(prose.exempt_reason, "motivation")

    def test_skip_region_exempts_enclosed_prose(self):
        intro = "This motivational overview paragraph is long enough to be a real prose unit on its own.\n"
        text = (
            "<!-- formalization: skip-begin (chapter overview) -->\n\n"
            + intro
            + "\n<!-- formalization: skip-end -->\n\n"
            + LEMMA
        )
        us = units(text)
        prose = next(u for u in us if u.kind == "prose" and "motivational overview" in u.snippet)
        self.assertEqual(prose.status, "exempt")
        self.assertEqual(prose.exempt_reason, "chapter overview")
        # The lemma after skip-end is unaffected.
        self.assertEqual(by_label(us, "lemma").status, "uncovered")

    def test_annotation_comment_block_is_structural(self):
        text = "<!-- formalization: skip-begin (x) -->\n\nsome prose unit body here long enough to matter.\n\n<!-- formalization: skip-end -->\n"
        us = units(text)
        # The comment-only blocks must not surface as their own uncovered prose.
        comment_units = [u for u in us if u.kind == "prose" and "formalization:" in u.snippet]
        self.assertTrue(all(u.structural for u in comment_units))

    def test_bare_proof_delimiter_block_is_structural(self):
        # A proof anchored as inside-environment pieces leaves the bare
        # \begin{proof} / \end{proof} delimiters unhighlighted; on their own they
        # are not formalizable prose and must not be flagged as gaps.
        self.assertTrue(cov.is_structural("\\begin{proof}[Proof]"))
        self.assertTrue(cov.is_structural("\\end{proof}"))
        # A delimiter line followed by real prose in the same block is NOT
        # structural — that proof body is genuine content to cover.
        self.assertFalse(cov.is_structural("\\begin{proof}[Proof]\nThe real argument goes here and is long."))

    def test_mathmeta_payload_is_structural_but_adjacent_prose_is_not(self):
        metadata = "\\begin{mathmeta}\n\\vars{x,y}\n\\type{x}{X}\n\\end{mathmeta}"
        self.assertTrue(cov.is_structural(metadata))
        self.assertFalse(cov.is_structural(metadata + "\nThis space has a countable basis."))

    def test_layout_commands_are_structural_but_do_not_hide_prose(self):
        for layout in (
            "\\begingroup\\small",
            "\\endgroup",
            "\\cleardoublepage\n\\phantomsection\n\\addcontentsline{toc}{chapter}{Index}\n\\printindex",
        ):
            self.assertTrue(cov.is_structural(layout))
            self.assertFalse(cov.is_structural(layout + "\nThis space has a countable basis."))


class SubstantiveGapTest(unittest.TestCase):
    """With the old --min-gap threshold gone, any uncovered run carrying real
    content is reported, while pure whitespace/markup runs between adjacent
    excerpts are not."""

    def test_dropped_leading_word_is_a_gap(self):
        # An excerpt anchors all but the leading "The"; that orphan word is now a
        # reported gap rather than being swallowed for being short.
        text = "The higher-dimensional cases use the Euclidean metric here as well.\n"
        start = text.index("higher")
        prose = next(u for u in units(text, covered=[(start, len(text))]) if u.kind == "prose")
        self.assertEqual(prose.status, "partial")
        self.assertEqual([g.text for g in prose.gaps], ["The"])

    def test_list_marker_between_anchors_is_not_a_gap(self):
        # The "*" bullet markers and whitespace left between two adjacent excerpts
        # in one list block carry no content, so the block stays covered.
        s1, s2 = "First anchored sentence sits right here.", "Second anchored sentence sits right here."
        text = f"*   {s1}\n*   {s2}\n"
        c1 = text.index(s1)
        c2 = text.index(s2)
        covered = [(c1, c1 + len(s1)), (c2, c2 + len(s2))]
        prose = next(u for u in units(text, covered=covered) if u.kind == "prose")
        self.assertEqual(prose.status, "covered")

    def test_is_substantive_gap_helper(self):
        # Real dropped content.
        self.assertTrue(cov.is_substantive_gap("The"))
        self.assertTrue(cov.is_substantive_gap(" $\\QQ^n$ "))
        # Whitespace / punctuation only.
        self.assertFalse(cov.is_substantive_gap("   "))
        self.assertFalse(cov.is_substantive_gap(". "))
        # List markers (Markdown bullet and ordered) and LaTeX delimiters.
        self.assertFalse(cov.is_substantive_gap("\n*   "))
        self.assertFalse(cov.is_substantive_gap("2.  "))
        self.assertFalse(cov.is_substantive_gap("\\end{proof}"))
        self.assertFalse(cov.is_substantive_gap("\\begin{proof}[Proof]"))
        self.assertFalse(cov.is_substantive_gap("\\begin{enumerate}"))
        self.assertFalse(cov.is_substantive_gap("\\item "))


class ValidationTest(unittest.TestCase):
    def test_unknown_directive_raises(self):
        with self.assertRaises(ValueError):
            units("<!-- formalization: bogus -->\n" + LEMMA)

    def test_unclosed_region_raises(self):
        with self.assertRaises(ValueError):
            units("<!-- formalization: skip-begin -->\n" + LEMMA)

    def test_skip_end_without_begin_raises(self):
        with self.assertRaises(ValueError):
            units("<!-- formalization: skip-end -->\n" + LEMMA)

    def test_bare_skip_block_with_anchor_raises(self):
        # A bare `skip` is shorthand for a one-block region, so an anchor landing
        # in the block it exempts is a contradiction and must error, just like a
        # skip-begin/skip-end region — not silently let the anchor win.
        text = "<!-- formalization: skip (motivation) -->\n" + LEMMA
        with self.assertRaises(ValueError):
            units(text, covered=[(0, len(text))])

    def test_bare_skip_block_without_anchor_is_fine(self):
        # No anchor inside the skipped block: still exempt, no error.
        text = "<!-- formalization: skip (cited to Kechris) -->\n" + LEMMA
        u = by_label(units(text), "lemma")
        self.assertEqual(u.status, "exempt")

    def test_skip_region_with_anchor_raises(self):
        intro = "This motivational overview paragraph is long enough to be a real prose unit on its own.\n"
        text = "<!-- formalization: skip-begin (overview) -->\n\n" + intro + "\n<!-- formalization: skip-end -->\n"
        start = text.index("This motivational")
        with self.assertRaises(ValueError):
            units(text, covered=[(start, start + 30)])

    def test_skip_before_environment_shades_later_anchor_raises(self):
        # A bare skip placed right before \begin{proof} shades the WHOLE proof
        # (the sourcemap's env rule), so an anchor in a later block of the proof
        # must be caught even though the paragraph-block check treats that block as
        # separate and in scope. This is the gate/shading divergence guard.
        text = (
            "<!-- formalization: skip (floor defs) -->\n"
            "\\begin{proof}\n"
            "Standard floor and fractional-part definitions, long enough to be a real block.\n"
            "\n"
            "A later proof paragraph that is genuinely formalized and anchored just below.\n"
            "\\end{proof}\n"
        )
        start = text.index("A later proof paragraph")
        with self.assertRaises(ValueError):
            units(text, covered=[(start, start + 45)])


def _check_lean(*lines: str):
    """Run check_decl_target_multiplicity over an in-memory Lean file."""
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / "Chap.lean"
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        cov.check_decl_target_multiplicity([path])


class DeclTargetMultiplicityTests(unittest.TestCase):
    def test_shared_proof_counts_each_source_passage(self):
        first = "The first argument follows by induction on the given natural number."
        second = "The second argument applies the same induction to the restricted family."
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            lean = root / "book/lean/Chap.lean"
            source = root / "book/src/chap.md"
            lean.parent.mkdir(parents=True)
            source.parent.mkdir(parents=True)
            source.write_text(f"{first}\n\n{second}\n", encoding="utf-8")
            lean.write_text(
                "\n".join(
                    [
                        _marker("proof", excerpt=first),
                        _marker("proof", excerpt=second),
                        "theorem foo : True := by trivial",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            cov.check_decl_target_multiplicity([lean])
            spans = cov.covered_spans_by_source(root, [lean])
            paragraphs = [u for u in cov.units_for_source(source, spans[str(source)]) if not u.structural]
            self.assertEqual(len(paragraphs), 2)
            self.assertEqual([u.status for u in paragraphs], ["covered", "covered"])

    def test_statement_plus_proof_is_allowed(self):
        _check_lean(
            _marker("statement"),
            _marker("proof", excerpt="the proof body"),
            "theorem foo : True := by trivial",
        )

    def test_duplicate_statement_raises(self):
        with self.assertRaises(ValueError):
            _check_lean(
                _marker("statement"),
                _marker("statement"),
                "theorem foo : True := by trivial",
            )

    def test_distinct_statement_excerpts_share_a_declaration(self):
        _check_lean(
            _marker("statement", excerpt="First conclusion."),
            _marker("statement", excerpt="Second conclusion."),
            "theorem foo : True := by trivial",
        )

    def test_duplicate_statement_excerpt_raises(self):
        with self.assertRaises(ValueError):
            _check_lean(
                _marker("statement", excerpt="Same conclusion."),
                _marker("statement", excerpt="Same   conclusion."),
                "theorem foo : True := by trivial",
            )

    def test_duplicate_proof_raises(self):
        with self.assertRaises(ValueError):
            _check_lean(
                _marker("proof", excerpt="a proof"),
                _marker("proof", excerpt="a   proof"),
                "theorem foo : True := by trivial",
            )

    def test_distinct_proof_passages_share_a_declaration(self):
        _check_lean(
            _marker("proof", excerpt="first induction case"),
            _marker("proof", excerpt="second induction case"),
            "theorem foo : True := by trivial",
        )

    def test_same_statement_in_different_chapters_is_allowed(self):
        _check_lean(
            _marker("statement", source="chapter.md", title="Main theorem"),
            _marker("statement", source="appendix.md", title="Main theorem"),
            "theorem foo : True := by trivial",
        )

    def test_distinct_statement_titles_are_allowed(self):
        _check_lean(
            _marker("statement", title="Uniform theorem"),
            _marker("statement", title="Special case"),
            "theorem foo : True := by trivial",
        )

    def test_duplicate_prose_is_allowed(self):
        # One declaration may anchor several prose passages (real usage in
        # BorelStructure.lean), so duplicate `prose` must not be flagged.
        _check_lean(
            _marker("prose", excerpt="first passage"),
            _marker("prose", excerpt="second passage"),
            "theorem foo : True := by trivial",
        )

    def test_same_target_on_different_decls_is_allowed(self):
        _check_lean(
            _marker("statement"),
            "theorem foo : True := by trivial",
            "",
            _marker("statement"),
            "theorem bar : True := by trivial",
        )


class MixedScopeTest(unittest.TestCase):
    def test_partial_skip_does_not_hide_local_claim(self):
        text = (
            "\\begin{theorem*}\n"
            "<!-- formalization: skip-begin (external input) -->\n"
            "External claim.\n<!-- formalization: skip-end -->\n"
            "Local consequence.\n\\end{theorem*}\n"
        )
        u = by_label(units(text), "theorem")
        self.assertEqual(u.status, "uncovered")
        a = text.index("Local consequence.")
        u = by_label(units(text, [(a, a + len("Local consequence."))]), "theorem")
        self.assertEqual(u.status, "covered")

    def test_partial_skip_leaves_other_unlinked_claims_visible(self):
        text = (
            "Local first.\n<!-- formalization: skip-begin (external) -->\n"
            "External.\n<!-- formalization: skip-end -->\nLocal last.\n"
        )
        u = next(u for u in units(text, [(0, len("Local first."))]) if not u.structural)
        self.assertEqual(u.status, "partial")
        self.assertTrue(any("Local last" in g.text for g in u.gaps))

    def test_structural_roadmap_and_layout_delimiters(self):
        text = (
            "<!-- formalization: structural (proof roadmap) -->\n"
            "We first give the construction and then prove uniqueness.\n\n"
            "\\begin{samepage}\n\n\\end{samepage}\n"
        )
        self.assertTrue(all(u.structural for u in units(text)))

    def test_index_only_commands_are_not_gaps(self):
        self.assertFalse(cov.is_substantive_gap(r"\end{proof}\termref{absoluteness}"))
        self.assertTrue(cov.is_substantive_gap(r"\termuse{absoluteness}"))

    def test_metadata_is_not_a_gap(self):
        self.assertFalse(
            cov.is_substantive_gap("<!-- formalization: require -->\n\\begin{mathmeta}\n\\define{Foo}\n\\end{mathmeta}")
        )


if __name__ == "__main__":
    unittest.main()
