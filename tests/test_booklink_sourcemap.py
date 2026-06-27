"""Tests for booklink_sourcemap: owner-relative source resolution and matching.

These cover `book_src_root` (the `<book>/lean -> <book>/src` owner derivation),
`discover_booklinks` reconstruction, and `build_sourcemap` end-to-end prose
matching — including that an excerpt reaching its Lean file through a symlink
keeps a book-local (lexical, not symlink-resolved) emitted source path. Run with
`python -m unittest` (stdlib only, no pytest).
"""

import os
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO_ROOT, "tools"))

import booklink_sourcemap as bsm  # noqa: E402


LEAN_MARKER = """\
import Mathlib

/-@ booklink:
  source: chap/sec.md
  target: prose
  excerpt: |
    The space $X$ is Polish.
-/
theorem sec_polish : True := trivial
"""

SOURCE_MD = "Intro paragraph.\n\nThe space $X$ is Polish.\n\nMore text.\n"


def make_book(root: Path, book: str) -> Path:
    """Create `<root>/<book>/{src/chap/sec.md, lean/MyBook/Sec.lean}`; return the Lean file."""
    (root / book / "src" / "chap").mkdir(parents=True)
    (root / book / "src" / "chap" / "sec.md").write_text(SOURCE_MD, encoding="utf-8")
    lean = root / book / "lean" / "MyBook" / "Sec.lean"
    lean.parent.mkdir(parents=True)
    lean.write_text(LEAN_MARKER, encoding="utf-8")
    return lean


class BookSrcRootTests(unittest.TestCase):
    def test_relative_path(self):
        self.assertEqual(
            bsm.book_src_root("polish-space/lean/PolishSpaceBook/X.lean"),
            "polish-space/src",
        )

    def test_absolute_path_uses_owner_component(self):
        self.assertEqual(
            bsm.book_src_root("/abs/here/polish-space-ch1/lean/Pkg/X.lean"),
            "polish-space-ch1/src",
        )

    def test_not_under_lean_raises(self):
        with self.assertRaises(ValueError):
            bsm.book_src_root("polish-space/src/foo.md")


class DiscoverBooklinksTests(unittest.TestCase):
    def test_reconstructs_owner_relative_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            # book_src_root extracts just the owner component, so an absolute
            # Lean path still reconstructs a repo-relative <book>/src source.
            lean = make_book(Path(tmp), "mybook")
            found = bsm.discover_booklinks([lean])
            self.assertEqual(len(found), 1)
            _lean, sources = found[0]
            self.assertEqual(sources, ["mybook/src/chap/sec.md"])


class BuildSourcemapTests(unittest.TestCase):
    def test_prose_match_is_book_local(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            lean = make_book(root, "mybook")
            sm = bsm.build_sourcemap(root, lean)
            self.assertEqual(sm["counts"], {"matched": 1})
            entry = sm["entries"][0]
            self.assertEqual(entry["booklink"]["source"], "chap/sec.md")
            self.assertEqual(entry["match"]["status"], "matched")
            self.assertEqual(
                entry["match"]["source"],
                str(root / "mybook" / "src" / "chap" / "sec.md"),
            )

    def test_excerpt_matches_across_reflowed_whitespace(self):
        # The excerpt is one line; the source wraps the same sentence across a
        # line break with indentation. A byte-exact compare would miss it, but the
        # whitespace-insensitive matcher resolves it, and the returned offsets
        # still bracket the exact source span.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            (root / "src" / "chap").mkdir(parents=True)
            wrapped = "Intro.\n\nThe space\n    $X$ is\n    Polish.\n\nEnd.\n"
            (root / "src" / "chap" / "sec.md").write_text(wrapped, encoding="utf-8")
            match = bsm.find_prose_match(root / "src" / "chap" / "sec.md", "The space $X$ is Polish.")
            self.assertEqual(match["status"], "matched")
            span = wrapped[match["startOffset"] : match["endOffset"]]
            self.assertEqual(span, "The space\n    $X$ is\n    Polish.")

    def test_excerpt_symlink_keeps_book_local_lexical_path(self):
        # An excerpt reaches its Lean file and source through symlinks into an
        # owner book; the emitted source must stay the book-local lexical path,
        # not the symlink-resolved owner path (this is what removed VIEW_PREFIX).
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            make_book(root, "owner")
            excerpt = root / "excerpt"
            excerpt.mkdir()
            (excerpt / "lean").symlink_to(root / "owner" / "lean")
            (excerpt / "src").symlink_to(root / "owner" / "src")
            lean = excerpt / "lean" / "MyBook" / "Sec.lean"
            sm = bsm.build_sourcemap(root, lean)
            entry = sm["entries"][0]
            self.assertEqual(entry["match"]["status"], "matched")
            self.assertEqual(
                entry["match"]["source"],
                str(root / "excerpt" / "src" / "chap" / "sec.md"),
            )


class ParseMarkerBodyTests(unittest.TestCase):
    def test_scalar_keys_strip_quotes(self):
        data = bsm.parse_marker_body(["  source: chap/sec.md", '  target: "prose"'])
        self.assertEqual(data, {"source": "chap/sec.md", "target": "prose"})

    def test_literal_block_dedents_and_keeps_internal_blank_lines(self):
        data = bsm.parse_marker_body(
            [
                "  excerpt: |",
                "    line one",
                "",
                "    line two",
                "  target: prose",
            ]
        )
        # The block scalar is dedented to its first non-blank line's indent, keeps
        # the interior blank, and ends at the next sibling-or-shallower key.
        self.assertEqual(data["excerpt"], "line one\n\nline two")
        self.assertEqual(data["target"], "prose")

    def test_unparseable_lines_are_skipped(self):
        data = bsm.parse_marker_body(["not a key", "  source: x.md"])
        self.assertEqual(data, {"source": "x.md"})


class FindDeclTests(unittest.TestCase):
    def test_plain_theorem(self):
        kind, name, line, _end = bsm.find_next_decl(["theorem foo : True := trivial"], 0)
        self.assertEqual((kind, name, line), ("theorem", "foo", 1))

    def test_attribute_and_modifier_prefixes(self):
        kind, name, _line, _end = bsm.find_next_decl(["@[simp] private noncomputable def bar := 1"], 0)
        self.assertEqual((kind, name), ("def", "bar"))

    def test_no_decl_returns_all_none(self):
        self.assertEqual(bsm.find_next_decl(["-- a comment", ""], 0), (None, None, None, None))

    def test_decl_end_stops_at_blank_after_body(self):
        lines = ["theorem foo : True :=", "  trivial", "", "theorem bar := trivial"]
        # Body covers the proof line; the run ends at the blank before `bar`.
        self.assertEqual(bsm.find_decl_end_line(lines, 0), 2)


class ParseLeanMarkersTests(unittest.TestCase):
    def test_extracts_marker_data_and_following_decl(self):
        with tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp) / "Sec.lean"
            lean.write_text(LEAN_MARKER, encoding="utf-8")
            markers = bsm.parse_lean_markers(lean)
            self.assertEqual(len(markers), 1)
            marker = markers[0]
            self.assertEqual(marker.data["source"], "chap/sec.md")
            self.assertEqual(marker.data["target"], "prose")
            self.assertEqual(marker.data["excerpt"], "The space $X$ is Polish.")
            self.assertEqual(marker.decl_kind, "theorem")
            self.assertEqual(marker.decl_name, "sec_polish")

    def test_unclosed_marker_raises(self):
        with tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp) / "Bad.lean"
            lean.write_text("/-@ booklink:\n  source: x.md\n", encoding="utf-8")
            with self.assertRaises(ValueError):
                bsm.parse_lean_markers(lean)


class ParseSkipSpansTests(unittest.TestCase):
    def test_region_block_and_reasons(self):
        md = (
            "<!-- formalization: skip-begin (region reason) -->\n"
            "Region body line one.\n"
            "Region body line two.\n"
            "<!-- formalization: skip-end -->\n"
            "\n"
            "Real content here.\n"
            "\n"
            "<!-- formalization: skip (block reason) -->\n"
            "Skipped paragraph one.\n"
            "Skipped paragraph two.\n"
            "\n"
            "Following kept paragraph.\n"
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "chap.md"
            path.write_text(md, encoding="utf-8")
            spans = bsm.parse_skip_spans(path)
            self.assertEqual([s["kind"] for s in spans], ["region", "block"])
            self.assertEqual(spans[0]["reason"], "region reason")
            self.assertEqual(spans[1]["reason"], "block reason")
            # The region span runs from the begin comment through the end comment.
            self.assertEqual(md[spans[0]["startOffset"] : spans[0]["startOffset"] + 4], "<!--")
            self.assertTrue(md[: spans[0]["endOffset"]].rstrip().endswith("-->"))
            # The block span ends at the blank line after the governed paragraph,
            # so "Following kept paragraph." is not covered.
            self.assertNotIn("Following kept", md[spans[1]["startOffset"] : spans[1]["endOffset"]])
            self.assertIn("Skipped paragraph two.", md[spans[1]["startOffset"] : spans[1]["endOffset"]])

    def test_block_governs_environment(self):
        md = (
            "<!-- formalization: skip (env reason) -->\n"
            "\\begin{remark*}\n"
            "Inside the remark.\n"
            "\\end{remark*}\n"
            "\n"
            "After.\n"
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "chap.md"
            path.write_text(md, encoding="utf-8")
            spans = bsm.parse_skip_spans(path)
            self.assertEqual(len(spans), 1)
            covered = md[spans[0]["startOffset"] : spans[0]["endOffset"]]
            self.assertIn("\\end{remark*}", covered)
            self.assertNotIn("After.", covered)

    def test_reason_keeps_inner_parentheses(self):
        md = "<!-- formalization: skip (cites (Brouwer) results) -->\nBody.\n"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "chap.md"
            path.write_text(md, encoding="utf-8")
            spans = bsm.parse_skip_spans(path)
            self.assertEqual(spans[0]["reason"], "cites (Brouwer) results")


class TextNormalizationTests(unittest.TestCase):
    def test_strip_latex_macros_unwraps_term_macros(self):
        self.assertEqual(
            bsm.strip_latex_macros(r"a \termdefineas{polish space}{Polish} b"),
            "a Polish b",
        )
        self.assertEqual(bsm.strip_latex_macros(r"\termuse{meager set}"), "meager set")

    def test_normalize_collapses_whitespace_and_casefolds(self):
        self.assertEqual(bsm.normalize("  The  SPACE\n is\tPolish  "), "the space is polish")


if __name__ == "__main__":
    unittest.main()
