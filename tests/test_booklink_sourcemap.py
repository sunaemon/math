"""Tests for booklink_sourcemap: owner-relative source resolution and matching.

These cover `book_src_root` (the `<book>/lean -> <book>/src` owner derivation),
`discover_booklinks` reconstruction, and `build_sourcemap` end-to-end prose
matching — including that an excerpt reaching its Lean file through a symlink
keeps a book-local (lexical, not symlink-resolved) emitted source path. Run with
`python -m unittest` (stdlib only, no pytest).
"""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "tools"))

import booklink_sourcemap as bsm
from booklink_fixtures import lean_booklink

LEAN_MARKER = (
    "import Mathlib\n\n"
    + lean_booklink("prose", source="chap/sec.md", excerpt="The space $X$ is Polish.")
    + "\ntheorem sec_polish : True := trivial\n"
)

SOURCE_MD = "Intro paragraph.\n\nThe space $X$ is Polish.\n\nMore text.\n"


def make_book(root: Path, book: str) -> Path:
    """Create `<root>/<book>/{src/chap/sec.md, lean/MyBook/Sec.lean}`; return the Lean file."""
    (root / book / "src" / "chap").mkdir(parents=True)
    (root / book / "src" / "chap" / "sec.md").write_text(SOURCE_MD, encoding="utf-8")
    lean = root / book / "lean" / "MyBook" / "Sec.lean"
    lean.parent.mkdir(parents=True)
    lean.write_text(LEAN_MARKER, encoding="utf-8")
    return lean


class StatementTitleTests(unittest.TestCase):
    def test_wrapped_title_with_bracketed_macro_argument(self):
        source = (
            "Intro.\n\n"
            "\\begin{theorem*}[\\termdefineas{interval theorem}{A theorem\n"
            "on $[0,1]$}]\n"
            "The assertion.\n"
            "\\end{theorem*}\n"
            "\\begin{lemma*}[Another result]\n"
            "Another assertion.\n"
            "\\end{lemma*}\n"
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "chapter.md"
            path.write_text(source)
            statements = bsm.parse_book_statements(path)
        self.assertEqual(len(statements), 2)
        self.assertEqual(bsm.normalize(statements[0].title), "a theorem on $[0,1]$")
        self.assertEqual(statements[0].start_line, 3)
        self.assertEqual(statements[0].end_line, 6)
        self.assertEqual(statements[0].start_offset, source.index("\\begin{theorem*}"))
        self.assertEqual(statements[1].title, "Another result")


class StatementExcerptTests(unittest.TestCase):
    def match(self, source, selector):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lean = make_book(root, "mybook")
            (root / "mybook/src/chap/sec.md").write_text(source)
            lean.write_text(
                "/-@ booklink:\n  source: chap/sec.md\n  target: statement\n"
                + selector
                + "-/\ntheorem existing : True := trivial\n"
            )
            return bsm.build_sourcemap(root, lean)["entries"][0]["match"]

    def test_excerpt_selects_named_or_unnamed_statement_not_first_unnamed(self):
        source = (
            "\\begin{theorem*}\nUnrelated.\n\\end{theorem*}\n\n"
            "\\begin{lemma*}[Intended]\nThe intended\nclaim.\n\\end{lemma*}\n"
        )
        result = self.match(source, "  excerpt: |\n    The intended claim.\n")
        self.assertEqual(result["status"], "matched")
        self.assertEqual(result["startLine"], 5)
        self.assertEqual(result["endLine"], 8)

    def test_missing_excerpt_does_not_fall_back_to_unnamed(self):
        result = self.match("\\begin{theorem*} Unrelated.\\end{theorem*}\n", "  excerpt: Missing claim.\n")
        self.assertEqual(result["status"], "unresolved")

    def test_ambiguous_excerpt_is_rejected_unless_kind_disambiguates(self):
        source = "\\begin{theorem*} Shared claim.\\end{theorem*}\n\\begin{lemma*} Shared claim.\\end{lemma*}\n"
        self.assertEqual(self.match(source, "  excerpt: Shared claim.\n")["status"], "unresolved")
        result = self.match(source, "  kind: lemma\n  excerpt: Shared claim.\n")
        self.assertEqual(result["status"], "matched")
        self.assertEqual(result["kind"], "lemma")

    def test_explicit_title_remains_authoritative(self):
        source = "\\begin{theorem*}[Selected] Actual claim.\\end{theorem*}\n"
        result = self.match(source, "  title: Selected\n  excerpt: Stale explanatory excerpt.\n")
        self.assertEqual(result["status"], "matched")


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


class ScopedSharedMarkerTests(unittest.TestCase):
    def test_excerpt_ignores_explicitly_excluded_appendix_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lean = make_book(root, "mybook")
            lean.write_text(
                LEAN_MARKER + "\n/-@ booklink:\n  source: absent-appendix.md\n"
                "  exclude-books: excerpt\n  target: statement\n  excerpt: Appendix.\n"
                "-/\ntheorem appendix : True := trivial\n"
            )
            alias = root / "excerpt/lean/MyBook/Sec.lean"
            alias.parent.mkdir(parents=True)
            alias.symlink_to(lean)
            self.assertEqual(len(bsm.parse_lean_markers(lean)), 2)
            self.assertEqual(len(bsm.parse_lean_markers(alias)), 1)
            self.assertEqual(bsm.discover_booklinks([alias])[0][1], ["excerpt/src/chap/sec.md"])
            # A typo without an exclusion is still discovered, so builds fail.
            self.assertIn("mybook/src/absent-appendix.md", bsm.discover_booklinks([lean])[0][1])


class BuildSourcemapTests(unittest.TestCase):
    def test_combined_map_includes_skip_only_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            lean = make_book(root, "mybook")
            preface = root / "mybook" / "src" / "preface.md"
            preface.write_text(
                "<!-- formalization: skip-begin (preface) -->\n\nText.\n\n<!-- formalization: skip-end -->\n",
                encoding="utf-8",
            )
            sm = bsm.build_combined_sourcemap(root, [lean], [preface])
            self.assertEqual(len(sm["skips"]), 1)
            self.assertEqual(sm["skips"][0]["source"], str(preface))
            self.assertEqual(sm["skips"][0]["reason"], "preface")

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

    def test_prose_ignores_correspondence_metadata_but_returns_original_span(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "source.md"
            metadata = '<!-- chapter-correspondence\n{"scope":"test","bindings":{}}\n-->'
            source = "前置き。\n" + metadata + "\nThe space " + metadata + "$X$ is Polish." + metadata
            path.write_text(source)
            match = bsm.find_prose_match(path, "The space $X$ is Polish.")
            self.assertEqual(match["status"], "matched")
            self.assertEqual(match["startOffset"], source.index("The space"))
            self.assertEqual(match["endOffset"], source.index("Polish.") + len("Polish."))
            self.assertEqual(
                source[match["startOffset"] : match["endOffset"]], "The space " + metadata + "$X$ is Polish."
            )
            self.assertEqual(bsm.find_prose_match(path, '"scope":"test"')["status"], "unresolved")

    def test_prose_projection_handles_inline_and_boundary_metadata(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "source.md"
            start = "<!-- chapter-correspondence-premise: sample -->"
            end = "<!-- chapter-correspondence-end: sample -->"
            source = start + "証" + end + "明 alpha" + start + " beta" + end
            path.write_text(source)
            for excerpt, expected in [
                ("証明", "証" + end + "明"),
                ("alpha", "alpha"),
                ("alpha beta", "alpha" + start + " beta"),
            ]:
                with self.subTest(excerpt=excerpt):
                    match = bsm.find_prose_match(path, excerpt)
                    self.assertEqual(match["status"], "matched")
                    self.assertEqual(source[match["startOffset"] : match["endOffset"]], expected)
            path.write_text("alpha <!-- ordinary author comment --> beta")
            self.assertEqual(bsm.find_prose_match(path, "alpha beta")["status"], "unresolved")

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


class SourceCacheTests(unittest.TestCase):
    def test_combined_build_reads_and_parses_each_shared_chapter_once(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = make_book(root, "book")
            source = root / "book/src/chap/sec.md"
            source.write_text(SOURCE_MD + "\n\\begin{theorem*}[Named]\nStatement.\n\\end{theorem*}\n")
            text = first.read_text() + "\n" + LEAN_MARKER.replace("target: prose", "target: statement\n  title: Named")
            first.write_text(text)
            second = first.with_name("Other.lean")
            second.write_text(text)
            original_read = Path.read_text
            reads = []

            def read(path, *args, **kwargs):
                if path == source:
                    reads.append(path)
                return original_read(path, *args, **kwargs)

            with (
                mock.patch.object(Path, "read_text", read),
                mock.patch.object(bsm, "parse_book_statements", wraps=bsm.parse_book_statements) as statements,
                mock.patch.object(bsm, "parse_skip_spans", wraps=bsm.parse_skip_spans) as skips,
                mock.patch.object(bsm, "line_offsets", wraps=bsm.line_offsets) as offsets,
                mock.patch.object(bsm, "chapter_rank_map", wraps=bsm.chapter_rank_map) as ranks,
            ):
                result = bsm.build_combined_sourcemap(root, [first, second], [source])
            self.assertEqual(result["counts"], {"matched": 4})
            self.assertEqual(len(reads), 1)
            self.assertEqual(
                (statements.call_count, skips.call_count, offsets.call_count, ranks.call_count), (1, 1, 1, 1)
            )
            source.write_text("Different saved source.\n")
            fresh = bsm.build_combined_sourcemap(root, [first, second])
            self.assertEqual(fresh["counts"], {"unresolved": 4})

    def test_tex_attachment_constructs_one_offset_table(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "book.tex"
            path.write_text(
                "".join(f"\\BooklinkStart[entry={i}]{{decl}}text\\BooklinkEnd[entry={i}]{{decl}}\n" for i in range(10))
            )
            source_map = {
                "entries": [
                    {
                        "lean": {"declName": "decl"},
                        "booklink": {"target": "prose"},
                        "match": {"status": "matched", "startOffset": i},
                    }
                    for i in range(10)
                ]
            }
            with mock.patch.object(bsm, "line_offsets", wraps=bsm.line_offsets) as offsets:
                bsm.attach_tex_matches(source_map, path)
            self.assertEqual(offsets.call_count, 1)
            self.assertEqual([entry["texMatch"]["startLine"] for entry in source_map["entries"]], list(range(1, 11)))


class FindDeclTests(unittest.TestCase):
    def test_plain_theorem(self):
        kind, name, line, _end = bsm.find_next_decl(["theorem foo : True := trivial"], 0)
        self.assertEqual((kind, name, line), ("theorem", "foo", 1))

    def test_attribute_and_modifier_prefixes(self):
        kind, name, _line, _end = bsm.find_next_decl(["@[simp] private noncomputable def bar := 1"], 0)
        self.assertEqual((kind, name), ("def", "bar"))

    def test_no_decl_returns_all_none(self):
        self.assertEqual(bsm.find_next_decl(["-- a comment", ""], 0), (None, None, None, None))

    def test_nested_documentation_is_not_a_declaration(self):
        lines = [
            "/-- Documentation",
            "lemma above proves the claim.",
            "/- nested comment -/",
            "theorem below gives the result.",
            "-/ @[simp] theorem actual : True := by trivial",
        ]
        kind, name, line, _end = bsm.find_next_decl(lines, 0)
        self.assertEqual((kind, name, line), ("theorem", "actual", 5))

    def test_comment_delimiters_in_attribute_strings_are_ignored(self):
        lines = [
            '@[deprecated "Use /- another -/ theorem" (since := "2026-10-21")] theorem actual : True := by trivial'
        ]
        kind, name, line, _end = bsm.find_next_decl(lines, 0)
        self.assertEqual((kind, name, line), ("theorem", "actual", 1))

    def test_decl_end_stops_at_blank_after_body(self):
        lines = ["theorem foo : True :=", "  trivial", "", "theorem bar := trivial"]
        # Body covers the proof line; the run ends at the blank before `bar`.
        self.assertEqual(bsm.find_decl_end_line(lines, 0), 2)

    def test_modifiers_unicode_and_quoted_identifiers(self):
        for prefix in ("partial", "unsafe", "protected", "public noncomputable", "private partial"):
            with self.subTest(prefix=prefix):
                result = bsm.find_next_decl([f"{prefix} def 命題' := 1", "def wrong := 2"], 0)
                self.assertEqual(result, ("def", "命題'", 1, 1))
        self.assertEqual(
            bsm.find_next_decl(["theorem N.«lemma /- -- @[x]» : True := by trivial"], 0)[1],
            "N.«lemma /- -- @[x]»",
        )

    def test_character_quote_does_not_start_a_string(self):
        lines = ["variable (c : Char := '\"')", "theorem actual : True := by trivial"]
        self.assertEqual(bsm.find_next_decl(lines, 0), ("theorem", "actual", 2, 2))

    def test_multiline_nested_attributes_are_not_declarations(self):
        lines = ["@[deprecated", '  "lemma fake" (since := "2026")]', "protected theorem actual : True := by trivial"]
        self.assertEqual(bsm.find_next_decl(lines, 0), ("theorem", "actual", 3, 3))

    def test_blank_lines_inside_proof_do_not_end_the_declaration(self):
        lines = [
            "theorem first : True := by",
            "  have h : True := by",
            "    trivial",
            "",
            "  exact h",
            "",
            "/-- Next declaration. -/",
            "theorem second : True := by trivial",
            "end Namespace",
        ]
        self.assertEqual(bsm.find_next_decl(lines, 0), ("theorem", "first", 1, 5))
        self.assertEqual(bsm.find_decl_end_line(lines, 7), 8)

    def test_literal_body_lines_are_included_without_scanning_their_contents(self):
        self.assertEqual(bsm.find_next_decl(["def c : Char :=", "  'x'"], 0)[3], 2)
        lines = ['def s := "a string', "theorem fake", 'end of string"', "def next := 2"]
        self.assertEqual(bsm.find_next_decl(lines, 0), ("def", "s", 1, 3))


class ParseLeanMarkersTests(unittest.TestCase):
    def test_adjacent_markers_share_the_actual_declaration(self):
        text = """/-@ booklink:
  source: chap/sec.md
  target: statement
  kind: theorem
  title: Definable graphs
-/
/-@ booklink:
  source: chap/sec.md
  target: proof
  excerpt: |
    Apply the definable-image
    lemma above. Define the graph using its pairs.
-/
theorem actual : True := by trivial"""
        with tempfile.TemporaryDirectory() as tmp:
            lean = Path(tmp) / "Sec.lean"
            lean.write_text(text, encoding="utf-8")
            markers = bsm.parse_lean_markers(lean)
            self.assertEqual(len(markers), 2)
            self.assertEqual(
                [(m.decl_kind, m.decl_name, m.decl_line) for m in markers],
                [("theorem", "actual", 14), ("theorem", "actual", 14)],
            )

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


class TexMarkerEntryPairingTests(unittest.TestCase):
    """Same-declaration booklinks must pair with tex spans in book order."""

    TEX = (
        "\\BooklinkStart[entry=7]{someDecl}claim body\\BooklinkEnd[entry=7]{someDecl}\n"
        "\\BooklinkStart[entry=8]{someDecl}proof body\\BooklinkEnd[entry=8]{someDecl}\n"
    )

    @staticmethod
    def _entry(target: str, start_offset: int | None = 0) -> dict:
        match: dict = {"status": "matched"}
        if start_offset is not None:
            match["startOffset"] = start_offset
        return {
            "lean": {"declName": "someDecl"},
            "booklink": {"target": target},
            "match": match,
        }

    def _attach(self, entries: list[dict], tex_text: str, injection_map: dict | None = None) -> list[dict]:
        with tempfile.TemporaryDirectory() as tmp:
            tex = Path(tmp) / "book-debug.tex"
            tex.write_text(tex_text, encoding="utf-8")
            source_map = {"entries": entries, "skips": []}
            bsm.attach_tex_matches(source_map, tex, injection_map)
        return entries

    def test_injected_identity_disambiguates_short_names_and_shared_bands(self):
        entries = [
            {
                "lean": {"declName": name, "source": module},
                "booklink": {"target": target},
                "match": {"status": "matched", "source": "chapter.md", "startOffset": start, "endOffset": end},
            }
            for name, module, target, start, end in [
                ("comp", "First.lean", "prose", 0, 10),
                ("comp", "Second.lean", "prose", 10, 20),
                ("other", "Third.lean", "proof", 10, 20),
                ("comp", "Second.lean", "statement", 10, 20),
                ("comp", "Second.lean", "proof", 20, 30),
            ]
        ]
        tex = (
            "\\BooklinkStart[entry=0]{comp}first\\BooklinkEnd[entry=0]{comp}"
            "\\BooklinkStart[entry=1]{comp,other}shared\\BooklinkEnd[entry=1]{comp,other}"
            "\\BooklinkStart[entry=3,kind=statement]{comp}statement\\BooklinkEnd[entry=3,kind=statement]{comp}"
            "\\BooklinkStart[entry=4]{comp}later\\BooklinkEnd[entry=4]{comp}"
        )
        result = self._attach(entries, tex)
        self.assertEqual([item["texMatch"].get("entry") for item in result], [0, 1, 1, 3, 4])

    def test_global_injection_numbers_and_translated_shared_bands_are_preserved(self):
        entries = [
            {
                "lean": {"declName": "comp", "source": f"Module{i}.lean", "markerLine": 5},
                "booklink": {"target": "prose"},
                "match": {
                    "status": "matched",
                    "source": "english.md",
                    "startOffset": i * 10,
                    "endOffset": (i + 1) * 10,
                },
            }
            for i in range(2)
        ]
        projected = json.loads(json.dumps(entries))
        for item in projected:
            item["match"].update(source="japanese.md", startOffset=0, endOffset=30)
        injection_map = {"entries": [{"lean": {}, "match": {}}, {"lean": {}, "match": {}}, *projected]}
        tex = "\\BooklinkStart[entry=2]{comp,comp}shared\\BooklinkEnd[entry=2]{comp,comp}"
        result = self._attach(entries, tex, injection_map)
        self.assertEqual([item["texMatch"].get("entry") for item in result], [2, 2])

    def test_translated_lean_symlink_uses_the_same_marker_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            real = Path(directory) / "English.lean"
            alias = Path(directory) / "Japanese.lean"
            real.write_text("theorem someDecl : True := trivial")
            alias.symlink_to(real)
            entry = self._entry("prose")
            entry["lean"].update(source=str(real), markerLine=1)
            entry["match"].update(source="english.md", endOffset=10)
            injected = json.loads(json.dumps(entry))
            injected["lean"]["source"] = str(alias)
            injected["match"]["source"] = "japanese.md"
            tex = "\\BooklinkStart[entry=0]{someDecl}body\\BooklinkEnd[entry=0]{someDecl}"
            result = self._attach([entry], tex, {"entries": [injected]})
            self.assertEqual(result[0]["texMatch"].get("entry"), 0)

    def test_numbered_marker_cannot_fall_back_to_another_declarations_span(self):
        entry = self._entry("prose")
        entry["match"].update(source="chapter.md", endOffset=10)
        result = self._attach([entry], "\\BooklinkStart[entry=7]{someDecl}wrong\\BooklinkEnd[entry=7]{someDecl}")[0]
        self.assertEqual(result["texMatch"]["status"], "unresolved")

    def test_legacy_names_do_not_match_namespace_suffixes(self):
        entry = self._entry("prose")
        entry["lean"]["declName"] = "comp"
        result = self._attach([entry], "\\BooklinkStart{Realizes.comp}wrong\\BooklinkEnd{Realizes.comp}")[0]
        self.assertEqual(result["texMatch"]["status"], "unresolved")

    def test_anonymous_instance_anchor_resolves_without_inventing_a_lean_name(self):
        marker = bsm.Marker(
            lean_file=Path("book/lean/Module.lean"),
            marker_line=3,
            end_line=5,
            data={"target": "proof"},
            decl_kind="instance",
            decl_name=None,
            decl_line=6,
            decl_end_line=9,
        )
        entry = bsm.marker_to_json(marker, {"status": "matched", "startOffset": 0})
        anchor = entry["lean"]["anchorName"]
        tex = f"\\BooklinkStart[entry=0]{{{anchor}}}argument\\BooklinkEnd[entry=0]{{{anchor}}}"
        result = self._attach([entry], tex)[0]
        self.assertIsNone(result["lean"]["declName"])
        self.assertEqual(result["texMatch"]["status"], "matched")
        missing = bsm.marker_to_json(
            bsm.Marker(lean_file=Path("book/lean/Module.lean"), marker_line=3, end_line=5, data={}), {}
        )
        self.assertNotIn("anchorName", missing["lean"])

    def test_prose_then_proof_take_successive_spans(self):
        entries = self._attach([self._entry("prose"), self._entry("proof")], self.TEX)
        self.assertEqual(entries[0]["texMatch"]["entry"], 7)
        self.assertEqual(entries[1]["texMatch"]["entry"], 8)

    def test_multiple_prose_booklinks_take_successive_spans(self):
        entries = self._attach([self._entry("prose"), self._entry("prose")], self.TEX)
        self.assertEqual(entries[0]["texMatch"]["entry"], 7)
        self.assertEqual(entries[1]["texMatch"]["entry"], 8)

    def test_repeated_declaration_names_share_a_band_without_consuming_the_next(self):
        tex = (
            "\\BooklinkStart[entry=7]{someDecl,someDecl}shared body"
            "\\BooklinkEnd[entry=7]{someDecl,someDecl}\n"
            "\\BooklinkStart[entry=9]{someDecl}later body\\BooklinkEnd[entry=9]{someDecl}\n"
        )
        entries = self._attach([self._entry("prose") for _ in range(3)], tex)
        self.assertEqual([entry["texMatch"]["entry"] for entry in entries], [7, 7, 9])
        self.assertEqual(entries[0]["texMatch"]["startOffset"], entries[1]["texMatch"]["startOffset"])

    def test_statement_pool_is_separate_from_body_pool(self):
        tex = (
            "\\BooklinkStart[entry=3,kind=statement]{someDecl}stmt\\BooklinkEnd[entry=3,kind=statement]{someDecl}\n"
            "\\BooklinkStart[entry=4]{someDecl}proof\\BooklinkEnd[entry=4]{someDecl}\n"
        )
        entries = self._attach([self._entry("statement"), self._entry("proof")], tex)
        self.assertEqual(entries[0]["texMatch"]["entry"], 3)
        self.assertEqual(entries[1]["texMatch"]["entry"], 4)

    def test_uninjected_entry_does_not_consume_a_span(self):
        entries = self._attach([self._entry("prose", start_offset=None), self._entry("proof")], self.TEX)
        self.assertEqual(entries[0]["texMatch"]["status"], "unresolved")
        self.assertEqual(entries[1]["texMatch"]["entry"], 7)

    def test_weak_candidate_does_not_consume_an_injected_span(self):
        weak = self._entry("prose")
        weak["match"]["status"] = "weak"
        entries = self._attach([weak, self._entry("proof")], self.TEX)
        self.assertEqual(entries[0]["texMatch"]["status"], "unresolved")
        self.assertEqual(entries[1]["texMatch"]["entry"], 7)

    def test_entries_beyond_available_spans_are_unresolved(self):
        entries = self._attach([self._entry("prose"), self._entry("prose"), self._entry("prose")], self.TEX)
        self.assertEqual(entries[2]["texMatch"]["status"], "unresolved")


class AnnotationAndTexGrammarTests(unittest.TestCase):
    def test_mixed_tex_marker_formats_are_rejected(self):
        old = "% BOOKLINK-START lean=decl\nBody.\n% BOOKLINK-END lean=decl\n"
        modern = "\\BooklinkStart{decl}Body.\\BooklinkEnd{decl}"
        self.assertEqual(len(bsm.parse_tex_booklink_spans(old)), 1)
        self.assertEqual(len(bsm.parse_tex_booklink_spans(modern)), 1)
        with self.assertRaisesRegex(ValueError, "mixed BOOKLINK"):
            bsm.parse_tex_booklink_spans(old + modern)

    def test_unknown_or_unbalanced_skip_annotations_fail_during_map_build(self):
        for text in (
            "<!-- formalization: skip-begin -->\nBody.",
            "<!-- formalization: skip-end -->",
            "<!-- formalization: bogus -->",
        ):
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "chapter.md"
                path.write_text(text)
                with self.assertRaises(ValueError):
                    bsm.parse_skip_spans(path)

    def test_make_manifest_generation_rejects_unbalanced_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "book/src/book.md"
            source.parent.mkdir(parents=True)
            source.write_text("<!-- formalization: skip-begin -->\nBody.\n")
            source.with_suffix(".json").write_text('{"source":"book/src/book.md","chapters":[]}')
            result = subprocess.run(
                [sys.executable, str(Path(REPO_ROOT) / "tools/books_mk.py"), "book/src/book.json"],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(result.returncode, 2)
            self.assertIn("unclosed 'formalization: skip-begin'", result.stderr)
            self.assertEqual(result.stdout, "")

    def test_shared_parser_preserves_nested_reason_parentheses(self):
        text = "<!-- formalization: skip-begin ((nested reason)) -->\nBody.\n<!-- formalization: skip-end -->"
        scope = bsm.parse_formalization_scope(text, "chapter.md")
        region = scope.regions[0]
        self.assertEqual(region.reason, "(nested reason)")
        self.assertEqual(text[region.opening.end_offset : region.closing.start_offset], "\nBody.\n")

    def test_normalization_does_not_replace_a_macro_name_prefix(self):
        self.assertEqual(bsm.strip_latex_macros(r"\R \RealSequenceSpace"), "R RealSequenceSpace")
        self.assertEqual(bsm.strip_latex_macros(r"\Rubbish"), " ")


class ParseTexSkipSpansTests(unittest.TestCase):
    def test_pairs_by_key_and_keeps_first_span(self):
        tex = "before \\SkipStart{ch-12}inner text\\SkipEnd{ch-12} after \\SkipStart{ch-40}x\\SkipEnd{ch-40}"
        spans = bsm.parse_tex_skip_spans(tex)
        self.assertEqual(sorted(spans), ["ch-12", "ch-40"])
        start, end = spans["ch-12"]
        self.assertEqual(tex[start:end], "inner text")

    def test_unmatched_end_is_ignored(self):
        self.assertEqual(bsm.parse_tex_skip_spans("\\SkipEnd{ch-1} \\SkipStart{ch-2}"), {})

    def test_attach_tex_matches_adds_skip_spans(self):
        with tempfile.TemporaryDirectory() as tmp:
            tex = Path(tmp) / "book-debug.tex"
            tex.write_text(
                "% BOOKLINK markers absent\n\\SkipStart{ch-7}skipped prose\\SkipEnd{ch-7}\n", encoding="utf-8"
            )
            source_map = {"entries": [], "skips": [{"key": "ch-7"}, {"key": "ch-9"}]}
            bsm.attach_tex_matches(source_map, tex)
        match = source_map["skips"][0]["texMatch"]
        self.assertEqual(match["status"], "matched")
        self.assertEqual(match["endOffset"] - match["startOffset"], len("skipped prose"))
        self.assertNotIn("texMatch", source_map["skips"][1])


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
