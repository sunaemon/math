"""Preview unit generation rejects chapter drift before touching old output."""

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import split_preview_tex as preview


class PreviewMappingTest(unittest.TestCase):
    def test_contents_preview_excludes_title_and_preserves_frontmatter(self):
        title = "\\frontmatter\n\\maketitle\n\n"
        contents = "{\n\\setcounter{tocdepth}{3}\n\\tableofcontents\n}\n\\mainmatter\n"
        units = preview.frontmatter_units(title + contents)
        self.assertEqual(units, [("_front", title), ("_contents", contents)])
        self.assertEqual(preview.frontmatter_units(title), [("_front", title)])

    def test_endmatter_previews_preserve_content_and_heading_preambles_in_either_order(self):
        index = "\\cleardoublepage\n\\phantomsection\n\\addcontentsline{toc}{chapter}{Index}\n\\printindex\n"
        bibliography = (
            "\\chapter*{References}\\label{bibliography}\n\\begin{CSLReferences}{0}{0}\nEntry\n\\end{CSLReferences}\n"
        )
        for chunks in ((index, bibliography), (bibliography, index)):
            body = "".join(chunks) + "\\backmatter\n"
            units = preview.endmatter_units(body.splitlines(keepends=True))
            self.assertEqual(
                [name for name, _ in units],
                ["_index", "_bibliography"] if chunks[0] == index else ["_bibliography", "_index"],
            )
            self.assertEqual("".join(text for _, text in units), body)
            self.assertTrue(dict(units)["_index"].startswith(index))
            self.assertTrue(dict(units)["_bibliography"].startswith(bibliography))

    def test_library_reports_missing_endmatter_as_value_error(self):
        with self.assertRaisesRegex(ValueError, "no index or bibliography"):
            preview.split_body(["\\chapter{Title}\n"])

    def test_mismatch_and_count_drift_leave_existing_units_untouched(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            chapter = root / "chapter.md"
            chapter.write_text("# Title {#sec:chapter}\n", encoding="utf-8")
            manifest = root / "book.json"
            manifest.write_text(json.dumps({"chapters": [str(chapter)]}), encoding="utf-8")
            tex = root / "book.tex"
            out = root / "build"
            units = out / "book-preview"
            units.mkdir(parents=True)
            old = units / "old.tex"
            old.write_text("prior output", encoding="utf-8")
            warm_aux = out / "book-preview-master.aux"
            warm_aux.write_text("\\@input{removed-chapter.aux}\n", encoding="utf-8")
            args = [
                "--debug-tex",
                str(tex),
                "--manifest",
                str(manifest),
                "--book-dir",
                str(root),
                "--stem",
                "book",
                "--out-dir",
                str(out),
            ]
            for body, message in [
                ("\\chapter{Wrong}\\label{sec:wrong}\n\\printindex\n", "tex label"),
                ("\\chapter{Title}\\label{sec:chapter}\n\\chapter{Extra}\n\\printindex\n", "chapter chunks"),
                ("\\chapter{Title}\n", "no index or bibliography"),
            ]:
                tex.write_text("\\begin{document}\n" + body + "\\end{document}\n", encoding="utf-8")
                with contextlib.redirect_stderr(io.StringIO()) as errors:
                    self.assertEqual(preview.main(args), 1)
                    self.assertIn(message, errors.getvalue())
                self.assertEqual(old.read_text(encoding="utf-8"), "prior output")
                self.assertTrue(warm_aux.exists(), "failed validation invalidated the existing cache")
            tex.write_text(
                "\\begin{document}\n\\chapter{Title}\\label{sec:chapter}\nText\n\\printindex\n\\end{document}\n",
                encoding="utf-8",
            )
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(preview.main(args), 0)
            self.assertFalse(old.exists())
            self.assertFalse(warm_aux.exists(), "obsolete chapter references survived a valid split")
            self.assertEqual(
                json.loads((units / "units.json").read_text(encoding="utf-8"))["chapters"], {"chapter": "chapter"}
            )
