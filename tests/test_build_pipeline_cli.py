"""Exercise process and file boundaries with real local tools, without TeX."""

import contextlib
import io
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import enable_booklink_highlight as highlight
import validate_book_build as validator


class BuildPipelineCliTest(unittest.TestCase):
    @unittest.skipUnless(shutil.which("make"), "make is required for the process boundary test")
    def test_real_make_preserves_status_stdout_stderr_and_duration(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "Makefile").write_text(
                "pass:\n\t@echo stdout-message\n\t@echo stderr-message >&2\nfail:\n\t@echo failure-message\n\t@false\n",
                encoding="utf-8",
            )
            with contextlib.chdir(root), contextlib.redirect_stdout(io.StringIO()):
                passed = validator.run_make([Path("pass")], root / "pass.log")
                failed = validator.run_make([Path("fail")], root / "fail.log")
            self.assertEqual(passed["exit_code"], 0)
            self.assertNotEqual(failed["exit_code"], 0)
            self.assertIn("stdout-message", (root / "pass.log").read_text(encoding="utf-8"))
            self.assertIn("stderr-message", (root / "pass.log").read_text(encoding="utf-8"))
            self.assertIn("failure-message", (root / "fail.log").read_text(encoding="utf-8"))
            self.assertGreaterEqual(passed["seconds"], 0)
            self.assertEqual(passed["command"][-1], "pass")
            self.assertEqual(passed["log"], str(root / "pass.log"))

    def test_highlight_transform_is_exact_and_idempotent(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "debug.tex"
            original = "preamble\n\\input{example/tex/macros.tex}\n\\begin{document}\nBody\n"
            path.write_text(original, encoding="utf-8")
            self.assertEqual(highlight.main(["highlight", str(path)]), 0)
            self.assertEqual(highlight.main(["highlight", str(path)]), 0)
            self.assertEqual(
                path.read_text(encoding="utf-8"),
                original.replace(
                    "\\input{example/tex/macros.tex}", "\\input{example/tex/macros.tex}\n\\booklinkhighlighttrue"
                ),
            )
            path.write_text("no macros input", encoding="utf-8")
            with contextlib.redirect_stderr(io.StringIO()) as errors:
                self.assertEqual(highlight.main(["highlight", str(path)]), 1)
            self.assertIn("no \\input", errors.getvalue())
            self.assertEqual(path.read_text(encoding="utf-8"), "no macros input")

    def test_discovery_lists_multiple_books_and_rejects_duplicate_stems(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for directory, stem in [("full", "full-book"), ("excerpt", "chapter-one")]:
                src = root / directory / "src"
                src.mkdir(parents=True)
                (src / f"{stem}.json").write_text(
                    json.dumps({"source": f"{directory}/src/{stem}.md", "chapters": []}), encoding="utf-8"
                )
            self.assertEqual(
                validator.discover_books(root),
                {"chapter-one": root / "excerpt/build/chapter-one", "full-book": root / "full/build/full-book"},
            )
            other = root / "duplicate/src"
            other.mkdir(parents=True)
            (other / "full-book.json").write_text(
                json.dumps({"source": "duplicate/src/full-book.md", "chapters": []}), encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "duplicate book stem"):
                validator.discover_books(root)
