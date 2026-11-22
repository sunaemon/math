"""Regression tests for current-target build validation without invoking TeX."""

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import validate_book_build as validator


class DiagnosticTests(unittest.TestCase):
    def test_real_warnings_and_errors_are_detected(self):
        for text in (
            "[WARNING] missing citation",
            "LaTeX Warning: undefined reference",
            "Package hyperref Warning: Token not allowed",
            "Overfull \\hbox (2pt too wide)",
            "Underfull \\vbox (badness 10000)",
            "Missing character: There is no x",
            "! Undefined control sequence.",
            "done (2 rejected, 0 warnings).",
            "done (0 rejected, 2 warnings).",
        ):
            with self.subTest(text=text):
                self.assertTrue(validator.diagnostics(text))

    def test_metadata_and_zero_counts_are_not_warnings(self):
        self.assertEqual(
            validator.diagnostics(
                "Package: infwarerr 2019/12/03 v1.5 Providing info/warning/error messages\n"
                "done (3 entries accepted, 0 rejected).\ndone (10 lines written, 0 warnings).\n ***********"
            ),
            [],
        )

    def test_generation_scan_ignores_intermediate_latex_warnings(self):
        findings = validator.diagnostics(
            "LaTeX Warning: Rerun to get cross-references right.\n[WARNING] missing citation",
            generation_only=True,
        )
        self.assertEqual([finding["line"] for finding in findings], [2])


BASE_MTIME_NS = 1_600_000_000_000_000_000
LATER_MTIME_NS = BASE_MTIME_NS + 120_000_000_000


class ValidationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.build = self.root / "book" / "build"
        self.build.mkdir(parents=True)
        self.stem = self.build / "example"
        self.report_dir = self.root / "report"
        self.report_dir.mkdir()
        self.books = {"example": self.stem}
        for suffix, content in {
            ".tex": b"source",
            ".pdf": b"PDF",
            ".log": b"Output written on example-debug.pdf (1 page).",
            ".idx": b"index entry",
            ".ind": b"index output",
            ".ilg": b"done (1 entries accepted, 0 rejected).\ndone (0 warnings).",
            # SHA-256 protocol fixture for b"index entry", independently fixed.
            ".index-sha256": b"9ff95b05550a7d94e0eee18df1fe0d3d8d3ecc2b2904a93e78a3ec9bdd655e54",
        }.items():
            (self.build / ("example-debug" + suffix)).write_bytes(content)
        for path in self.build.iterdir():
            os.utime(path, ns=(BASE_MTIME_NS, BASE_MTIME_NS))

    def test_old_unrelated_logs_do_not_affect_pass(self):
        (self.build / "example-preview-old.log").write_text("! Fatal error\n")
        (self.build / "example.log").write_text("Overfull \\hbox\n")
        self.assertEqual(validator.check_debug(self.stem, self.report_dir), [])
        self.assertFalse((self.report_dir / "example.log").exists())

    def test_missing_final_log_fails(self):
        (self.build / "example-debug.log").unlink()
        self.assertTrue(validator.check_debug(self.stem, self.report_dir))

    def test_incomplete_or_stale_pdf_fails(self):
        log = self.build / "example-debug.log"
        log.write_text("LaTeX started but did not finish")
        os.utime(self.build / "example-debug.tex", ns=(LATER_MTIME_NS, LATER_MTIME_NS))
        findings = validator.check_debug(self.stem, self.report_dir)
        self.assertTrue(any("completion" in finding["text"] for finding in findings))
        self.assertTrue(any("predates" in finding["text"] for finding in findings))

    def test_stale_index_fails(self):
        (self.build / "example-debug.idx").write_text("changed index")
        self.assertTrue(
            any("index output" in finding["text"] for finding in validator.check_debug(self.stem, self.report_dir))
        )

    def fake_make(self, text, code=0):
        def run(targets, log):
            log.write_text(text)
            return {"command": ["make", *map(str, targets)], "exit_code": code, "seconds": 0, "log": str(log)}

        return run

    def test_failed_build_cannot_pass_using_old_pdf(self):
        with patch.object(validator, "run_make", side_effect=self.fake_make("build failed", 2)):
            result = validator.validate("debug", self.books, self.report_dir)
        self.assertFalse(result["passed"])
        self.assertEqual(result["commands"][0]["exit_code"], 2)

    def test_success_uses_final_pass_not_intermediate_warnings(self):
        with (
            patch.object(validator, "run_make", side_effect=self.fake_make("LaTeX Warning: Rerun required")),
            patch.object(validator.latex_lock, "acquire_lock"),
            patch.object(validator.latex_lock, "release_lock"),
        ):
            result = validator.validate("debug", self.books, self.report_dir)
        self.assertTrue(result["passed"])

    def test_tex_warning_fails_even_if_make_succeeds(self):
        self.stem.with_suffix(".tex").write_text("output")
        with patch.object(validator, "run_make", side_effect=self.fake_make("[WARNING] missing citation")):
            result = validator.validate("tex", self.books, self.report_dir)
        self.assertFalse(result["passed"])
        self.assertFalse(self.stem.with_suffix(".tex").exists(), "retry must regenerate the warning's source")

    def test_tex_books_share_one_make_invocation(self):
        second = self.build / "second"
        for stem in (self.stem, second):
            stem.with_suffix(".tex").write_text("output")
        books = {**self.books, "second": second}
        with patch.object(validator, "run_make", side_effect=self.fake_make("")) as build:
            result = validator.validate("tex", books, self.report_dir)
        self.assertTrue(result["passed"])
        build.assert_called_once_with(
            [self.stem.with_suffix(".tex"), second.with_suffix(".tex")], self.report_dir / "tex-build.log"
        )

    def test_batched_tex_warning_invalidates_all_selected_outputs(self):
        second = self.build / "second"
        for stem in (self.stem, second):
            stem.with_suffix(".tex").write_text("output")
        with patch.object(validator, "run_make", side_effect=self.fake_make("[WARNING] missing citation")):
            result = validator.validate("tex", {**self.books, "second": second}, self.report_dir)
        self.assertFalse(result["passed"])
        self.assertFalse(self.stem.with_suffix(".tex").exists())
        self.assertFalse(second.with_suffix(".tex").exists())

    def test_debug_generation_warning_cannot_disappear_on_noop_retry(self):
        with (
            patch.object(validator, "run_make", side_effect=self.fake_make("[WARNING] missing citation")),
            patch.object(validator.latex_lock, "acquire_lock"),
            patch.object(validator.latex_lock, "release_lock"),
        ):
            result = validator.validate("debug", self.books, self.report_dir)
        self.assertFalse(result["passed"])
        self.assertFalse((self.build / "example-debug.tex").exists())
        self.assertTrue((self.build / "example-debug.pdf").exists())
        self.assertTrue((self.build / "example-debug.log").exists())

    def test_main_writes_failure_report_and_returns_nonzero(self):
        previous = Path.cwd()
        os.chdir(self.root)
        try:
            with (
                patch.object(validator, "discover_books", return_value=self.books),
                patch.object(validator, "run_make", side_effect=self.fake_make("build failed", 2)),
                patch("builtins.print"),
            ):
                code = validator.main(["debug", "--book", "example"])
            self.assertEqual(code, 1)
            reports = list(Path("build/validation").glob("*/report.json"))
            self.assertEqual(len(reports), 1)
            report = json.loads(reports[0].read_text())
            self.assertFalse(report["passed"])
            self.assertEqual(report["commands"][0]["exit_code"], 2)
            self.assertFalse(Path("build/.book-validation.lock").exists())
        finally:
            os.chdir(previous)

    def test_tex_missing_output_fails_even_if_make_succeeds(self):
        with patch.object(validator, "run_make", side_effect=self.fake_make("")):
            result = validator.validate("tex", self.books, self.report_dir)
        self.assertFalse(result["passed"])

    def test_discovery_works_with_only_public_excerpt(self):
        source_dir = self.root / "public-excerpt" / "src"
        source_dir.mkdir(parents=True)
        (source_dir / "excerpt.json").write_text(
            json.dumps(
                {
                    "source": "public-excerpt/src/excerpt.md",
                    "chapters": [],
                }
            )
        )
        self.assertEqual(
            validator.discover_books(self.root),
            {
                "excerpt": self.root / "public-excerpt" / "build" / "excerpt",
            },
        )


if __name__ == "__main__":
    unittest.main()
