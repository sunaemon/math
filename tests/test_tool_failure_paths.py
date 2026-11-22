"""Failure results of explicit maintenance commands must be actionable."""

import contextlib
import io
import os
import sys
import tempfile
import unittest
from argparse import Namespace
from pathlib import Path
from unittest.mock import MagicMock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import audit_translation_coverage as audit
import po_diff
import split_skip_blocks as split
import vendor_notices as vendor
from project_translation_sourcemap import ChapterProjection, Segment


class MaintenanceFailureTest(unittest.TestCase):
    def test_fetch_reports_failed_components_but_attempts_the_whole_batch(self):
        with (
            patch.object(vendor, "load_manifest", return_value={"components": [{"id": "a"}, {"id": "b"}]}),
            patch.object(vendor, "fetch_one", side_effect=[False, True]) as fetch,
        ):
            self.assertEqual(vendor.cmd_fetch_license(Namespace(all=True)), 1)
            self.assertEqual(fetch.call_count, 2)

    def test_invalid_utf8_license_is_reported_without_overwriting(self):
        response = MagicMock()
        response.__enter__.return_value.read.return_value = b"\xff"
        with (
            patch.object(vendor.urllib.request, "urlopen", return_value=response),
            contextlib.redirect_stdout(io.StringIO()) as output,
        ):
            self.assertFalse(
                vendor.fetch_one(
                    {
                        "id": "a",
                        "version": "1",
                        "licenseUrl": "https://example.invalid/license",
                        "licenseFile": "LICENSE",
                    }
                )
            )
        self.assertIn("leaving LICENSE unchanged", output.getvalue())

    def test_manual_skip_blocks_have_a_failing_result_and_summary(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            (root / "chapter.md").write_text("source", encoding="utf-8")
            with (
                patch.object(split.cov, "covered_spans_by_source", return_value={"chapter.md": []}),
                patch.object(split, "process_source", return_value=("source", ["L1: MANUAL: unsafe cut"])),
                contextlib.redirect_stdout(io.StringIO()) as output,
            ):
                self.assertEqual(split.main(["split", "--root", str(root), "proof.lean"]), 1)
                self.assertIn("Manual blocks remaining: 1", output.getvalue())

    def test_po_diff_missing_argument_reports_usage(self):
        with contextlib.redirect_stderr(io.StringIO()) as output, self.assertRaises(SystemExit) as raised:
            po_diff.main([])
        self.assertEqual(raised.exception.code, 2)
        self.assertIn("usage:", output.getvalue())

    def test_audit_can_run_outside_repository_and_optionally_gate_gaps(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            source = root / "source.md"
            target = root / "ja.md"
            text = "\\begin{proof}\nUnlinked argument.\n\\end{proof}\n"
            source.write_text(text, encoding="utf-8")
            target.write_text(text, encoding="utf-8")
            chapter = ChapterProjection(source, target, text, text, [Segment(0, len(text), 0, len(text))])
            with (
                patch.object(audit.projection, "load_projections", return_value={"source": chapter}),
                patch.object(audit.booklinks, "build_combined_sourcemap", return_value={"entries": []}),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                self.assertEqual(audit.main(["--repo-root", os.fspath(root)]), 0)
                self.assertEqual(audit.main(["--repo-root", os.fspath(root), "--strict"]), 1)
            report = root / "build/translation-coverage-audit/report.json"
            self.assertIn('"uncovered"', report.read_text(encoding="utf-8"))

    def test_missing_audit_inputs_get_a_concise_diagnostic(self):
        with tempfile.TemporaryDirectory() as temporary, contextlib.redirect_stderr(io.StringIO()) as output:
            self.assertEqual(audit.main(["--repo-root", temporary]), 2)
            self.assertIn("translation coverage audit failed:", output.getvalue())
            self.assertNotIn("Traceback", output.getvalue())
