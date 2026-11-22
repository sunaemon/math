"""Safety and ordering checks for the translation edit helper."""

from __future__ import annotations

import contextlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import edit_translation as editor


class EditTranslationTest(unittest.TestCase):
    def test_replaces_decoded_multiline_fields_and_preserves_comments(self):
        text = '# u_A\nmsgid "u_"\n"A"\nmsgstr "値u_A"\n'
        changed = editor.replace_po(text, "u_A", r"\IndicatorFunction{A}")
        self.assertTrue(changed.startswith("# u_A\n"))
        self.assertIn("\\\\IndicatorFunction{A}", changed)
        self.assertNotIn("値u_A", changed)

    def test_plural_catalog_is_rejected(self):
        with self.assertRaises(ValueError):
            editor.replace_po('msgid_plural "items"\n', "item", "object")

    def test_finish_stops_on_failure_without_recording_review(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with (
                patch.object(editor, "run_make", side_effect=RuntimeError("failed")) as run,
                self.assertRaises(RuntimeError),
            ):
                editor.finish(root, ["chapter"], ["book"])
            self.assertEqual(run.call_count, 1)
            self.assertFalse((root / editor.STATUS).exists())

    def test_finish_preserves_other_chapters_and_flags_and_orders_checks(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            status = root / editor.STATUS
            status.parent.mkdir(parents=True)
            source = root / "chapter.md"
            source.write_text("English")
            data = {
                "chapters": {
                    "chapter.md": {"source": "chapter.md", "sourceBlob": "old", "typesettingReview": True},
                    "other.md": {"sourceBlob": "unchanged"},
                }
            }
            status.write_text(json.dumps(data))
            with patch.object(editor, "run_make") as run, patch.object(editor, "read_po"):
                editor.finish(root, ["chapter"], ["book"])
            saved = json.loads(status.read_text())
            self.assertEqual(saved["chapters"]["other.md"], data["chapters"]["other.md"])
            self.assertTrue(saved["chapters"]["chapter.md"]["typesettingReview"])
            self.assertEqual(saved["chapters"]["chapter.md"]["sourceBlob"], editor.git_blob_hash(source))
            self.assertEqual(
                [call.args[1] for call in run.call_args_list],
                [
                    "translation-ja-update-catalogs",
                    "translation-ja-generate",
                    "lint-book",
                    "validate-tex",
                    "lint",
                ],
            )

    def test_preview_and_long_line_failure_do_not_write_files(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            status = root / editor.STATUS
            status.parent.mkdir(parents=True)
            source = root / "chapter.md"
            source.write_text("$u_A$\n")
            po = status.parent / "ja/chapter.po"
            po.parent.mkdir()
            po.write_text('msgid "$u_A$\\n"\nmsgstr "$u_A$\\n"\n')
            status.write_text(json.dumps({"chapters": {"chapter.md": {"source": "chapter.md"}}}))
            before = {path: path.read_bytes() for path in (source, po, status)}
            with patch.object(editor, "run_make") as run, contextlib.redirect_stdout(io.StringIO()):
                editor.replace_chapters(root, ["chapter"], "u_A", r"\IndicatorFunction{A}", False)
                with self.assertRaises(ValueError):
                    editor.replace_chapters(root, ["chapter"], "u_A", "x" * 121, True)
                run.assert_not_called()
            self.assertEqual(before, {path: path.read_bytes() for path in before})
            with patch.object(editor, "run_make") as run, contextlib.redirect_stdout(io.StringIO()):
                editor.replace_chapters(root, ["chapter"], "u_A", r"\IndicatorFunction{A}", True)
            self.assertEqual(source.read_text(), "$\\IndicatorFunction{A}$\n")
            messages = editor.read_po(po)
            self.assertEqual(messages[0].msgid, source.read_text())
            self.assertEqual(messages[0].msgstr, source.read_text())
            self.assertEqual(status.read_bytes(), before[status])
            run.assert_called_once_with(root, "translation-ja-update-catalogs")

    def test_catalog_update_does_not_prepare_stale_generated_books(self):
        result = subprocess.run(
            ["make", "-n", "-W", "polish-space/src/polish-space-book/preface.md", "translation-ja-update-catalogs"],
            cwd=editor.ROOT,
            capture_output=True,
            text=True,
            check=True,
        )
        self.assertIn("--no-translations", result.stdout)
        self.assertNotIn("check_translation_workflow.py", result.stdout)
        self.assertNotIn("prepare_part1_edition.py", result.stdout)
        self.assertNotIn("tools/books_mk.py", result.stdout)


if __name__ == "__main__":
    unittest.main()
