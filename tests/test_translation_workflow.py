"""Tests for translation validation and installation of a checked render."""

from __future__ import annotations

import contextlib
import io
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "tools"))

import check_translation_workflow as checker


class GitBlobHashTest(unittest.TestCase):
    def test_empty_file_has_the_standard_git_blob_id(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "empty"
            path.write_bytes(b"")
            self.assertEqual(
                checker.git_blob_hash(path),
                "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391",
            )


class WorkflowCliTest(unittest.TestCase):
    def test_structure_parse_error_has_a_concise_cli_diagnostic(self):
        error = checker.check_translation_structure.StructureParseError("unclosed argument")
        stderr = io.StringIO()
        with patch.object(checker, "check_workflow", side_effect=error), contextlib.redirect_stderr(stderr):
            result = checker.main(
                [
                    "--po4a",
                    "po4a",
                    "--config",
                    "config",
                    "--l10n-dir",
                    "l10n",
                    "--translated-dir",
                    "translated",
                    "--status",
                    "status",
                ]
            )
        self.assertEqual(result, 1)
        self.assertIn("unclosed argument", stderr.getvalue())
        self.assertNotIn("Traceback", stderr.getvalue())


class TranslationStatusTest(unittest.TestCase):
    def _fixture(self, root: Path, source_blob: str) -> tuple[Path, Path, Path]:
        source = root / "english" / "chapter.md"
        source.parent.mkdir()
        source.write_text("English source\n", encoding="utf-8")
        l10n = root / "ja-book" / "l10n"
        translated = root / "ja-book" / "src"
        l10n.mkdir(parents=True)
        translated.mkdir(parents=True)
        status = l10n / "translation-status.json"
        status.write_text(
            json.dumps(
                {
                    "language": "ja",
                    "chapters": {
                        "chapter.md": {
                            "source": "english/chapter.md",
                            "sourceBlob": source_blob,
                        }
                    },
                }
            ),
            encoding="utf-8",
        )
        return l10n, translated, status

    def test_status_loads_current_source_blob(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "english" / "chapter.md"
            source.parent.mkdir()
            source.write_text("English source\n", encoding="utf-8")
            source_blob = "20eb7ebfa7523d76f242795567b8f366319a8f52"  # git hash-object of b"English source\n"
            source.unlink()
            source.parent.rmdir()
            l10n, translated, status = self._fixture(root, source_blob)
            chapters = checker._load_status(root, l10n, translated, status)
            self.assertEqual([chapter.filename for chapter in chapters], ["chapter.md"])

    def test_status_rejects_stale_source_blob(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            l10n, translated, status = self._fixture(root, "0" * 40)
            with self.assertRaisesRegex(checker.TranslationCheckError, "English source changed"):
                checker._load_status(root, l10n, translated, status)


class TranslationRenderTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.chapters = []
        for name in ("first", "last"):
            paths = [
                self.root / directory / f"{name}{suffix}"
                for directory, suffix in (("english", ".md"), ("output", ".md"), ("ja", ".po"), ("pot", ".pot"))
            ]
            for path in paths:
                path.parent.mkdir(exist_ok=True)
                path.write_text("old content\n", encoding="utf-8")
            self.chapters.append(checker.Chapter(f"{name}.md", *paths, "unused"))
        (self.root / "po4a.cfg").write_text(
            "\n".join(
                f"[type: book-markdown] $(source)/{chapter.filename} $lang:$(output)/{chapter.filename}"
                for chapter in self.chapters
            ),
            encoding="utf-8",
        )
        self.content = b"checked translation\n"
        self.render_calls = 0

    def run_workflow(self, *, write_generated=False, diagnostics=None, catalog_error=False, terminology_error=False):
        def render(command, **_kwargs):
            self.render_calls += 1
            output = Path(next(arg.removeprefix("output=") for arg in command if arg.startswith("output=")))
            for chapter in self.chapters:
                (output / chapter.filename).write_bytes(self.content)

        with (
            patch.object(checker, "_load_status", return_value=self.chapters),
            patch.object(checker, "_check_catalogs") as check_catalogs,
            patch.object(checker, "_check_terminology") as check_terminology,
            patch.object(checker, "_run", side_effect=render),
            patch.object(checker, "_compare_message_sets") as compare_catalogs,
            patch.object(
                checker.check_translation_structure, "compare_files", side_effect=diagnostics or [[], []]
            ) as compare_structure,
        ):
            if catalog_error:
                compare_catalogs.side_effect = [None, None, checker.TranslationCheckError("stale catalog")]
            if terminology_error:
                check_terminology.side_effect = checker.TranslationCheckError("terminology differs")
            checker.check_workflow(
                repo_root=self.root,
                po4a="po4a",
                config=self.root / "po4a.cfg",
                l10n_dir=self.root,
                translated_dir=self.root / "output",
                status_path=self.root / "status.json",
                catalogs_only=False,
                write_generated=write_generated,
            )
            check_catalogs.assert_called_once_with(self.root, self.chapters)
            check_terminology.assert_called_once_with(self.chapters, self.root / "glossary-ja.yaml")
            self.assertTrue(compare_catalogs.called)
            self.assertTrue(compare_structure.called)
        self.assertEqual(self.render_calls, 1)

    def test_config_chapter_sets_must_match_in_both_directions(self):
        config = self.root / "po4a.cfg"
        original = config.read_text(encoding="utf-8")
        for invalid in (
            original.splitlines()[0],
            original + "\n[type: book] $(source)/extra.md $lang:$(output)/extra.md",
        ):
            config.write_text(invalid, encoding="utf-8")
            with self.assertRaisesRegex(checker.TranslationCheckError, "chapter set differs"):
                self.run_workflow(write_generated=True)
            self.assertEqual(self.render_calls, 0)

    def test_failed_atomic_publication_retains_previous_output(self):
        path = self.chapters[0].translated
        with (
            patch.object(Path, "replace", side_effect=OSError("publication failed")),
            self.assertRaisesRegex(OSError, "publication failed"),
        ):
            checker._atomic_write(path, b"new content")
        self.assertEqual(path.read_bytes(), b"old content\n")
        self.assertEqual(list(path.parent.glob(f".{path.name}.*")), [])

    def test_install_repairs_missing_and_stale_outputs(self):
        self.chapters[0].translated.unlink()
        self.run_workflow(write_generated=True)
        for chapter in self.chapters:
            self.assertEqual(chapter.translated.read_bytes(), self.content)

    def test_unchanged_output_keeps_modification_time(self):
        for chapter in self.chapters:
            chapter.translated.write_bytes(self.content)
            os.utime(chapter.translated, ns=(1_000_000_000, 1_000_000_000))
        self.run_workflow(write_generated=True)
        for chapter in self.chapters:
            self.assertEqual(chapter.translated.stat().st_mtime_ns, 1_000_000_000)

    def test_late_structure_failure_leaves_all_outputs_untouched(self):
        with self.assertRaisesRegex(checker.TranslationCheckError, "structure differs"):
            self.run_workflow(write_generated=True, diagnostics=[[], ["missing label"]])
        for chapter in self.chapters:
            self.assertEqual(chapter.translated.read_text(), "old content\n")

    def test_late_catalog_failure_leaves_all_outputs_untouched(self):
        with self.assertRaisesRegex(checker.TranslationCheckError, "stale catalog"):
            self.run_workflow(write_generated=True, catalog_error=True)
        for chapter in self.chapters:
            self.assertEqual(chapter.translated.read_text(), "old content\n")

    def test_terminology_failure_prevents_render_and_install(self):
        with self.assertRaisesRegex(checker.TranslationCheckError, "terminology differs"):
            self.run_workflow(write_generated=True, terminology_error=True)
        self.assertEqual(self.render_calls, 0)
        for chapter in self.chapters:
            self.assertEqual(chapter.translated.read_text(), "old content\n")

    def test_install_rejects_symlink_without_changing_earlier_output(self):
        last = self.chapters[-1]
        last.translated.unlink()
        last.translated.symlink_to(last.source)
        with self.assertRaisesRegex(checker.TranslationCheckError, "symlink"):
            self.run_workflow(write_generated=True)
        self.assertEqual(self.chapters[0].translated.read_text(), "old content\n")
        self.assertEqual(last.source.read_text(), "old content\n")
        self.assertTrue(last.translated.is_symlink())

    def test_read_only_check_rejects_stale_output(self):
        with self.assertRaisesRegex(checker.TranslationCheckError, "is stale"):
            self.run_workflow()
        for chapter in self.chapters:
            self.assertEqual(chapter.translated.read_text(), "old content\n")

    def test_read_only_check_accepts_current_outputs(self):
        for chapter in self.chapters:
            chapter.translated.write_bytes(self.content)
        self.run_workflow()


if __name__ == "__main__":
    unittest.main()
