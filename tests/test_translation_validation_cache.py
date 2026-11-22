"""Chapter reuse, invalidation and failure safety of translation validation."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import check_translation_workflow as checker
from translation_validation_cache import RenderCache, fingerprint


class ChapterCacheTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.chapters = []
        for name in ["first", "last"]:
            paths = [
                self.root / directory / (name + suffix)
                for directory, suffix in [("english", ".md"), ("output", ".md"), ("ja", ".po"), ("pot", ".pot")]
            ]
            for path in paths:
                path.parent.mkdir(exist_ok=True)
                path.write_text(name)
            self.chapters.append(checker.Chapter(name + ".md", *paths, "reviewed"))
        self.config = self.root / "po4a.cfg"
        self.config.write_text(
            "[options] --keep 0\n"
            + "\n".join(
                "[type: book-markdown] $(source)/" + chapter.filename + " \\\n  $lang:$(output)/" + chapter.filename
                for chapter in self.chapters
            )
        )
        self.glossary = self.root / "glossary-ja.yaml"
        self.glossary.write_text("glossary")
        self.toolchain = "tools-v1"
        self.rendered = []
        self.fail = False

    def run_workflow(self, *, write=False, cache=True, catalogs_only=False):
        def render(command, **_kwargs):
            config = Path(command[-1]).read_text()
            output = Path(next(arg[7:] for arg in command if arg.startswith("output=")))
            selected = [chapter for chapter in self.chapters if "$(source)/" + chapter.filename in config]
            self.rendered.append([chapter.filename for chapter in selected])
            for chapter in selected:
                (output / chapter.filename).write_bytes(chapter.source.read_bytes())

        with (
            patch.object(checker, "_load_status", return_value=self.chapters),
            patch.object(checker, "_check_catalogs"),
            patch.object(checker, "_check_terminology"),
            patch.object(checker, "_compare_message_sets"),
            patch.object(checker, "_run", side_effect=render),
            patch.object(checker, "toolchain_fingerprint", return_value=self.toolchain),
            patch.object(
                checker.check_translation_structure,
                "compare_files",
                side_effect=lambda *_: ["bad structure"] if self.fail else [],
            ),
        ):
            checker.check_workflow(
                repo_root=self.root,
                po4a="po4a",
                config=self.config,
                l10n_dir=self.root,
                translated_dir=self.root / "output",
                status_path=self.root / "status.json",
                catalogs_only=catalogs_only,
                write_generated=write,
                cache_dir=self.root / "cache" if cache else None,
            )

    def test_warm_check_reuses_all_and_still_rejects_stale_output(self):
        self.run_workflow()
        self.run_workflow()
        self.assertEqual(self.rendered, [["first.md", "last.md"]])
        self.chapters[0].translated.write_text("tampered")
        with self.assertRaisesRegex(checker.TranslationCheckError, "is stale"):
            self.run_workflow()
        self.run_workflow(write=True)
        self.assertEqual(self.chapters[0].translated.read_text(), "first")
        self.assertEqual(len(self.rendered), 1)

    def test_each_chapter_input_invalidates_only_its_chapter(self):
        for attribute in ["source", "po", "pot"]:
            with self.subTest(attribute=attribute):
                self.run_workflow(write=True)
                path = getattr(self.chapters[0], attribute)
                path.write_text(path.read_text() + " edit")
                self.run_workflow(write=True)
                self.assertEqual(self.rendered[-1], ["first.md"])

    def test_global_dependencies_invalidate_every_chapter(self):
        self.run_workflow()
        for path in [self.config, self.glossary]:
            path.write_text(path.read_text() + "\n# edit")
            self.run_workflow()
            self.assertEqual(self.rendered[-1], ["first.md", "last.md"])
        self.toolchain = "tools-v2"
        self.run_workflow()
        self.assertEqual(self.rendered[-1], ["first.md", "last.md"])

    def test_corrupt_cache_entry_is_a_miss(self):
        self.run_workflow()
        next((self.root / "cache").glob("*.json")).write_text("{broken")
        self.run_workflow()
        self.assertEqual(len(self.rendered[-1]), 1)

    def test_failure_publishes_neither_cache_nor_outputs(self):
        self.chapters[0].translated.write_text("keep")
        self.fail = True
        with self.assertRaisesRegex(checker.TranslationCheckError, "structure differs"):
            self.run_workflow(write=True)
        self.assertEqual(list((self.root / "cache").glob("*.json")), [])
        self.assertEqual(self.chapters[0].translated.read_text(), "keep")

    def test_catalog_only_check_does_not_seed_full_validation_cache(self):
        self.run_workflow(catalogs_only=True)
        self.assertFalse((self.root / "cache").exists())
        self.run_workflow()
        self.assertEqual(len(self.rendered), 2)

    def test_cache_can_be_disabled_and_symlinks_are_not_overwritten(self):
        self.run_workflow()
        self.run_workflow(cache=False)
        self.assertEqual(len(self.rendered), 2)
        chapter = self.chapters[0]
        chapter.translated.unlink()
        chapter.translated.symlink_to(chapter.source)
        with self.assertRaisesRegex(checker.TranslationCheckError, "symlink"):
            self.run_workflow(write=True)
        self.assertTrue(chapter.translated.is_symlink())

    def test_cached_render_checksum_is_verified(self):
        cache = RenderCache(self.root / "cache", "common")
        cache.write("key", b"good")
        path = self.root / "cache/key.json"
        entry = json.loads(path.read_text())
        entry["render"] = "bad"
        path.write_text(json.dumps(entry))
        self.assertIsNone(cache.read("key"))

    def test_fingerprint_uses_content_instead_of_modification_time(self):
        path = self.glossary
        original = fingerprint([path])
        path.touch()
        self.assertEqual(original, fingerprint([path]))
        path.write_text("changed")
        self.assertNotEqual(original, fingerprint([path]))

    def test_input_changed_during_validation_is_not_cached_or_published(self):
        original_key = RenderCache.key
        calls = 0

        def changing_key(cache, paths, context):
            nonlocal calls
            calls += 1
            if calls == 3:
                self.chapters[0].po.write_text("concurrent edit")
            return original_key(cache, paths, context)

        with (
            patch.object(RenderCache, "key", changing_key),
            self.assertRaisesRegex(checker.TranslationCheckError, "inputs changed"),
        ):
            self.run_workflow(write=True)
        self.assertFalse((self.root / "cache").exists())

    def test_toolchain_changed_during_validation_is_rejected(self):
        with (
            patch.object(checker, "fingerprint", side_effect=["before", "after"]),
            self.assertRaisesRegex(checker.TranslationCheckError, "tools changed"),
        ):
            self.run_workflow(write=True)
        self.assertFalse((self.root / "cache").exists())


if __name__ == "__main__":
    unittest.main()
