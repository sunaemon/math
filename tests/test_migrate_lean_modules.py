"""Keep diagnostic-driven migrations local to the reported source locations."""

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import migrate_lean_modules as migration


class MigrationScopeTests(unittest.TestCase):
    def run_migration(self, files, diagnostics):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = root / "polish-space/lean"
            sources.mkdir(parents=True)
            for name, source in files.items():
                (sources / name).write_text(source)
            excerpt = root / "polish-space-ch1/lean/PolishSpaceBook.lean"
            excerpt.parent.mkdir(parents=True)
            excerpt.write_text("module\npublic import Init\n")
            log = root / "diagnostics.log"
            log.write_text(diagnostics)
            with (
                patch.object(migration, "ROOT", root),
                patch.object(sys, "argv", ["migration", "--diagnostics", str(log)]),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                migration.main()
            return {name: (sources / name).read_text() for name in files}

    def test_set_alias_does_not_rename_measure_or_user_restriction(self):
        source = (
            "module\npublic import Init\n"
            "def setUse := C.restrict f\n"
            "def measureUse := μ.restrict D\n"
            "def ownUse := covering.restrict h\n"
        )
        result = self.run_migration(
            {"Example.lean": source},
            "warning: lean/Example.lean:3:16: `Set.restrict` has been deprecated: Use `Set.domRestrict` instead\n",
        )["Example.lean"]
        self.assertIn("C.domRestrict f", result)
        self.assertIn("μ.restrict D", result)
        self.assertIn("covering.restrict h", result)

    def test_zf_class_migration_preserves_coerced_set(self):
        source = "theorem example (M : Class.{u}) := f (Class.ofSet S)\n"
        expected = "theorem example (M : ZFClass.{u}) := f (S : ZFClass)\n"
        self.assertEqual(migration.migrate_zf_class(source), expected)
        self.assertEqual(migration.migrate_zf_class(expected), expected)

    def test_private_export_stays_in_its_reported_module(self):
        source = "module\npublic import Init\nprivate def helper := 1\n"
        result = self.run_migration(
            {"First.lean": source, "Second.lean": source},
            "error: lean/First.lean:4:1: Unknown identifier `helper`\n"
            "Note: A private declaration `helper` (from the current module) exists "
            "but would need to be public to access here.\n",
        )
        self.assertNotIn("private def helper", result["First.lean"])
        self.assertIn("private def helper", result["Second.lean"])


if __name__ == "__main__":
    unittest.main()
