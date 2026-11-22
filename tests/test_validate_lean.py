"""Test incremental Lean validation without compiling mathlib."""

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import validate_lean as validator


class LeanValidationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.project = self.root / "book"
        (self.project / "lean" / "Example").mkdir(parents=True)
        (self.project / "lakefile.toml").write_text('[[lean_lib]]\nname="Example"\nsrcDir="lean"\n')
        (self.project / "lean" / "Example" / "Part.lean").write_text("-- source\n")

    def fake_build(self, text, code=0):
        def run(command, **kwargs):
            self.assertEqual(command[0:2], ["lake", "build"])
            kwargs["stdout"].write(text)
            return subprocess.CompletedProcess(command, code)

        return run

    def test_project_discovery_and_module_validation(self):
        self.assertEqual(validator.select_projects(self.root, [], []), [self.project])
        self.assertEqual(validator.select_projects(self.root, ["book", "book"], ["Example.Part"]), [self.project])
        for project, module in (("missing", "Example.Part"), ("book", "Example.Missing"), ("book", "--help")):
            with self.subTest(project=project, module=module), self.assertRaises(ValueError):
                validator.select_projects(self.root, [project], [module])

    def test_module_selection_requires_one_project(self):
        other = self.root / "excerpt"
        other.mkdir()
        (other / "lakefile.toml").write_text("")
        with self.assertRaisesRegex(ValueError, "exactly one"):
            validator.select_projects(self.root, [], ["Example.Part"])

    def test_targeted_build_deduplicates_modules_and_ignores_old_logs(self):
        (self.root / "old.log").write_text("error: obsolete failure")
        with patch.object(
            validator.subprocess, "run", side_effect=self.fake_build("Build completed successfully")
        ) as run:
            result = validator.run_build(self.project, ["Example.Part", "Example.Part"], self.root)
        self.assertTrue(result["passed"])
        self.assertEqual(run.call_args.args[0], ["lake", "build", "Example.Part"])
        self.assertEqual(run.call_args.kwargs["cwd"], self.project)

    def test_nonzero_exit_and_zero_exit_warning_fail(self):
        for text, code in (
            ("build failed", 1),
            ("warning: declaration uses 'sorry'", 0),
            ("⚠ Replayed Example.Part", 0),
        ):
            with (
                self.subTest(text=text),
                patch.object(validator.subprocess, "run", side_effect=self.fake_build(text, code)),
            ):
                result = validator.run_build(self.project, [], self.root)
            self.assertFalse(result["passed"])

    def test_launch_failure_saves_failure_report_and_releases_lock(self):
        previous = Path.cwd()
        os.chdir(self.root)
        try:
            with patch.object(validator.subprocess, "run", side_effect=FileNotFoundError("lake missing")):
                self.assertEqual(validator.main(["--project", "book"]), 1)
            path = next(Path("build/validation").glob("lean-*/report.json"))
            self.assertFalse(json.loads(path.read_text())["passed"])
            self.assertFalse(Path("build/.lean-validation.lock").exists())
        finally:
            os.chdir(previous)


if __name__ == "__main__":
    unittest.main()
