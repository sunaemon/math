"""Exercise the real Make templates with a failing typesetter, without TeX."""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# This fake models the file/retry contract documented in
# tools/refresh_debug_pdf.py:refresh and Makefile's book-rules. It does not model
# TeX or makeindex semantics; real debug validation separately checks those.
FAKE_TOOL = r"""
import os
import re
import sys
from pathlib import Path

mode, *args = sys.argv[1:]
if mode == "pandoc":
    output = Path(args[args.index("-o") + 1])
    output.write_text("\\input{bk/tex/macros.tex}\n\\begin{document}\n\\chapter{Chapter}\n"
                      "\\label{sec:chapter}\nText\n\\printindex\n\\end{document}\n")
elif mode == "index":
    idx = Path(args[-1])
    idx.with_suffix(".ind").write_text(idx.read_text())
else:
    job = next((a.split("=", 1)[1] for a in args if a.startswith("-jobname=")),
               Path(args[-1]).stem)
    output_dir = Path(next(a.split("=", 1)[1] for a in args if a.startswith("-output-directory=")))
    with Path("calls").open("a") as log:
        log.write(job + "\n")
    aux = "aux\n"
    if job.endswith("-preview-master"):
        units = re.findall(r"\\include\{([^{}]+)\}", Path(args[-1]).read_text())
        aux = "".join("\\@input{" + name + ".aux}\n" for name in units)
    (output_dir / (job + ".aux")).write_text(aux)
    if job.endswith("-debug"):
        idx = output_dir / (job + ".idx")
        idx.write_text("new term\n")
        ind = idx.with_suffix(".ind")
        warning = "" if ind.exists() and ind.read_text() == idx.read_text() else "missing destination\n"
        idx.with_suffix(".log").write_text(warning)
    (output_dir / (job + ".pdf")).write_text("partial\n")
    if os.environ.get("FAIL_JOB") == job:
        sys.exit(1)
    (output_dir / (job + ".pdf")).write_text("complete\n")
"""


@unittest.skipUnless(shutil.which("make"), "make is required for build recovery tests")
class BookBuildRecoveryTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for directory in ("bk/src", "bk/tex", "bk/build", "tools", "polish-space/tex"):
            (self.root / directory).mkdir(parents=True)
        for filename in (
            "bk/src/book.md",
            "bk/tex/macros.tex",
            "bk/tex/locale.tex",
            "bk/tex/references.bib",
            "tools/book_manifest.py",
            "polish-space/tex/formula-overlays.lua",
            "filter",
        ):
            (self.root / filename).touch()
        (self.root / "bk/src/chapter.md").write_text("# Chapter {#sec:chapter}\n")
        (self.root / "bk/src/book.json").write_text(json.dumps({"chapters": ["bk/src/chapter.md"]}))
        shutil.copy2(ROOT / "tools/split_preview_tex.py", self.root / "tools/split_preview_tex.py")
        shutil.copy2(ROOT / "tools/refresh_debug_pdf.py", self.root / "tools/refresh_debug_pdf.py")
        shutil.copy2(ROOT / "tools/enable_booklink_highlight.py", self.root / "tools/enable_booklink_highlight.py")
        (self.root / "fake.py").write_text(FAKE_TOOL)
        source = (ROOT / "Makefile").read_text()
        templates = []
        for name in ("book-dir-rules", "book-rules", "book-preview-rules"):
            match = re.search(
                rf"^define[ \t]+{re.escape(name)}[ \t]*\n.*?^endef[ \t]*$", source, re.MULTILINE | re.DOTALL
            )
            if match is None:
                self.fail(f"production Makefile template is missing or malformed: {name}")
            templates.append(match.group(0))
        # Include the production failure-cleanup policy as well as its templates.
        policies = "\n".join(line for line in source.splitlines() if line.startswith(".DELETE_ON_ERROR:"))
        (self.root / "Makefile").write_text(
            f"""
{policies}
PYTHON := {sys.executable}
PANDOC := $(PYTHON) fake.py pandoc
LUALATEX := $(PYTHON) fake.py latex
MAKEINDEX := $(PYTHON) fake.py index
LATEX_LOCK := $(PYTHON) {ROOT}/tools/latex_lock.py --
FILTER_BIN := filter
book_DIR := bk
book_MANIFEST := bk/src/book.json
book_INPUTS := bk/src/book.md bk/src/chapter.md
book_CHAPTERS := bk/src/chapter.md
book_PANDOC_INPUTS := $(book_INPUTS)
.PHONY: require-mise require-tex
require-mise require-tex:
\t@:
"""
            + "\n".join(templates)
            + """
$(eval $(call book-dir-rules,bk))
$(eval $(call book-rules,book))
$(eval $(call book-preview-rules,book))
"""
        )
        self.pdf = "bk/build/book-preview-chapter.pdf"
        self.warm = "book-preview-master"

    def make(self, target, fail_job=None):
        env = {key: value for key, value in os.environ.items() if key != "FAIL_JOB"}
        if fail_job:
            env["FAIL_JOB"] = fail_job
        return subprocess.run(
            ["make", target],
            cwd=self.root,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )

    def assertPassed(self, result):
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_debug_tex_uses_the_real_highlight_transform(self):
        self.assertPassed(self.make("bk/build/book-debug.tex"))
        output = (self.root / "bk/build/book-debug.tex").read_text(encoding="utf-8")
        self.assertEqual(output.count(r"\booklinkhighlighttrue"), 1)

    def test_failed_preview_is_removed_and_retried(self):
        self.assertPassed(self.make("bk/build/book-preview-master.aux"))
        result = self.make(self.pdf, "book-preview-chapter")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertFalse((self.root / self.pdf).exists(), "failed PDF was left as a fresh target")
        self.assertPassed(self.make(self.pdf))
        self.assertEqual((self.root / self.pdf).read_text(), "complete\n")

    def test_index_preview_builds_and_reuses_the_complete_book_index(self):
        target = "bk/build/book-preview-_index.pdf"
        self.assertPassed(self.make(target))
        build = self.root / "bk/build"
        self.assertEqual((build / "book-preview-_index.ind").read_text(), "new term\n")
        self.assertEqual((build / "book-preview-_index.ind").read_bytes(), (build / "book-debug.ind").read_bytes())
        self.assertTrue((build / "book-preview/_index.tex").exists())
        self.assertFalse((build / "book-preview/_endmatter.tex").exists())
        self.assertEqual((self.root / "calls").read_text().splitlines()[-1], "book-preview-_index")
        calls = (self.root / "calls").read_text()
        self.assertPassed(self.make(target))
        self.assertEqual((self.root / "calls").read_text(), calls)

    def test_failed_warm_aux_is_removed_and_both_passes_are_retried(self):
        result = self.make(self.pdf, self.warm)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertFalse(
            (self.root / f"bk/build/{self.warm}.aux").exists(), "incomplete warm aux was left as a completed cache"
        )
        self.assertPassed(self.make(self.pdf))
        self.assertEqual(
            (self.root / "calls").read_text().splitlines(), [self.warm, self.warm, self.warm, "book-preview-chapter"]
        )

    def test_locale_change_rebuilds_tex_and_preview_without_rewarming(self):
        self.assertPassed(self.make("bk/build/book.tex"))
        self.assertPassed(self.make(self.pdf))
        for path in self.root.rglob("*"):
            if path.is_file():
                os.utime(path, (1, 1))
        for filename in ("bk/build/book.tex", "bk/build/book-debug.tex", "bk/build/book-preview-master.tex", self.pdf):
            os.utime(self.root / filename, (2, 2))
        locale = self.root / "bk/tex/locale.tex"
        locale.write_text("new presentation strings\n")
        self.assertPassed(self.make("bk/build/book.tex"))
        self.assertPassed(self.make(self.pdf))
        self.assertGreater((self.root / "bk/build/book.tex").stat().st_mtime, 2)
        self.assertGreater((self.root / "bk/build/book-debug.tex").stat().st_mtime, 2)
        self.assertEqual(
            (self.root / "calls").read_text().splitlines(),
            [self.warm, self.warm, "book-preview-chapter", "book-preview-chapter"],
        )

    def test_obsolete_warm_chapters_are_removed_before_preview(self):
        self.assertPassed(self.make(self.pdf))
        warm_aux = self.root / f"bk/build/{self.warm}.aux"
        warm_aux.write_text(warm_aux.read_text() + "\\@input{removed-chapter.aux}\n")
        # Keep this deterministic on Make versions with second-granularity mtimes.
        os.utime(self.root / self.pdf, (1, 1))
        # A normal split must inspect the actual cache, even if units.json
        # already describes the current layout from an earlier text edit.
        master = self.root / "bk/build/book-preview-master.tex"
        master.unlink()
        self.assertPassed(self.make(self.pdf))
        self.assertNotIn("removed-chapter", warm_aux.read_text())
        self.assertEqual(
            (self.root / "calls").read_text().splitlines(),
            [self.warm, self.warm, "book-preview-chapter", self.warm, self.warm, "book-preview-chapter"],
        )

    def test_incremental_debug_refreshes_stale_index_then_reuses_it(self):
        stem = self.root / "bk/build/book-debug"
        stem.with_suffix(".aux").write_text("aux\n")
        # The prior LaTeX pass already wrote a new idx, but did not rebuild ind.
        stem.with_suffix(".idx").write_text("new term\n")
        stem.with_suffix(".ind").write_text("old term\n")
        self.assertPassed(self.make("bk/build/book-debug.pdf"))
        self.assertEqual(stem.with_suffix(".ind").read_text(), "new term\n")
        self.assertEqual(stem.with_suffix(".log").read_text(), "")
        self.assertEqual((self.root / "calls").read_text().splitlines(), ["book-debug"] * 2)
        stem.with_suffix(".pdf").unlink()
        self.assertPassed(self.make("bk/build/book-debug.pdf"))
        self.assertEqual((self.root / "calls").read_text().splitlines(), ["book-debug"] * 3)

    def test_failed_incremental_debug_is_removed_and_retried(self):
        stem = self.root / "bk/build/book-debug"
        stem.with_suffix(".aux").write_text("aux\n")
        result = self.make("bk/build/book-debug.pdf", "book-debug")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertFalse(stem.with_suffix(".pdf").exists())
        self.assertPassed(self.make("bk/build/book-debug.pdf"))
        self.assertEqual(stem.with_suffix(".log").read_text(), "")


if __name__ == "__main__":
    unittest.main()
