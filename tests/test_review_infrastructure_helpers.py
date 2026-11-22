"""Regression checks for the infrastructure review's source-selection boundaries."""

import fcntl
import importlib.util
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("extract_section", ROOT / "tools/extract_book_section.py")
EXTRACT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(EXTRACT)

TEMPLATE_SPEC = importlib.util.spec_from_file_location("prepare_templates", ROOT / "tools/prepare_pandoc_templates.py")
TEMPLATES = importlib.util.module_from_spec(TEMPLATE_SPEC)
TEMPLATE_SPEC.loader.exec_module(TEMPLATES)


class TemplateGuardTests(unittest.TestCase):
    def test_caption_removal_and_changed_caption_block_fail(self):
        for changed in (r"\usepackage{caption}", "\\usepackage{caption}\n\\captionsetup[table]{skip=7pt}\n"):
            with self.assertRaisesRegex(ValueError, "table-caption"):
                TEMPLATES.adapt_captions(changed)
        self.assertEqual(TEMPLATES.adapt_captions("no caption package"), "no caption package")

    def test_font_override_rejects_unreviewed_upstream_changes(self):
        upstream = "before\n\\IfFileExists{microtype.sty}{}{}\n"
        local = (
            "$-- Based on the bundled Pandoc font-settings.latex partial.\n"
            "$-- Only the conditional around microtype is local; Japanese books opt out.\n"
            "before\n$if(disable-microtype)$\n"
            "% LuaTeX-ja provides the Japanese typography; do not load incompatible microtype.\n"
            "$else$\n\\IfFileExists{microtype.sty}{}{}\n$endif$\n"
        )
        TEMPLATES.verify_font_override(upstream, local)
        with self.assertRaisesRegex(ValueError, "updated Pandoc font-settings"):
            TEMPLATES.verify_font_override(upstream + "new font logic\n", local)
        with self.assertRaisesRegex(ValueError, "local Pandoc"):
            TEMPLATES.verify_font_override(upstream, local.removesuffix("$endif$\n"))


class SectionExtractionTests(unittest.TestCase):
    def test_long_fence_ignores_short_closing_fence(self):
        source = "# Before\n````latex\n```\n# Hidden\n````\n# After {#after}\n"
        headers = EXTRACT.parse_headers(source.splitlines())
        self.assertEqual([item["title"] for item in headers], ["Before", "After"])
        self.assertEqual(headers[1]["line"], 6)

    def test_comments_indented_code_and_math_are_not_attributes(self):
        source = "<!--\n# Hidden\n-->\n    # Code\n# Space $\\{0,1\\}$\n# Named {#named}\n"
        headers = EXTRACT.parse_headers(source.splitlines())
        self.assertEqual([item["title"] for item in headers], ["Space $\\{0,1\\}$", "Named"])
        self.assertEqual([item["label"] for item in headers], ["", "named"])


class BuildSelectionTests(unittest.TestCase):
    def run_helper(self, listing, *arguments):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Makefile").touch()
            calls = root / "calls"
            make = root / "make"
            make.write_text(
                '#!/bin/sh\ncase "$*" in *list-books*) printf "%s\\n" "$TEST_BOOKS";; '
                '*) printf "%s\\n" "$*" > "$TEST_CALLS";; esac\n'
            )
            make.chmod(0o755)
            result = subprocess.run(
                ["python3", str(ROOT / ".codex/skills/book-build/scripts/build_book_document.py"), *arguments],
                cwd=root,
                env=dict(os.environ, PATH=f"{root}:{os.environ['PATH']}", TEST_BOOKS=listing, TEST_CALLS=str(calls)),
                text=True,
                capture_output=True,
                check=False,
            )
            return result, calls.read_text() if calls.exists() else ""

    def test_public_checkout_selects_available_excerpt(self):
        result, command = self.run_helper("polish-space-ch1 polish-space-ch1 polish-space-ch1/src/polish-space-ch1.md")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(command.strip(), "validate-tex BOOKS=polish-space-ch1")

    def test_private_checkout_prefers_full_canonical_book(self):
        listing = (
            "polish-space-ch1 polish-space-ch1 polish-space-ch1/src/polish-space-ch1.md\n"
            "polish-space-book polish-space polish-space/src/polish-space-book.md"
        )
        result, command = self.run_helper(listing)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(command.strip(), "validate-tex BOOKS=polish-space-book")

    def test_chapter_source_is_rejected_before_any_build(self):
        result, command = self.run_helper("book book book/src/book.md", "--source", "book/src/book/chapter.md")
        self.assertEqual(result.returncode, 2)
        self.assertEqual(command, "")


class SetupDryRunTests(unittest.TestCase):
    def test_missing_perl_modules_with_existing_cpanm_does_not_install_or_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binaries = root / "bin"
            binaries.mkdir()
            calls = root / "unexpected-installs"
            for name in ("perl", "mise"):
                executable = binaries / name
                executable.write_text("#!/bin/sh\nexit 1\n")
                executable.chmod(0o755)
            for name in ("cpanm", "curl"):
                executable = binaries / name
                executable.write_text('#!/bin/sh\nprintf x >> "$TEST_INSTALL_CALLS"\nexit 77\n')
                executable.chmod(0o755)
            env = dict(
                os.environ,
                PATH=f"{binaries}:{os.environ['PATH']}",
                TEST_INSTALL_CALLS=str(calls),
                PROVISION_LEAN="0",
                TEXLIVE_ROOT=str(root / ".texlive"),
                PERL_LOCAL_LIB=str(root / ".perllib"),
            )
            result = subprocess.run(
                ["bash", str(ROOT / "setup.sh"), "--dry-run"],
                cwd=root,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn(str(binaries / "cpanm"), result.stderr)
            self.assertFalse(calls.exists())


class CacheDeletionTests(unittest.TestCase):
    def test_only_untracked_cache_inside_repository_is_removed(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            repo = base / "repo"
            repo.mkdir()
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            tracked = repo / "source[1]"
            tracked.mkdir()
            (tracked / "book.md").write_text("source")
            subprocess.run(["git", "--literal-pathspecs", "-C", str(repo), "add", "source[1]"], check=True)
            external = base / "external"
            external.mkdir()
            alias = repo / "alias"
            alias.symlink_to(external, target_is_directory=True)
            cache = repo / ".perllib"
            cache.mkdir()
            (cache / "derived").write_text("cache")
            for target in (base, repo, repo / ".git", tracked, external, alias):
                result = subprocess.run(
                    ["bash", str(ROOT / "tools/remove_setup_cache.sh"), str(repo), str(target)],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertNotEqual(result.returncode, 0, str(target))
                self.assertTrue(target.exists())
            result = subprocess.run(
                ["bash", str(ROOT / "tools/remove_setup_cache.sh"), str(repo), str(cache)], check=False
            )
            self.assertEqual(result.returncode, 0)
            self.assertFalse(cache.exists())
            self.assertEqual((tracked / "book.md").read_text(), "source")


class FileLockTests(unittest.TestCase):
    def test_lock_survives_exec_and_is_released_after_holder_exits(self):
        with tempfile.TemporaryDirectory() as directory:
            lock = Path(directory) / "lock"
            command = [
                sys.executable,
                str(ROOT / "tools/with_file_lock.py"),
                str(lock),
                sys.executable,
                "-c",
                "import sys; print('ready', flush=True); sys.stdin.read()",
            ]
            with subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True) as holder:
                try:
                    self.assertEqual(holder.stdout.readline().strip(), "ready")
                    with lock.open("r+") as probe:
                        with self.assertRaises(BlockingIOError):
                            fcntl.flock(probe.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                        holder.terminate()
                        holder.wait(timeout=5)
                        fcntl.flock(probe.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                finally:
                    if holder.poll() is None:
                        holder.kill()
                        holder.wait()

    def test_concurrent_worktree_cache_clones_copy_once(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            repo, worktree = base / "main", base / "worktree"
            repo.mkdir()
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            (repo / ".gitignore").write_text(".perllib/\n")
            subprocess.run(["git", "-C", str(repo), "add", ".gitignore"], check=True)
            subprocess.run(
                [
                    "git",
                    "-C",
                    str(repo),
                    "-c",
                    "user.name=Test",
                    "-c",
                    "user.email=test@example.invalid",
                    "commit",
                    "-qm",
                    "fixture",
                ],
                check=True,
            )
            subprocess.run(["git", "-C", str(repo), "worktree", "add", "--detach", "-q", str(worktree)], check=True)
            cache = repo / ".perllib"
            cache.mkdir()
            (cache / "compiled").write_text("derived")
            spy = base / "copy"
            calls = base / "copies"
            spy.write_text('#!/bin/sh\nprintf x >> "$TEST_COPIES"\nsleep 0.1\nexec cp -Rp "$@"\n')
            spy.chmod(0o755)
            env = dict(os.environ, CP_COW=str(spy), TEST_COPIES=str(calls))
            command = ["bash", str(ROOT / "tools/worktree_caches.sh")]
            processes = [
                subprocess.Popen(command, cwd=worktree, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                for _ in range(2)
            ]
            for process in processes:
                _, errors = process.communicate(timeout=20)
                self.assertEqual(process.returncode, 0, errors.decode())
            self.assertEqual(calls.read_text(), "x")
            self.assertEqual((worktree / ".perllib/compiled").read_text(), "derived")


if __name__ == "__main__":
    unittest.main()
