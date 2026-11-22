"""Make include generation and validation agree on artifact identities."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import validate_book_build as validator


class BookIdentityTest(unittest.TestCase):
    def test_both_entry_points_share_master_and_stem_validation(self):
        for stem, source, accepted in [("book", "book", True), ("book", "other", False), ("bad.dot", "bad.dot", False)]:
            with self.subTest(stem=stem, source=source), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                src = root / "bk/src"
                src.mkdir(parents=True)
                manifest = src / f"{stem}.json"
                (src / f"{source}.md").write_text("# Title\n", encoding="utf-8")
                manifest.write_text(json.dumps({"source": f"bk/src/{source}.md", "chapters": []}), encoding="utf-8")
                result = subprocess.run(
                    [sys.executable, str(ROOT / "tools/books_mk.py"), f"bk/src/{stem}.json"],
                    cwd=root,
                    check=False,
                    capture_output=True,
                    text=True,
                )
                if accepted:
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertIn("BOOK_STEMS := book\n", result.stdout)
                    self.assertIn("book_DIR := bk\n", result.stdout)
                    self.assertIn("book_SOURCE := bk/src/book.md\n", result.stdout)
                    self.assertEqual(set(validator.discover_books(root)), {stem})
                else:
                    self.assertEqual(result.returncode, 2)
                    with self.assertRaises(ValueError):
                        validator.discover_books(root)
