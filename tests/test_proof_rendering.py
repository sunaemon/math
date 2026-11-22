"""Render the passages that previously needed translation-only raw-TeX fences.

Exercise Pandoc itself, where the Unicode/nested-proof tail duplication happens,
not just the structural translation checker. `make test-python` supplies the
pinned Pandoc executable through mise.
"""

from __future__ import annotations

import re
import shutil
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which("pandoc"), "Pandoc is required for the rendering regression")
class ProofRenderingTest(unittest.TestCase):
    def test_canonical_and_translated_proofs_render_once(self):
        for book in ("polish-space", "polish-space-ja"):
            for chapter in ("determinacy", "polish-groups"):
                with self.subTest(book=book, chapter=chapter):
                    path = ROOT / book / "src" / "polish-space-book" / f"{chapter}.md"
                    if not path.is_file():
                        self.skipTest("full-book chapter is not shipped in this checkout")
                    source = path.read_text()
                    # Neither language should need the old whole-proof wrapper.
                    self.assertNotIn("```{=latex}", source)
                    self.assertIsNone(re.search(r"(?<!\\)\\$", source, re.MULTILINE))
                    rendered = subprocess.run(
                        ["pandoc", "-f", "markdown", "-t", "latex"],
                        input=source,
                        text=True,
                        capture_output=True,
                        check=True,
                    ).stdout
                    for marker in (r"\begin{proof}", r"\end{proof}"):
                        self.assertEqual(rendered.count(marker), source.count(marker))
                    # Pandoc's duplicate tail escaped the second closing command
                    # as prose; merely counting raw proof environments missed it.
                    self.assertFalse(r"\textbackslash end\{proof\}" in rendered, "duplicated proof tail")
                    self.assertFalse(r"\textbackslash begin\{proof\}" in rendered, "escaped proof opening")
                    for label in re.findall(r"\\label\{[^}]+\}", source):
                        self.assertEqual(rendered.count(label), source.count(label))
                    conclusion = (
                        r"\pi_x:G/G_x\to G\cdot x"
                        if chapter == "polish-groups"
                        else r"\label{sec:martin-inverse-limits}"
                    )
                    self.assertEqual(rendered.count(conclusion), 1)


if __name__ == "__main__":
    unittest.main()
