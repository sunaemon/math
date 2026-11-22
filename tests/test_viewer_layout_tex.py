"""Viewer layout variants preserve document content and semantic anchors."""

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from viewer_layout_tex import layout_tex


class ViewerLayoutTest(unittest.TestCase):
    def test_reflows_english_and_japanese_without_changing_body(self):
        body = r"\begin{document}\BooklinkStart[entry=42]日本語 $x^2$\end{document}"
        for cls in ("book", "ltjsbook"):
            source = (
                "\\documentclass[\n10pt,a5paper,twoside,openright]{" + cls + "}\n"
                r"\usepackage[paper=a5paper,inner=18mm,outer=16mm]{geometry}" + "\n" + body
            )
            result = layout_tex(source, "b6", "12")
            self.assertIn(r"\documentclass[12pt,a5paper,twoside,openright]{" + cls + "}", result)
            self.assertIn("inner=18mm,outer=16mm,paperwidth=128mm,paperheight=182mm", result)
            self.assertNotIn("paper=a5paper", result)
            self.assertTrue(result.endswith(body))
            self.assertEqual(layout_tex(source, "default", "default"), source)

    def test_rejects_unsupported_or_unrecognized_inputs(self):
        with self.assertRaises(ValueError):
            layout_tex("", "a0", "10")
        with self.assertRaises(ValueError):
            layout_tex(r"\begin{document}", "a5", "12")


if __name__ == "__main__":
    unittest.main()
