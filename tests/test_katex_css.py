"""Preserve font-face boundaries and the root math style when trimming KaTeX."""

import importlib.util
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("prepare_katex_css", ROOT / "tools/prepare_katex_css.py")
prepare = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prepare)


class KatexCssTests(unittest.TestCase):
    def test_trimming_preserves_font_rules_and_root_style(self):
        css = (
            '@font-face{font-family:A;src:url(a.woff2) format("woff2"),url(a.ttf) format("truetype")}'
            '@font-face{font-family:B;src:url(b.woff2) format("woff2"),url(b.ttf) format("truetype")}'
            ".katex{font:normal 1.21em KaTeX_Main}"
        )
        trimmed = prepare.woff2_only(css)
        self.assertEqual(trimmed.count("@font-face{"), 2)
        self.assertEqual(trimmed.count("}"), 3)
        self.assertNotIn(".ttf", trimmed)
        self.assertIn("}.katex{font:", trimmed)
        self.assertEqual(prepare.woff2_only(trimmed), trimmed)

    def test_vendored_css_has_one_face_per_font_and_keeps_math_base_style(self):
        vendor = ROOT / "tools/formalization-viewer/vendor/katex"
        css = (vendor / "katex.min.css").read_text(encoding="utf-8")
        faces = re.findall(r"@font-face\{([^{}]*)\}", css)
        self.assertEqual(len(faces), len(list((vendor / "fonts").glob("*.woff2"))))
        for face in faces:
            self.assertEqual(face.count("font-family:"), 1)
            self.assertEqual(face.count("src:"), 1)
        self.assertRegex(css, r"(?:^|})\.katex\{font:")
        for font in re.findall(r"url\((fonts/[^)]+)\)", css):
            self.assertTrue((vendor / font).is_file(), font)


if __name__ == "__main__":
    unittest.main()
