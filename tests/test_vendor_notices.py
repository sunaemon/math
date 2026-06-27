"""Tests for tools/vendor_notices.py.

The most important is the up-to-date gate: THIRD-PARTY-NOTICES.md must equal what
the script generates from vendor/manifest.json, so the committed notices (and the
viewer's About panel, which reads the same manifest) never drift. The rest pin
the rendering, the license-URL templating, and set-version.
Run with `python -m unittest` (stdlib only, no pytest).
"""

import json
import os
import sys
import tempfile
import unittest
from argparse import Namespace
from pathlib import Path
from unittest import mock

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO_ROOT, "tools"))

import vendor_notices as vn  # noqa: E402


class NoticesUpToDateTest(unittest.TestCase):
    def test_notices_match_manifest(self):
        expected = vn.render_notices(vn.load_manifest())
        actual = vn.NOTICES.read_text(encoding="utf-8")
        self.assertEqual(
            actual,
            expected,
            "THIRD-PARTY-NOTICES.md is stale; run `python tools/vendor_notices.py generate`",
        )

    def test_check_command_passes(self):
        self.assertEqual(vn.cmd_check(None), 0)

    def test_every_component_has_a_nonempty_license_file(self):
        for component in vn.load_manifest()["components"]:
            rel = component.get("licenseFile")
            self.assertTrue(rel, f"{component['id']} has no licenseFile")
            self.assertTrue((vn.VENDOR_DIR / rel).is_file(), f"missing license file for {component['id']}: {rel}")
            self.assertTrue(vn.read_license_text(component).strip(), f"empty license text for {component['id']}")


class RenderTest(unittest.TestCase):
    def test_render_includes_metadata(self):
        manifest = {
            "components": [
                {
                    "id": "x",
                    "name": "X",
                    "version": "1.2.3",
                    "spdx": "MIT",
                    "homepage": "https://example.test/x",
                    "files": ["x/a", "x/b"],
                    "licenseFile": None,
                }
            ]
        }
        out = vn.render_notices(manifest)
        self.assertIn("## X", out)
        self.assertIn("Version: 1.2.3", out)
        self.assertIn("License: MIT", out)
        self.assertIn("`x/a`, `x/b`", out)
        self.assertIn("https://example.test/x", out)

    def test_pointer_when_license_not_inlined(self):
        manifest = {
            "components": [
                {
                    "id": "y",
                    "name": "Y",
                    "version": "1",
                    "spdx": "Apache-2.0",
                    "homepage": "https://example.test/y",
                    "files": [],
                    "licenseFile": "pdfjs/LICENSE",
                    "licenseInline": False,
                }
            ]
        }
        out = vn.render_notices(manifest)
        self.assertIn("see [pdfjs/LICENSE](pdfjs/LICENSE)", out)
        self.assertNotIn("```", out.split("## Y", 1)[1])  # no fenced license block


class LicenseUrlTest(unittest.TestCase):
    def test_version_substitution(self):
        self.assertEqual(
            vn.license_url({"version": "0.16.11", "licenseUrl": "https://x/v{version}/LICENSE"}),
            "https://x/v0.16.11/LICENSE",
        )
        self.assertIsNone(vn.license_url({"version": "1"}))


class SetVersionTest(unittest.TestCase):
    def test_set_version_writes_manifest(self):
        manifest = vn.load_manifest()
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as handle:
            json.dump(manifest, handle)
            tmp = Path(handle.name)
        try:
            with mock.patch.object(vn, "MANIFEST", tmp):
                vn.cmd_set_version(Namespace(id="katex", version="9.9.9"))
            updated = json.loads(tmp.read_text(encoding="utf-8"))
            katex = next(c for c in updated["components"] if c["id"] == "katex")
            self.assertEqual(katex["version"], "9.9.9")
        finally:
            tmp.unlink()


if __name__ == "__main__":
    unittest.main()
