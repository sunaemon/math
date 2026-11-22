"""The publication excerpt must preserve the canonical Japanese mathematics."""

import contextlib
import io
import json
import re
import sys
import tempfile
import unittest
from collections import Counter
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import prepare_part1_edition as edition
from check_translation_structure import snapshot
from project_part1_sourcemap import EditionProjection, project_map


class PartOneEditionTest(unittest.TestCase):
    def test_positions_follow_edits_without_reusing_removed_text(self):
        source = "<!-- metadata -->\nfirst\nsee §{outside}.\nlast\nPART II\n"
        target = "PRELUDE\nfirst\nsee 本編「参照先」.\nlast\n"
        projection = EditionProjection(source, target)
        for needle in ("first", "last"):
            start = source.index(needle)
            bounds = projection.span(start, start + len(needle))
            self.assertIsNotNone(bounds)
            self.assertEqual(target[slice(*bounds)], needle)
        start = source.index("see")
        end = source.index("\nlast")
        self.assertEqual(target[slice(*projection.span(start, end))], "see 本編「参照先」.")
        self.assertIsNone(projection.span(source.index("PART II"), len(source)))

    def test_viewer_map_keeps_only_included_chapters_and_rewrites_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            book = Path(directory)
            generated = book / "build/source"
            generated.mkdir(parents=True)
            with patch.object(edition, "OUT", generated), contextlib.redirect_stdout(io.StringIO()):
                edition.prepare()
            original = ROOT / "polish-space-ja/src/polish-space-book/polish-spaces.md"
            text = original.read_text()
            needle = "# ポーランド空間 {#sec:polish-spaces}"
            start = text.index(needle)
            entry = {
                "match": {
                    "status": "matched",
                    "source": str(original),
                    "startOffset": start,
                    "endOffset": start + len(needle),
                },
                "lean": {"source": str(ROOT / "polish-space-ja/lean/PolishSpaceBook/PolishSpaces.lean")},
                "texMatch": {"entry": 999},
            }
            excluded = {"match": {"source": str(original.with_name("preface.md"))}}
            projected = project_map({"entries": [entry, excluded]}, edition=book)
            self.assertEqual(projected["entryCount"], 1)
            match = projected["entries"][0]["match"]
            excerpt = Path(match["source"]).read_text()
            self.assertEqual(excerpt[match["startOffset"] : match["endOffset"]], needle)
            self.assertEqual(projected["leanFiles"], [str(book / "lean/PolishSpaceBook/PolishSpaces.lean")])
            self.assertNotIn("texMatch", projected["entries"][0])

    def test_only_part_one_preserves_math_citations_and_headings(self):
        manifest = json.loads((ROOT / "polish-space-part1-ja/src/polish-space-part1-ja.json").read_text())
        self.assertEqual(len(manifest["chapters"]), 8)
        with tempfile.TemporaryDirectory() as directory:
            generated = Path(directory)
            with patch.object(edition, "OUT", generated), contextlib.redirect_stdout(io.StringIO()):
                edition.prepare()
            provenance = json.loads((generated / "provenance.json").read_text())
            self.assertEqual(len(provenance["chapters"]), 8)
            for source, included in zip(provenance["chapters"], manifest["chapters"], strict=True):
                original = (ROOT / source["source"]).read_text()
                original = re.split(r"\\part\{", original, maxsplit=1)[0]
                text = (generated / Path(included).name).read_text()
                original_structure = snapshot(original)
                generated_structure = snapshot(text)
                expected_math = Counter(item.value for item in original_structure.mathematics)
                for label, title in provenance["externalSections"].items():
                    count = original.count(f"§{{{label}}}")
                    for formula in snapshot(title).mathematics:
                        expected_math[formula.value] += count
                self.assertEqual(Counter(item.value for item in generated_structure.mathematics), expected_math)
                self.assertEqual(
                    [item.value for item in generated_structure.headings],
                    [item.value for item in original_structure.headings],
                )
                self.assertEqual(
                    [item.value for item in generated_structure.citations],
                    [item.value for item in original_structure.citations],
                )
            combined = (generated / "body.md").read_text()
            self.assertEqual(combined.count("\\part{"), 1)
            self.assertNotIn("part-definability-classification", combined)
            local = set(re.findall(r"\{#([^}]+)\}", combined))
            self.assertLessEqual(set(re.findall(r"§\{([^}]+)\}", combined)), local)


if __name__ == "__main__":
    unittest.main()
