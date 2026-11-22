#!/usr/bin/env python3
"""Project the reviewed Japanese source positions onto the Part I excerpt.

Line alignment limits character alignment to the edition's small local edits.
No English offsets or full-book PDF positions are reused for this edition.
"""

from __future__ import annotations

import argparse
import copy
import difflib
import json
from collections import Counter
from pathlib import Path

from booklink_sourcemap import attach_tex_matches, line_offsets, span_json
from project_translation_sourcemap import write_projected_map

ROOT = Path(__file__).resolve().parents[1]
EDITION = ROOT / "polish-space-part1-ja"
JAPANESE = ROOT / "polish-space-ja"


class EditionProjection:
    def __init__(self, original: str, excerpt: str):
        self.original = original
        self.excerpt = excerpt
        self.blocks: list[tuple[str, int, int, int, int]] = []
        old_lines, new_lines = original.splitlines(keepends=True), excerpt.splitlines(keepends=True)
        old_offsets, new_offsets = line_offsets(original), line_offsets(excerpt)
        # Include an end sentinel even when the final line has no newline.
        old_offsets = old_offsets[: len(old_lines)] + [len(original)]
        new_offsets = new_offsets[: len(new_lines)] + [len(excerpt)]
        for tag, a, b, c, d in difflib.SequenceMatcher(None, old_lines, new_lines, autojunk=False).get_opcodes():
            start, end, target, target_end = old_offsets[a], old_offsets[b], new_offsets[c], new_offsets[d]
            if tag != "replace":
                self.blocks.append((tag, start, end, target, target_end))
                continue
            for kind, i, j, k, l in difflib.SequenceMatcher(
                None, original[start:end], excerpt[target:target_end], autojunk=False
            ).get_opcodes():
                self.blocks.append((kind, start + i, start + j, target + k, target + l))

    def span(self, start: int, end: int) -> tuple[int, int] | None:
        if not 0 <= start < end <= len(self.original):
            raise ValueError(f"Invalid original span: {start}..{end}")
        portions = []
        for tag, a, b, c, d in self.blocks:
            if a >= end or b <= start or tag == "delete":
                continue
            if tag == "equal":
                portions.append((c + max(start, a) - a, c + min(end, b) - a))
            else:
                portions.append((c, d))
        if not portions:
            return None
        return portions[0][0], portions[-1][1]


def project_map(source_map: dict, edition: Path = EDITION, japanese: Path = JAPANESE) -> dict:
    provenance = json.loads((edition / "build/source/provenance.json").read_text())
    chapters = {}
    for chapter in provenance["chapters"]:
        source = ROOT / chapter["source"]
        target = edition / "build/source" / source.name
        chapters[str(source)] = (target, EditionProjection(source.read_text(), target.read_text()))

    def rewrite(span: dict) -> bool:
        pair = chapters.get(span.get("source"))
        if not pair:
            return False
        target, projection = pair
        if not isinstance(span.get("startOffset"), int) or not isinstance(span.get("endOffset"), int):
            return False
        offsets = projection.span(span["startOffset"], span["endOffset"])
        if offsets is None:
            return False
        start, end = offsets
        span.update(span_json(projection.excerpt, start, end))
        span["source"] = str(target)
        return True

    projected = copy.deepcopy(source_map)
    entries = []
    for entry in projected.get("entries", []):
        if not rewrite(entry.get("match", {})):
            continue
        entry.pop("texMatch", None)
        lean = entry.get("lean", {})
        if lean.get("source"):
            lean["source"] = str(edition / Path(lean["source"]).relative_to(japanese))
        entries.append(entry)
    projected["entries"] = entries
    projected["skips"] = [skip for skip in projected.get("skips", []) if rewrite(skip)]
    for skip in projected["skips"]:
        skip.pop("texMatch", None)
    projected["entryCount"] = len(entries)
    projected["counts"] = dict(Counter(entry["match"]["status"] for entry in entries))
    projected["root"] = str(edition)
    projected["leanFiles"] = sorted({entry["lean"]["source"] for entry in entries})
    projected["leanFile"] = projected["leanFiles"][0] if projected["leanFiles"] else None
    projected["edition"] = {"sourceProject": str(japanese), "chapters": list(chapters)}
    for key in ("texFile", "texMarkerCount", "texCounts"):
        projected.pop(key, None)
    return projected


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-map", type=Path, required=True)
    parser.add_argument("--tex-file", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    projected = project_map(json.loads(args.source_map.read_text()))
    if args.tex_file:
        attach_tex_matches(projected, args.tex_file.absolute())
    write_projected_map(args.out, projected)
    print(f"Part I sourcemap: {len(projected['entries'])} entries -> {args.out}")


if __name__ == "__main__":
    main()
