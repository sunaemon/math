#!/usr/bin/env python3
"""Project a canonical booklink sourcemap onto a po4a translation.

Lean booklink markers continue to name the canonical English chapters.  This
tool pairs those chapters with a translated book manifest and rewrites matched and weak candidate
source spans to the corresponding PO message spans.  Untranslated fallback
chapters whose bytes are identical use exact offsets; translated messages use
their whole target message as a deliberately coarse but stable highlight,
refined to aligned sentence spans when both sides split into the same number
of sentences and every aligned pair carries the identical sequence of inline
formula and section-reference anchors. Matching theorem, proof, and metadata
delimiters also separate structural regions within a single PO message.
Overlapping translated booklinks share one verified target region carrying all
their declarations, so coarse PO alignment remains compatible with TeX injection.
"""

from __future__ import annotations

import argparse
import ast
import copy
import json
import os
import re
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from book_manifest import read_manifest
from check_translation_structure import normalize_math


class ProjectionError(RuntimeError):
    """A source map cannot be projected without guessing."""


@dataclass(frozen=True)
class PoMessage:
    msgid: str
    msgstr: str
    line: int = field(default=1, compare=False)


@dataclass(frozen=True)
class Segment:
    source_start: int
    source_end: int
    target_start: int
    target_end: int
    subsegments: tuple[Segment, ...] | None = None
    refinement: str = "po-sentence"


@dataclass(frozen=True)
class NormalizedText:
    text: str
    starts: tuple[int, ...]
    ends: tuple[int, ...]


@dataclass
class ChapterProjection:
    source: Path
    target: Path
    source_text: str
    target_text: str
    segments: list[Segment] | None

    def project_span(self, start: int, end: int) -> tuple[int, int, str]:
        if start < 0 or end <= start or end > len(self.source_text):
            raise ProjectionError(f"{self.source}: invalid source span {start}..{end}")
        if self.segments is None:
            return start, end, "exact"
        overlaps = [segment for segment in self.segments if segment.source_start < end and segment.source_end > start]
        if not overlaps:
            excerpt = self.source_text[start:end].replace("\n", " ")[:100]
            raise ProjectionError(f"{self.source}: no PO message covers {start}..{end}: {excerpt!r}")
        starts: list[int] = []
        ends: list[int] = []
        refined = True
        refinement = "po-sentence"
        for segment in overlaps:
            chosen = [sub for sub in (segment.subsegments or ()) if sub.source_start < end and sub.source_end > start]
            if chosen:
                if segment.refinement == "po-structure":
                    refinement = "po-structure"
                starts.extend(sub.target_start for sub in chosen)
                ends.extend(sub.target_end for sub in chosen)
            else:
                starts.append(segment.target_start)
                ends.append(segment.target_end)
                refined = False
        return min(starts), max(ends), refinement if refined else "po-message"


def _quoted(value: str, path: Path, line_number: int) -> str:
    try:
        parsed = ast.literal_eval(value)
    except (SyntaxError, ValueError) as error:
        raise ProjectionError(f"{path}:{line_number}: invalid PO string") from error
    if not isinstance(parsed, str):
        raise ProjectionError(f"{path}:{line_number}: expected a PO string")
    return parsed


def read_po(path: Path) -> list[PoMessage]:
    """Read reviewed singular messages; reject fuzzy entries before projection."""
    messages: list[PoMessage] = []
    msgid = ""
    msgstr = ""
    field: str | None = None
    seen = False
    obsolete = False
    fuzzy = False
    translation_line = 1

    def finish() -> None:
        nonlocal msgid, msgstr, field, seen, obsolete, fuzzy, translation_line
        if seen and not obsolete and msgid:
            if fuzzy:
                raise ProjectionError(f"{path}:{translation_line}: fuzzy PO entry cannot be projected")
            messages.append(PoMessage(msgid, msgstr, translation_line))
        msgid = ""
        msgstr = ""
        field = None
        seen = False
        obsolete = False
        fuzzy = False
        translation_line = 1

    for line_number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.strip()
        if not line:
            finish()
            continue
        if line.startswith("#~"):
            obsolete = True
            continue
        if line.startswith("#,"):
            fuzzy = fuzzy or "fuzzy" in {flag.strip() for flag in line[2:].split(",")}
            continue
        if line.startswith("#"):
            continue
        if line.startswith("msgid "):
            msgid = _quoted(line.removeprefix("msgid "), path, line_number)
            field = "msgid"
            seen = True
            continue
        if line.startswith("msgstr "):
            msgstr = _quoted(line.removeprefix("msgstr "), path, line_number)
            translation_line = line_number
            field = "msgstr"
            seen = True
            continue
        if line.startswith(("msgid_plural ", "msgstr[")):
            raise ProjectionError(f"{path}:{line_number}: plural PO entries are not supported")
        if line.startswith('"'):
            value = _quoted(line, path, line_number)
            if field == "msgid":
                msgid += value
            elif field == "msgstr":
                msgstr += value
            else:
                raise ProjectionError(f"{path}:{line_number}: orphan PO continuation")
            continue
        raise ProjectionError(f"{path}:{line_number}: unrecognized PO syntax")
    finish()
    return messages


def normalize_with_positions(text: str) -> NormalizedText:
    normalized: list[str] = []
    starts: list[int] = []
    ends: list[int] = []
    in_space = False
    for offset, character in enumerate(text):
        if character.isspace():
            if in_space:
                ends[-1] = offset + 1
            else:
                normalized.append(" ")
                starts.append(offset)
                ends.append(offset + 1)
                in_space = True
        else:
            normalized.append(character)
            starts.append(offset)
            ends.append(offset + 1)
            in_space = False
    return NormalizedText("".join(normalized), tuple(starts), tuple(ends))


def _normalized_message(text: str) -> str:
    return normalize_with_positions(text).text.strip()


def _occurrences(haystack: NormalizedText, needle: str) -> list[tuple[int, int]]:
    positions: list[tuple[int, int]] = []
    cursor = 0
    while True:
        found = haystack.text.find(needle, cursor)
        if found < 0:
            return positions
        last = found + len(needle) - 1
        positions.append((haystack.starts[found], haystack.ends[last]))
        cursor = found + len(needle)


_JA_SENTENCE_ENDERS = "。．！？"
_EN_SENTENCE_ENDERS = ".!?"
_SENTENCE_CLOSERS = "*)\"'’”]"
_ABBREVIATION_BEFORE_PERIOD = re.compile(r"(?:^|[\s(])(?:e\.g|i\.e|cf|vs|etc|resp|viz)$", re.IGNORECASE)
_ANCHOR = re.compile(r"\$\$.*?\$\$|\$[^$]*\$|§\{[^}]*\}", re.DOTALL)


def _mask_protected(text: str) -> str:
    """Mask math spans entirely and sentence punctuation inside brace groups."""
    out = list(text)
    i = 0
    n = len(text)
    depth = 0
    while i < n:
        character = text[i]
        if character == "$":
            marker = "$$" if text.startswith("$$", i) else "$"
            close = text.find(marker, i + len(marker))
            stop = n if close < 0 else close + len(marker)
            for j in range(i, stop):
                if not text[j].isspace():
                    out[j] = "M"
            i = stop
            continue
        if character == "{":
            depth += 1
        elif character == "}":
            depth = max(depth - 1, 0)
        elif depth > 0 and (character in _EN_SENTENCE_ENDERS or character in _JA_SENTENCE_ENDERS):
            out[i] = "M"
        i += 1
    return "".join(out)


_HTML_COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)


def _sentence_spans(text: str) -> list[tuple[int, int]]:
    """Split into trimmed sentence spans. An HTML comment (e.g. a
    formalization-skip marker inside a paragraph) is its own segment and a hard
    boundary — it carries no sentence punctuation, so it would otherwise glue
    onto the following sentence and drag any span that ends at the comment
    (a skip region ends at its closing comment) past that sentence. Comments
    are kept verbatim in translations, so both sides split identically."""
    spans: list[tuple[int, int]] = []
    cursor = 0
    for match in _HTML_COMMENT.finditer(text):
        spans.extend(
            (start + cursor, end + cursor) for start, end in _plain_sentence_spans(text[cursor : match.start()])
        )
        spans.append((match.start(), match.end()))
        cursor = match.end()
    spans.extend((start + cursor, end + cursor) for start, end in _plain_sentence_spans(text[cursor:]))
    return spans


def _plain_sentence_spans(text: str) -> list[tuple[int, int]]:
    """Split comment-free text into trimmed sentence spans; Japanese enders
    always end a sentence, ASCII enders only before a non-lowercase
    continuation and not after a known abbreviation."""
    masked = _mask_protected(text)
    n = len(masked)
    boundaries: list[int] = []
    for i, character in enumerate(masked):
        is_boundary = False
        if character in _JA_SENTENCE_ENDERS:
            is_boundary = True
        elif character in _EN_SENTENCE_ENDERS and not _ABBREVIATION_BEFORE_PERIOD.search(masked, 0, i):
            j = i + 1
            while j < n and masked[j] in _SENTENCE_CLOSERS:
                j += 1
            if j >= n:
                is_boundary = True
            elif masked[j].isspace():
                following = masked[j:].lstrip()
                if following and not following[0].islower():
                    is_boundary = True
        if is_boundary:
            j = i + 1
            while j < n and masked[j] in _SENTENCE_CLOSERS:
                j += 1
            boundaries.append(j)
    spans: list[tuple[int, int]] = []
    cursor = 0
    for boundary in [*boundaries, n]:
        if boundary <= cursor:
            continue
        piece = text[cursor:boundary]
        stripped = piece.strip()
        if stripped:
            lead = len(piece) - len(piece.lstrip())
            spans.append((cursor + lead, cursor + lead + len(piece.strip())))
        cursor = boundary
    return spans


def _anchors(text: str) -> list[str]:
    return [
        normalize_math(match.group(0)) if match.group(0).startswith("$") else match.group(0)
        for match in _ANCHOR.finditer(text)
    ]


def _sentence_subsegments(
    source_text: str,
    target_text: str,
    source_span: tuple[int, int],
    target_span: tuple[int, int],
) -> tuple[Segment, ...] | None:
    """Align source and target message occurrences sentence by sentence, or
    return None when the alignment cannot be verified."""
    source_slice = source_text[source_span[0] : source_span[1]]
    target_slice = target_text[target_span[0] : target_span[1]]
    source_sentences = _sentence_spans(source_slice)
    target_sentences = _sentence_spans(target_slice)
    if len(source_sentences) < 2 or len(source_sentences) != len(target_sentences):
        return None
    subsegments: list[Segment] = []
    for (source_start, source_end), (target_start, target_end) in zip(source_sentences, target_sentences, strict=True):
        # Compare each sentence's anchors as a multiset: natural Japanese
        # word order routinely permutes the formulas within a sentence, which
        # is still strong evidence the sentences correspond. Cross-sentence
        # misalignment keeps failing, since the sentences' own anchor sets
        # then disagree.
        if sorted(_anchors(source_slice[source_start:source_end])) != sorted(
            _anchors(target_slice[target_start:target_end])
        ):
            return None
        subsegments.append(
            Segment(
                source_span[0] + source_start,
                source_span[0] + source_end,
                target_span[0] + target_start,
                target_span[0] + target_end,
            )
        )
    return tuple(subsegments)


_STRUCTURAL_DELIMITER = re.compile(
    r"(?m)^[ \t]*\\(?:begin|end)\{(?:theorem\*|lemma\*|proposition\*|corollary\*|"
    r"claim\*|fact\*|recall\*|definition\*|example\*|construction\*|remark\*|statement\*|proof|mathmeta)\}"
)


def _structural_delimiters(text: str) -> list[re.Match[str]]:
    masked = _HTML_COMMENT.sub(lambda match: " " * len(match.group()), _mask_protected(text))
    return list(_STRUCTURAL_DELIMITER.finditer(masked))


def _structural_subsegments(
    source_text: str,
    target_text: str,
    source_span: tuple[int, int],
    target_span: tuple[int, int],
) -> tuple[Segment, ...] | None:
    """Pair exact structural delimiters inside verified PO occurrences.

    Sentence refinement runs only within each resulting region, so punctuation
    cannot attach the end of a statement to the beginning of its proof.
    Mismatched delimiters or formula anchors retain the whole-message fallback.
    """
    source_slice = source_text[slice(*source_span)]
    target_slice = target_text[slice(*target_span)]
    source_tags = _structural_delimiters(source_slice)
    target_tags = _structural_delimiters(target_slice)
    if not source_tags or [m.group().strip() for m in source_tags] != [m.group().strip() for m in target_tags]:
        return None
    source_bounds = [0, *(offset for tag in source_tags for offset in tag.span()), len(source_slice)]
    target_bounds = [0, *(offset for tag in target_tags for offset in tag.span()), len(target_slice)]
    segments: list[Segment] = []
    for a, b, c, d in zip(source_bounds[:-1], source_bounds[1:], target_bounds[:-1], target_bounds[1:], strict=True):
        left, right = source_slice[a:b], target_slice[c:d]
        if not left.strip() and not right.strip():
            continue
        if not left.strip() or not right.strip() or sorted(_anchors(left)) != sorted(_anchors(right)):
            return None
        source_piece = (
            source_span[0] + a + len(left) - len(left.lstrip()),
            source_span[0] + b - len(left) + len(left.rstrip()),
        )
        target_piece = (
            target_span[0] + c + len(right) - len(right.lstrip()),
            target_span[0] + d - len(right) + len(right.rstrip()),
        )
        sentences = _sentence_subsegments(source_text, target_text, source_piece, target_piece)
        segments.extend(sentences or (Segment(*source_piece, *target_piece),))
    return tuple(segments)


def po_segments(source_text: str, target_text: str, messages: list[PoMessage], path: Path) -> list[Segment]:
    source = normalize_with_positions(source_text)
    target = normalize_with_positions(target_text)
    segments: list[Segment] = []
    for message in messages:
        source_needle = _normalized_message(message.msgid)
        target_needle = _normalized_message(message.msgstr)
        if not source_needle or not target_needle:
            continue
        source_hits = _occurrences(source, source_needle)
        target_hits = _occurrences(target, target_needle)
        if len(source_hits) != len(target_hits):
            preview = message.msgid.replace("\n", " ")[:90]
            raise ProjectionError(
                f"{path}: PO message occurrence mismatch ({len(source_hits)} source, "
                f"{len(target_hits)} target): {preview!r}"
            )
        for source_span, target_span in zip(source_hits, target_hits, strict=True):
            structural = bool(
                _structural_delimiters(source_text[slice(*source_span)])
                or _structural_delimiters(target_text[slice(*target_span)])
            )
            refine = _structural_subsegments if structural else _sentence_subsegments
            segments.append(
                Segment(
                    *source_span,
                    *target_span,
                    refine(source_text, target_text, source_span, target_span),
                    "po-structure" if structural else "po-sentence",
                )
            )
    return sorted(segments, key=lambda segment: (segment.source_start, segment.source_end))


def _manifest_pairs(source_manifest: Path, target_manifest: Path) -> list[tuple[Path, Path]]:
    _source_master, source_chapters = read_manifest(source_manifest)
    _target_master, target_chapters = read_manifest(target_manifest)
    if len(source_chapters) != len(target_chapters):
        raise ProjectionError("canonical and translated manifests have different chapter counts")
    pairs: list[tuple[Path, Path]] = []
    for source, target in zip(source_chapters, target_chapters, strict=True):
        source_path = source_manifest.resolve().parents[2] / source
        target_path = target_manifest.resolve().parents[2] / target
        if source_path.name != target_path.name:
            raise ProjectionError(f"chapter mismatch: {source_path.name} vs {target_path.name}")
        pairs.append((source_path, target_path))
    return pairs


def load_projections(source_manifest: Path, target_manifest: Path, po_dir: Path) -> dict[Path, ChapterProjection]:
    projections: dict[Path, ChapterProjection] = {}
    for source, target in _manifest_pairs(source_manifest, target_manifest):
        source = source.resolve()
        target = target.absolute()
        source_text = source.read_text(encoding="utf-8")
        target_text = target.read_text(encoding="utf-8")
        if source_text == target_text:
            segments = None
        else:
            po = po_dir / f"{target.stem}.po"
            if not po.is_file():
                raise ProjectionError(f"{target}: translated bytes differ but {po} does not exist")
            segments = po_segments(source_text, target_text, read_po(po), po)
        projections[source] = ChapterProjection(source, target, source_text, target_text, segments)
    return projections


def _line_column(text: str, offset: int) -> tuple[int, int]:
    line = text.count("\n", 0, offset) + 1
    previous = text.rfind("\n", 0, offset)
    return line, offset if previous < 0 else offset - previous - 1


def _rewrite_span(span: dict[str, Any], projection: ChapterProjection) -> None:
    start = span.get("startOffset")
    end = span.get("endOffset")
    if not isinstance(start, int) or not isinstance(end, int):
        raise ProjectionError(f"{projection.source}: matched span lacks integer offsets")
    target_start, target_end, kind = projection.project_span(start, end)
    start_line, start_column = _line_column(projection.target_text, target_start)
    end_line, end_column = _line_column(projection.target_text, target_end)
    span.update(
        {
            "source": str(projection.target.absolute()),
            "startLine": start_line,
            "startColumn": start_column,
            "startOffset": target_start,
            "endLine": end_line,
            "endColumn": end_column,
            "endOffset": target_end,
            "translationProjection": kind,
        }
    )


def _source_projection(source: str, projections: dict[Path, ChapterProjection], root: Path) -> ChapterProjection | None:
    path = Path(source)
    resolved = path.resolve() if path.is_absolute() else (root / path).resolve()
    return projections.get(resolved)


def _rewrite_lean_path(value: Any, source_project: Path, target_project: Path) -> Any:
    if not isinstance(value, str):
        return value
    path = Path(value)
    if not path.is_absolute():
        return value
    try:
        relative = path.resolve().relative_to(source_project.resolve())
    except ValueError:
        return value
    return str((target_project.absolute() / relative).absolute())


def _share_projected_booklink_spans(projected: dict[str, Any], projections: dict[Path, ChapterProjection]) -> None:
    """Give overlapping translated booklinks one common target region.

    Disjoint English excerpts can cover parts of the same PO message. Expanding
    them to verified message/sentence boundaries may produce nested or crossing
    target spans. The injector already groups identical spans into one band
    carrying every declaration, so use the union of each connected overlap
    group on both the injection map and the viewer map. Exact fallback spans
    remain untouched; statement/prose boundaries must not be merged.
    """
    chapters = {str(chapter.target.absolute()): chapter for chapter in projections.values()}
    by_source: dict[str, list[dict[str, Any]]] = {}
    for entry in projected.get("entries", []):
        if not isinstance(entry, dict):
            continue
        match = entry.get("match", {})
        if (
            isinstance(match, dict)
            and match.get("status") == "matched"
            and match.get("translationProjection") in {"po-message", "po-sentence", "po-structure"}
        ):
            by_source.setdefault(match["source"], []).append(entry)

    def share(group: list[dict[str, Any]]) -> None:
        if len(group) < 2:
            return
        spans = [entry["match"] for entry in group]
        # Proof and prose links both use a body band in the TeX injector. Keep
        # their individual targets for Lean highlighting, but let them share a
        # translated paragraph. Only a statement/body boundary is incompatible.
        kinds = {"statement" if entry.get("booklink", {}).get("target") == "statement" else "body" for entry in group}
        if len(kinds) != 1:
            raise ProjectionError(f"{spans[0]['source']}: overlapping translation spans mix statements and prose")
        if len({(span["startOffset"], span["endOffset"]) for span in spans}) == 1:
            return
        start = min(span["startOffset"] for span in spans)
        end = max(span["endOffset"] for span in spans)
        text = chapters[spans[0]["source"]].target_text
        start_line, start_column = _line_column(text, start)
        end_line, end_column = _line_column(text, end)
        for span in spans:
            span.update(
                startOffset=start,
                endOffset=end,
                startLine=start_line,
                startColumn=start_column,
                endLine=end_line,
                endColumn=end_column,
                translationProjection="po-shared",
            )

    for entries in by_source.values():
        group: list[dict[str, Any]] = []
        end = -1
        for entry in sorted(entries, key=lambda entry: (entry["match"]["startOffset"], entry["match"]["endOffset"])):
            span = entry["match"]
            if span["startOffset"] >= end:
                share(group)
                group = []
            group.append(entry)
            end = max(end, span["endOffset"])
        share(group)


def project_map(
    source_map: dict[str, Any],
    projections: dict[Path, ChapterProjection],
    source_project: Path,
    target_project: Path,
) -> dict[str, Any]:
    projected = copy.deepcopy(source_map)
    for entry in projected.get("entries", []):
        if not isinstance(entry, dict):
            continue
        match = entry.get("match")
        if (
            isinstance(match, dict)
            and match.get("status") in {"matched", "weak"}
            and isinstance(match.get("source"), str)
        ):
            projection = _source_projection(match["source"], projections, source_project.resolve().parent)
            if projection is not None:
                # A weak candidate stays weak: projection changes navigation,
                # not confidence, and only matched entries are injected into TeX.
                # Retain the exact evidence span. A widened navigation band is
                # not evidence that every sentence of its PO message is linked.
                entry["canonicalMatch"] = copy.deepcopy(match)
                _rewrite_span(match, projection)
        lean = entry.get("lean")
        if isinstance(lean, dict):
            lean["source"] = _rewrite_lean_path(lean.get("source"), source_project, target_project)

    _share_projected_booklink_spans(projected, projections)

    for skip in projected.get("skips", []):
        if not isinstance(skip, dict) or not isinstance(skip.get("source"), str):
            continue
        projection = _source_projection(skip["source"], projections, source_project.resolve().parent)
        if projection is not None:
            _rewrite_span(skip, projection)

    projected["root"] = str(target_project.resolve())
    projected["leanFile"] = _rewrite_lean_path(projected.get("leanFile"), source_project, target_project)
    lean_files = projected.get("leanFiles")
    if isinstance(lean_files, list):
        projected["leanFiles"] = [_rewrite_lean_path(value, source_project, target_project) for value in lean_files]
    projected["translation"] = {
        "canonicalProject": str(source_project.resolve()),
        "project": str(target_project.resolve()),
        "projection": "po-message",
        "coverage": "canonical-units; projected bands are navigation only",
    }
    return projected


def write_projected_map(path: Path, projected: dict[str, Any]) -> None:
    """Publish a complete map, including when another build is reading it."""
    path.parent.mkdir(parents=True, exist_ok=True)
    content = json.dumps(projected, ensure_ascii=False, indent=2) + "\n"
    descriptor, name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            stream.write(content)
        temporary.chmod(path.stat().st_mode & 0o777 if path.exists() else 0o644)
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-map", type=Path, required=True)
    parser.add_argument("--source-manifest", type=Path, required=True)
    parser.add_argument("--translation-manifest", type=Path, required=True)
    parser.add_argument("--po-dir", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        source_map = json.loads(args.source_map.read_text(encoding="utf-8"))
        if not isinstance(source_map, dict):
            raise ProjectionError("source map root must be an object")
        projections = load_projections(args.source_manifest, args.translation_manifest, args.po_dir)
        source_project = args.source_manifest.parent.parent
        target_project = args.translation_manifest.parent.parent
        projected = project_map(source_map, projections, source_project, target_project)
        write_projected_map(args.out, projected)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError, ProjectionError) as error:
        print(f"translation sourcemap projection failed: {error}", file=sys.stderr)
        return 1
    print(f"translation sourcemap: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
