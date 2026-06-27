#!/usr/bin/env python3
"""Build a source map from Lean booklink markers to book source locations."""

import argparse
import difflib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any


def book_src_root(lean_file: Path | str) -> str:
    """Repo-relative `<book>/src` for a `<book>/lean/...` Lean file.

    Booklink `source:` values are written relative to the formalizing book's
    source root (for example `polish-space-book/polish-spaces.md`), so the
    marker stays book-agnostic. The owning book is the path component just
    before `lean/`; the real source lives under `<book>/src/`."""
    parts = PurePosixPath(lean_file).parts
    try:
        index = parts.index("lean")
    except ValueError as error:
        raise ValueError(f"Lean file is not under a <book>/lean/ tree: {lean_file}") from error
    if index == 0:
        raise ValueError(f"Lean file is not under a <book>/lean/ tree: {lean_file}")
    return f"{parts[index - 1]}/src"


# Keep in sync with statementEnvironments in tools/book-filter/Main.hs.
STATEMENT_ENVS = {
    "theorem",
    "lemma",
    "proposition",
    "corollary",
    "claim",
    "fact",
    "definition",
    "example",
    "construction",
    "remark",
    "statement",
    "recall",
}


@dataclass
class Marker:
    lean_file: Path
    marker_line: int
    end_line: int
    data: dict[str, Any]
    decl_kind: str | None = None
    decl_name: str | None = None
    decl_line: int | None = None
    decl_end_line: int | None = None


@dataclass
class Statement:
    source: Path
    kind: str
    title: str | None
    start_line: int
    end_line: int
    start_offset: int
    end_offset: int


@dataclass
class TexBooklinkSpan:
    names: list[str]
    kind: str | None
    start_offset: int
    end_offset: int
    entry: int | None = None


def strip_latex_macros(text: str) -> str:
    replacements = {
        r"\R": "R",
        r"\QQ": "Q",
        r"\NN": "N",
        r"\omega": "omega",
        r"\ell": "l",
        r"\infty": "infty",
        r"\Gdelta": "Gdelta",
        r"\Fsigma": "Fsigma",
        r"\CantorSpace": "CantorSpace",
        r"\BaireSpace": "BaireSpace",
        r"\HilbertCube": "HilbertCube",
        r"\RealSequenceSpace": "RealSequenceSpace",
        r"\IncludedIn": " included in ",
        r"\cong": " congruent to ",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)

    def second_arg(match: re.Match[str]) -> str:
        return match.group(2)

    def first_arg(match: re.Match[str]) -> str:
        return match.group(1)

    text = re.sub(r"\\termdefineas\{([^{}]*)\}\{([^{}]*)\}", second_arg, text)
    text = re.sub(r"\\termuseas\{([^{}]*)\}\{([^{}]*)\}", second_arg, text)
    text = re.sub(r"\\termdefine\{([^{}]*)\}", first_arg, text)
    text = re.sub(r"\\termuse\{([^{}]*)\}", first_arg, text)
    text = re.sub(r"\\[A-Za-z]+\{([^{}]*)\}", first_arg, text)
    text = re.sub(r"\\[A-Za-z]+", " ", text)
    return text


def normalize(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip().casefold()


def parse_marker_body(body: list[str]) -> dict[str, Any]:
    data: dict[str, Any] = {}
    i = 0
    while i < len(body):
        raw = body[i]
        if not raw.strip():
            i += 1
            continue
        match = re.match(r"(\s*)([A-Za-z_][A-Za-z0-9_-]*)\s*:\s*(.*?)\s*$", raw)
        if not match:
            i += 1
            continue
        key_indent_raw, key, value = match.groups()
        key_indent = len(key_indent_raw)
        if value == "|":
            i += 1
            block: list[str] = []
            base_indent: int | None = None
            while i < len(body):
                next_raw = body[i]
                next_indent = len(next_raw) - len(next_raw.lstrip())
                if next_indent <= key_indent and re.match(r"\s*[A-Za-z_][A-Za-z0-9_-]*\s*:", next_raw):
                    break
                if next_raw.strip() and base_indent is None:
                    base_indent = next_indent
                if base_indent is None:
                    block.append("")
                else:
                    block.append(next_raw[base_indent:] if len(next_raw) >= base_indent else "")
                i += 1
            data[key] = "\n".join(block).strip("\n")
            continue
        data[key] = value.strip().strip('"')
        i += 1
    return data


def find_decl_end_line(lines: list[str], decl_index: int) -> int:
    decl_prefix = r"(?:@\[[^\]]+\]\s*)*(?:private\s+)?(?:noncomputable\s+)?"
    next_decl_re = re.compile(rf"^\s*{decl_prefix}(theorem|lemma|def|abbrev|instance|class|structure|example)\b")
    last_nonblank = decl_index
    for idx in range(decl_index + 1, len(lines)):
        stripped = lines[idx].strip()
        if not stripped or stripped == "/-@ booklink:" or next_decl_re.match(lines[idx]):
            break
        last_nonblank = idx
    return last_nonblank + 1


def find_next_decl(lines: list[str], start: int) -> tuple[str | None, str | None, int | None, int | None]:
    decl_prefix = r"(?:@\[[^\]]+\]\s*)*(?:private\s+)?(?:noncomputable\s+)?"
    decl_re = re.compile(
        rf"\s*{decl_prefix}(theorem|lemma|def|abbrev|instance|class|structure|example)\s+([A-Za-z0-9_'.]+)?"
    )
    for idx in range(start, len(lines)):
        match = decl_re.match(lines[idx])
        if match:
            return match.group(1), match.group(2), idx + 1, find_decl_end_line(lines, idx)
    return None, None, None, None


def parse_lean_markers(path: Path) -> list[Marker]:
    lines = path.read_text(encoding="utf-8").splitlines()
    markers: list[Marker] = []
    i = 0
    while i < len(lines):
        if lines[i].strip() == "/-@ booklink:":
            marker_line = i + 1
            body: list[str] = []
            i += 1
            while i < len(lines) and lines[i].strip() != "-/":
                body.append(lines[i])
                i += 1
            if i >= len(lines):
                raise ValueError(f"unclosed booklink marker at {path}:{marker_line}")
            end_line = i + 1
            data = parse_marker_body(body)
            decl_kind, decl_name, decl_line, decl_end_line = find_next_decl(lines, i + 1)
            markers.append(Marker(path, marker_line, end_line, data, decl_kind, decl_name, decl_line, decl_end_line))
        i += 1
    return markers


def parse_book_statements(path: Path) -> list[Statement]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    offsets = line_offsets(text)
    begin_re = re.compile(r"\\begin\{(" + "|".join(sorted(STATEMENT_ENVS)) + r")\*?\}(?:\[(.*)\])?")
    statements: list[Statement] = []
    for idx, line in enumerate(lines):
        match = begin_re.search(line)
        if not match:
            continue
        kind = match.group(1)
        title = match.group(2)
        end_line = idx + 1
        end_re = re.compile(r"\\end\{" + re.escape(kind) + r"\*?\}")
        for j in range(idx + 1, len(lines)):
            if end_re.search(lines[j]):
                end_line = j + 1
                break
        statements.append(
            Statement(
                source=path,
                kind=kind,
                title=strip_latex_macros(title).strip() if title else None,
                start_line=idx + 1,
                end_line=end_line,
                start_offset=offsets[idx],
                end_offset=offsets[end_line - 1] + len(lines[end_line - 1]),
            )
        )
    return statements


# A `<!-- formalization: skip ... -->` comment marks book prose that is
# deliberately not a formalization obligation. `skip-begin`/`skip-end` bracket a
# region; a bare `skip` governs the single block that follows it. The reason text
# is whatever sits between the `skip[-variant]` keyword and the closing `-->`,
# usually wrapped in parentheses (which may themselves contain parentheses, so we
# strip a single outer pair rather than parsing balanced parens).
SKIP_COMMENT_RE = re.compile(
    r"<!--\s*formalization:\s*skip(?P<variant>-begin|-end)?\b(?P<rest>.*?)-->",
    re.DOTALL,
)


def skip_reason(rest: str) -> str | None:
    reason = rest.strip()
    if reason.startswith("(") and reason.endswith(")"):
        reason = reason[1:-1].strip()
    reason = re.sub(r"\s+", " ", reason)
    return reason or None


def block_after_marker(text: str, after: int) -> int:
    """End offset of the single block a bare `skip` marker governs.

    The marker applies to the next block: either a `\\begin{env}...\\end{env}`
    environment or, failing that, the paragraph up to the next blank line."""
    n = len(text)
    i = after
    while i < n and text[i] in " \t\r\n":
        i += 1
    if i >= n:
        return after
    content_start = i
    line_end = text.find("\n", content_start)
    if line_end == -1:
        line_end = n
    begin_match = re.match(r"\s*\\begin\{([A-Za-z*]+)\}", text[content_start:line_end])
    if begin_match:
        end_re = re.compile(r"\\end\{" + re.escape(begin_match.group(1)) + r"\}")
        end_match = end_re.search(text, content_start)
        if end_match:
            eol = text.find("\n", end_match.end())
            return eol if eol != -1 else n
        return line_end
    para_end = text.find("\n\n", content_start)
    return n if para_end == -1 else para_end


def parse_skip_spans(path: Path) -> list[dict[str, Any]]:
    """Spans for the `formalization: skip` comments in one book source.

    Region markers (`skip-begin`/`skip-end`) span from the opening comment to the
    closing comment inclusive; a bare `skip` spans from the comment through the
    block it governs. Offsets are code-point offsets, matching the rest of the map."""
    text = path.read_text(encoding="utf-8")
    spans: list[dict[str, Any]] = []
    stack: list[tuple[int, str | None]] = []
    for match in SKIP_COMMENT_RE.finditer(text):
        variant = match.group("variant")
        reason = skip_reason(match.group("rest"))
        if variant == "-begin":
            stack.append((match.start(), reason))
        elif variant == "-end":
            if not stack:
                continue
            start_offset, start_reason = stack.pop()
            spans.append(_skip_span(path, text, start_offset, match.end(), "region", start_reason))
        else:
            spans.append(_skip_span(path, text, match.start(), block_after_marker(text, match.end()), "block", reason))
    spans.sort(key=lambda span: span["startOffset"])
    return spans


def _skip_span(
    path: Path, text: str, start_offset: int, end_offset: int, kind: str, reason: str | None
) -> dict[str, Any]:
    # `key` is the stable join between this map and the TeX anchors the book
    # filter injects (`\SkipStart{key}` -> hypertarget `skip-key-start`). It is a
    # pure function of the source file and code-point offset, so the all-books
    # filter map and the per-book viewer map agree on it without a counter.
    key = f"{path.stem}-{start_offset}"
    span: dict[str, Any] = {"source": str(path), "kind": kind, "key": key}
    if reason:
        span["reason"] = reason
    span.update(span_json(text, start_offset, end_offset))
    return span


def line_offsets(text: str) -> list[int]:
    offsets = [0]
    for match in re.finditer(r"\n", text):
        offsets.append(match.end())
    return offsets


def offset_to_line(offsets: list[int], offset: int) -> int:
    lo, hi = 0, len(offsets)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if offsets[mid] <= offset:
            lo = mid
        else:
            hi = mid
    return lo + 1


def offset_to_line_column(offsets: list[int], offset: int) -> tuple[int, int]:
    line = offset_to_line(offsets, offset)
    return line, offset - offsets[line - 1]


def span_json(text: str, start_offset: int, end_offset: int) -> dict[str, int]:
    offsets = line_offsets(text)
    start_line, start_column = offset_to_line_column(offsets, start_offset)
    end_line, end_column = offset_to_line_column(offsets, end_offset)
    return {
        "startLine": start_line,
        "startColumn": start_column,
        "startOffset": start_offset,
        "endLine": end_line,
        "endColumn": end_column,
        "endOffset": end_offset,
    }


def parse_tex_booklink_spans(tex_text: str) -> list[TexBooklinkSpan]:
    offsets = line_offsets(tex_text)
    lines = tex_text.splitlines()
    spans: list[TexBooklinkSpan] = []
    stack: list[tuple[list[str], str | None, int, int | None]] = []
    marker_re = re.compile(
        r"\s*% BOOKLINK-(START|END) lean=([^\s]*)(?:\s+entry=(\d+))?(?:\s+kind=([A-Za-z0-9_-]+))?\s*$"
    )
    for index, line in enumerate(lines):
        match = marker_re.match(line)
        if not match:
            continue
        marker_end, raw_names, raw_entry, marker_kind = match.groups()
        names = [name.strip() for name in raw_names.split(",") if name.strip()]
        line_start = offsets[index]
        line_end = line_start + len(line)
        if marker_end == "START":
            content_start = line_end + 1 if line_end < len(tex_text) else line_end
            stack.append((names, marker_kind, content_start, int(raw_entry) if raw_entry else None))
        elif stack:
            start_names, start_kind, start_offset, start_entry = stack.pop()
            if set(start_names) == set(names) and start_kind == marker_kind:
                spans.append(TexBooklinkSpan(start_names, start_kind, start_offset, line_start, start_entry))
    command_re = re.compile(r"\\Booklink(Start|End)(?:\[([^\]]*)\])?\{([^{}]*)\}")
    stack = []
    for match in command_re.finditer(tex_text):
        marker_end, raw_options, raw_names = match.groups()
        marker_kind = booklink_option_value(raw_options, "kind")
        raw_entry = booklink_option_value(raw_options, "entry")
        entry = int(raw_entry) if raw_entry and raw_entry.isdigit() else None
        names = [name.strip() for name in raw_names.split(",") if name.strip()]
        if marker_end == "Start":
            stack.append((names, marker_kind, match.end(), entry))
        elif stack:
            start_names, start_kind, start_offset, start_entry = stack.pop()
            if set(start_names) == set(names) and start_kind == marker_kind:
                spans.append(TexBooklinkSpan(start_names, start_kind, start_offset, match.start(), start_entry))
    return spans


def booklink_option_value(raw_options: str | None, key: str) -> str | None:
    if raw_options is None:
        return None
    for option in raw_options.split(","):
        option_key, sep, option_value = option.strip().partition("=")
        if sep and option_key == key:
            return option_value
    return None


def lean_name_matches(decl_name: str | None, full_name: str) -> bool:
    if not decl_name:
        return False
    return full_name == decl_name or full_name.endswith("." + decl_name)


def tex_marker_match_for_entry(
    entry: dict[str, Any],
    tex_file: Path,
    tex_text: str,
    spans: list[TexBooklinkSpan],
) -> dict[str, Any]:
    lean = entry.get("lean")
    decl_name = lean.get("declName") if isinstance(lean, dict) else None
    if not isinstance(decl_name, str):
        return {"status": "unresolved", "reason": "missing Lean declaration name"}

    booklink = entry.get("booklink")
    target = booklink.get("target") if isinstance(booklink, dict) else None

    for span in spans:
        if any(lean_name_matches(decl_name, name) for name in span.names):
            # A declaration whose statement and proof are booklinked separately
            # appears in two spans: the statement span (kind=statement) and the
            # proof span (no kind). Pick the half matching this entry's target,
            # so a statement entry never lands on the proof span and — the case
            # that was being missed — a proof entry never falls back to the
            # statement span that lists the same declaration.
            if target == "statement" and span.kind != "statement":
                continue
            if target == "proof" and span.kind == "statement":
                continue
            result: dict[str, Any] = {
                "status": "matched",
                "score": 1.0,
                "source": str(tex_file),
                "names": span.names,
            }
            if span.kind is not None:
                result["kind"] = span.kind
            if span.entry is not None:
                # The PDF \BooklinkStart[entry=N] number / booklink-entry-N named
                # destination; the viewer maps an entry to its PDF target by this,
                # not by array position (the PDF numbers booklinks globally).
                result["entry"] = span.entry
            result.update(span_json(tex_text, span.start_offset, span.end_offset))
            result["markerStartOffset"] = span.start_offset
            result["markerEndOffset"] = span.end_offset
            return result
    return {"status": "unresolved", "reason": "no TeX BOOKLINK marker for Lean declaration"}


def attach_tex_matches(source_map: dict[str, Any], tex_file: Path) -> None:
    counts: dict[str, int] = {}
    tex_text = tex_file.read_text(encoding="utf-8")
    spans = parse_tex_booklink_spans(tex_text)
    for entry in source_map.get("entries", []):
        if not isinstance(entry, dict):
            continue
        tex_match = tex_marker_match_for_entry(entry, tex_file, tex_text, spans)
        entry["texMatch"] = tex_match
        status = str(tex_match.get("status"))
        counts[status] = counts.get(status, 0) + 1
    source_map["texFile"] = str(tex_file)
    source_map["texMarkerCount"] = len(spans)
    source_map["texCounts"] = counts


def find_prose_match(path: Path, excerpt: str) -> dict[str, Any]:
    original = path.read_text(encoding="utf-8")
    tokens = excerpt.split()
    if not tokens:
        return {"status": "unresolved", "reason": "empty excerpt"}
    # Match the excerpt against the source ignoring whitespace differences: every
    # run of whitespace between tokens matches any run of whitespace (spaces, a
    # line break, indentation). This keeps an anchor valid when the source is
    # reflowed — e.g. a long line re-wrapped at a different column — instead of
    # silently losing the match on a byte-exact compare. The returned offsets are
    # still exact source code-point offsets (the regex match span), so coverage
    # intervals and shading are unaffected.
    pattern = re.compile(r"\s+".join(re.escape(tok) for tok in tokens))
    found = pattern.search(original)
    if found is not None:
        result: dict[str, Any] = {
            "status": "matched",
            "score": 1.0,
            "source": str(path),
        }
        result.update(span_json(original, found.start(), found.end()))
        return result
    span = {
        "startLine": None,
        "startColumn": None,
        "startOffset": None,
        "endLine": None,
        "endColumn": None,
        "endOffset": None,
    }
    return {
        "status": "unresolved",
        "reason": "excerpt not found (whitespace-insensitive search)",
        "score": 0.0,
        "source": str(path),
        **span,
    }


def match_statement(marker: Marker, statements: list[Statement]) -> dict[str, Any]:
    wanted_title = normalize(str(marker.data.get("title", "")))
    wanted_kind = str(marker.data.get("kind", "")).casefold()
    best: tuple[float, Statement | None] = (0.0, None)
    for statement in statements:
        if wanted_kind and wanted_kind != statement.kind.casefold():
            continue
        title = normalize(statement.title or "")
        score = 1.0 if title == wanted_title else difflib.SequenceMatcher(None, wanted_title, title).ratio()
        if score > best[0]:
            best = (score, statement)

    score, statement = best
    if statement is None:
        return {"status": "unresolved", "reason": "no statement candidates"}
    status = "matched" if score >= 0.9 else "weak" if score >= 0.65 else "unresolved"
    text = statement.source.read_text(encoding="utf-8")
    result: dict[str, Any] = {
        "status": status,
        "score": round(score, 3),
        "source": str(statement.source),
        "kind": statement.kind,
        "title": statement.title,
    }
    result.update(span_json(text, statement.start_offset, statement.end_offset))
    return result


def marker_to_json(marker: Marker, match: dict[str, Any]) -> dict[str, Any]:
    return {
        "lean": {
            "source": str(marker.lean_file),
            "markerLine": marker.marker_line,
            "markerEndLine": marker.end_line,
            "declKind": marker.decl_kind,
            "declName": marker.decl_name,
            "declLine": marker.decl_line,
            "declEndLine": marker.decl_end_line,
        },
        "booklink": marker.data,
        "match": match,
    }


def build_sourcemap(root: Path, lean_file: Path) -> dict[str, Any]:
    markers = parse_lean_markers(lean_file)
    statements_by_source: dict[Path, list[Statement]] = {}
    entries: list[dict[str, Any]] = []
    skip_sources: dict[str, Path] = {}

    for marker in markers:
        source_value = marker.data.get("source")
        if not isinstance(source_value, str):
            match = {"status": "unresolved", "reason": "missing source"}
            entries.append(marker_to_json(marker, match))
            continue

        # Lexical (not .resolve()): a chapter reached through a symlinked tree
        # (an excerpt sharing another book's chapter) keeps its book-local path,
        # so the emitted source is already book-local and needs no view rewrite.
        source = root / book_src_root(lean_file) / source_value
        if not source.exists():
            match = {"status": "unresolved", "reason": f"source does not exist: {source_value}"}
            entries.append(marker_to_json(marker, match))
            continue
        skip_sources.setdefault(str(source), source)

        target = marker.data.get("target")
        if target == "statement":
            if source not in statements_by_source:
                statements_by_source[source] = parse_book_statements(source)
            match = match_statement(marker, statements_by_source[source])
        elif target in {"prose", "proof"}:
            excerpt = marker.data.get("excerpt")
            if isinstance(excerpt, str):
                match = find_prose_match(source, excerpt)
            else:
                match = {"status": "unresolved", "reason": "missing excerpt"}
        else:
            match = {"status": "unresolved", "reason": f"unknown target: {target}"}
        entries.append(marker_to_json(marker, match))

    counts: dict[str, int] = {}
    for entry in entries:
        status = str(entry["match"].get("status"))
        counts[status] = counts.get(status, 0) + 1

    skips = [span for source in skip_sources.values() for span in parse_skip_spans(source)]

    return {
        "version": 2,
        "coordinateSystem": {
            "line": "1-based",
            "column": "0-based Unicode code-point offset within line",
            "offset": "0-based Unicode code-point offset within file",
            "end": "exclusive",
        },
        "root": str(root),
        "leanFile": str(lean_file),
        "entryCount": len(entries),
        "counts": counts,
        "entries": entries,
        "skips": skips,
    }


def build_combined_sourcemap(root: Path, lean_files: list[Path]) -> dict[str, Any]:
    maps = [build_sourcemap(root, lean_file) for lean_file in lean_files]
    entries = [entry for source_map in maps for entry in source_map["entries"]]
    counts: dict[str, int] = {}
    for entry in entries:
        status = str(entry["match"].get("status"))
        counts[status] = counts.get(status, 0) + 1

    # The same chapter can be formalized across several Lean files, so dedup the
    # skip spans by (source, startOffset) to avoid repeated overlays.
    seen_skips: set[tuple[str, int]] = set()
    skips: list[dict[str, Any]] = []
    for source_map in maps:
        for span in source_map.get("skips", []):
            key = (str(span.get("source")), int(span.get("startOffset", -1)))
            if key in seen_skips:
                continue
            seen_skips.add(key)
            skips.append(span)

    return {
        "version": 2,
        "coordinateSystem": maps[0]["coordinateSystem"],
        "root": str(root),
        "leanFile": str(lean_files[0]),
        "leanFiles": [str(lean_file) for lean_file in lean_files],
        "entryCount": len(entries),
        "counts": counts,
        "entries": entries,
        "skips": skips,
    }


def discover_booklinks(lean_files: list[Path]) -> list[tuple[Path, list[str]]]:
    """The (lean file, marker source values) pairs for files carrying booklink
    markers. This is the single source of truth for which Lean files formalize
    which chapters; the Makefile derives its lists from it."""
    found: list[tuple[Path, list[str]]] = []
    for lean_file in lean_files:
        src_root = book_src_root(lean_file)
        sources = sorted(
            {
                f"{src_root}/{marker.data['source']}"
                for marker in parse_lean_markers(lean_file)
                if isinstance(marker.data.get("source"), str)
            }
        )
        if sources:
            found.append((lean_file, sources))
    return found


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lean_file", type=Path, nargs="+")
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--out", type=Path)
    parser.add_argument("--tex-file", type=Path)
    args = parser.parse_args(argv[1:])

    root = args.root.resolve()
    # Lexical (not .resolve()): an excerpt book owns its chapter Lean file through
    # a symlink, and book_src_root must read the book-local path to keep the
    # emitted sources book-local rather than following the link to the owner.
    lean_files = [lean_file if lean_file.is_absolute() else (root / lean_file) for lean_file in args.lean_file]
    try:
        source_map = build_combined_sourcemap(root, lean_files)
    except ValueError as exc:
        print(f"booklink_sourcemap.py: {exc}", file=sys.stderr)
        return 2
    if args.tex_file:
        tex_file = (root / args.tex_file).resolve() if not args.tex_file.is_absolute() else args.tex_file
        if not tex_file.exists():
            print(f"booklink_sourcemap.py: TeX file does not exist: {tex_file}", file=sys.stderr)
            return 2
        attach_tex_matches(source_map, tex_file)

    output = json.dumps(source_map, indent=2, ensure_ascii=False) + "\n"
    if args.out:
        out = (root / args.out).resolve() if not args.out.is_absolute() else args.out
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(output, encoding="utf-8")
        print(
            f"wrote {out} ({source_map['entryCount']} entries; {source_map['counts']}"
            + f"; {len(source_map.get('skips', []))} skips"
            + (f"; tex {source_map['texCounts']}" if "texCounts" in source_map else "")
            + ")",
            file=sys.stderr,
        )
    else:
        print(output, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
