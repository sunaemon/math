#!/usr/bin/env python3
"""Build a source map from Lean booklink markers to book source locations."""

import argparse
import difflib
import json
import re
import sys
from bisect import bisect_right
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path, PurePosixPath
from typing import Any

from book_manifest import read_manifest
from formalization_annotations import parse_formalization_scope


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


@dataclass(frozen=True)
class SourceDocument:
    """One source snapshot; all derived coordinates refer to these exact bytes."""

    path: Path
    text: str

    @cached_property
    def offsets(self) -> list[int]:
        return line_offsets(self.text)

    @cached_property
    def prose_projection(self) -> tuple[str, list[int], list[int]]:
        """Omit correspondence metadata, retaining a sparse map to original code points."""
        parts, projected_starts, original_starts = [], [], []
        cursor = projected = 0
        metadata = re.compile(r"<!--\s*chapter-correspondence(?:\s|[-:]).*?-->", re.DOTALL)
        for match in metadata.finditer(self.text):
            if cursor < match.start():
                chunk = self.text[cursor : match.start()]
                parts.append(chunk)
                projected_starts.append(projected)
                original_starts.append(cursor)
                projected += len(chunk)
            cursor = match.end()
        if cursor < len(self.text):
            parts.append(self.text[cursor:])
            projected_starts.append(projected)
            original_starts.append(cursor)
        return "".join(parts), projected_starts, original_starts

    @cached_property
    def statements(self) -> list[Statement]:
        return parse_book_statements(self.path, text=self.text, offsets=self.offsets)

    @cached_property
    def skips(self) -> list[dict[str, Any]]:
        return parse_skip_spans(self.path, text=self.text, offsets=self.offsets)


class SourceCache:
    """Shared within one build only; later builds always reread saved sources."""

    def __init__(self):
        self.documents: dict[Path, SourceDocument] = {}

    def document(self, path: Path) -> SourceDocument:
        if path not in self.documents:
            self.documents[path] = SourceDocument(path, path.read_text(encoding="utf-8"))
        return self.documents[path]


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
        text = re.sub(re.escape(old) + r"(?![A-Za-z])", lambda _match, replacement=new: replacement, text)

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


_DECLARATION = re.compile(
    r"^\s*(?:(?:private|protected|public|noncomputable|partial|unsafe|scoped|local|nonrec)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|class|structure|example|inductive|opaque|axiom|constant)\b\s*"
)
_DECL_NAME = re.compile(r"(?:«[^»]+»|[^\s:({\[\]=,;«»])+")
_COMMAND_BOUNDARY = re.compile(
    r"^\s*(?:(?:local|scoped)\s+)?(?:end|namespace|section|variable|variables|open|attribute|"
    r"set_option|include|omit|export|infixl?|infixr|prefix|postfix|notation|syntax|macro|elab|"
    r"initialize|mutual)\b|^\s*#"
)
_CHAR_LITERAL = re.compile(r"'(?:\\(?:u\{[0-9a-fA-F]+\}|[0-9]{1,3}|.)|[^'\\\n])'")


def _lean_code_lines(lines: list[str]) -> list[str]:
    """Mask comments, literals and attributes without moving line positions.

    Quoted identifiers remain intact. Literal placeholders cannot be mistaken
    for declarations but still count as body lines, including multiline strings.
    This is a navigation scanner, not a replacement for Lean's parser.
    """
    result = []
    depth = 0
    in_string = False
    for line in lines:
        code: list[str] = []
        pos = 0
        if in_string:
            code.append('"')
        while pos < len(line):
            if depth:
                if line.startswith("/-", pos):
                    depth += 1
                    pos += 2
                elif line.startswith("-/", pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
            elif in_string:
                if line[pos] == "\\":
                    pos += 2
                elif line[pos] == '"':
                    in_string = False
                    pos += 1
                else:
                    pos += 1
            elif line.startswith("--", pos):
                break
            elif line.startswith("/-", pos):
                depth = 1
                code.append(" ")
                pos += 2
            elif line[pos] == "«" and "»" in line[pos + 1 :]:
                end = line.index("»", pos + 1) + 1
                code.append(line[pos:end])
                pos = end
            elif line[pos] == "'" and (pos == 0 or not (line[pos - 1].isalnum() or line[pos - 1] in "_'")):
                char = _CHAR_LITERAL.match(line, pos)
                if char:
                    code.append("_")
                    pos = char.end()
                else:
                    code.append(line[pos])
                    pos += 1
            elif line[pos] == '"':
                in_string = True
                code.append('""')
                pos += 1
            else:
                code.append(line[pos])
                pos += 1
        result.append("".join(code))
    # Attribute brackets can nest and extend over several source lines. Their
    # strings/comments have already been masked, so only real brackets count.
    attribute_depth = 0
    for index, code in enumerate(result):
        visible = list(code)
        pos = 0
        while pos < len(code):
            if code[pos] == "«" and "»" in code[pos + 1 :]:
                pos = code.index("»", pos + 1) + 1
                continue
            if not attribute_depth and code.startswith("@[", pos):
                visible[pos] = visible[pos + 1] = " "
                attribute_depth = 1
                pos += 2
                continue
            if attribute_depth:
                if code[pos] == "[":
                    attribute_depth += 1
                elif code[pos] == "]":
                    attribute_depth -= 1
                visible[pos] = " "
            pos += 1
        result[index] = "".join(visible)
    return result


def _declaration(code: str) -> tuple[str, str | None] | None:
    match = _DECLARATION.match(code)
    if match is None:
        return None
    rest = code[match.end() :]
    if match[1] == "class" and rest.startswith("inductive "):
        rest = rest.removeprefix("inductive ").lstrip()
    name = _DECL_NAME.match(rest)
    return match[1], name[0].rstrip(".") if name else None


def find_decl_end_line(lines: list[str], decl_index: int, *, code_lines: list[str] | None = None) -> int:
    code_lines = _lean_code_lines(lines) if code_lines is None else code_lines
    indent = len(lines[decl_index]) - len(lines[decl_index].lstrip())
    last_body = decl_index
    for idx in range(decl_index + 1, len(lines)):
        raw = lines[idx]
        code = code_lines[idx]
        current_indent = len(raw) - len(raw.lstrip())
        if current_indent <= indent:
            if raw.lstrip().startswith(("/-@ booklink:", "/--")):
                break
            if _declaration(code) is not None or _COMMAND_BOUNDARY.match(code):
                break
        if code.strip():
            last_body = idx
    return last_body + 1


def find_next_decl(
    lines: list[str], start: int, *, code_lines: list[str] | None = None
) -> tuple[str | None, str | None, int | None, int | None]:
    code_lines = _lean_code_lines(lines) if code_lines is None else code_lines
    for idx in range(start, len(lines)):
        declaration = _declaration(code_lines[idx])
        if declaration is not None:
            kind, name = declaration
            return kind, name, idx + 1, find_decl_end_line(lines, idx, code_lines=code_lines)
    return None, None, None, None


def parse_lean_markers(path: Path) -> list[Marker]:
    lines = path.read_text(encoding="utf-8").splitlines()
    markers: list[Marker] = []
    code_lines = None
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
            # Shared Lean files can link chapters absent from an excerpt book.
            # Use lexical ownership, not resolve(): symlinked copies belong to
            # the excerpt. Unknown/missing sources otherwise remain errors.
            excluded = str(data.get("exclude-books", "")).split()
            if excluded and PurePosixPath(book_src_root(path)).parts[-2] in excluded:
                i += 1
                continue
            if code_lines is None:
                code_lines = _lean_code_lines(lines)
            decl_kind, decl_name, decl_line, decl_end_line = find_next_decl(lines, i + 1, code_lines=code_lines)
            markers.append(Marker(path, marker_line, end_line, data, decl_kind, decl_name, decl_line, decl_end_line))
        i += 1
    return markers


def parse_book_statements(path: Path, *, text: str | None = None, offsets: list[int] | None = None) -> list[Statement]:
    if text is None:
        text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    if offsets is None:
        offsets = line_offsets(text)
    begin_re = re.compile(r"\\begin\{(" + "|".join(sorted(STATEMENT_ENVS)) + r")\*?\}")
    statements: list[Statement] = []
    for idx, line in enumerate(lines):
        match = begin_re.search(line)
        if not match:
            continue
        kind = match.group(1)
        # Titles may wrap across source lines. Braced macro arguments can
        # themselves contain brackets, so a line-local regex is insufficient.
        title_start = offsets[idx] + match.end()
        title = None
        if text[title_start : title_start + 1] == "[":
            braces = 0
            brackets = 1
            cursor = title_start + 1
            while cursor < len(text):
                char = text[cursor]
                if char == "\\":
                    cursor += 2
                    continue
                if char == "{":
                    braces += 1
                elif char == "}":
                    braces -= 1
                elif braces == 0 and char == "[":
                    brackets += 1
                elif braces == 0 and char == "]":
                    brackets -= 1
                    if brackets == 0:
                        title = text[title_start + 1 : cursor]
                        break
                cursor += 1
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


def parse_skip_spans(path: Path, *, text: str | None = None, offsets: list[int] | None = None) -> list[dict[str, Any]]:
    """Spans for the `formalization: skip` comments in one book source.

    Region markers (`skip-begin`/`skip-end`) span from the opening comment to the
    closing comment inclusive; a bare `skip` spans from the comment through the
    block it governs. Offsets are code-point offsets, matching the rest of the map."""
    if text is None:
        text = path.read_text(encoding="utf-8")
    if offsets is None:
        offsets = line_offsets(text)
    spans: list[dict[str, Any]] = []
    scope = parse_formalization_scope(text, str(path))
    for region in scope.regions:
        spans.append(
            _skip_span(
                path,
                text,
                region.opening.start_offset,
                region.closing.end_offset,
                "region",
                region.reason,
                offsets=offsets,
            )
        )
    for annotation in scope.annotations:
        if annotation.directive == "skip":
            spans.append(
                _skip_span(
                    path,
                    text,
                    annotation.start_offset,
                    block_after_marker(text, annotation.end_offset),
                    "block",
                    annotation.reason,
                    offsets=offsets,
                )
            )
    spans.sort(key=lambda span: span["startOffset"])
    return spans


def _skip_span(
    path: Path,
    text: str,
    start_offset: int,
    end_offset: int,
    kind: str,
    reason: str | None,
    *,
    offsets: list[int] | None = None,
) -> dict[str, Any]:
    # `key` is the stable join between this map and the TeX anchors the book
    # filter injects (`\SkipStart{key}` -> hypertarget `skip-key-start`). It is a
    # pure function of the source file and code-point offset, so the all-books
    # filter map and the per-book viewer map agree on it without a counter.
    key = f"{path.stem}-{start_offset}"
    span: dict[str, Any] = {"source": str(path), "kind": kind, "key": key}
    if reason:
        span["reason"] = reason
    span.update(span_json(text, start_offset, end_offset, offsets=offsets))
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


def span_json(text: str, start_offset: int, end_offset: int, *, offsets: list[int] | None = None) -> dict[str, int]:
    if offsets is None:
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


def parse_tex_booklink_spans(tex_text: str, *, offsets: list[int] | None = None) -> list[TexBooklinkSpan]:
    if offsets is None:
        offsets = line_offsets(tex_text)
    lines = tex_text.splitlines()
    spans: list[TexBooklinkSpan] = []
    stack: list[tuple[list[str], str | None, int, int | None]] = []
    has_comment_markers = False
    marker_re = re.compile(
        r"\s*% BOOKLINK-(START|END) lean=([^\s]*)(?:\s+entry=(\d+))?(?:\s+kind=([A-Za-z0-9_-]+))?\s*$"
    )
    for index, line in enumerate(lines):
        match = marker_re.match(line)
        if not match:
            continue
        has_comment_markers = True
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
    if has_comment_markers and command_re.search(tex_text):
        raise ValueError("mixed BOOKLINK comment and command markers in TeX")
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


def parse_tex_skip_spans(tex_text: str) -> dict[str, tuple[int, int]]:
    """Content spans between \\SkipStart{key} and \\SkipEnd{key} pairs, by key."""
    spans: dict[str, tuple[int, int]] = {}
    starts: dict[str, int] = {}
    for match in re.finditer(r"\\Skip(Start|End)\{([^{}]*)\}", tex_text):
        kind, key = match.groups()
        if kind == "Start":
            starts[key] = match.end()
        else:
            start = starts.pop(key, None)
            if start is not None and key not in spans:
                spans[key] = (start, match.start())
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
    return full_name == decl_name


def tex_marker_match_for_entry(
    entry: dict[str, Any],
    tex_file: Path,
    tex_text: str,
    spans: list[TexBooklinkSpan],
    used: dict[tuple[str, str], int] | None = None,
    *,
    offsets: list[int] | None = None,
    injected_entry: int | None = None,
) -> dict[str, Any]:
    lean = entry.get("lean")
    decl_name = (lean.get("anchorName") or lean.get("declName")) if isinstance(lean, dict) else None
    if not isinstance(decl_name, str):
        return {"status": "unresolved", "reason": "missing Lean declaration name"}

    booklink = entry.get("booklink")
    target = booklink.get("target") if isinstance(booklink, dict) else None

    # A declaration can carry several booklinks: a statement/proof pair, or
    # several prose paragraphs (fact bundles). The statement span is tagged
    # kind=statement; every other span is untagged, so kind alone cannot
    # separate a proof from a prose claim on the same declaration, nor one
    # prose paragraph from another. Entries are in book order and same-name
    # spans appear in the tex in book order too, so pair the n-th injected
    # entry of a declaration with the n-th span of the matching pool.
    # Grouped injections retain one name per booklink, including repeated names
    # when several excerpts of the same declaration share a translated region.
    # Count each occurrence so all those entries resolve to the shared band and
    # subsequent excerpts still pair with the next distinct span.
    decl_spans = [span for span in spans for name in span.names if lean_name_matches(decl_name, name)]
    if target == "statement":
        pool = "statement"
        candidates = [span for span in decl_spans if span.kind == "statement"]
    else:
        pool = "body"
        candidates = [span for span in decl_spans if span.kind != "statement"]

    # Only booklinks with a resolved book position were injected into the tex,
    # so an unmatched entry must not consume a span index.
    match = entry.get("match")
    injected = (
        isinstance(match, dict) and match.get("status") == "matched" and isinstance(match.get("startOffset"), int)
    )
    if not injected:
        return {"status": "unresolved", "reason": "booklink has no book position, so no TeX marker"}

    index = 0
    if used is not None:
        key = (decl_name, pool)
        index = used.get(key, 0)
        used[key] = index + 1
    if injected_entry is None and index >= len(candidates):
        return {"status": "unresolved", "reason": "no TeX BOOKLINK marker for Lean declaration"}

    if injected_entry is not None:
        # Main.hs numbers the injection by the first source-map array index
        # in its shared source span. Names alone cannot distinguish modules or
        # namespaces that declare the same short name.
        identified = [span for span in spans if span.entry == injected_entry]
        if len(identified) != 1 or identified[0] not in candidates:
            return {"status": "unresolved", "reason": "missing or inconsistent TeX BOOKLINK entry identity"}
        span = identified[0]
    else:
        span = candidates[index]
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
    result.update(span_json(tex_text, span.start_offset, span.end_offset, offsets=offsets))
    result["markerStartOffset"] = span.start_offset
    result["markerEndOffset"] = span.end_offset
    return result


def attach_tex_matches(source_map: dict[str, Any], tex_file: Path, injection_map: dict[str, Any] | None = None) -> None:
    counts: dict[str, int] = {}
    tex_text = tex_file.read_text(encoding="utf-8")
    offsets = line_offsets(tex_text)
    spans = parse_tex_booklink_spans(tex_text, offsets=offsets)
    used: dict[tuple[str, str], int] = {}
    entries = source_map.get("entries", [])
    identities: dict[tuple[str, int, int, str], int] = {}

    def injection_key(entry: dict[str, Any]) -> tuple[str, int, int, str] | None:
        match = entry.get("match", {})
        lean = entry.get("lean", {})
        if match.get("status") != "matched" or not (lean.get("anchorName") or lean.get("declName")):
            return None
        source, start, end = match.get("source"), match.get("startOffset"), match.get("endOffset")
        if not isinstance(source, str) or not isinstance(start, int) or not isinstance(end, int):
            return None
        kind = "statement" if entry.get("booklink", {}).get("target") == "statement" else "body"
        return source, start, end, kind

    injection_entries = injection_map.get("entries", []) if injection_map is not None else entries
    for index, entry in enumerate(injection_entries):
        if isinstance(entry, dict) and (key := injection_key(entry)) is not None:
            identities.setdefault(key, index)
    # The filter may inject several books from one global map, and translated
    # passages may merge bands. Locate each marker in that exact input map;
    # a book-local array index or canonical English offsets are not its ID.
    marker_identities: dict[tuple[str, int], int] = {}
    canonical_identities: dict[tuple[str, int], set[int]] = {}
    for entry in injection_entries:
        key = injection_key(entry)
        lean = entry.get("lean", {})
        if key is not None and isinstance(lean.get("source"), str) and isinstance(lean.get("markerLine"), int):
            marker = (lean["source"], lean["markerLine"])
            if marker in marker_identities:
                raise ValueError(f"duplicate Lean marker identity: {marker}")
            marker_identities[marker] = identities[key]
            canonical = (str(Path(marker[0]).resolve()), marker[1])
            canonical_identities.setdefault(canonical, set()).add(identities[key])
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        key = injection_key(entry)
        if injection_map is not None:
            lean = entry.get("lean", {})
            identity = marker_identities.get((lean.get("source"), lean.get("markerLine")))
            if identity is None and isinstance(lean.get("source"), str):
                aliases = canonical_identities.get((str(Path(lean["source"]).resolve()), lean.get("markerLine")), set())
                # Translations rewrite the Lean path to a symlinked tree.
                # Prefer lexical ownership above; accept a realpath alias only
                # when it identifies exactly one injection in this book.
                if len(aliases) == 1:
                    identity = next(iter(aliases))
        else:
            identity = identities.get(key) if key is not None else None
        if injection_map is not None and identity is None:
            tex_match = {"status": "unresolved", "reason": "Lean marker not injected into TeX"}
        else:
            tex_match = tex_marker_match_for_entry(
                entry, tex_file, tex_text, spans, used, offsets=offsets, injected_entry=identity
            )
        entry["texMatch"] = tex_match
        status = str(tex_match.get("status"))
        counts[status] = counts.get(status, 0) + 1
    # Skip regions get their own tex spans (from \SkipStart/\SkipEnd pairs) so
    # the viewer's copy-TeX shortcut works on skip bands, not just booklink
    # markers. Skips missing from the tex simply carry no texMatch.
    skip_spans = parse_tex_skip_spans(tex_text)
    for skip in source_map.get("skips", []):
        if not isinstance(skip, dict):
            continue
        span = skip_spans.get(skip.get("key"))
        if span is None:
            continue
        tex_match = {"status": "matched", "score": 1.0, "source": str(tex_file)}
        tex_match.update(span_json(tex_text, span[0], span[1], offsets=offsets))
        skip["texMatch"] = tex_match
    source_map["texFile"] = str(tex_file)
    source_map["texMarkerCount"] = len(spans)
    source_map["texCounts"] = counts


def find_prose_match(path: Path, excerpt: str, *, document: SourceDocument | None = None) -> dict[str, Any]:
    if document is None:
        document = SourceDocument(path, path.read_text(encoding="utf-8"))
    original = document.text
    tokens = excerpt.split()
    if not tokens:
        return {"status": "unresolved", "reason": "empty excerpt"}
    # Match the excerpt against the source ignoring whitespace differences: every
    # run of whitespace between tokens matches any run of whitespace (spaces, a
    # line break, indentation). This keeps an anchor valid when the source is
    # reflowed — e.g. a long line re-wrapped at a different column — instead of
    # silently losing the match on a byte-exact compare. The returned offsets are
    # projected back to exact source code-point offsets, including any intervening
    # correspondence metadata. Coverage intervals and shading retain their source
    # coordinates; metadata itself cannot satisfy an excerpt.
    pattern = re.compile(r"\s+".join(re.escape(tok) for tok in tokens))
    searchable, projected_starts, original_starts = document.prose_projection
    found = pattern.search(searchable)
    if found is not None:

        def original_offset(position: int) -> int:
            segment = bisect_right(projected_starts, position) - 1
            return original_starts[segment] + position - projected_starts[segment]

        result: dict[str, Any] = {
            "status": "matched",
            "score": 1.0,
            "source": str(path),
        }
        result.update(
            span_json(
                original, original_offset(found.start()), original_offset(found.end() - 1) + 1, offsets=document.offsets
            )
        )
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


def match_statement(marker: Marker, statements: list[Statement], *, cache: SourceCache | None = None) -> dict[str, Any]:
    cache = cache if cache is not None else SourceCache()
    # An explicitly supplied excerpt is a selector when there is no title.
    # Previously it was ignored, so every excerpt-only marker selected the first
    # unnamed statement in the chapter, even if it described an unrelated result.
    if "title" not in marker.data and "excerpt" in marker.data:
        tokens = str(marker.data["excerpt"]).split()
        pattern = re.compile(r"\s+".join(re.escape(token) for token in tokens)) if tokens else None
        kind = str(marker.data.get("kind", "")).casefold()
        candidates = []
        for statement in statements:
            if kind and kind != statement.kind.casefold():
                continue
            document = cache.document(statement.source)
            text = document.text
            if pattern and pattern.search(text, statement.start_offset, statement.end_offset):
                candidates.append(statement)
        if len(candidates) != 1:
            return {"status": "unresolved", "reason": f"statement excerpt has {len(candidates)} candidates"}
        statement = candidates[0]
        document = cache.document(statement.source)
        text = document.text
        return {
            "status": "matched",
            "score": 1.0,
            "source": str(statement.source),
            "kind": statement.kind,
            "title": statement.title,
            **span_json(text, statement.start_offset, statement.end_offset, offsets=document.offsets),
        }
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
    document = cache.document(statement.source)
    text = document.text
    result: dict[str, Any] = {
        "status": status,
        "score": round(score, 3),
        "source": str(statement.source),
        "kind": statement.kind,
        "title": statement.title,
    }
    result.update(span_json(text, statement.start_offset, statement.end_offset, offsets=document.offsets))
    return result


def marker_to_json(marker: Marker, match: dict[str, Any]) -> dict[str, Any]:
    # An anonymous instance has a source location but no written declaration name.
    # Give only the rendering layer an anchor; do not invent a Lean declaration.
    anchor = {}
    if marker.decl_kind == "instance" and marker.decl_name is None and marker.decl_line is not None:
        anchor["anchorName"] = f"anonymousInstance_{marker.lean_file.stem}_{marker.decl_line}"
    return {
        "lean": {
            "source": str(marker.lean_file),
            "markerLine": marker.marker_line,
            "markerEndLine": marker.end_line,
            "declKind": marker.decl_kind,
            "declName": marker.decl_name,
            "declLine": marker.decl_line,
            "declEndLine": marker.decl_end_line,
            **anchor,
        },
        "booklink": marker.data,
        "match": match,
    }


def chapter_rank_map(root: Path, lean_files: list[Path]) -> dict[str, int]:
    """Book-order rank for chapter sources, read from the per-book document
    manifests (`<book>/src/*.json`) of the books the Lean files belong to.
    Paths are joined lexically onto `root`, matching the entry `source` values,
    which are also lexical (never resolved through symlinks)."""
    rank: dict[str, int] = {}
    seen_roots: set[Path] = set()
    for lean_file in lean_files:
        src_root = root / book_src_root(lean_file)
        if src_root in seen_roots:
            continue
        seen_roots.add(src_root)
        for manifest in sorted(src_root.glob("*.json")):
            try:
                _source, chapters = read_manifest(manifest)
            except ValueError:
                continue
            for chapter in chapters:
                rank.setdefault(str(root / chapter), len(rank))
    return rank


def order_entries_by_book(
    entries: list[dict[str, Any]], chapter_rank: dict[str, int] | None = None
) -> list[dict[str, Any]]:
    """Order entries by their occurrence in the book: chapters in manifest
    order, then match start offset within each chapter. The viewer's marker
    palette and prev/next navigation follow this array order, so it should read
    like the book, not like the Lean file. Sources absent from every manifest
    sort after the manifest chapters in first-appearance order, and the sort is
    stable, so entries without a resolved position keep their Lean-relative
    order at the end of their group."""
    source_rank: dict[str, int] = dict(chapter_rank or {})
    for entry in entries:
        source = entry["match"].get("source")
        if isinstance(source, str):
            source_rank.setdefault(source, len(source_rank))

    def key(entry: dict[str, Any]) -> tuple[int, int, int]:
        match = entry["match"]
        source = match.get("source")
        rank = source_rank[source] if isinstance(source, str) else len(source_rank)
        offset = match.get("startOffset")
        if isinstance(offset, int):
            return (rank, 0, offset)
        return (rank, 1, 0)

    return sorted(entries, key=key)


def build_sourcemap(
    root: Path, lean_file: Path, *, cache: SourceCache | None = None, chapter_rank: dict[str, int] | None = None
) -> dict[str, Any]:
    cache = cache if cache is not None else SourceCache()
    markers = parse_lean_markers(lean_file)
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
            match = match_statement(marker, cache.document(source).statements, cache=cache)
        elif target in {"prose", "proof"}:
            excerpt = marker.data.get("excerpt")
            if isinstance(excerpt, str):
                match = find_prose_match(source, excerpt, document=cache.document(source))
            else:
                match = {"status": "unresolved", "reason": "missing excerpt"}
        else:
            match = {"status": "unresolved", "reason": f"unknown target: {target}"}
        entries.append(marker_to_json(marker, match))

    entries = order_entries_by_book(
        entries, chapter_rank if chapter_rank is not None else chapter_rank_map(root, [lean_file])
    )
    counts: dict[str, int] = {}
    for entry in entries:
        status = str(entry["match"].get("status"))
        counts[status] = counts.get(status, 0) + 1

    skips = [dict(span) for source in skip_sources.values() for span in cache.document(source).skips]

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


def build_combined_sourcemap(
    root: Path,
    lean_files: list[Path],
    extra_skip_sources: list[Path] | None = None,
    *,
    cache: SourceCache | None = None,
) -> dict[str, Any]:
    cache = cache if cache is not None else SourceCache()
    ranks = chapter_rank_map(root, lean_files)
    maps = [build_sourcemap(root, lean_file, cache=cache, chapter_rank=ranks) for lean_file in lean_files]
    # Re-sort across Lean files: two files formalizing the same chapter must
    # interleave by book position, not stay grouped per Lean file.
    entries = order_entries_by_book(
        [entry for source_map in maps for entry in source_map["entries"]],
        ranks,
    )
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
            skips.append(dict(span))
    for source in extra_skip_sources or []:
        for span in cache.document(source).skips:
            key = (str(span.get("source")), int(span.get("startOffset", -1)))
            if key in seen_skips:
                continue
            seen_skips.add(key)
            skips.append(dict(span))

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
    parser.add_argument("--injection-map", type=Path, help="Exact sourcemap passed to inject-booklinks")
    parser.add_argument("--skip-source", type=Path, nargs="*", default=[])
    args = parser.parse_args(argv[1:])

    root = args.root.resolve()
    # Lexical (not .resolve()): an excerpt book owns its chapter Lean file through
    # a symlink, and book_src_root must read the book-local path to keep the
    # emitted sources book-local rather than following the link to the owner.
    lean_files = [lean_file if lean_file.is_absolute() else (root / lean_file) for lean_file in args.lean_file]
    skip_sources = [source if source.is_absolute() else (root / source) for source in args.skip_source]
    try:
        source_map = build_combined_sourcemap(root, lean_files, skip_sources)
    except ValueError as exc:
        print(f"booklink_sourcemap.py: {exc}", file=sys.stderr)
        return 2
    if args.tex_file:
        tex_file = (root / args.tex_file).resolve() if not args.tex_file.is_absolute() else args.tex_file
        if not tex_file.exists():
            print(f"booklink_sourcemap.py: TeX file does not exist: {tex_file}", file=sys.stderr)
            return 2
        try:
            injection_map = (
                json.loads((root / args.injection_map).read_text(encoding="utf-8")) if args.injection_map else None
            )
            attach_tex_matches(source_map, tex_file, injection_map)
        except (OSError, ValueError) as exc:
            print(f"booklink_sourcemap.py: {exc}", file=sys.stderr)
            return 2

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
