#!/usr/bin/env python3
"""Check that a translated book chapter preserves source structure.

The prose of a translation may change freely, but the identifiers and markup
that connect a chapter to the rest of the book must not drift.  This tool
compares two Markdown files in source order and checks their headings, labels,
citations, math metadata, LaTeX environments, formalization-scope markers,
layout controls, mathematics, and canonical term-index identities.

Usage:

    tools/check_translation_structure.py SOURCE TRANSLATION

The checker uses only the Python standard library.  It deliberately ignores
fenced code examples, inline code, YAML front matter, and ordinary HTML comments.
Raw ``{=latex}`` and ``{=tex}`` blocks remain checked as rendered content. The
``formalization:`` comments are read separately because they are structural.

Exit codes: 0 match, 1 structural differences, 2 execution or command-line usage failure.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Located:
    """A structural value together with its source location."""

    value: Any
    offset: int
    line: int


@dataclass
class Snapshot:
    headings: list[Located]
    labels: list[Located]
    citations: list[Located]
    mathmeta: list[Located]
    environments: list[Located]
    formalization: list[Located]
    layout: list[Located]
    mathematics: list[Located]
    terms: list[Located]
    structural_order: list[Located]


class StructureParseError(ValueError):
    """Raised when structural markup cannot be parsed safely."""


_ATX_HEADING = re.compile(r"(?m)^(?P<marks>#{1,6})[ \t]+(?P<body>[^\n]*)$")
_HTML_COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)
_ENVIRONMENT = re.compile(r"\\(?P<action>begin|end)\s*\{(?P<name>[^{}\n]+)\}")
_FORMALIZATION = re.compile(
    r"<!--\s*formalization:\s*(?P<directive>[A-Za-z-]+)\b.*?-->",
    re.DOTALL,
)
_TERM_MACRO = re.compile(r"\\term(?P<operation>define|use|forward|ref)(?:as)?(?=\s*\{)")
_PANDOC_CITATION = re.compile(r"(?<![\w@])@(?P<key>[A-Za-z0-9][A-Za-z0-9_.:+/?<>~&%#$-]*)")
_LATEX_CITATION = re.compile(r"\\(?:[A-Za-z]*cite[A-Za-z]*)\s*(?:\[[^\]\n]*\]\s*)*\{(?P<keys>[^{}\n]+)\}")
_MATH_ENVIRONMENTS = {
    "align",
    "align*",
    "displaymath",
    "equation",
    "equation*",
    "eqnarray",
    "eqnarray*",
    "gather",
    "gather*",
    "multline",
    "multline*",
}


def _line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _blank(text: str) -> str:
    """Replace content with spaces while preserving offsets and newlines."""
    return "".join("\n" if char == "\n" else " " for char in text)


def _replace_ranges(text: str, ranges: list[tuple[int, int]]) -> str:
    if not ranges:
        return text
    chars = list(text)
    for start, end in ranges:
        for index in range(start, end):
            if chars[index] != "\n":
                chars[index] = " "
    return "".join(chars)


def _yaml_range(text: str) -> tuple[int, int] | None:
    if not re.match(r"\A---[ \t]*(?:\n|\Z)", text):
        return None
    closing = re.search(r"(?m)^(?:---|\.\.\.)[ \t]*(?:\n|\Z)", text[4:])
    if closing is None:
        raise StructureParseError("unclosed YAML front matter")
    return 0, 4 + closing.end()


def _fenced_code_ranges(text: str) -> list[tuple[int, int]]:
    ranges: list[tuple[int, int]] = []
    active: tuple[str, int, int, bool, int] | None = None
    for line_match in re.finditer(r".*(?:\n|\Z)", text):
        line = line_match.group(0).rstrip("\n")
        if active is None:
            opening = re.match(r"^[ ]{0,3}(?P<fence>`{3,}|~{3,})", line)
            if opening:
                fence = opening.group("fence")
                raw_tex = bool(re.fullmatch(r"[ \t]*\{=(?:latex|tex)\}[ \t]*", line[opening.end() :]))
                active = (fence[0], len(fence), line_match.start(), raw_tex, line_match.end())
            continue
        char, length, start, raw_tex, opening_end = active
        if re.match(rf"^[ ]{{0,3}}{re.escape(char)}{{{length},}}[ \t]*$", line):
            if raw_tex:
                # Raw TeX is rendered book content, not a code example. Mask
                # only its delimiters so math, labels and environments remain
                # checked even when a nested proof needs an explicit raw block.
                ranges.extend(((start, opening_end), (line_match.start(), line_match.end())))
            else:
                ranges.append((start, line_match.end()))
            active = None
    if active is not None:
        ranges.append((active[2], active[4] if active[3] else len(text)))
    return ranges


def _inline_code_ranges(text: str) -> list[tuple[int, int]]:
    ranges: list[tuple[int, int]] = []
    index = 0
    while index < len(text):
        if text[index] != "`":
            index += 1
            continue
        end_marks = index + 1
        while end_marks < len(text) and text[end_marks] == "`":
            end_marks += 1
        delimiter = text[index:end_marks]
        close = text.find(delimiter, end_marks)
        while close >= 0 and (
            (close > 0 and text[close - 1] == "`")
            or (close + len(delimiter) < len(text) and text[close + len(delimiter)] == "`")
        ):
            close = text.find(delimiter, close + len(delimiter))
        if close < 0:
            index = end_marks
            continue
        ranges.append((index, close + len(delimiter)))
        index = close + len(delimiter)
    return ranges


def _mask_code_and_yaml(text: str) -> str:
    ranges = _fenced_code_ranges(text)
    yaml = _yaml_range(text)
    if yaml is not None:
        ranges.append(yaml)
    masked = _replace_ranges(text, ranges)
    return _replace_ranges(masked, _inline_code_ranges(masked))


def _content_text(text: str) -> str:
    """Hide non-content spans without changing length or newline positions."""
    masked = _mask_code_and_yaml(text)
    return _HTML_COMMENT.sub(lambda match: _blank(match.group(0)), masked)


def _heading_value(body: str, level: int) -> tuple[int, str | None]:
    body = re.sub(r"[ \t]+#+[ \t]*$", "", body)
    attributes = re.search(r"[ \t]+\{(?P<attributes>[^{}\n]*)\}[ \t]*$", body)
    heading_id = None
    if attributes:
        id_match = re.search(r"(?:^|[ \t])#(?P<id>[^ \t.}]+)", attributes.group("attributes"))
        if id_match:
            heading_id = id_match.group("id")
    return level, heading_id


def _extract_headings(text: str, content: str) -> list[Located]:
    return [
        Located(
            _heading_value(match.group("body"), len(match.group("marks"))),
            match.start(),
            _line_number(text, match.start()),
        )
        for match in _ATX_HEADING.finditer(content)
    ]


def _extract_regex_values(
    text: str,
    content: str,
    pattern: re.Pattern[str],
    value,
) -> list[Located]:
    return [
        Located(value(match), match.start(), _line_number(text, match.start())) for match in pattern.finditer(content)
    ]


def _strip_latex_comment(line: str) -> str:
    for index, char in enumerate(line):
        if char != "%":
            continue
        backslashes = 0
        cursor = index - 1
        while cursor >= 0 and line[cursor] == "\\":
            backslashes += 1
            cursor -= 1
        if backslashes % 2 == 0:
            return line[:index]
    return line


def _extract_mathmeta(text: str, content: str) -> list[Located]:
    result: list[Located] = []
    block_pattern = re.compile(
        r"\\begin\{mathmeta\}(?P<body>.*?)\\end\{mathmeta\}",
        re.DOTALL,
    )
    for block in block_pattern.finditer(content):
        body_start = block.start("body")
        cursor = body_start
        for line in block.group("body").splitlines(keepends=True):
            directive = _strip_latex_comment(line).strip()
            if directive:
                offset = cursor + len(line) - len(line.lstrip())
                result.append(Located(directive, offset, _line_number(text, offset)))
            cursor += len(line)
    return result


def _extract_citations(text: str, content: str) -> list[Located]:
    found: list[Located] = []
    for match in _PANDOC_CITATION.finditer(content):
        found.append(Located(match.group("key").rstrip(".:"), match.start(), _line_number(text, match.start())))
    for match in _LATEX_CITATION.finditer(content):
        for key in match.group("keys").split(","):
            cleaned = key.strip()
            if cleaned:
                found.append(Located(cleaned, match.start(), _line_number(text, match.start())))
    return sorted(found, key=lambda item: item.offset)


def _brace_argument(text: str, opening: int) -> tuple[str, int]:
    if opening >= len(text) or text[opening] != "{":
        raise StructureParseError("internal error: expected an opening brace")
    depth = 1
    index = opening + 1
    while index < len(text):
        char = text[index]
        if char == "\\":
            index += 2
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return text[opening + 1 : index], index + 1
        index += 1
    raise StructureParseError(f"unclosed braced argument at line {_line_number(text, opening)}")


def _extract_terms(text: str, content: str) -> list[Located]:
    result: list[Located] = []
    for match in _TERM_MACRO.finditer(content):
        opening = match.end()
        while opening < len(content) and content[opening].isspace():
            opening += 1
        argument, _end = _brace_argument(content, opening)
        identity = re.sub(r"\s+", " ", argument.strip())
        result.append(
            Located(
                (match.group("operation"), identity),
                match.start(),
                _line_number(text, match.start()),
            )
        )
    return result


def _mask_hidden_term_identities(content: str) -> str:
    """Hide non-rendered keys from math checks, retaining source locations.

    An ``as`` macro renders its second argument, while its first argument is
    checked separately as a canonical term identity. Plain term macros render
    their key, except for ``termref``, which only records an index reference.
    """
    ranges: list[tuple[int, int]] = []
    for match in _TERM_MACRO.finditer(content):
        alias = match.group().endswith("as")
        if not alias and match.group("operation") != "ref":
            continue
        opening = match.end()
        while opening < len(content) and content[opening].isspace():
            opening += 1
        _identity, end = _brace_argument(content, opening)
        if alias:
            display = end
            while display < len(content) and content[display].isspace():
                display += 1
            _brace_argument(content, display)
        ranges.append((opening + 1, end - 1))
    return _replace_ranges(content, ranges)


def _is_escaped(text: str, offset: int) -> bool:
    backslashes = 0
    offset -= 1
    while offset >= 0 and text[offset] == "\\":
        backslashes += 1
        offset -= 1
    return backslashes % 2 == 1


def _find_unescaped(text: str, delimiter: str, start: int) -> int:
    position = text.find(delimiter, start)
    while position >= 0:
        if not _is_escaped(text, position):
            return position
        position = text.find(delimiter, position + len(delimiter))
    return -1


def _math_environment_at(content: str, offset: int) -> tuple[str, int] | None:
    opening = re.match(r"\\begin\{(?P<name>[^{}\n]+)\}", content[offset:])
    if opening is None or opening.group("name") not in _MATH_ENVIRONMENTS:
        return None
    name = opening.group("name")
    token = re.compile(rf"\\(?P<action>begin|end)\{{{re.escape(name)}\}}")
    depth = 0
    for match in token.finditer(content, offset):
        if match.group("action") == "begin":
            depth += 1
        else:
            depth -= 1
            if depth == 0:
                body_start = offset + opening.end()
                return content[body_start : match.start()].strip(), match.end()
    return None


def normalize_math(payload: str) -> str:
    """Compare mathematical tokens, allowing plain prose to be translated.

    Text can move around its mathematical arguments in Japanese. Its meaning,
    like prose outside formulas, needs translation review. Keep symbolic labels
    such as I, Ax, Borel and (ii), and conservatively retain text containing
    numbers, TeX commands, nested groups or embedded mathematics.
    """

    def prose(match: re.Match[str]) -> str:
        body = match.group(1).strip()
        if re.fullmatch(r"(?:[A-Z][A-Za-z–-]*|\([ivxlcdm]+\))", body):
            return match.group(0)
        if any(not (char.isalpha() or char.isspace() or char in ".,:;'\"-–—()、。，：；「」『』（）") for char in body):
            return match.group(0)
        return " "

    payload = re.sub(r"\\(?:text|textrm|textnormal|mbox)\{([^{}\\$]*)\}", prose, payload)
    # Tokenize instead of removing all whitespace: \\in X and \\inX differ.
    return " ".join(re.findall(r"\\[A-Za-z]+|\\.|[^\s]", payload))


def _extract_mathematics(text: str, content: str) -> list[Located]:
    result: list[Located] = []
    index = 0
    while index < len(content):
        environment = _math_environment_at(content, index) if content.startswith(r"\begin{", index) else None
        if environment is not None:
            payload, end = environment
            name_match = re.match(r"\\begin\{(?P<name>[^{}\n]+)\}", content[index:])
            assert name_match is not None
            result.append(
                Located(
                    (f"environment:{name_match.group('name')}", normalize_math(payload)),
                    index,
                    _line_number(text, index),
                )
            )
            index = end
            continue

        delimiter = None
        closing = None
        kind = None
        if content.startswith("$$", index) and not _is_escaped(content, index):
            delimiter, closing, kind = "$$", "$$", "display"
        elif content.startswith(r"\[", index) and not _is_escaped(content, index):
            delimiter, closing, kind = r"\[", r"\]", "display"
        elif content.startswith(r"\(", index) and not _is_escaped(content, index):
            delimiter, closing, kind = r"\(", r"\)", "inline"
        elif content[index] == "$" and not _is_escaped(content, index):
            delimiter, closing, kind = "$", "$", "inline"

        if delimiter is None or closing is None or kind is None:
            index += 1
            continue
        end = _find_unescaped(content, closing, index + len(delimiter))
        if end < 0:
            index += len(delimiter)
            continue
        payload = normalize_math(content[index + len(delimiter) : end])
        result.append(Located((kind, payload), index, _line_number(text, index)))
        index = end + len(closing)
    return result


def snapshot(text: str) -> Snapshot:
    """Extract the translation-sensitive structure from one Markdown source."""
    content = _content_text(text)
    marker_content = _mask_code_and_yaml(text)
    headings = _extract_headings(text, content)
    labels = _extract_regex_values(
        text,
        content,
        re.compile(r"\\label\s*\{(?P<label>[^{}\n]+)\}"),
        lambda match: match.group("label"),
    )
    citations = _extract_citations(text, content)
    mathmeta = _extract_mathmeta(text, content)
    environments = _extract_regex_values(
        text,
        content,
        _ENVIRONMENT,
        lambda match: (match.group("action"), match.group("name")),
    )
    formalization = _extract_regex_values(
        text,
        marker_content,
        _FORMALIZATION,
        lambda match: match.group("directive"),
    )
    layout = _extract_regex_values(
        text,
        content,
        re.compile(r"\\(?P<control>part|printindex)\b"),
        lambda match: match.group("control"),
    )
    mathematics = _extract_mathematics(text, _mask_hidden_term_identities(content))
    terms = _extract_terms(text, content)

    structural_order = sorted(
        [
            *(Located(("heading", *item.value), item.offset, item.line) for item in headings),
            *(Located(("environment", *item.value), item.offset, item.line) for item in environments),
            *(Located(("formalization", item.value), item.offset, item.line) for item in formalization),
            *(Located(("layout", item.value), item.offset, item.line) for item in layout),
        ],
        key=lambda item: item.offset,
    )
    return Snapshot(
        headings=headings,
        labels=labels,
        citations=citations,
        mathmeta=mathmeta,
        environments=environments,
        formalization=formalization,
        layout=layout,
        mathematics=mathematics,
        terms=terms,
        structural_order=structural_order,
    )


def _short(value: Any, limit: int = 88) -> str:
    rendered = repr(value).replace("\n", r"\n")
    if len(rendered) > limit:
        return rendered[: limit - 3] + "..."
    return rendered


def _first_mismatch(name: str, source: list[Located], translation: list[Located]) -> str | None:
    limit = min(len(source), len(translation))
    for index in range(limit):
        if source[index].value != translation[index].value:
            return (
                f"{name} item {index + 1}: source line {source[index].line} has "
                f"{_short(source[index].value)}; translation line {translation[index].line} has "
                f"{_short(translation[index].value)}"
            )
    if len(source) > limit:
        item = source[limit]
        return f"{name}: translation is missing source item {limit + 1} from line {item.line}: {_short(item.value)}"
    if len(translation) > limit:
        item = translation[limit]
        return f"{name}: translation has extra item {limit + 1} at line {item.line}: {_short(item.value)}"
    return None


def _multiset_mismatch(name: str, source: list[Located], translation: list[Located]) -> str | None:
    """Compare reorderable structural items while retaining useful locations."""
    source_counts = Counter(item.value for item in source)
    translation_counts = Counter(item.value for item in translation)
    if source_counts == translation_counts:
        return None

    missing = next((item for item in source if source_counts[item.value] > translation_counts[item.value]), None)
    extra = next(
        (item for item in translation if translation_counts[item.value] > source_counts[item.value]),
        None,
    )
    details: list[str] = []
    if missing is not None:
        details.append(f"translation is missing source line {missing.line}: {_short(missing.value)}")
    if extra is not None:
        details.append(f"translation has an extra item at line {extra.line}: {_short(extra.value)}")
    return f"{name}: {'; '.join(details)}"


_COMPARISONS = (
    ("headings", "headings"),
    ("LaTeX labels", "labels"),
    ("mathmeta directives", "mathmeta"),
    ("LaTeX environments", "environments"),
    ("formalization markers", "formalization"),
    ("part/index controls", "layout"),
)

_MULTISET_COMPARISONS = (
    ("citations", "citations"),
    ("mathematics", "mathematics"),
    ("term identities", "terms"),
)


def compare_texts(source_text: str, translation_text: str) -> list[str]:
    """Return concise diagnostics for every mismatching structural category."""
    source = snapshot(source_text.replace("\r\n", "\n"))
    translation = snapshot(translation_text.replace("\r\n", "\n"))
    diagnostics: list[str] = []
    for name, attribute in _COMPARISONS:
        mismatch = _first_mismatch(name, getattr(source, attribute), getattr(translation, attribute))
        if mismatch is not None:
            diagnostics.append(mismatch)
    for name, attribute in _MULTISET_COMPARISONS:
        mismatch = _multiset_mismatch(name, getattr(source, attribute), getattr(translation, attribute))
        if mismatch is not None:
            diagnostics.append(mismatch)

    structure_fields_match = all(
        [item.value for item in getattr(source, attribute)] == [item.value for item in getattr(translation, attribute)]
        for attribute in ("headings", "environments", "formalization", "layout")
    )
    if structure_fields_match:
        ordering = _first_mismatch(
            "structural ordering",
            source.structural_order,
            translation.structural_order,
        )
        if ordering is not None:
            diagnostics.append(ordering)
    return diagnostics


def compare_files(source: Path, translation: Path) -> list[str]:
    return compare_texts(
        source.read_text(encoding="utf-8"),
        translation.read_text(encoding="utf-8"),
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, metavar="SOURCE")
    parser.add_argument("translation", type=Path, metavar="TRANSLATION")
    args = parser.parse_args(argv)
    try:
        diagnostics = compare_files(args.source, args.translation)
    except (OSError, UnicodeError, StructureParseError) as error:
        print(f"translation structure check failed: {error}", file=sys.stderr)
        return 2
    if diagnostics:
        print(f"{args.translation}: structure differs from {args.source}", file=sys.stderr)
        for diagnostic in diagnostics:
            print(f"  - {diagnostic}", file=sys.stderr)
        return 1
    print(f"translation structure OK: {args.translation}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
