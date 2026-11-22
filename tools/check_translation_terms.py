#!/usr/bin/env python3
"""Check Japanese PO translations against the shared index/terminology glossary.

Read-only. Explicit avoid lists check rendered text; opt-in definition keys check
termdefine displays. Ambiguous variants can be restricted to English source
phrases. This does not infer translations or rewrite mathematical content.
YAML is read with the repository's existing Pandoc dependency, as in book-filter.

Exit codes: 0 success, 1 validation or execution failure, 2 command-line usage error.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from check_translation_structure import (
    StructureParseError,
    _brace_argument,
    _content_text,
    _is_escaped,
    _mask_hidden_term_identities,
    _replace_ranges,
)
from project_translation_sourcemap import PoMessage, ProjectionError, read_po


class TerminologyError(ValueError):
    """Invalid glossary or unsupported input; never silently disable a rule."""


@dataclass(frozen=True)
class Rule:
    id: str
    preferred: str
    avoid: tuple[str, ...]
    source_terms: tuple[str, ...]
    definition_keys: tuple[str, ...]
    definition_forms: tuple[str, ...]


@dataclass(frozen=True)
class Glossary:
    terms: int
    rules: tuple[Rule, ...]


def _meta_value(node: dict[str, Any]) -> Any:
    kind, value = node["t"], node["c"]
    if kind == "MetaMap":
        return {key: _meta_value(item) for key, item in value.items()}
    if kind == "MetaList":
        return [_meta_value(item) for item in value]
    if kind in {"MetaString", "MetaBool"}:
        return value
    if kind == "MetaInlines":
        result = []
        for inline in value:
            if inline["t"] == "Str":
                result.append(inline["c"])
            elif inline["t"] in {"Space", "SoftBreak", "LineBreak"}:
                result.append(" ")
            else:
                raise TerminologyError("glossary values must be plain text, without Markdown markup")
        return "".join(result)
    raise TerminologyError(f"unsupported glossary value: {kind}; use plain strings or lists")


def _string(value: Any, name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise TerminologyError(f"{name}: expected a nonempty string")
    return value


def _strings(value: Any, name: str) -> tuple[str, ...]:
    if not isinstance(value, list):
        raise TerminologyError(f"{name}: expected a list of strings")
    values = tuple(_string(item, name) for item in value)
    if len(set(values)) != len(values):
        raise TerminologyError(f"{name}: duplicate values")
    return values


def _compact(text: str) -> str:
    return re.sub(r"\s+", "", text)


def parse_glossary(data: Any) -> Glossary:
    if not isinstance(data, dict) or str(data.get("version")) != "1" or data.get("language") != "ja":
        raise TerminologyError("expected glossary version 1, language ja")
    if set(data) - {"version", "language", "terms", "spellings"}:
        raise TerminologyError("unknown glossary field")
    terms = data.get("terms")
    spellings = data.get("spellings", [])
    if not isinstance(terms, list) or not terms or not isinstance(spellings, list):
        raise TerminologyError("terms must be a nonempty list; spellings must be a list")
    ids: set[str] = set()
    english_keys: set[str] = set()
    definition_keys: set[str] = set()
    rules = []
    for entries, is_term in ((terms, True), (spellings, False)):
        for entry in entries:
            if not isinstance(entry, dict):
                raise TerminologyError("glossary entries must be objects")
            allowed = {"id", "avoid", "note"}
            allowed |= (
                {"english", "japanese", "reading", "status", "source_terms", "definition_keys", "definition_forms"}
                if is_term
                else {"preferred"}
            )
            unknown = set(entry) - allowed
            if unknown:
                raise TerminologyError(f"{entry.get('id', '?')}: unknown fields {sorted(unknown)}")
            identity = _string(entry.get("id"), "id")
            if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", identity) or identity in ids:
                raise TerminologyError(f"invalid or duplicate id: {identity}")
            ids.add(identity)
            preferred = _string(entry.get("japanese" if is_term else "preferred"), identity)
            if "note" in entry:
                _string(entry["note"], f"{identity}.note")
            if is_term:
                english = _string(entry.get("english"), f"{identity}.english")
                if english in english_keys:
                    raise TerminologyError(f"duplicate English index key: {english}")
                english_keys.add(english)
                if entry.get("status") not in {"draft", "approved"}:
                    raise TerminologyError(f"{identity}: expected draft or approved status")
                if "reading" in entry:
                    _string(entry["reading"], f"{identity}.reading")
            avoid = _strings(entry.get("avoid", []), f"{identity}.avoid")
            source = _strings(entry.get("source_terms", []), f"{identity}.source_terms")
            keys = _strings(entry.get("definition_keys", []), f"{identity}.definition_keys")
            forms = _strings(entry.get("definition_forms", [preferred]), f"{identity}.definition_forms")
            if source and not avoid or "definition_forms" in entry and not keys or not forms:
                raise TerminologyError(f"{identity}: scope/forms without corresponding checks")
            if any(_compact(v) in _compact(form) for v in avoid for form in (preferred, *forms)):
                raise TerminologyError(f"{identity}: an avoided spelling conflicts with an accepted form")
            if definition_keys.intersection(keys):
                raise TerminologyError(f"{identity}: duplicate definition key")
            definition_keys.update(keys)
            if avoid or keys:
                rules.append(Rule(identity, preferred, avoid, source, keys, forms))
    # Prevent a global rule from rejecting another entry's accepted spelling.
    for rule in rules:
        if not rule.source_terms:
            for entry in terms:
                accepted = [entry["japanese"], *entry.get("definition_forms", [])]
                if any(_compact(v) in _compact(form) for v in rule.avoid for form in accepted):
                    raise TerminologyError(f"{rule.id}: conflicts with preferred spelling for {entry['id']}")
    return Glossary(len(terms), tuple(rules))


def load_glossary(path: Path) -> Glossary:
    text = path.read_text(encoding="utf-8")
    result = subprocess.run(
        ["pandoc", "-f", "markdown-smart", "-t", "json"],
        input=f"---\n{text}\n---\n",
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode:
        raise TerminologyError(f"{path}: cannot parse YAML: {result.stderr.strip()}")
    try:
        meta = json.loads(result.stdout)["meta"]
        return parse_glossary({key: _meta_value(value) for key, value in meta.items()})
    except (KeyError, TypeError, json.JSONDecodeError) as error:
        raise TerminologyError(f"{path}: invalid glossary metadata") from error


_DEFINITION = re.compile(r"\\termdefine(?P<alias>as)?\s*(?=\{)")
_HIDDEN = re.compile(
    r"§\{[^}]*\}|\{#[^}]*\}|\\(?:label|ref|pageref|index|cite\w*)\{[^}]*\}"
    r"|\[@[^\]]*\]|\]\([^)]*\)|\\(?:href|url)\{[^}]*\}"
)


def _definitions(content: str) -> list[tuple[str, str]]:
    result = []
    for match in _DEFINITION.finditer(content):
        key, end = _brace_argument(content, match.end())
        display = key
        if match["alias"]:
            while end < len(content) and content[end].isspace():
                end += 1
            display, _end = _brace_argument(content, end)
        result.append((" ".join(key.split()), display))
    return result


def check_message(message: PoMessage, glossary: Glossary) -> list[str]:
    content = _content_text(message.msgstr)
    hidden = []
    # In Markdown, percent signs remain prose. Only explicitly raw TeX fences
    # interpret them as comments; mathmeta is hidden as a complete environment.
    raw_tex = re.compile(r"(?m)^[ ]{0,3}(?P<fence>`{3,}|~{3,})[ \t]*\{=(?:latex|tex)\}[ \t]*\n")
    for opening in raw_tex.finditer(message.msgstr):
        closing = re.search(
            rf"(?m)^[ ]{{0,3}}{re.escape(opening['fence'][0])}{{{len(opening['fence'])},}}[ \t]*$",
            message.msgstr[opening.end() :],
        )
        end = len(content) if closing is None else opening.end() + closing.start()
        for match in re.finditer("%", content[opening.end() : end]):
            start = opening.end() + match.start()
            if not _is_escaped(content, start):
                line_end = content.find("\n", start, end)
                hidden.append((start, end if line_end < 0 else line_end))
    hidden.extend(match.span() for match in re.finditer(r"\\begin\{mathmeta\}.*?\\end\{mathmeta\}", content, re.DOTALL))
    content = _replace_ranges(content, hidden)
    definitions = _definitions(content)
    visible = _mask_hidden_term_identities(content)
    # Keep excluded spans as barriers, so phrases cannot join across code or keys.
    if len(visible) != len(message.msgstr):
        raise ValueError("term masking must preserve source offsets")
    visible = "".join("\0" if a != b else b for a, b in zip(message.msgstr, visible, strict=True))
    visible = _HIDDEN.sub("\0", visible)
    visible = _compact(visible)
    source = " ".join(message.msgid.casefold().split())
    errors = []
    for rule in glossary.rules:
        in_scope = not rule.source_terms or any(
            re.search(r"(?<!\w)" + re.escape(" ".join(term.casefold().split())) + r"(?!\w)", source)
            for term in rule.source_terms
        )
        if in_scope:
            for variant in rule.avoid:
                if _compact(variant) in visible:
                    errors.append(f"{rule.id}: avoid {variant!r}; use {rule.preferred!r}")
        for key, display in definitions:
            if key in rule.definition_keys and _compact(display) not in {_compact(f) for f in rule.definition_forms}:
                errors.append(f"{rule.id}: definition {key!r} displays {display!r}; expected {rule.definition_forms!r}")
    return errors


def check_catalogs(paths: list[Path], glossary: Glossary) -> list[str]:
    diagnostics = []
    for path in paths:
        for message in read_po(path):
            for diagnostic in check_message(message, glossary):
                diagnostics.append(f"{path}:{message.line}: {diagnostic}")
    return diagnostics


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--glossary", type=Path, default=Path("polish-space-ja/l10n/glossary-ja.yaml"))
    parser.add_argument("catalogs", nargs="*", type=Path)
    args = parser.parse_args(argv)
    paths = args.catalogs or sorted((args.glossary.parent / "ja").glob("*.po"))
    try:
        if not paths:
            raise TerminologyError("no PO catalogs to check")
        glossary = load_glossary(args.glossary)
        errors = check_catalogs(paths, glossary)
        if errors:
            print("\n".join(errors), file=sys.stderr)
            return 1
    except (OSError, UnicodeError, TerminologyError, ProjectionError, StructureParseError) as error:
        print(f"translation terminology check failed: {error}", file=sys.stderr)
        return 1
    print(f"translation terminology OK: {len(paths)} catalogs, {glossary.terms} terms, {len(glossary.rules)} rules")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
