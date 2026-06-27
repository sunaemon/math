#!/usr/bin/env python3
import argparse
import json
import re
import sys
from pathlib import Path


DEFAULT_SOURCE = Path("polish-space/src/polish-space-book.md")
DEFAULT_MANIFEST = Path("polish-space/src/polish-space-book.json")
HEADER_RE = re.compile(r"^(?P<marks>#{1,6})\s+(?P<title>.*?)(?:\s+\{(?P<attrs>[^}]*)\})?\s*$")
LABEL_RE = re.compile(r"#(?P<label>[-A-Za-z0-9_:]+)")


FENCE_RE = re.compile(r"^(\s*)(`{3,}|~{3,})")


def parse_headers(lines):
    headers = []
    fence = None
    for index, line in enumerate(lines, start=1):
        fence_match = FENCE_RE.match(line)
        if fence_match:
            marker = fence_match.group(2)
            if fence is None:
                fence = marker[0]
            elif marker.startswith(fence * 3):
                fence = None
            continue
        if fence is not None:
            continue
        match = HEADER_RE.match(line)
        if not match:
            continue
        attrs = match.group("attrs") or ""
        label_match = LABEL_RE.search(attrs)
        headers.append(
            {
                "line": index,
                "level": len(match.group("marks")),
                "title": match.group("title").strip(),
                "label": label_match.group("label") if label_match else "",
            }
        )
    return headers


def find_by_line(headers, line_number):
    containing = None
    for header in headers:
        if header["line"] <= line_number:
            containing = header
        else:
            break
    return [containing] if containing else []


def find_matches(headers, query):
    if query.isdigit():
        return find_by_line(headers, int(query))

    normalized = query.lower()
    matches = [
        header
        for header in headers
        if query == header["label"] or normalized in header["label"].lower() or normalized in header["title"].lower()
    ]

    exact = [header for header in matches if query == header["label"] or normalized == header["title"].lower()]
    return exact or matches


def section_end(headers, match, total_lines):
    for header in headers:
        if header["line"] > match["line"] and header["level"] <= match["level"]:
            return header["line"] - 1
    return total_lines


def print_section(source, lines, headers, match):
    start = match["line"]
    end = section_end(headers, match, len(lines))
    label = f" {{{match['label']}}}" if match["label"] else ""
    print(f"match: line {start}, level {match['level']}, {match['title']}{label}")
    print(f"range: {source}:{start}-{end}")
    print()
    for line_number in range(start, end + 1):
        print(f"{line_number}: {lines[line_number - 1]}", end="")


def load_manifest_sources(manifest):
    if not manifest.is_file():
        return []
    try:
        data = json.loads(manifest.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        sys.exit(f"error: could not parse manifest {manifest}: {exc}")
    return [Path(path) for path in data.get("chapters", [])]


def main():
    parser = argparse.ArgumentParser(
        description=(
            "Extract a section from repository .md sources by label, title fragment, "
            "or line number. By default, search chapter files from polish-space/src/polish-space-book.json."
        )
    )
    parser.add_argument(
        "--source",
        help=(
            ".md source file to inspect. If omitted, searches chapter files from "
            f"{DEFAULT_MANIFEST}; falls back to {DEFAULT_SOURCE}."
        ),
    )
    parser.add_argument(
        "--manifest",
        default=str(DEFAULT_MANIFEST),
        help=f"chapter manifest to use when --source is omitted; default: {DEFAULT_MANIFEST}",
    )
    parser.add_argument("query")
    args = parser.parse_args()

    if args.source:
        sources = [Path(args.source)]
    else:
        sources = load_manifest_sources(Path(args.manifest))
        if not sources:
            sources = [DEFAULT_SOURCE]

    missing = [source for source in sources if not source.is_file()]
    if missing:
        sys.exit(f"error: source file does not exist: {missing[0]}")

    if args.query.isdigit() and not args.source and len(sources) > 1:
        sys.exit("error: line-number queries require --source when searching chapter files")

    all_matches = []
    for source in sources:
        lines = source.read_text(encoding="utf-8", errors="replace").splitlines(keepends=True)
        headers = parse_headers(lines)
        for match in find_matches(headers, args.query):
            all_matches.append((source, lines, headers, match))

    exact_matches = [
        item for item in all_matches if args.query == item[3]["label"] or args.query.lower() == item[3]["title"].lower()
    ]
    matches = exact_matches or all_matches

    if not matches:
        sys.exit(f"error: no section matched {args.query!r}")
    if len(matches) > 1:
        print(f"error: {len(matches)} sections matched {args.query!r}; use a more specific query", file=sys.stderr)
        for source, _lines, _headers, header in matches[:25]:
            label = f" {{{header['label']}}}" if header["label"] else ""
            print(
                f"{source}:{header['line']}: level {header['level']}, {header['title']}{label}",
                file=sys.stderr,
            )
        if len(matches) > 25:
            print(f"... {len(matches) - 25} more match(es)", file=sys.stderr)
        return 2

    source, lines, headers, match = matches[0]
    print_section(source, lines, headers, match)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
