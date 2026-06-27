#!/usr/bin/env python3
"""Emit Make variables for every chaptered book manifest.

Each `<dir>/src/<stem>.json` manifest defines a book whose master source is
`<stem>.md` and whose artifacts build into `<dir>/build/`. This script turns
all manifests into a single Make include (`BOOK_STEMS` plus per-book
`<stem>_DIR`, `<stem>_MANIFEST`, `<stem>_SOURCE`, `<stem>_CHAPTERS`,
`<stem>_INPUTS`, and the `<stem>_PANDOC_INPUTS` / `<stem>_BOOKLINK_DEPS` pair
that routes booklink chapters through their injected copies), so the Makefile
needs one process per `make` invocation no matter how many books exist.

The Lean files passed after `--leans` are scanned for booklink markers — the
markers name the chapter each Lean file formalizes, so no separate registry is
kept. From them the include also gets `BOOKLINK_LEANS` / `BOOKLINK_SOURCES`,
per-book `<stem>_BOOKLINK_LEANS`, and per-directory `<dir>_VIEWER_DEPS` (the
artifacts the formalization viewer needs for that project).
"""

import re
import sys
from pathlib import Path, PurePosixPath

from booklink_sourcemap import discover_booklinks
from book_manifest import read_manifest

STEM_PATTERN = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]*$")


def fail(message: str) -> int:
    print(f"books_mk.py: {message}", file=sys.stderr)
    return 2


def main(argv: list[str]) -> int:
    args = argv[1:]
    lean_files: list[str] = []
    if "--leans" in args:
        split = args.index("--leans")
        args, lean_files = args[:split], args[split + 1 :]
    manifests = args
    if not manifests:
        return fail("usage: books_mk.py MANIFEST... [--leans LEAN_FILE...]")

    try:
        booklinks = discover_booklinks([Path(lean) for lean in lean_files])
    except (OSError, ValueError) as exc:
        return fail(str(exc))
    source_to_leans: dict[str, list[str]] = {}
    for lean_file, sources in booklinks:
        for marker_source in sources:
            source_to_leans.setdefault(marker_source, []).append(str(lean_file))

    stems: list[str] = []
    lines: list[str] = []
    seen: dict[str, str] = {}
    viewer_deps: dict[str, list[str]] = {}
    for raw in manifests:
        manifest = PurePosixPath(raw)
        parts = manifest.parts
        if len(parts) != 3 or parts[1] != "src" or manifest.suffix != ".json":
            return fail(f"manifest path must look like <dir>/src/<stem>.json: {manifest}")
        stem = manifest.stem
        if not STEM_PATTERN.match(stem):
            return fail(f"book stem must match {STEM_PATTERN.pattern}: {manifest}")
        if stem in seen:
            return fail(f"duplicate book stem {stem!r}: {seen[stem]} and {manifest}")
        seen[stem] = str(manifest)

        try:
            source, chapters = read_manifest(Path(raw))
        except ValueError as exc:
            return fail(str(exc))
        if PurePosixPath(source).stem != stem:
            return fail(f"{manifest}: source file must be named {stem}.md, got {source}")
        for value in (source, *chapters):
            if re.search(r"[\s#$%:]", value):
                return fail(f"{manifest}: path is not Make-safe: {value!r}")

        # Booklink markers and chapter inputs are matched by their book-local
        # path: a booklink source is relative to its Lean file's own book src
        # (booklink_sourcemap.book_src_root), so an excerpt that owns its Lean
        # file through a symlink matches its own book-local chapter directly and
        # the sourcemap stays book-local with no path rewrite. A chapter that
        # has booklinks is built through an injected copy under
        # $(BUILD_DIR)/booklink-src/<input>; PANDOC_INPUTS is the pandoc input
        # list with such chapters swapped for their injected copies, and
        # BOOKLINK_DEPS lists those copies as prerequisites.
        book_leans: list[str] = []
        pandoc_inputs: list[str] = []
        booklink_deps: list[str] = []
        for inp in [source, *chapters]:
            leans = source_to_leans.get(inp, [])
            if leans:
                book_leans.extend(leans)
                injected = f"$(BUILD_DIR)/booklink-src/{inp}"
                pandoc_inputs.append(injected)
                booklink_deps.append(injected)
            else:
                pandoc_inputs.append(inp)
        book_leans = sorted(set(book_leans))

        stems.append(stem)
        lines.append(f"{stem}_DIR := {parts[0]}")
        lines.append(f"{stem}_MANIFEST := {manifest}")
        lines.append(f"{stem}_SOURCE := {source}")
        lines.append(f"{stem}_CHAPTERS := {' '.join(chapters)}")
        lines.append(f"{stem}_INPUTS := {' '.join([source, *chapters])}")
        lines.append(f"{stem}_PANDOC_INPUTS := {' '.join(pandoc_inputs)}")
        if booklink_deps:
            lines.append(f"{stem}_BOOKLINK_DEPS := {' '.join(sorted(set(booklink_deps)))}")
        lines.append(f"{stem}_BOOKLINK_LEANS := {' '.join(book_leans)}")

        deps = viewer_deps.setdefault(parts[0], [])
        if book_leans:
            deps.append(f"{parts[0]}/build/{stem}-sourcemap.json")
        # The debug PDF carries the booklink destinations the scroll-sync relies
        # on, so it stays the viewer default; the release PDF is built too and the
        # data-driven PDF selector offers it as the clean (un-synced) reading view.
        deps.append(f"{parts[0]}/build/{stem}-debug.pdf")
        deps.append(f"{parts[0]}/build/{stem}.pdf")

    print("# Generated by tools/books_mk.py; do not edit.")
    print(f"BOOKS_MK_MANIFESTS := {' '.join(manifests)}")
    print(f"BOOKS_MK_LEAN_FILES := {' '.join(lean_files)}")
    print(f"BOOK_STEMS := {' '.join(stems)}")
    print(f"BOOKLINK_LEANS := {' '.join(str(lean) for lean, _sources in booklinks)}")
    print(f"BOOKLINK_SOURCES := {' '.join(sorted(source_to_leans))}")
    print("\n".join(lines))
    for dirname, deps in viewer_deps.items():
        print(f"{dirname}_VIEWER_DEPS := {' '.join(deps)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
