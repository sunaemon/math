#!/usr/bin/env python3
"""Split a rendered debug ``.tex`` into an ``\\include``-structured master so a
single chapter can be re-typeset with ``\\includeonly`` for a fast preview.

The debug ``.tex`` (booklink-highlight enabled) is one monolithic document. This
tool slices it, without touching its content, into:

* a *master* (``<stem>-preview-master.tex``): the original preamble followed by
  ``\\include`` of every unit, plus an ``\\includeonly`` hook driven by a
  ``\\PreviewOnly`` macro the build passes on the command line; and
* one *unit* file per front-matter / chapter / end-matter span under
  ``<stem>-preview/``.

Because the chapter spans are copied verbatim, every ``\\BooklinkStart[entry=N]``
and ``\\SkipStart{key}`` keeps its global number, so the whole-book source map and
the viewer overlays resolve against a chapter preview exactly as against the full
debug PDF — no renumbering, no source-map regeneration.

The preview is a *separate* artifact: the canonical debug PDF and source map are
untouched. The full master build only exists to populate every unit's ``.aux`` so
``\\includeonly`` cross-references resolve; the user only ever views one chapter.

The master keeps the preamble verbatim (its only external path is the
repo-relative ``\\input`` of ``macros.tex``, and the book uses inline TikZ with no
``\\includegraphics``), so the build runs from the repo root exactly like the
debug build, with ``-output-directory`` set to the build dir. Units are
``\\include``'d by bare name; the build puts the unit dir on ``TEXINPUTS`` so the
names resolve while each unit's ``.aux`` lands flat in the output dir.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

BOUNDARY = re.compile(r"\\(chapter\*?|part)\b")
LABEL = re.compile(r"\\label\{sec:([A-Za-z0-9:_-]+)\}")
# A chapter source's leading "# Title {#sec:ID}" anchor (Pandoc heading id).
HEADING_ID = re.compile(r"^\#\s+.*\{\#([A-Za-z0-9:_-]+)\}", re.MULTILINE)


def split_body(body: list[str]) -> tuple[int, list[int]]:
    """Return ``(end_start, unit_starts)``: the index where the end matter
    (``\\printindex`` and the bibliography) begins, and the body-line indices that
    open each chapter unit. A ``\\part`` immediately followed by a ``\\chapter`` is
    folded into that chapter's unit so the part heading travels with it."""
    end_start = next(
        (i for i, ln in enumerate(body) if ln.startswith(r"\printindex")),
        None,
    )
    if end_start is None:
        raise SystemExit(
            "split_preview_tex: no \\printindex line found in the debug .tex; "
            "expected the index/bibliography end matter to follow the last chapter"
        )
    # Pull the index's page-break preamble (\cleardoublepage \phantomsection
    # \addcontentsline) into the end matter so it is not stranded on the last
    # chapter.
    lead = (r"\cleardoublepage", r"\phantomsection", r"\addcontentsline", r"\protect")
    while end_start > 0:
        prev = body[end_start - 1].lstrip()
        if prev and prev.startswith(lead):
            end_start -= 1
        else:
            break

    boundaries = [i for i in range(end_start) if BOUNDARY.match(body[i])]
    starts: list[int] = []
    for i in boundaries:
        if starts and body[starts[-1]].startswith(r"\part") and "".join(body[starts[-1] + 1 : i]).strip() == "":
            continue  # \part directly precedes this \chapter: one unit
        starts.append(i)
    return end_start, starts


def chapter_id(chapter_md: Path) -> str | None:
    """The ``sec:ID`` anchor of a chapter source's first heading, if any."""
    try:
        text = chapter_md.read_text(encoding="utf-8")
    except OSError:
        return None
    m = HEADING_ID.search(text)
    if not m:
        return None
    ident = m.group(1)
    return ident[4:] if ident.startswith("sec:") else ident


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--debug-tex", required=True, type=Path)
    ap.add_argument("--manifest", required=True, type=Path)
    ap.add_argument("--book-dir", required=True, help="book directory, e.g. polish-space")
    ap.add_argument("--stem", required=True, help="book stem, e.g. polish-space-book")
    ap.add_argument("--out-dir", required=True, type=Path)
    args = ap.parse_args(argv)

    src = args.debug_tex.read_text(encoding="utf-8")
    lines = src.splitlines(keepends=True)
    try:
        bd = next(i for i, ln in enumerate(lines) if ln.startswith(r"\begin{document}"))
        ed = next(i for i, ln in enumerate(lines) if ln.startswith(r"\end{document}"))
    except StopIteration:
        print(f"split_preview_tex: {args.debug_tex} has no \\begin/\\end{{document}}", file=sys.stderr)
        return 1

    preamble = "".join(lines[:bd])
    body = lines[bd + 1 : ed]

    end_start, starts = split_body(body)
    if not starts:
        print(f"split_preview_tex: no chapter boundaries found in {args.debug_tex}", file=sys.stderr)
        return 1

    # Chapters appear in the .tex in manifest order, one \chapter (or \chapter*)
    # each, so name chapter chunks positionally against the manifest. \part-only
    # chunks (a part heading with intro prose before its first chapter) get a
    # neutral _part-N name and never consume a chapter slot. The chunk's own
    # sec:ID is cross-checked against the manifest chapter's heading id, so an
    # ordering drift is reported rather than silently mis-mapped.
    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    chapter_paths = [Path(c) for c in manifest.get("chapters", [])]
    has_chapter = re.compile(r"\\chapter\*?\b")

    units: list[tuple[str, str]] = [("_front", "".join(body[: starts[0]]))]
    chapter_map: dict[str, str] = {}
    ci = pi = 0
    for k, i in enumerate(starts):
        j = starts[k + 1] if k + 1 < len(starts) else end_start
        chunk = "".join(body[i:j])
        if not has_chapter.search(chunk):
            units.append((f"_part-{pi}", chunk))
            pi += 1
            continue
        if ci < len(chapter_paths):
            name = chapter_paths[ci].stem
            label = LABEL.search(chunk)
            expect = chapter_id(chapter_paths[ci])
            if label and expect and label.group(1) != expect:
                print(
                    f"split_preview_tex: warning: chapter #{ci} ({name}) tex label "
                    f"sec:{label.group(1)} != manifest heading sec:{expect}",
                    file=sys.stderr,
                )
        else:
            name = f"_chapter-extra-{ci}"
        units.append((name, chunk))
        chapter_map[name] = name
        ci += 1
    units.append(("_endmatter", "".join(body[end_start:])))
    if ci != len(chapter_paths):
        print(
            f"split_preview_tex: warning: {ci} chapter chunks vs {len(chapter_paths)} manifest chapters",
            file=sys.stderr,
        )

    out_dir = args.out_dir
    unit_dir = out_dir / f"{args.stem}-preview"
    unit_dir.mkdir(parents=True, exist_ok=True)
    # Clear stale units from a previous chapter set so renamed/removed chapters
    # do not linger and get \include'd.
    for old in unit_dir.glob("*.tex"):
        old.unlink()

    # Units are \include'd by bare name; the build adds the unit dir to TEXINPUTS
    # so the names resolve while their .aux files stay flat in the output dir.
    include_names = []
    for name, text in units:
        (unit_dir / f"{name}.tex").write_text(text, encoding="utf-8")
        include_names.append(name)

    includes = "\n".join(rf"\include{{{n}}}" for n in include_names)
    # \PreviewOnly (a repo build passes it as \def on the command line) selects a
    # single \include; absent, every unit is typeset (the full warm-aux build).
    hook = r"\ifdefined\PreviewOnly\expandafter\includeonly\expandafter{\PreviewOnly}\fi" + "\n"
    master = preamble + hook + r"\begin{document}" + "\n" + includes + "\n" + r"\end{document}" + "\n"
    (out_dir / f"{args.stem}-preview-master.tex").write_text(master, encoding="utf-8")

    # Map a chapter source basename -> its \include unit, for the viewer/build to
    # resolve which preview to build for an edited .md.
    (unit_dir / "units.json").write_text(
        json.dumps(
            {"stem": args.stem, "chapters": chapter_map, "units": [n for n, _ in units]},
            indent=2,
        ),
        encoding="utf-8",
    )
    print(f"  split-preview: {len(units)} units ({len(chapter_map)} chapters) -> {unit_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
