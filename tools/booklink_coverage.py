#!/usr/bin/env python3
"""Report book-source regions not yet covered by a Lean booklink.

A booklink marker in a Lean file points at a chunk of book prose (an `excerpt`
for `target: prose`/`proof`) or at a statement environment (`target:
statement`, matched by title). `tools/booklink_sourcemap.py` resolves each
marker to a span in the owning `<book>/src/*.md` file. This tool inverts that
map: it segments each covered book source into statement environments and prose
paragraphs, measures how much of every unit overlaps a matched span, and prints
the prose and claims that have no — or only partial — Lean correspondence.

Coverage is measured at character granularity, so a paragraph whose first
sentence is anchored to a Lean declaration but whose remaining claims are not
shows up as `partial`, with the uncovered sub-segments listed. This is what
makes the report check *all* prose, not only whole-paragraph gaps.

Usage mirrors booklink_sourcemap.py: pass the Lean file(s) whose markers define
the coverage, and the report covers every book source those markers reference.

    tools/booklink_coverage.py polish-space/lean/PolishSpaceBook/ConcreteCantorBaireModels.lean

A unit can also be marked *exempt* — intentionally out of formalization scope
rather than a missing proof. Exempt units never appear in the gap list. A unit
is exempt only when an explicit author annotation in the book source opts it out.
Environment names such as example or remark do not determine mathematical scope:

    <!-- formalization: skip (cited to Kechris 1995) -->     # next unit
    <!-- formalization: skip-begin (chapter overview) -->    # ... region ...
    <!-- formalization: skip-end -->
    <!-- formalization: require -->                          # override a skip region

These ride in HTML comments, which pandoc drops, so they never render. Partial
skip regions exclude only their own content, never the rest of a mixed unit.

A `skip` must not contain any booklinked span, whether it is a bare single-block
`skip` or a `skip-begin`/`skip-end` region: a skip declares prose deliberately
out of formalization scope, so overlapping a Lean anchor is a contradiction, and
the tool errors (exit 2) rather than silently letting the anchor win. A bare
`skip` is just shorthand for a one-block region and obeys the same rule. Narrow
the skip — split the block so the anchored sentence sits outside it — or drop the
booklink.

Options:
    --source <book-local.md>   restrict the report to one book source
    --statements-only          only report statement environments
    --all                      also report structural units (headings, tables, ...)
    --show-exempt              list exempt units and their reasons
    --strict                   exit 1 if any non-exempt unit is uncovered/partial
    --json                     emit machine-readable JSON instead of text
"""

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

import booklink_sourcemap as bk
from formalization_annotations import FormalizationAnnotation, parse_formalization_scope


@dataclass
class Gap:
    start_line: int
    end_line: int
    text: str


@dataclass
class Unit:
    kind: str  # "statement" or "prose"
    label: str | None  # e.g. "theorem: Alexandrov's theorem", or None
    start_line: int
    end_line: int
    start_offset: int
    end_offset: int
    total_chars: int
    covered_chars: int
    status: str  # "covered" | "partial" | "uncovered" | "exempt"
    structural: bool
    snippet: str
    exempt_reason: str | None = None
    gaps: list[Gap] = field(default_factory=list)


def merge_intervals(intervals: list[tuple[int, int]]) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    for start, end in sorted(intervals):
        if out and start <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], end))
        else:
            out.append((start, end))
    return out


def overlap_length(start: int, end: int, intervals: list[tuple[int, int]]) -> int:
    total = 0
    for c0, c1 in intervals:
        lo, hi = max(start, c0), min(end, c1)
        if hi > lo:
            total += hi - lo
    return total


def complement(start: int, end: int, intervals: list[tuple[int, int]]) -> list[tuple[int, int]]:
    """Sub-intervals of [start, end) covered by no interval (intervals pre-merged)."""
    gaps: list[tuple[int, int]] = []
    cursor = start
    for c0, c1 in intervals:
        if c1 <= start or c0 >= end:
            continue
        if c0 > cursor:
            gaps.append((cursor, min(c0, end)))
        cursor = max(cursor, c1)
        if cursor >= end:
            break
    if cursor < end:
        gaps.append((cursor, end))
    return gaps


def covered_spans_by_source(root: Path, lean_files: list[Path]) -> dict[str, list[tuple[int, int]]]:
    """Matched booklink spans, grouped by the book source file they land in."""
    source_map = bk.build_combined_sourcemap(root, lean_files)
    spans: dict[str, list[tuple[int, int]]] = {}
    for entry in source_map["entries"]:
        match = entry.get("match", {})
        source = match.get("source")
        if not isinstance(source, str):
            lean_source = entry.get("lean", {}).get("source")
            book_source = entry.get("booklink", {}).get("source")
            if isinstance(lean_source, str) and isinstance(book_source, str):
                source = str(root / bk.book_src_root(lean_source) / book_source)
        if isinstance(source, str):
            # Failed selectors must remain visible as zero-coverage chapters.
            spans.setdefault(source, [])
        # A `statement` target attaches its best candidate's offsets even when the
        # title only matched weakly or did not resolve at all (match_statement in
        # booklink_sourcemap), unlike the prose path which nulls offsets on a miss.
        # Counting an "unresolved" match as covered would let a drifted/typo'd
        # booklink title silently mark the nearest statement covered, hiding the
        # real gap. Only genuinely resolved matches (matched/weak) count.
        if match.get("status") not in ("matched", "weak"):
            continue
        start = match.get("startOffset")
        end = match.get("endOffset")
        if source is None or start is None or end is None:
            continue
        spans.setdefault(source, []).append((start, end))
    return {source: merge_intervals(ivals) for source, ivals in spans.items()}


def check_decl_target_multiplicity(lean_files: list[Path]) -> None:
    """Reject duplicate links, while allowing a declaration to serve several passages.

    The viewer determines the signature/body span independently for each entry.
    Several proof paragraphs, or statements in different chapters, can therefore
    share a declaration without making that split ambiguous. Only repeated
    selectors for the same source and target are redundant. Preserve the existing
    allowance for prose links. Raise (exit 2) on duplicate statement/proof links.
    """
    for lean_file in lean_files:
        seen: dict[tuple, int] = {}
        for marker in bk.parse_lean_markers(lean_file):
            target = marker.data.get("target")
            if marker.decl_line is None or target not in {"statement", "proof"}:
                continue
            fields = (
                ("source", "kind", "title")
                if target == "statement" and "title" in marker.data
                else ("source", "kind", "excerpt")
            )
            selector = tuple(" ".join(str(marker.data.get(field, "")).split()) for field in fields)
            key = (marker.decl_name, marker.decl_line, target, selector)
            if key in seen:
                raise ValueError(
                    f"{lean_file}: declaration '{marker.decl_name}' (line {marker.decl_line}) has "
                    f"duplicate `target: {target}` links at lines {seen[key]} and {marker.marker_line}; "
                    "keep one link for each source passage"
                )
            seen[key] = marker.marker_line


_STRUCTURAL_LINE = re.compile(
    r"^\s*(#|\\begin\{(mathmeta|center|tikzpicture|figure|table|proof|enumerate|itemize|samepage)\}"
    r"|\\end\{(mathmeta|center|tikzpicture|figure|table|proof|enumerate|itemize|samepage)\}"
    r"|\\part\*?\{|\\paragraph\*?\{|\\define\{|\\forward\{|\\index\{|\\label\{|\||!\[|:--|\\node|child\b)"
)

_HTML_COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)


def is_structural(text: str) -> bool:
    """A paragraph that carries no formalizable mathematical prose: headings,
    index/label directives, tables, tikz pictures, mathmeta blocks, bare
    proof-environment delimiters (a `\\begin{proof}` / `\\end{proof}` line on its
    own, left unhighlighted when a proof is anchored in inside-environment
    pieces), and blocks that are nothing but HTML comments (including the
    `formalization-scope` annotations parsed below — they steer coverage, they
    are not prose to cover)."""
    without_comments = _HTML_COMMENT.sub("", text)
    without_comments = re.sub(r"\\begin\{mathmeta\}.*?\\end\{mathmeta\}", "", without_comments, flags=re.DOTALL)
    without_comments = re.sub(
        r"\\(?:begingroup|endgroup|small|cleardoublepage|phantomsection|printindex)\b"
        r"|\\addcontentsline\{[^{}]*\}\{[^{}]*\}\{[^{}]*\}",
        "",
        without_comments,
    )
    lines = [ln for ln in without_comments.splitlines() if ln.strip()]
    if not lines:
        return True
    return all(_STRUCTURAL_LINE.match(ln) for ln in lines)


class ScopeResolver:
    """Resolves each book unit to in-scope or exempt, from explicit author `formalization:` annotations (single-unit skip/require and
    skip-begin/skip-end regions)."""

    def __init__(self, text: str, source: str):
        self.text = text
        scope = parse_formalization_scope(text, source)
        self.regions = [
            (region.opening.end_offset, region.closing.start_offset, region.reason) for region in scope.regions
        ]
        self.points = [
            annotation for annotation in scope.annotations if annotation.directive not in {"skip-begin", "skip-end"}
        ]

    def _governing_point(self, unit_start: int, unit_end: int) -> FormalizationAnnotation | None:
        """The annotation that governs a unit: either it immediately precedes the
        unit (only whitespace between the comment and the unit), or it sits at the
        very start of the unit (a leading comment in the same block, only
        whitespace before it). The latter is the natural authoring form
        `<!-- formalization: skip -->` on the line directly above prose."""
        best: FormalizationAnnotation | None = None
        for ann in self.points:
            precedes = ann.end_offset <= unit_start and not self.text[ann.end_offset : unit_start].strip()
            leads = (
                unit_start <= ann.start_offset
                and ann.end_offset <= unit_end
                and not self.text[unit_start : ann.start_offset].strip()
            )
            if (precedes or leads) and (best is None or ann.end_offset > best.end_offset):
                best = ann
        return best

    def classify(self, unit_start: int, unit_end: int) -> tuple[bool, str | None]:
        """Return (exempt, reason). An explicit `require` always wins."""
        point = self._governing_point(unit_start, unit_end)
        if point is not None and point.directive == "require":
            return False, None
        if point is not None and point.directive == "skip":
            return True, point.reason or "explicit skip"
        skipped = self.skipped_spans(unit_start, unit_end)
        if skipped and not any(
            is_substantive_gap(self.text[a:b]) for a, b in complement(unit_start, unit_end, skipped)
        ):
            reasons = [
                reason or "explicit skip region" for a, b, reason in self.regions if a < unit_end and unit_start < b
            ]
            return True, "; ".join(dict.fromkeys(reasons))
        return False, None

    def skipped_spans(self, start: int, end: int) -> list[tuple[int, int]]:
        point = self._governing_point(start, end)
        if point and point.directive == "require":
            return []
        if point and point.directive == "skip":
            return [(start, end)]
        return merge_intervals([(max(start, a), min(end, b)) for a, b, _ in self.regions if a < end and start < b])

    def governing_skip_point(self, unit_start: int, unit_end: int) -> FormalizationAnnotation | None:
        """The bare `skip` point governing this unit, if any. A `require` override
        yields None, since that unit is forced in scope. A bare `skip` is shorthand
        for a one-block skip region, so the no-anchor rule in
        `check_skip_blocks_unlinked` applies to the block it exempts."""
        point = self._governing_point(unit_start, unit_end)
        if point is not None and point.directive == "skip":
            return point
        return None


def paragraph_blocks(text: str) -> list[tuple[int, int, str]]:
    """Split a file into (start_offset, end_offset, text) blocks on blank-line runs."""
    blocks: list[tuple[int, int, str]] = []
    offset = 0
    buf_start: int | None = None
    buf: list[str] = []
    for line in text.splitlines(keepends=True):
        if line.strip() == "":
            if buf:
                joined = "".join(buf)
                blocks.append((buf_start, buf_start + len(joined), joined))
                buf, buf_start = [], None
        else:
            if buf_start is None:
                buf_start = offset
            buf.append(line)
        offset += len(line)
    if buf:
        joined = "".join(buf)
        blocks.append((buf_start, buf_start + len(joined), joined))
    return blocks


def snippet_of(text: str, limit: int = 90) -> str:
    flat = re.sub(r"\s+", " ", text).strip()
    return flat if len(flat) <= limit else flat[: limit - 1] + "…"


# Markup that can sit in the uncovered run between two adjacent booklink excerpts
# without being prose: LaTeX environment delimiters / item commands and Markdown
# list-item markers (`*`, `-`, `1.`, `2)`). Stripping these first lets a genuinely
# dropped word like "The" still register as a gap while a leftover `\end{proof}`
# delimiter or a bare list marker does not.
_GAP_MARKUP = re.compile(
    r"\\(?:begin|end)\{[A-Za-z*]+\}(?:\[[^\]]*\])?"  # \begin{proof}[Proof], \end{enumerate}
    r"|\\(?:termref|TermRef|index)\{[^{}]*\}"  # index-only metadata
    r"|\\item\b"  # list-item command
    r"|^[ \t]*#{1,6}[ \t]+[^\n]*(?:\n|$)"  # standalone Markdown heading
    r"|^[ \t]*(?:[*+-]|\d+[.)])[ \t]+",  # Markdown bullet / ordered-list markers
    re.MULTILINE,
)


def is_substantive_gap(seg: str) -> bool:
    """An uncovered complement run worth reporting: it carries actual prose or
    math content, not just whitespace, list markers, or environment delimiters
    left between adjacent booklink excerpts. After stripping such markup, a run
    counts as content as soon as it has one alphanumeric character, so a dropped
    word like "The" is a gap while a bare "*"/"2." marker, a leftover
    `\\end{proof}`, or punctuation between two anchors is not."""
    seg = _HTML_COMMENT.sub("", seg)
    seg = re.sub(r"\\begin\{mathmeta\}.*?\\end\{mathmeta\}", "", seg, flags=re.DOTALL)
    return bool(re.search(r"[^\W_]", _GAP_MARKUP.sub("", seg)))


def build_unit(
    kind: str,
    label: str | None,
    start: int,
    end: int,
    text: str,
    offsets: list[int],
    covered: list[tuple[int, int]],
    resolver: "ScopeResolver",
) -> Unit:
    body = text[start:end]
    total = end - start
    covered_chars = overlap_length(start, end, covered)
    effective = merge_intervals([*covered, *resolver.skipped_spans(start, end)])
    real_gaps = [(a, b) for a, b in complement(start, end, effective) if is_substantive_gap(text[a:b])]
    exempt, exempt_reason = resolver.classify(start, end)
    if covered_chars > 0 and not real_gaps:
        # All in-scope content is anchored; explicit skip regions are checked separately.
        status = "covered"
        exempt_reason = None
    elif exempt:
        status = "exempt"
    elif covered_chars == 0:
        status = "uncovered"
    else:
        status = "partial"
    gaps: list[Gap] = []
    if status == "partial":
        for a, b in real_gaps:
            seg = text[a:b]
            gaps.append(
                Gap(
                    start_line=bk.offset_to_line(offsets, a),
                    end_line=bk.offset_to_line(offsets, max(a, b - 1)),
                    text=snippet_of(seg),
                )
            )
    return Unit(
        kind=kind,
        label=label,
        start_line=bk.offset_to_line(offsets, start),
        end_line=bk.offset_to_line(offsets, max(start, end - 1)),
        start_offset=start,
        end_offset=end,
        total_chars=total,
        covered_chars=covered_chars,
        status=status,
        structural=(
            is_structural(body)
            or bool((point := resolver._governing_point(start, end)) and point.directive == "structural")
        )
        if kind == "prose"
        else False,
        snippet=snippet_of(body),
        exempt_reason=exempt_reason if status == "exempt" else None,
        gaps=gaps,
    )


def check_skip_regions_unlinked(
    resolver: "ScopeResolver", covered: list[tuple[int, int]], offsets: list[int], source: str
) -> None:
    """A `skip-begin`/`skip-end` region marks prose deliberately out of
    formalization scope, so it must not contain a booklinked span. A region that
    overlaps a Lean anchor is a contradiction — the prose is declared both
    skipped and formalized — and the silent "anchor wins" reconciliation in
    `build_unit` would otherwise hide it. Raise rather than paper over it; the
    fix is to narrow the skip region or drop the booklink.

    A bare single-block `skip` obeys the same rule via
    `check_skip_blocks_unlinked`; it is shorthand for a one-block region, not a
    softer exemption."""
    for start, end, _ in resolver.regions:
        for c0, c1 in covered:
            lo, hi = max(start, c0), min(end, c1)
            if hi > lo:
                raise ValueError(
                    f"{source}: 'formalization: skip-begin'…'skip-end' region "
                    f"(L{bk.offset_to_line(offsets, start)}-L{bk.offset_to_line(offsets, end)}) "
                    f"contains a booklinked span "
                    f"(L{bk.offset_to_line(offsets, lo)}-L{bk.offset_to_line(offsets, max(lo, hi - 1))}); "
                    f"a skip region must not be formalized. "
                    f"Narrow the skip region or remove the booklink."
                )


def check_skip_blocks_unlinked(
    resolver: "ScopeResolver", units: list[Unit], covered: list[tuple[int, int]], offsets: list[int], source: str
) -> None:
    """A bare single-block `formalization: skip` is shorthand for a one-block
    `skip-begin`/`skip-end` region, so it obeys the same rule: the block it
    exempts must not contain a booklinked span. Declaring prose skipped while a
    Lean anchor lands in it is a contradiction, and the silent "anchor wins"
    reconciliation in `build_unit` would otherwise hide it. Raise (exit 2) rather
    than paper over it; the fix is to narrow the skip — split the block so the
    anchored sentence sits outside it — or drop the booklink."""
    for u in units:
        point = resolver.governing_skip_point(u.start_offset, u.end_offset)
        if point is None:
            continue
        for c0, c1 in covered:
            lo, hi = max(u.start_offset, c0), min(u.end_offset, c1)
            if hi > lo:
                raise ValueError(
                    f"{source}: 'formalization: skip' block "
                    f"(L{bk.offset_to_line(offsets, u.start_offset)}-L{bk.offset_to_line(offsets, u.end_offset)}) "
                    f"contains a booklinked span "
                    f"(L{bk.offset_to_line(offsets, lo)}-L{bk.offset_to_line(offsets, max(lo, hi - 1))}); "
                    f"a skip block must not be formalized. "
                    f"Narrow the skip (split the block so the anchored text is outside it) "
                    f"or remove the booklink."
                )


def check_shading_skips_unlinked(
    path: Path, covered: list[tuple[int, int]], offsets: list[int], *, document: bk.SourceDocument | None = None
) -> None:
    """Enforce that no *shading* skip-span covers a booklink anchor.

    The checks above model a skip's extent with blank-line paragraph blocks. The
    PDF gray shading uses a different model (`booklink_sourcemap.parse_skip_spans`
    → `block_after_marker`): a bare skip placed immediately before `\\begin{env}`
    extends to the matching `\\end{env}` so the injected `\\SkipStart`/`\\SkipEnd`
    never straddle the environment. That env rule can balloon far past the author's
    intent — e.g. a skip before `\\begin{proof}` grays the whole proof, including
    anchored steps the paragraph-block check considers in scope.

    Checking the shading spans directly keeps the gate and the rendered shading in
    lockstep: whatever the PDF would gray must not be formalized. The fix for a
    ballooned span is to move the skip *inside* the environment (so it governs only
    the intended block); otherwise narrow the skip or drop the booklink."""
    skip_spans = document.skips if document is not None else bk.parse_skip_spans(path, offsets=offsets)
    for span in skip_spans:
        a, b = span["startOffset"], span["endOffset"]
        for c0, c1 in covered:
            lo, hi = max(a, c0), min(b, c1)
            if hi > lo:
                raise ValueError(
                    f"{path}: 'formalization: skip' shading span "
                    f"(L{bk.offset_to_line(offsets, a)}-L{bk.offset_to_line(offsets, b - 1)}) "
                    f"covers a booklinked span "
                    f"(L{bk.offset_to_line(offsets, lo)}-L{bk.offset_to_line(offsets, max(lo, hi - 1))}); "
                    f"the PDF would shade formalized prose. Move the skip inside the "
                    f"environment, narrow it, or remove the booklink."
                )


def units_for_source(
    path: Path, covered: list[tuple[int, int]], *, document: bk.SourceDocument | None = None
) -> list[Unit]:
    if document is None:
        document = bk.SourceDocument(path, path.read_text(encoding="utf-8"))
    text = document.text
    offsets = document.offsets
    resolver = ScopeResolver(text, str(path))
    check_skip_regions_unlinked(resolver, covered, offsets, str(path))
    statements = document.statements
    stmt_ranges = [(s.start_offset, s.end_offset) for s in statements]

    units: list[Unit] = []
    for stmt in statements:
        label = f"{stmt.kind}: {stmt.title}" if stmt.title else stmt.kind
        units.append(
            build_unit(
                "statement",
                label,
                stmt.start_offset,
                stmt.end_offset,
                text,
                offsets,
                covered,
                resolver,
            )
        )
    statement_intervals = merge_intervals(stmt_ranges)
    for start, end, _body in paragraph_blocks(text):
        # A block may contain prose before/after a statement without blank lines.
        # Subtract the statement, rather than double-counting it or losing the tail.
        for part_start, part_end in complement(start, end, statement_intervals):
            if text[part_start:part_end].strip():
                units.append(build_unit("prose", None, part_start, part_end, text, offsets, covered, resolver))

    units.sort(key=lambda u: u.start_offset)
    check_skip_blocks_unlinked(resolver, units, covered, offsets, str(path))
    check_shading_skips_unlinked(path, covered, offsets, document=document)
    return units


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("lean_file", type=Path, nargs="+")
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--source", type=str, help="restrict to one book-local source path")
    parser.add_argument("--statements-only", action="store_true")
    parser.add_argument("--all", action="store_true", help="include structural units")
    parser.add_argument("--show-exempt", action="store_true", help="list exempt units and their reasons")
    parser.add_argument(
        "--strict",
        action="store_true",
        help="exit 1 if any non-exempt unit is uncovered or partial (firm md<->Lean correspondence gate)",
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv[1:])

    root = args.root.resolve()
    lean_files = [lf if lf.is_absolute() else (root / lf) for lf in args.lean_file]

    try:
        check_decl_target_multiplicity(lean_files)
        covered_by_source = covered_spans_by_source(root, lean_files)
    except ValueError as exc:
        print(f"booklink_coverage.py: {exc}", file=sys.stderr)
        return 2

    report: list[dict[str, Any]] = []
    for source in sorted(covered_by_source):
        if args.source and not source.endswith(args.source):
            continue
        path = Path(source) if Path(source).is_absolute() else (root / source)
        if not path.exists():
            continue
        try:
            units = units_for_source(path, covered_by_source[source])
        except ValueError as exc:
            print(f"booklink_coverage.py: {exc}", file=sys.stderr)
            return 2
        if args.statements_only:
            units = [u for u in units if u.kind == "statement"]
        if not args.all:
            units = [u for u in units if not u.structural]

        def stat(kind: str, status: str, units=units) -> int:
            return sum(1 for u in units if u.kind == kind and u.status == status)

        # "flagged" is the real-gap list: uncovered/partial, never exempt.
        flagged = [u for u in units if u.status in {"uncovered", "partial"}]
        exempt = [u for u in units if u.status == "exempt"]
        report.append(
            {
                "source": source,
                "statements": {
                    "covered": stat("statement", "covered"),
                    "partial": stat("statement", "partial"),
                    "uncovered": stat("statement", "uncovered"),
                    "exempt": stat("statement", "exempt"),
                },
                "prose": {
                    "covered": stat("prose", "covered"),
                    "partial": stat("prose", "partial"),
                    "uncovered": stat("prose", "uncovered"),
                    "exempt": stat("prose", "exempt"),
                },
                "flagged": [asdict(u) for u in flagged],
                "exempt": [asdict(u) for u in exempt],
            }
        )

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
        if args.strict and any(item["flagged"] for item in report):
            return 1
        return 0

    total_flagged = 0
    for item in report:
        s, p = item["statements"], item["prose"]
        total_flagged += len(item["flagged"])
        print(f"\n=== {item['source']} ===")
        print(
            f"  statements: {s['covered']} covered, {s['partial']} partial, "
            f"{s['uncovered']} uncovered, {s['exempt']} exempt"
            f"   |   prose: {p['covered']} covered, {p['partial']} partial, "
            f"{p['uncovered']} uncovered, {p['exempt']} exempt"
        )
        for u in item["flagged"]:
            tag = u["label"] if u["kind"] == "statement" else "prose"
            mark = "UNCOVERED" if u["status"] == "uncovered" else "partial"
            print(f"  L{u['start_line']:>4}-{u['end_line']:<4} [{mark}] [{tag}]  {u['snippet']}")
            for g in u["gaps"]:
                print(f"        ↳ gap L{g['start_line']}-{g['end_line']}: {g['text']}")
        if args.show_exempt:
            for u in item["exempt"]:
                tag = u["label"] if u["kind"] == "statement" else "prose"
                print(f"  L{u['start_line']:>4}-{u['end_line']:<4} [exempt] [{tag}]  {u['snippet']}")
                print(f"        ↳ reason: {u['exempt_reason']}")

    if args.strict and total_flagged:
        print(
            f"\nbooklink_coverage.py: {total_flagged} non-exempt unit(s) lack Lean correspondence "
            f"(use a `formalization: skip` annotation to exempt, or add a booklink).",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
