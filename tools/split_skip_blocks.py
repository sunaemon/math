#!/usr/bin/env python3
"""Auto-narrow bare `formalization: skip` blocks that contain a booklink anchor.

Since `booklink_coverage.py` now treats a bare single-block `skip` as a one-block
skip region (it must not contain a booklinked span), any skip block that overlaps
a Lean anchor errors the gate. This tool rewrites those blocks so the anchored
text leaves the skip, while keeping the genuinely out-of-scope commentary skipped.

Per flagged block it computes the *covered hull* — the span from the first to the
last booklinked character — and keeps that hull in scope (covered prose plus any
display math interleaved with it). The substantial uncovered runs *before* and
*after* the hull are re-wrapped in their own bare `skip`, but only when the cut is
rendering-safe: the preceding line ends a sentence or a display-math/environment
block, and the following line starts a new sentence or structural element. A block
that is one flowing paragraph with no safe internal cut falls back to a plain
un-skip (the whole block goes in scope; its uncovered commentary becomes an
ordinary reported gap, never a build error).

Dry-run by default: prints a unified diff and a per-block plan. Pass --apply to
write the changes.

    tools/split_skip_blocks.py <lean files...> [--source chap.md] [--apply]
"""

import argparse
import difflib
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import booklink_coverage as cov  # noqa: E402
import booklink_sourcemap as bk  # noqa: E402

# A line whose stripped text ends a sentence or a display-math / environment block,
# so a paragraph break may follow it.
_ENDS_UNIT = re.compile(r"(?:[.:!?]|\$\$|\\\\|\\end\{[^}]*\}|\})\s*$")
# A line that cleanly starts a new sentence or structural element. A bare `\end`
# is excluded: starting a paragraph on it would orphan an environment closer.
_STARTS_UNIT = re.compile(r"^(?:[A-Z]|\$\$|\\item\b|\\begin\b|#|\*|\d+\.)")


def line_bounds(text: str, start: int, end: int) -> list[tuple[int, int]]:
    """Absolute [line_start, line_end) bounds for every line in text[start:end]."""
    bounds = []
    i = start
    while i < end:
        nl = text.find("\n", i, end)
        stop = end if nl == -1 else nl + 1
        bounds.append((i, stop))
        i = stop
    return bounds


def safe_cut(text: str, cut: int, body_start: int) -> bool:
    """May we insert a paragraph break at offset `cut` (a line boundary)? Never
    inside a `$$ … $$` display-math block — an odd number of `$$` between the block
    body start and the cut means the cut would sever opening from closing."""
    if text[body_start:cut].count("$$") % 2 == 1:
        return False
    prev_nl = text.rfind("\n", 0, cut - 1) + 1 if cut > 0 else 0
    prev = text[prev_nl:cut]
    nl = text.find("\n", cut)
    nxt = text[cut : (nl if nl != -1 else len(text))]
    if not prev.strip() or not nxt.strip():
        return True  # already a blank-line boundary
    return bool(_ENDS_UNIT.search(prev.strip())) and bool(_STARTS_UNIT.match(nxt.strip()))


def flagged_blocks(text: str, covered, resolver):
    """Yield (block_start, block_end, point, covered_in_block) for skip blocks that
    overlap a covered span, in source order. Every flagged unit is a bare-skip-led
    paragraph block; statement environments are exempted differently and never
    carry a bare skip in practice, so blank-line blocks suffice here."""
    for a, b, _ in cov.paragraph_blocks(text):
        pt = resolver.governing_skip_point(a, b)
        if pt is None:
            continue
        hits = [(max(a, c0), min(b, c1)) for c0, c1 in covered if min(b, c1) > max(a, c0)]
        if hits:
            yield a, b, pt, sorted(hits)


def reason_of(pt) -> str:
    return pt.reason or "out of formalization scope"


def plan_block(text, a, b, pt, hits):
    """Return (new_block_text, note). The block runs [a, b); pt is its skip comment."""
    comment = text[pt.start_offset : pt.end_offset]
    body_start = pt.end_offset
    while body_start < b and text[body_start] == "\n":
        body_start += 1
    hull_start = min(h[0] for h in hits)
    hull_end = max(h[1] for h in hits)

    lines = line_bounds(text, body_start, b)
    interior = [ls for ls, le in lines if ls > body_start]
    hull_first_ls = next((ls for ls, le in lines if ls <= hull_start < le), body_start)
    hull_last_le = next((le for ls, le in lines if ls <= hull_end - 1 < le), b)

    # Skip the leading uncovered run up to the LATEST rendering-safe paragraph break
    # at or before the hull's first line, and the trailing run from the EARLIEST
    # safe break at or after the hull's last line. Snapping outward past the hull
    # absorbs interleaved math/prose into the in-scope region rather than orphaning a
    # covered span or splitting a sentence (e.g. "…neighborhood is $$…$$" stays whole).
    lead_cut = None
    for cut in interior:
        if cut <= hull_first_ls and safe_cut(text, cut, body_start):
            lead_cut = cut
    trail_cut = None
    for cut in interior:
        if cut >= hull_last_le and safe_cut(text, cut, body_start):
            trail_cut = cut
            break

    keep_lead = lead_cut is not None and len(text[body_start:lead_cut].strip()) >= 40
    keep_trail = trail_cut is not None and len(text[trail_cut:b].strip()) >= 40

    in_lo = lead_cut if keep_lead else body_start
    in_hi = trail_cut if keep_trail else b
    in_scope = text[in_lo:in_hi].strip("\n")

    parts = []
    if keep_lead:
        parts.append(comment + "\n" + text[body_start:lead_cut].strip("\n"))
    parts.append(in_scope)
    if keep_trail:
        parts.append(comment + "\n" + text[trail_cut:b].strip("\n"))

    # Preserve the block's own trailing newline so the blank line separating it
    # from the following block survives the splice.
    if not (keep_lead or keep_trail):
        # No rendering-safe line-boundary cut isolates the anchor (the covered span
        # starts mid-line or the block is one flowing paragraph). Auto-un-skipping
        # would resurface cited commentary as gaps, so leave it for a hand-edit.
        return None, "MANUAL: no safe automatic cut — hand-edit (mid-line split or narrower re-skip)"

    new_block = "\n\n".join(parts) + "\n"
    note = "split: " + "+".join(
        (["lead-skip"] if keep_lead else []) + ["in-scope"] + (["trail-skip"] if keep_trail else [])
    )
    return new_block, note


def process_source(path: Path, covered) -> tuple[str, list[str]]:
    text = path.read_text(encoding="utf-8")
    resolver = cov.ScopeResolver(text, str(path))
    edits = []  # (a, b, new_text, note)
    for a, b, pt, hits in flagged_blocks(text, covered, resolver):
        new_block, note = plan_block(text, a, b, pt, hits)
        edits.append((a, b, new_block, note))
    edits.sort(reverse=True)
    offsets = bk.line_offsets(text)
    new_text = text
    notes = []
    for a, b, new_block, note in edits:
        ln = bk.offset_to_line(offsets, a)
        notes.append(f"L{ln}: {note}")
        if new_block is not None:
            new_text = new_text[:a] + new_block + new_text[b:]
    return new_text, list(reversed(notes))


def main(argv) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("lean_file", type=Path, nargs="+")
    ap.add_argument("--root", type=Path, default=Path.cwd())
    ap.add_argument("--source", type=str, help="restrict to one book-local source path")
    ap.add_argument("--apply", action="store_true", help="write changes (default: dry-run diff)")
    args = ap.parse_args(argv[1:])

    root = args.root.resolve()
    leans = [lf if lf.is_absolute() else root / lf for lf in args.lean_file]
    covered_by_source = cov.covered_spans_by_source(root, leans)

    seen = set()
    any_change = False
    for source in sorted(covered_by_source):
        if args.source and not source.endswith(args.source):
            continue
        path = Path(source) if Path(source).is_absolute() else root / source
        if not path.exists():
            continue
        real = str(path.resolve())
        if real in seen:
            continue
        seen.add(real)
        new_text, notes = process_source(path, covered_by_source[source])
        if not notes:
            continue
        any_change = True
        print(f"\n=== {path} ===")
        for n in notes:
            print(f"  {n}")
        if args.apply:
            path.write_text(new_text, encoding="utf-8")
            print("  [written]")
        else:
            old = path.read_text(encoding="utf-8")
            diff = difflib.unified_diff(
                old.splitlines(keepends=True),
                new_text.splitlines(keepends=True),
                fromfile=str(path),
                tofile=str(path) + " (proposed)",
            )
            sys.stdout.writelines(diff)
    if not any_change:
        print("No flagged skip blocks found.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
