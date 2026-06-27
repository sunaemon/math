// Unit tests for the pure PDF skip-band geometry. Run with `node --test`.
//
// The fixtures mirror real measurements from the debug PDF: the skip
// hypertargets land on text baselines, and hyperref raises the *start* anchor
// ~a baselineskip so it falls a line above the region's first line. The wash
// must still cover whole line boxes, cap-to-descender — these tests pin that.

import { test } from "node:test";
import assert from "node:assert/strict";
import {
  groupTextLines,
  SNAP_TOL,
  snapBandTop,
  snapBandBottom,
  skipBandSegments,
  lineIndexBelow,
  lineIndexAt,
  mainLineBelow,
  endLineResolve,
  endLineBottom,
  flowBandSegments,
  type LineBox,
} from "./skip-bands.ts";

// Map a PDF y (origin bottom-left) to a top-down fraction of an 800-pt page,
// like pdf.js convertToViewportPoint / viewport.height does.
const PAGE = 800;
const toFrac = (y: number) => (PAGE - y) / PAGE;
const approx = (a: number, b: number, eps = 1e-9) => Math.abs(a - b) <= eps;

test("groupTextLines: merges runs on one baseline and sorts top→bottom", () => {
  // Two runs share baseline 700 (a tall one and a short one); one run at 680.
  const lines = groupTextLines(
    [
      { baseline: 700, height: 10 },
      { baseline: 700, height: 20 }, // taller run widens the line box
      { baseline: 680, height: 10 },
    ],
    toFrac,
  );
  assert.equal(lines.length, 2);
  // Sorted by baseline as a top-down fraction: baseline 700 (higher) first.
  assert.ok(approx(lines[0].baseline, toFrac(700)));
  assert.ok(approx(lines[1].baseline, toFrac(680)));
  // The merged line box uses the taller run: top = 700 + 0.8*20, bottom = 700 - 0.2*20.
  assert.ok(approx(lines[0].top, toFrac(700 + 0.8 * 20)));
  assert.ok(approx(lines[0].bottom, toFrac(700 - 0.2 * 20)));
  // Top is above the baseline is above the bottom (fractions increase downward).
  assert.ok(lines[0].top < lines[0].baseline && lines[0].baseline < lines[0].bottom);
});

test("groupTextLines: skips blankless runs of zero height without NaN", () => {
  const lines = groupTextLines([{ baseline: 500, height: 0 }], toFrac);
  assert.equal(lines.length, 1);
  assert.ok(approx(lines[0].top, toFrac(500)));
  assert.ok(approx(lines[0].bottom, toFrac(500)));
});

// A realistic page slice: a section heading, a three-line skipped paragraph,
// then the next paragraph. Baselines ~18pt apart (one line); height ~10pt.
function paragraphLines(): { lines: LineBox[]; firstTop: number; lastBottom: number } {
  const h = 10;
  const baselines = { heading: 540, l1: 520, l2: 502, l3: 484, next: 464 };
  const lines = groupTextLines(
    Object.values(baselines).map((baseline) => ({ baseline, height: h })),
    toFrac,
  );
  return {
    lines,
    firstTop: toFrac(baselines.l1 + 0.8 * h), // top of the first content line
    lastBottom: toFrac(baselines.l3 - 0.2 * h), // bottom of the last content line
  };
}

test("snapBandTop: skips the raised start anchor's line, takes the next line's top", () => {
  const { lines, firstTop } = paragraphLines();
  // The start hypertarget is raised ~a line, landing just under the heading
  // baseline (540) — a line above the first content line l1 (baseline 520).
  const rawStart = toFrac(538);
  const top = snapBandTop(rawStart, lines);
  assert.ok(approx(top, firstTop), `expected first content line top ${firstTop}, got ${top}`);
  // It must NOT just return the raw anchor (that was the upward-shift bug).
  assert.notEqual(top, rawStart);
});

test("snapBandBottom: takes the bottom of the line at the end anchor (descenders)", () => {
  const { lines, lastBottom } = paragraphLines();
  // The end hypertarget sits on the last content line's baseline (484).
  const rawEnd = toFrac(484);
  const bottom = snapBandBottom(rawEnd, lines);
  assert.ok(approx(bottom, lastBottom), `expected last content line bottom ${lastBottom}, got ${bottom}`);
  // Reaches below the baseline so descenders are covered.
  assert.ok(bottom > toFrac(484));
});

test("snap: a one-line skip covers exactly that line, cap-to-descender", () => {
  const { lines } = paragraphLines();
  // Start raised above l1, end on l1's baseline → band is just l1's box.
  const top = snapBandTop(toFrac(528), lines);
  const bottom = snapBandBottom(toFrac(520), lines);
  const h = 10;
  assert.ok(approx(top, toFrac(520 + 0.8 * h)));
  assert.ok(approx(bottom, toFrac(520 - 0.2 * h)));
  assert.ok(top < bottom);
});

test("snap: falls back to the raw fraction when the page has no text lines", () => {
  assert.equal(snapBandTop(0.42, []), 0.42);
  assert.equal(snapBandBottom(0.42, []), 0.42);
});

test("skipBandSegments: single page yields one [top, bottom] segment", () => {
  const segs = skipBandSegments({ pageNumber: 5, frac: 0.3 }, { pageNumber: 5, frac: 0.6 });
  assert.deepEqual(segs, [{ pageNumber: 5, top: 0.3, bottom: 0.6 }]);
});

test("skipBandSegments: degenerate (end at/above start) yields nothing", () => {
  assert.deepEqual(skipBandSegments({ pageNumber: 5, frac: 0.6 }, { pageNumber: 5, frac: 0.6 }), []);
  assert.deepEqual(skipBandSegments({ pageNumber: 5, frac: 0.6 }, { pageNumber: 5, frac: 0.3 }), []);
  assert.deepEqual(skipBandSegments({ pageNumber: 6, frac: 0.1 }, { pageNumber: 5, frac: 0.9 }), []);
});

test("skipBandSegments: cross-page splits into start, full middles, end", () => {
  const segs = skipBandSegments({ pageNumber: 4, frac: 0.7 }, { pageNumber: 7, frac: 0.2 });
  assert.deepEqual(segs, [
    { pageNumber: 4, top: 0.7, bottom: null }, // start page: from anchor to page bottom
    { pageNumber: 5, top: 0, bottom: null }, // full intermediate page
    { pageNumber: 6, top: 0, bottom: null }, // full intermediate page
    { pageNumber: 7, top: 0, bottom: 0.2 }, // end page: from top to anchor
  ]);
});

test("skipBandSegments: adjacent pages have no intermediate full page", () => {
  const segs = skipBandSegments({ pageNumber: 4, frac: 0.8 }, { pageNumber: 5, frac: 0.1 });
  assert.deepEqual(segs, [
    { pageNumber: 4, top: 0.8, bottom: null },
    { pageNumber: 5, top: 0, bottom: 0.1 },
  ]);
});

// --- Booklink text-flow highlighting (mid-line start/end) ---

const FLOW_LINES: LineBox[] = [
  { top: 0.1, bottom: 0.16, baseline: 0.15, left: 0.1 },
  { top: 0.2, bottom: 0.26, baseline: 0.25, left: 0.1 },
  { top: 0.3, bottom: 0.36, baseline: 0.35, left: 0.1 },
];

test("lineIndexBelow: picks the first line below a raised start anchor", () => {
  // Anchor raised a line above its content (frac 0.05 < line0 baseline 0.15).
  assert.equal(lineIndexBelow(0.05, FLOW_LINES), 0);
  // Anchor sitting just above line 2's baseline lands on line 2.
  assert.equal(lineIndexBelow(0.25, FLOW_LINES), 2);
  // Nothing below → -1.
  assert.equal(lineIndexBelow(0.99, FLOW_LINES), -1);
});

test("lineIndexAt: picks the line at/just above an end anchor", () => {
  assert.equal(lineIndexAt(0.15, FLOW_LINES), 0);
  assert.equal(lineIndexAt(0.35, FLOW_LINES), 2);
  // Above the first baseline → -1.
  assert.equal(lineIndexAt(0.0, FLOW_LINES), -1);
});

// The start line is just lineIndexAt: \BooklinkStart records the exact baseline of
// the span's first glyph (macros.tex forces horizontal mode so a paragraph/list
// start is not raised). These exercise lineIndexAt as the start resolver.
test("start: lineIndexAt picks the line the exact anchor sits on (mid-line)", () => {
  // Anchor on line 1's baseline (0.25); the start line is line 1, start x is the
  // anchor's own x — no disambiguation needed.
  assert.equal(lineIndexAt(0.25, FLOW_LINES), 1);
});

test("start: lineIndexAt picks the paragraph's own first line (un-raised)", () => {
  // A paragraph start records the first line's baseline exactly (0.15 = line 0), so
  // lineIndexAt returns line 0 — not the previous line, as a raised anchor would.
  assert.equal(lineIndexAt(0.15, FLOW_LINES), 0);
});

// endLineResolve: reading-order end against the exact end marker.
const END_LINES: LineBox[] = [
  { top: 0.59, bottom: 0.61, baseline: 0.6, left: 0.32 }, // 0 centered display formula (last content line)
  { top: 0.79, bottom: 0.81, baseline: 0.8, left: 0.03 }, // 1 a left-aligned text line
];

test("endLineResolve: a mid-line end covers up to the marker x on its own line", () => {
  // Marker on line 1's baseline (0.8) past its text start (x 0.5 > left 0.03):
  // the cut is on line 1 at x 0.5.
  assert.deepEqual(endLineResolve(0.8, 0.5, END_LINES), { index: 1, right: 0.5 });
});

test("endLineResolve: a marker at a line's left edge falls back to the line above", () => {
  // Marker on line 1's baseline (0.8) but at the left margin (x 0.02 < left 0.03):
  // no glyph on line 1 precedes it (it overshot onto the next paragraph), so the
  // end is the formula line above, covered full width. This is the formula→
  // paragraph case (entry 47) — the band stops before line 1, no overlap.
  assert.deepEqual(endLineResolve(0.8, 0.02, END_LINES), { index: 0, right: 1 });
});

test("endLineResolve: a marker in the gap below a display line covers that line full width", () => {
  // Marker below the formula line (0.7 > 0.6 + tol) at the left margin: the whole
  // formula precedes the marker in reading order, so it is covered full width. This
  // is the display-equation-then-blank-line case (entry 36).
  assert.deepEqual(endLineResolve(0.7, 0.04, END_LINES), { index: 0, right: 1 });
});

test("flowBandSegments: single line uses [startX, endX]", () => {
  const segs = flowBandSegments(
    {
      startPage: 3,
      startTop: 0.2,
      startBottom: 0.26,
      nextTop: null,
      endPage: 3,
      endTop: 0.2,
      endBottom: 0.26,
      startX: 0.3,
      endX: 0.7,
    },
    true,
  );
  assert.deepEqual(segs, [{ pageNumber: 3, top: 0.2, bottom: 0.26, left: 0.3, right: 0.7 }]);
});

test("flowBandSegments: multi-line indents first line, full middle, trims last", () => {
  // Start on line 0 (top 0.10), end on line 2 (top 0.30, bottom 0.36), all one page.
  const segs = flowBandSegments(
    {
      startPage: 3,
      startTop: 0.1,
      startBottom: 0.16,
      nextTop: 0.2, // line 1 top
      endPage: 3,
      endTop: 0.3,
      endBottom: 0.36,
      startX: 0.4,
      endX: 0.6,
    },
    false,
  );
  assert.deepEqual(segs, [
    { pageNumber: 3, top: 0.1, bottom: 0.2, left: 0.4, right: 1 }, // first line from startX to edge
    { pageNumber: 3, top: 0.2, bottom: 0.3, left: 0, right: 1 }, // full-width middle line(s)
    { pageNumber: 3, top: 0.3, bottom: 0.36, left: 0, right: 0.6 }, // last line to endX
  ]);
});

test("flowBandSegments: two adjacent lines have no middle block", () => {
  const segs = flowBandSegments(
    {
      startPage: 3,
      startTop: 0.1,
      startBottom: 0.16,
      nextTop: 0.2,
      endPage: 3,
      endTop: 0.2,
      endBottom: 0.26,
      startX: 0.4,
      endX: 0.6,
    },
    false,
  );
  assert.deepEqual(segs, [
    { pageNumber: 3, top: 0.1, bottom: 0.2, left: 0.4, right: 1 },
    { pageNumber: 3, top: 0.2, bottom: 0.26, left: 0, right: 0.6 },
  ]);
});

test("flowBandSegments: start line last on page flows onto the next page", () => {
  // Start line is the last on page 3 (nextTop null); end on line at page 4.
  const segs = flowBandSegments(
    {
      startPage: 3,
      startTop: 0.9,
      startBottom: 0.96,
      nextTop: null,
      endPage: 4,
      endTop: 0.1,
      endBottom: 0.16,
      startX: 0.4,
      endX: 0.6,
    },
    false,
  );
  assert.deepEqual(segs, [
    { pageNumber: 3, top: 0.9, bottom: 0.96, left: 0.4, right: 1 }, // first line only
    { pageNumber: 4, top: 0, bottom: 0.1, left: 0, right: 1 }, // next page top down to last line
    { pageNumber: 4, top: 0.1, bottom: 0.16, left: 0, right: 0.6 }, // last line to endX
  ]);
});

// --- Regressions for the booklink-overlay bugs reported on borel-structure ---
//
// Each drives the production path end-to-end (lineIndexAt start / endLineResolve →
// flowBandSegments) on line boxes modeled on the real debug-PDF page geometry, with
// the anchors at their *exact* (un-raised) positions, so a future change that
// reintroduces a bug fails here.

// Helper: resolve a span the way pdf.ts does, from exact start/end markers,
// including the cap that keeps the last line's box from dipping into the line
// below it (a display equation's subscripts vs the next paragraph).
function resolveBand(lines: LineBox[], start: { frac: number; x: number }, end: { frac: number; x: number }) {
  // A \BooklinkStart before a \begin{env} (statement spans, proofs whose excerpt
  // opens with \begin{proof}) is raised by \leavevmode into the inter-paragraph
  // gap, landing above its first rendered line; lineIndexAt then picks the line
  // above it. Detect that (the picked line's baseline is well above the anchor) and
  // snap DOWN to the first line below, covering from its left edge. An exact inline
  // start sits on its glyph's baseline and keeps lineIndexAt + the anchor's own x.
  let si = lineIndexAt(start.frac, lines);
  const raised = si >= 0 && lines[si].baseline < start.frac - SNAP_TOL;
  // After snapping down, advance past a superscript sub-run of the heading line so
  // the band starts on the heading, not its raised superscript (see mainLineBelow).
  if (raised) si = mainLineBelow(lineIndexBelow(start.frac, lines), lines);
  const er = endLineResolve(end.frac, end.x, lines);
  const sLine = lines[si];
  const startX = raised ? sLine.left : start.x;
  const eLine = lines[er.index];
  const nextStart = si + 1 < lines.length ? Math.max(lines[si + 1].top, sLine.bottom) : null;
  const endBottom = endLineBottom(lines, er.index);
  return flowBandSegments(
    {
      startPage: 1,
      startTop: sLine.top,
      startBottom: sLine.bottom,
      nextTop: nextStart,
      endPage: 1,
      endTop: eLine.top,
      endBottom,
      startX,
      endX: er.right,
    },
    si === er.index,
  );
}

// Two adjacent prose booklinks: the previous entry ends mid-line ("P∈Γ.") and the
// next entry begins the following paragraph ("At the first…"). With exact anchors
// the start sits on its own first line, so it never reaches up into the preceding
// entry's last line. Modeled on entries 41 and 42.
const ADJACENT_LINES: LineBox[] = [
  { top: 0.232, bottom: 0.25, baseline: 0.244, left: 0.04 }, // 0 "P∈Γ." — prev entry (41) last line
  { top: 0.256, bottom: 0.274, baseline: 0.268, left: 0.03 }, // 1 "At the first…" — next entry (42) first line
  { top: 0.43, bottom: 0.448, baseline: 0.442, left: 0.18 }, // 2 a centered display sub-line — entry 42 end
];

test("regression: a paragraph-start booklink does not overlap the preceding entry's last line", () => {
  // Entry 41 ends mid-line on line 0 (marker x 0.11 past its left 0.04).
  const a = resolveBand(ADJACENT_LINES, { frac: 0.244, x: 0.04 }, { frac: 0.244, x: 0.11 });
  // Entry 42 starts exactly on line 1's baseline and ends at the display sub-line.
  const b = resolveBand(ADJACENT_LINES, { frac: 0.268, x: 0.03 }, { frac: 0.46, x: 0.04 });
  const aBottom = Math.max(...a.map((s) => s.bottom ?? 1));
  const bTop = Math.min(...b.map((s) => s.top));
  assert.ok(aBottom <= bTop, "entry 41's band must not reach into entry 42's first line");
});

// A statement booklink on a theorem-like environment (recall*/lemma*/…) whose
// \BooklinkStart sits before \begin{env}, separated by a blank line. \leavevmode
// strands a zero-glyph paragraph in the gap, so the start destination lands ~a
// baselineskip above the run-in heading line — here in the gap (frac 0.255)
// between the preceding skip/motivation block's last line (0) and the heading (1).
// lineIndexAt would resolve it onto line 0 and overlap the band above; snapping
// down must land on line 1. Modeled on the "Separability and second countability"
// recall, where the motivation skip band sits directly above. The end marker is
// exact on line 1.
const STATEMENT_AFTER_GAP_LINES: LineBox[] = [
  { top: 0.232, bottom: 0.25, baseline: 0.244, left: 0.04 }, // 0 motivation last line — the skip band above ends here
  { top: 0.27, bottom: 0.288, baseline: 0.282, left: 0.04 }, // 1 "Recall (…). For metrizable…" — statement first line
  { top: 0.294, bottom: 0.312, baseline: 0.306, left: 0.04 }, // 2 "…equivalent to second countability." — statement end
];

test("regression: a statement start raised into the gap snaps onto its heading, not the line above", () => {
  // Start destination at frac 0.255 (gap above line 1); end exact on line 2. The
  // raise is auto-detected from the geometry (the anchor sits in a gap, not on a
  // line), so no caller flag is needed.
  const segs = resolveBand(STATEMENT_AFTER_GAP_LINES, { frac: 0.255, x: 0.06 }, { frac: 0.306, x: 0.3 });
  const bandTop = Math.min(...segs.map((s) => s.top));
  // The band must begin at the heading line (1), never reach line 0's box.
  assert.ok(bandTop >= STATEMENT_AFTER_GAP_LINES[1].top - 1e-9, "statement band must start at its heading line");
  assert.ok(bandTop > STATEMENT_AFTER_GAP_LINES[0].bottom - 1e-9, "statement band must not reach the line above it");
  // The heading line is covered from its left edge, not the stray anchor x.
  const headingSeg = segs.find((s) => s.top <= STATEMENT_AFTER_GAP_LINES[1].baseline);
  assert.ok(
    headingSeg && headingSeg.left <= STATEMENT_AFTER_GAP_LINES[1].left + 1e-9,
    "heading covered from left edge",
  );
});

// A proof booklink whose excerpt opens with \begin{proof}: its \BooklinkStart is
// injected before \begin{proof}, a blank line away, so the destination is raised
// into the gap (frac 0.288) above the proof's first line (2) — and below the
// statement's last line (1), which a beige statement band already covers. With no
// snap-down the green proof band's start lands on line 1 and paints over the
// statement (the "proposition covered in green" report). It must snap onto line 2.
const PROOF_AFTER_STATEMENT_LINES: LineBox[] = [
  { top: 0.2, bottom: 0.218, baseline: 0.212, left: 0.04 }, // 0 "Proposition (Open subspaces)." — statement heading
  { top: 0.224, bottom: 0.242, baseline: 0.236, left: 0.04 }, // 1 "…are Polish." — statement last line
  { top: 0.3, bottom: 0.318, baseline: 0.312, left: 0.04 }, // 2 "Proof. Let U⊆X be open…" — proof first line
  { top: 0.324, bottom: 0.342, baseline: 0.336, left: 0.04 }, // 3 "…separability of U." — proof last line
];

test("regression: a \\begin{proof} booklink start does not paint over the statement above it", () => {
  // Statement band covers lines 0–1 (start exact on line 0). Proof start is raised
  // into the gap at frac 0.288 (below line 1's baseline 0.236, above line 2's 0.312).
  const stmt = resolveBand(PROOF_AFTER_STATEMENT_LINES, { frac: 0.212, x: 0.04 }, { frac: 0.236, x: 0.5 });
  const proof = resolveBand(PROOF_AFTER_STATEMENT_LINES, { frac: 0.288, x: 0.06 }, { frac: 0.336, x: 0.4 });
  const stmtBottom = Math.max(...stmt.map((s) => s.bottom ?? 1));
  const proofTop = Math.min(...proof.map((s) => s.top));
  // The proof band must start at the proof's first line (2), clear of the
  // statement's last line (1) — no overlap, so no green over the proposition.
  assert.ok(proofTop >= PROOF_AFTER_STATEMENT_LINES[2].top - 1e-9, "proof band must start at the proof's first line");
  assert.ok(proofTop >= stmtBottom - 1e-9, "proof band must not reach into the statement band above it");
});

// A mid-line start on a line that carries a subscript sub-line just below its
// baseline (the ₁ of Δ⁰₁). The full-width middle must not bleed up over the left of
// the start line — the text before the start ("one prefix that falls out of the
// tree.") must stay uncovered. Modeled on the real page-68 geometry of entry 54.
const SUBSCRIPT_START_LINES: LineBox[] = [
  { top: 0.85, bottom: 0.864, baseline: 0.862, left: 0.04 }, // 0 "…A Δ⁰₁ set …, so" (start mid-line at x 0.5)
  { top: 0.857, bottom: 0.869, baseline: 0.867, left: 0.5 }, // 1 the ₁ subscript sub-line (box overlaps line 0 in y)
  { top: 0.9, bottom: 0.915, baseline: 0.91, left: 0.04 }, // 2 a later content line — the span flows down to here
];

test("regression: a mid-line start with a subscript sub-line does not cover the text before it", () => {
  // Start mid-line on line 0 at x 0.5 (the text to its left, "one prefix that falls
  // out of the tree.", must stay uncovered) and the span flows down to line 2. The
  // subscript sub-line (1) overlaps line 0 in y; the full-width middle must begin at
  // line 0's bottom, not at the subscript's top, or it would bleed up over line 0's
  // left half.
  const segs = resolveBand(SUBSCRIPT_START_LINES, { frac: 0.862, x: 0.5 }, { frac: 0.91, x: 0.5 });
  // Every segment overlapping line 0's box must stay right of the mid-line start x.
  const overStart = segs.filter((s) => s.top < SUBSCRIPT_START_LINES[0].bottom - 1e-9);
  assert.ok(overStart.length > 0, "the start line must be covered");
  assert.ok(
    overStart.every((s) => s.left >= 0.5 - 1e-9),
    "no segment over the start line may extend left of the mid-line start x",
  );
});

// An excerpt ending with a centered display equation, then a blank line. pdf.js
// splits the equation into a main and a lower subscript sub-line; the end marker
// lands in the gap below them. The whole equation must be covered full width, not
// a left sliver (the reported "half split"). Modeled on entry 36.
const FORMULA_END_LINES: LineBox[] = [
  { top: 0.718, bottom: 0.735, baseline: 0.732, left: 0.038 }, // 0 "Recall from Alexandrov…" (paragraph start)
  { top: 0.738, bottom: 0.755, baseline: 0.752, left: 0.038 }, // 1 "a countable union of closed sets…"
  { top: 0.759, bottom: 0.775, baseline: 0.772, left: 0.038 }, // 2 "open sets. The two classes are dual:"
  { top: 0.795, bottom: 0.812, baseline: 0.809, left: 0.322 }, // 3 "A is Fσ ⟺ X∖A is Gδ." (centered, main)
  { top: 0.803, bottom: 0.815, baseline: 0.813, left: 0.401 }, // 4 "σδ" (formula subscripts, lower sub-baseline)
  { top: 0.862, bottom: 0.879, baseline: 0.876, left: 0.038 }, // 5 "Longer strings…" (next paragraph)
];

test("regression: a booklink ending in a display formula covers the whole formula, not a left sliver", () => {
  // Start exact on line 0; end marker in the gap below the formula (0.84) at the
  // left margin — the whole formula precedes it, so it is covered full width.
  const segs = resolveBand(FORMULA_END_LINES, { frac: 0.732, x: 0.038 }, { frac: 0.84, x: 0.038 });
  const fTop = FORMULA_END_LINES[3].top;
  const fBottom = FORMULA_END_LINES[4].bottom;
  const overFormula = segs.filter((s) => (s.bottom ?? 1) > fTop && s.top < fBottom);
  assert.ok(overFormula.length > 0, "the formula must be covered by at least one segment");
  assert.ok(
    overFormula.every((s) => s.right === 1),
    "every segment over the display formula must span full width",
  );
  assert.ok(
    Math.min(...overFormula.map((s) => s.top)) <= fTop && Math.max(...overFormula.map((s) => s.bottom ?? 1)) >= fBottom,
    "the band must reach the formula's top and bottom",
  );
});

// Two adjacent booklinks where the first ends with a display equation immediately
// followed (no blank line) by the second's paragraph. With no blank line the
// equation's last sub-line box (its superscripts/subscripts) overlaps the next
// paragraph's first line in y — line 2's box dips below line 3's top. Modeled on
// the real page-63 geometry of entries 47 ("…Π⁰ = ⋃ Π⁰") and 46 ("The class Σ⁰ …"),
// where entry 47 was shading the top half of "The class …".
const FORMULA_THEN_PARA_LINES: LineBox[] = [
  { top: 0.52, bottom: 0.535, baseline: 0.53, left: 0.03 }, // 0 "Taking complements …" (entry 47 first line)
  { top: 0.575, bottom: 0.59, baseline: 0.585, left: 0.18 }, // 1 "Π⁰ = ⋃ Π⁰" formula main (centered)
  { top: 0.596, bottom: 0.608, baseline: 0.605, left: 0.1 }, // 2 formula's lowest sub-line — entry 47 end (box dips low)
  { top: 0.599, bottom: 0.616, baseline: 0.612, left: 0.03 }, // 3 "The class Σ⁰ …" entry 46 first line (overlaps line 2 in y)
  { top: 0.66, bottom: 0.678, baseline: 0.672, left: 0.03 }, // 4 "then β := …" (entry 46 second line)
];

test("regression: adjacent entries split at a formula→paragraph boundary without overlapping", () => {
  // Entry 47 (Taking complements … Π⁰ = ⋃ Π⁰): end marker overshot onto line 3's
  // baseline (0.612) at the left margin (x 0.028 ≤ line 3 left 0.03), so reading
  // order ends it on the formula's lowest sub-line (2), full width.
  const er = endLineResolve(0.612, 0.028, FORMULA_THEN_PARA_LINES);
  assert.equal(er.index, 2, "entry 47 must end on the formula, not the next paragraph's line");
  const a = resolveBand(FORMULA_THEN_PARA_LINES, { frac: 0.53, x: 0.03 }, { frac: 0.612, x: 0.028 });

  // Entry 46 (The class Σ⁰ …): starts exactly on line 3 and ends mid-line on line 4.
  const bSi = lineIndexAt(0.612, FORMULA_THEN_PARA_LINES);
  assert.equal(bSi, 3);
  const b = resolveBand(FORMULA_THEN_PARA_LINES, { frac: 0.612, x: 0.03 }, { frac: 0.672, x: 0.5 });

  // Even though the formula's sub-line box (line 2) dips into "The class" (line 3),
  // the cap keeps entry 47 from shading line 3: its band stops at line 3's top, and
  // the two bands meet there with no overlap.
  const aBottom = Math.max(...a.map((s) => s.bottom ?? 1));
  const bTop = Math.min(...b.map((s) => s.top));
  assert.ok(aBottom <= FORMULA_THEN_PARA_LINES[3].top + 1e-9, "entry 47 must not dip into 'The class' (line 3)");
  assert.ok(aBottom <= bTop, "the two bands must not overlap");
});

// endLineBottom on its own: a subscript run of the end line (shorter, just below it)
// must be skipped, while a full-height following line is capped against.
test("endLineBottom: skips the end line's own subscript sub-run, covering the whole line", () => {
  const lines: LineBox[] = [
    { top: 0.109, bottom: 0.126, baseline: 0.122, left: 0.04 }, // 0 main text (end line)
    { top: 0.117, bottom: 0.129, baseline: 0.127, left: 0.16 }, // 1 its subscripts (shorter, lower baseline)
    { top: 0.139, bottom: 0.156, baseline: 0.153, left: 0.12 }, // 2 next paragraph (full height)
  ];
  // The shorter sub-run (1) is skipped, so the bottom is the main line's own bottom,
  // not the sub-run's top (0.117) — the bug that chopped the wash to a sliver.
  assert.ok(approx(endLineBottom(lines, 0), 0.126), "must reach the main line's bottom");
  // A full-height following line that overlaps would still cap (display→tight text).
  const overlapping: LineBox[] = [
    { top: 0.596, bottom: 0.608, baseline: 0.605, left: 0.18 }, // 0 short formula sub-line (end line)
    { top: 0.599, bottom: 0.616, baseline: 0.612, left: 0.03 }, // 1 full-height next paragraph, dips up
  ];
  assert.ok(approx(endLineBottom(overlapping, 0), 0.599), "a full-height following line still caps");
});

// A two-line prose booklink whose LAST line carries subscripts (the "p_{n+1}/q_{n+1}
// is in lowest terms" paragraph, entry 85): pdf.js groups the subscripts into a
// shorter LineBox just below the main last line. The wash must cover the whole last
// line, not stop at the subscript box's top (the reported "half-covered" marker).
// Line boxes modeled on the real debug-PDF page-51 geometry.
const SUBSCRIPT_END_LINES: LineBox[] = [
  { top: 0.08906, bottom: 0.1058, baseline: 0.10245, left: 0.0356 }, // 0 "For n≥1 … any common" (first line)
  { top: 0.09721, bottom: 0.10893, baseline: 0.10658, left: 0.4286 }, // 1 first line's subscripts (shorter)
  { top: 0.10915, bottom: 0.12588, baseline: 0.12253, left: 0.0356 }, // 2 "divisor of … lowest terms" (last line)
  { top: 0.1173, bottom: 0.12902, baseline: 0.12668, left: 0.16 }, // 3 last line's subscripts (shorter, lower)
  { top: 0.13927, bottom: 0.15601, baseline: 0.15266, left: 0.1208 }, // 4 next paragraph
];

test("regression: a prose booklink whose last line has subscripts is covered in full", () => {
  // Exact inline start on line 0; end mid-line on line 2 at x 0.82 (after "terms.").
  const segs = resolveBand(SUBSCRIPT_END_LINES, { frac: 0.10245, x: 0.0356 }, { frac: 0.12253, x: 0.82 });
  const last = SUBSCRIPT_END_LINES[2];
  const overLast = segs.filter((s) => (s.bottom ?? 1) > last.top + 1e-9 && s.top < last.bottom - 1e-9);
  assert.ok(overLast.length > 0, "the last line must be covered");
  assert.ok(
    Math.max(...overLast.map((s) => s.bottom ?? 1)) >= last.bottom - 1e-9,
    "the wash must reach the last line's full bottom, not stop at the subscript box top",
  );
});

// A statement booklink (König's lemma, entry 71) whose heading/first line carries a
// superscript: the ⁽<ω⁾ of 2^{<ω} groups into a shorter LineBox with a *higher*
// baseline, sorted just above the main heading line "Lemma (König). If T⊆2…". The
// \BooklinkStart sits before \begin{lemma*}, raised by \leavevmode into the gap
// above; snapping down with lineIndexBelow alone lands on the superscript sub-run,
// so the band starts high and indented to the superscript's x and the heading's
// left ascenders poke out above the wash (the reported wrong span). mainLineBelow
// must advance onto the heading line. Line boxes are the real page-39 debug-PDF
// geometry (page height 595.276pt, body crop 50pt margins).
const STATEMENT_SUPERSCRIPT_HEADING_LINES: LineBox[] = [
  { top: 0.71712, bottom: 0.73392, baseline: 0.73056, left: 0.00313 }, // 0 preceding skip block's last line
  { top: 0.77523, bottom: 0.78699, baseline: 0.78464, left: 0.37527 }, // 1 "<ω" superscript of 2^{<ω} (shorter, higher)
  { top: 0.77724, bottom: 0.79404, baseline: 0.79068, left: 0.00313 }, // 2 "Lemma (König). If T⊆2…" heading (main)
  { top: 0.79539, bottom: 0.80715, baseline: 0.80479, left: 0.64413 }, // 3 "n" superscript of 2^n on the last line
  { top: 0.79741, bottom: 0.8142, baseline: 0.81084, left: 0.00125 }, // 4 "level is empty: … belongs to T." last line
];

test("mainLineBelow: advances past a heading's superscript sub-run onto the main line", () => {
  // lineIndexBelow snaps the raised start onto line 1 (the superscript); mainLineBelow
  // must step onto line 2 (the heading), then stop — line 2 is not a sub-run of line 3.
  assert.equal(mainLineBelow(1, STATEMENT_SUPERSCRIPT_HEADING_LINES), 2);
  // Already on a main line → unchanged.
  assert.equal(mainLineBelow(2, STATEMENT_SUPERSCRIPT_HEADING_LINES), 2);
  // -1 (no line below the anchor) passes straight through.
  assert.equal(mainLineBelow(-1, STATEMENT_SUPERSCRIPT_HEADING_LINES), -1);
});

test("regression: a statement heading carrying a superscript starts the band on the heading, not the superscript", () => {
  // Start raised into the gap (frac 0.76061) above the heading; end exact on the
  // last line (frac 0.81079, after "T." at x 0.85133).
  const segs = resolveBand(
    STATEMENT_SUPERSCRIPT_HEADING_LINES,
    { frac: 0.76061, x: 0.01565 },
    { frac: 0.81079, x: 0.85133 },
  );
  const heading = STATEMENT_SUPERSCRIPT_HEADING_LINES[2];
  // The band must begin at the heading line's top, not the superscript's higher top.
  const bandTop = Math.min(...segs.map((s) => s.top));
  assert.ok(approx(bandTop, heading.top, 1e-4), `band must start at the heading top ${heading.top}, got ${bandTop}`);
  // Every segment covering the heading's vertical extent must reach its left edge —
  // no left-indented sliver (the superscript's x 0.375) leaving the heading's left
  // ascenders uncovered.
  const overHeading = segs.filter((s) => (s.bottom ?? 1) > heading.top + 1e-9 && s.top < heading.bottom - 1e-9);
  assert.ok(overHeading.length > 0, "the heading line must be covered");
  assert.ok(
    overHeading.every((s) => s.left <= heading.left + 1e-9),
    "no segment over the heading may be indented past its left edge",
  );
});
