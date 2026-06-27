// Pure geometry for the PDF `formalization: skip` overlay bands. No DOM or
// pdf.js dependencies, so it is unit-tested directly (skip-bands.test.ts); pdf.ts
// feeds it anchor positions and text-line data and handles the actual drawing.
//
// Everything here is in *page-height fractions* (0 = page top, 1 = page bottom),
// which are independent of the pane's pixel width. That is what lets a band
// resolved once render correctly at any size: pdf.ts multiplies these fractions
// by the page's current height at draw time.

// `left` is the line's leftmost glyph as a fraction of the page width (0 when no
// x mapping was supplied), used to tell a mid-line booklink start from a raised
// line/item-start one.
export type LineBox = { top: number; bottom: number; baseline: number; left: number };

// A glyph run reduced to what line-grouping needs: its baseline (PDF y, page
// coordinates), glyph-box height, and optional left x (PDF points).
export type TextRun = { baseline: number; height: number; x?: number };

export type SkipSegment = { pageNumber: number; top: number; bottom: number | null };

// Slack (fraction of page height, ~a quarter line) so an anchor sitting exactly
// on a baseline still matches that line rather than the next one.
export const SNAP_TOL = 0.004;

// Group glyph runs into per-line boxes expressed as fractions of the page
// height. Runs that share a (rounded) baseline form one line; its box spans the
// union of an 0.8/0.2 ascent/descent split of each run's height, matching how
// body type sits in its line box. `toFraction` maps a PDF y to a top-down page
// fraction (pdf.js `viewport.convertToViewportPoint(0, y)[1] / viewport.height`).
// `xToFraction` (optional) maps a PDF x to a page-width fraction for each line's
// left edge. Result is sorted top→bottom by baseline.
export function groupTextLines(
  runs: TextRun[],
  toFraction: (pdfY: number) => number,
  xToFraction?: (pdfX: number) => number,
): LineBox[] {
  const byLine = new Map<number, { pdfTop: number; pdfBottom: number; pdfBase: number; pdfLeft: number }>();
  for (const run of runs) {
    const h = run.height > 0 ? run.height : 0;
    const x = typeof run.x === "number" ? run.x : Infinity;
    const rec = byLine.get(Math.round(run.baseline));
    if (rec) {
      rec.pdfTop = Math.max(rec.pdfTop, run.baseline + 0.8 * h);
      rec.pdfBottom = Math.min(rec.pdfBottom, run.baseline - 0.2 * h);
      rec.pdfLeft = Math.min(rec.pdfLeft, x);
    } else {
      byLine.set(Math.round(run.baseline), {
        pdfTop: run.baseline + 0.8 * h,
        pdfBottom: run.baseline - 0.2 * h,
        pdfBase: run.baseline,
        pdfLeft: x,
      });
    }
  }
  return [...byLine.values()]
    .map((r) => ({
      top: toFraction(r.pdfTop),
      bottom: toFraction(r.pdfBottom),
      baseline: toFraction(r.pdfBase),
      left: xToFraction && Number.isFinite(r.pdfLeft) ? xToFraction(r.pdfLeft) : 0,
    }))
    .sort((a, b) => a.baseline - b.baseline);
}

// Snap the band's top onto the first line *below* the start anchor: hyperref
// raises that anchor ~a baselineskip, so it lands a line above the region's
// first line. Returns that line's top, or the raw anchor fraction if the page
// has no text lines (e.g. a figure-only page).
export function snapBandTop(frac: number, lines: LineBox[]): number {
  let best: LineBox | null = null;
  for (const line of lines)
    if (line.baseline > frac + SNAP_TOL && (!best || line.baseline < best.baseline)) best = line;
  return best ? best.top : frac;
}

// Snap the band's bottom onto the line *at* the end anchor (which sits on the
// region's last baseline) so the wash reaches that line's descenders. Returns
// that line's bottom, or the raw anchor fraction if no line matches.
export function snapBandBottom(frac: number, lines: LineBox[]): number {
  let best: LineBox | null = null;
  for (const line of lines)
    if (line.baseline <= frac + SNAP_TOL && (!best || line.baseline > best.baseline)) best = line;
  return best ? best.bottom : frac;
}

// The index of the first line *below* a start anchor (hyperref raises that
// anchor ~a baselineskip, so it lands a line above the region's first line),
// matching snapBandTop. -1 if the page has no line below the anchor.
export function lineIndexBelow(frac: number, lines: LineBox[]): number {
  let best = -1;
  let bestBaseline = Infinity;
  for (let i = 0; i < lines.length; i += 1) {
    if (lines[i].baseline > frac + SNAP_TOL && lines[i].baseline < bestBaseline) {
      best = i;
      bestBaseline = lines[i].baseline;
    }
  }
  return best;
}

// The index of the line *at* an end anchor (which sits on the region's last
// baseline), matching snapBandBottom. -1 if no line is at/above the anchor.
export function lineIndexAt(frac: number, lines: LineBox[]): number {
  let best = -1;
  let bestBaseline = -Infinity;
  for (let i = 0; i < lines.length; i += 1) {
    if (lines[i].baseline <= frac + SNAP_TOL && lines[i].baseline > bestBaseline) {
      best = i;
      bestBaseline = lines[i].baseline;
    }
  }
  return best;
}

// Slack (page-width fraction) for the end-anchor x test below.
const X_TOL = 0.01;

// The booklink *start* line is simply lineIndexAt: the \BooklinkStart macro records
// the exact pen baseline of the span's first glyph (it forces horizontal mode so a
// paragraph/list start is not lifted into the inter-line space — see macros.tex),
// so the anchor sits on its own line and needs no disambiguation. The first line's
// left edge is the anchor's own x (start.xFrac in pdf.ts). lineIndexAt is reused
// directly; this comment marks that the start needs nothing more.

// Resolve a booklink *end* marker to its last covered line and that line's right
// edge, by pure reading order: the highlight ends at the last glyph that precedes
// the marker. A line strictly above the marker is wholly before it (covered full
// width). On the marker's own line, only glyphs to the left of the marker precede
// it (covered up to the marker x); if none do — the marker sits at that line's left
// edge because it overshot onto the next paragraph, as happens when an excerpt ends
// with a display equation immediately followed by text — that line is not covered,
// and the end falls back to the last qualifying line above it. No thresholds beyond
// the inherent line grouping: with the marker at its true position this is exact.
// Returns the line index (-1 if no line precedes the marker) and its right edge as
// a page-width fraction.
export function endLineResolve(frac: number, xFrac: number, lines: LineBox[]): { index: number; right: number } {
  let index = -1;
  let right = 0;
  for (let i = 0; i < lines.length; i += 1) {
    const line = lines[i];
    if (line.baseline > frac + SNAP_TOL) break; // below the marker (lines are sorted top→bottom)
    if (line.baseline < frac - SNAP_TOL) {
      index = i; // wholly above the marker → covered full width
      right = 1;
    } else if (xFrac > line.left + X_TOL) {
      index = i; // the marker's own line, with glyphs to the left of it
      right = xFrac;
    }
  }
  return { index, right };
}

// A following LineBox set in a font this much shorter than the end line (or less)
// is treated as a subscript / sub-baseline run of the end line itself, not as a
// genuine next line. Subscripts are typically ~0.7 of the body size, so 0.9 leaves
// a wide margin while still capping against equal-height (genuine) following lines.
const SUBRUN_HEIGHT_RATIO = 0.9;

// The bottom edge a booklink's last line should reach. The line box is
// [eLine.top, eLine.bottom], but if a *following* line abuts it with no blank-line
// gap — a display equation whose descenders overlap the next paragraph — eLine's box
// dips into that line, so cap the band at the following line's top.
//
// The subtlety: a subscript or sub-baseline run of the end line itself groups into
// its own LineBox (a smaller font, baseline a couple points lower) sorted right after
// `ei`, with its box top *above* eLine's bottom. That run is part of eLine's own text
// line, not a following line; capping against it chops eLine's wash to a sliver (the
// reported "half-covered" band). Tell the two apart by height — a subscript is set
// smaller than eLine, a genuine following line is not — skip the shorter sub-runs and
// cap against the first full-height line below. This mirrors the start side's
// `max(nextLine.top, sLine.bottom)` clamp, which already keeps the first line whole.
export function endLineBottom(endLines: LineBox[], ei: number): number {
  const eLine = endLines[ei];
  const eHeight = eLine.bottom - eLine.top;
  for (let j = ei + 1; j < endLines.length; j += 1) {
    const line = endLines[j];
    if (line.bottom - line.top < eHeight * SUBRUN_HEIGHT_RATIO) continue; // subscript of eLine
    return Math.min(eLine.bottom, line.top);
  }
  return eLine.bottom;
}

// When a raised start snaps DOWN with lineIndexBelow, the first line under the
// anchor can be a *superscript* sub-run of the real first line, not that line
// itself: a heading/first line carrying a superscript — the ⁽<ω⁾ of 2^{<ω}, the
// ⁽ω⁾ of ω^ω in a statement heading — groups into a shorter LineBox with a
// *higher* baseline, sorted just above the main line. Starting the band there
// covers only the superscript (high, and indented to the superscript's x) and
// leaves the main line's left ascenders poking out above the wash. Advance past
// such a sub-run onto the main line below it: a following line that is taller (a
// superscript is set smaller — the same SUBRUN_HEIGHT_RATIO as endLineBottom) and
// abuts it with no blank-line gap (its box top sits above the sub-run's bottom).
// This is the start-side mirror of endLineBottom, which skips the *end* line's
// trailing subscript sub-runs. -1 (no line) passes straight through.
export function mainLineBelow(index: number, lines: LineBox[]): number {
  let i = index;
  while (i >= 0 && i + 1 < lines.length) {
    const cur = lines[i];
    const next = lines[i + 1];
    const curHeight = cur.bottom - cur.top;
    const nextHeight = next.bottom - next.top;
    // `cur` is a superscript of `next` when it is shorter than `next` and their
    // boxes overlap in y (next.top above cur.bottom — no blank line between them).
    // Genuine adjacent text lines never overlap, so this never skips a real line.
    if (curHeight < nextHeight * SUBRUN_HEIGHT_RATIO && next.top < cur.bottom) i += 1;
    else break;
  }
  return i;
}

export type FlowSegment = { pageNumber: number; top: number; bottom: number | null; left: number; right: number };

// Highlight a booklink span as a text selection flows: the first line runs from
// its start x to the right edge, the lines between run full width, and the last
// line runs from the left edge to its end x. All y positions are page-height
// fractions; left/right are page-width fractions (0..1). `nextTop` is the top of
// the line after the start line *on the start page*, or null when the start line
// is the last line on its page (the flow resumes at the top of the next page).
// Reuses skipBandSegments for the page-splitting, then tags each piece's x range.
export function flowBandSegments(
  p: {
    startPage: number;
    startTop: number;
    startBottom: number;
    nextTop: number | null;
    endPage: number;
    endTop: number;
    endBottom: number;
    startX: number;
    endX: number;
  },
  sameLine: boolean,
): FlowSegment[] {
  if (sameLine) {
    if (p.endBottom <= p.startTop || p.endX <= p.startX) return [];
    return [{ pageNumber: p.startPage, top: p.startTop, bottom: p.endBottom, left: p.startX, right: p.endX }];
  }
  const tag = (segs: SkipSegment[], left: number, right: number): FlowSegment[] =>
    segs.map((s) => ({ ...s, left, right }));
  // First line: [startX → right edge], down to where the full-width block begins.
  const bound1 = { pageNumber: p.startPage, frac: p.nextTop != null ? p.nextTop : p.startBottom };
  const first = tag(skipBandSegments({ pageNumber: p.startPage, frac: p.startTop }, bound1), p.startX, 1);
  // Middle lines: full width, from the block start to the top of the last line.
  const restStart = p.nextTop != null ? bound1 : { pageNumber: p.startPage + 1, frac: 0 };
  const bound2 = { pageNumber: p.endPage, frac: p.endTop };
  const middle = tag(skipBandSegments(restStart, bound2), 0, 1);
  // Last line: [left edge → endX].
  const last = tag(skipBandSegments(bound2, { pageNumber: p.endPage, frac: p.endBottom }), 0, p.endX);
  return [...first, ...middle, ...last];
}

// Split a start/end placement into one segment per page. All positions are
// page-height fractions; `bottom: null` means "down to the page bottom". A region
// whose end is above its start (degenerate) yields no segments.
export function skipBandSegments(
  start: { pageNumber: number; frac: number },
  end: { pageNumber: number; frac: number },
): SkipSegment[] {
  if (end.pageNumber < start.pageNumber) return [];
  if (start.pageNumber === end.pageNumber) {
    if (end.frac <= start.frac) return [];
    return [{ pageNumber: start.pageNumber, top: start.frac, bottom: end.frac }];
  }
  const segments: SkipSegment[] = [{ pageNumber: start.pageNumber, top: start.frac, bottom: null }];
  for (let page = start.pageNumber + 1; page < end.pageNumber; page += 1) {
    segments.push({ pageNumber: page, top: 0, bottom: null });
  }
  segments.push({ pageNumber: end.pageNumber, top: 0, bottom: end.frac });
  return segments;
}
