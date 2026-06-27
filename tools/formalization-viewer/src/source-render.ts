// Source-pane rendering: turn a source file's text plus its booklink mark
// spans and syntax-highlight tokens into the per-line HTML shown in the md /
// lean / tex panes, with Lean fold regions collapsed. Pure functions over their
// arguments (the only dependency is escapeHtml); click/hover handlers are
// delegated on the pane in app.ts, so the emitted HTML carries data-* only.
// Also owns the per-entry mark color used by both the marks and the rail.

import { escapeHtml } from "./util.js";
import { buildLineStarts, offsetToLine, bucketByLine, convertSpansToUtf16 } from "./source-offsets.js";
import { lineSegments, wrapperKey } from "./source-segments.js";

// One hue per booklink kind, as an "R, G, B" triple the .mark CSS renders at low
// opacity. Color encodes the span's role rather than an arbitrary per-entry hue:
// a statement, its proof, and surrounding prose each read as their kind across
// every pane. (Skipped prose is grey and lives in its own .skip-mark layer.)
const TARGET_COLORS: Record<string, string> = {
  statement: "202, 138, 4", // yellow
  proof: "22, 163, 74", // green
  prose: "37, 99, 235", // blue
};
// Fallback hue for a span with an unknown/missing kind.
const DEFAULT_MARK_RGB = "124, 58, 237"; // violet

export function colorForTarget(target?: string | null): string {
  return (target != null && TARGET_COLORS[target]) || DEFAULT_MARK_RGB;
}

export function markerStyle(target?: string | null): string {
  return `--mark-rgb: ${colorForTarget(target)};`;
}

// The pure offset/line/span math lives in source-offsets.ts (no DOM/util deps,
// so it is unit tested directly). Re-exported here so existing importers keep
// resolving these from source-render.
export { buildLineStarts, offsetToLine, bucketByLine, convertSpansToUtf16 };

export function tokenPiece(
  lineText: string,
  segment: { start: number; end: number; token?: { cls: string } | null },
): string {
  const piece = escapeHtml(lineText.slice(segment.start, segment.end));
  return segment.token ? `<span class="${segment.token.cls}">${piece}</span>` : piece;
}

export function renderSource(
  pre: HTMLElement,
  text: string,
  spans: any[],
  paneName: string,
  highlights: any[] = [],
  folds: any[] = [],
  spanOffsetSpace: "utf16" | "codepoint" = "utf16",
  skipSpans: any[] = [],
): void {
  const lineStarts = buildLineStarts(text);
  const markItems = convertSpansToUtf16(text, spans, spanOffsetSpace).map((span, index) => ({
    startOffset: span.startOffset,
    endOffset: span.endOffset,
    index: Number.isInteger(span.entryIndex) ? span.entryIndex : index,
    target: typeof span.target === "string" ? span.target : null,
    spanLength: span.endOffset - span.startOffset,
  }));
  // `formalization: skip` overlays: book prose deliberately left unformalized.
  // A separate layer from booklink marks (its own class, no per-entry hue, no
  // click/hover/rail wiring) so it never collides with the entry machinery.
  const skipItems = convertSpansToUtf16(text, skipSpans, spanOffsetSpace).map((span, index) => ({
    startOffset: span.startOffset,
    endOffset: span.endOffset,
    index,
    // The skip region's stable key (shared with the PDF skip-band anchors), used
    // to light every fragment of one skip across panes on hover.
    key: typeof span.key === "string" ? span.key : "",
    reason: typeof span.reason === "string" ? span.reason : "",
    skipKind: typeof span.kind === "string" ? span.kind : "",
    spanLength: span.endOffset - span.startOffset,
  }));
  const marksByLine = bucketByLine(lineStarts, text.length, markItems);
  const skipsByLine = bucketByLine(lineStarts, text.length, skipItems);
  const tokensByLine = bucketByLine(lineStarts, text.length, highlights);

  const lines = text.split("\n");
  const lineDivs = lines.map((lineText, lineIndex) => {
    const marks = marksByLine.get(lineIndex) || [];
    const skips = skipsByLine.get(lineIndex) || [];
    const tokens = tokensByLine.get(lineIndex) || [];
    // Split the line at every mark/skip/token boundary into elementary intervals,
    // each tagged with its covering mark, skip, and token (see source-segments).
    const segments = lineSegments(lineText.length, marks, skips, tokens);

    // Coalesce a run of intervals sharing the same covering span into one
    // wrapper element, with token spans nested inside, so a highlighted span
    // renders as a single continuous background rather than one box per token.
    let body = "";
    let i = 0;
    while (i < segments.length) {
      const key = wrapperKey(segments[i]);
      if (!key) {
        body += tokenPiece(lineText, segments[i]);
        i += 1;
        continue;
      }
      let inner = "";
      let j = i;
      while (j < segments.length && wrapperKey(segments[j]) === key) {
        inner += tokenPiece(lineText, segments[j]);
        j += 1;
      }
      const mark = segments[i].mark;
      if (mark) {
        body += `<span class="mark" data-pane="${paneName}" data-entry="${mark.index}" style="${markerStyle(mark.target)}">${inner}</span>`;
      } else {
        const skip = segments[i].skip;
        const reason = skip.reason ? ` title="${escapeHtml(skip.reason)}"` : "";
        body += `<span class="skip-mark" data-skip="${skip.index}" data-skip-key="${escapeHtml(skip.key)}" data-skip-kind="${escapeHtml(skip.skipKind)}"${reason}>${inner}</span>`;
      }
      i = j;
    }
    return `<div class="line" data-line="${lineIndex + 1}">${body || " "}</div>`;
  });

  // Map fold ranges to start-line -> end-line (0-based), skipping single-line
  // comments (nothing to collapse).
  const foldByStart: Map<number, number> = new Map();
  for (const fold of folds) {
    const startLine = offsetToLine(lineStarts, fold.startOffset);
    const endLine = offsetToLine(lineStarts, Math.max(fold.startOffset, fold.endOffset - 1));
    if (endLine > startLine) foldByStart.set(startLine, endLine);
  }

  if (!foldByStart.size) {
    pre.innerHTML = lineDivs.join("");
    return;
  }

  // Wrap each folded run in a collapsed <details>: the opener line is the
  // clickable summary, the rest hides until expanded.
  let html = "";
  let i = 0;
  while (i < lineDivs.length) {
    if (foldByStart.has(i)) {
      const end = foldByStart.get(i) as number;
      const hidden = end - i;
      const label = `${hidden} hidden line${hidden === 1 ? "" : "s"}`;
      html += `<details class="lean-fold"><summary class="fold-summary" data-fold-count="${label}">${lineDivs[i]}</summary>${lineDivs.slice(i + 1, end + 1).join("")}</details>`;
      i = end + 1;
    } else {
      html += lineDivs[i];
      i += 1;
    }
  }
  pre.innerHTML = html;
}
