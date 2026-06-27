// Pure offset/line/span arithmetic shared by the source-pane renderer: building
// the line-start table, mapping a character offset to its line, bucketing spans
// onto the lines they cover, and converting codepoint offsets to UTF-16. Split
// out of source-render.ts so this off-by-one-prone math has no dependencies (in
// particular not escapeHtml/util, which touch the DOM at load) and can be unit
// tested directly with `node --test`.

export function buildLineStarts(text: string): number[] {
  const starts = [0];
  for (let i = 0; i < text.length; i += 1) {
    if (text[i] === "\n") starts.push(i + 1);
  }
  return starts;
}

export function offsetToLine(lineStarts: number[], offset: number): number {
  let lo = 0;
  let hi = lineStarts.length;
  while (lo + 1 < hi) {
    const mid = Math.floor((lo + hi) / 2);
    if (lineStarts[mid] <= offset) lo = mid;
    else hi = mid;
  }
  return lo;
}

export function bucketByLine(lineStarts: number[], textLength: number, items: any[]): Map<number, any[]> {
  const byLine: Map<number, any[]> = new Map();
  for (const item of items) {
    if (!Number.isInteger(item.startOffset) || !Number.isInteger(item.endOffset)) continue;
    if (item.endOffset <= item.startOffset) continue;
    const startLine = offsetToLine(lineStarts, item.startOffset);
    const endLine = offsetToLine(lineStarts, Math.max(item.startOffset, item.endOffset - 1));
    for (let line = startLine; line <= endLine; line += 1) {
      const lineStart = lineStarts[line];
      // Clamp to the line's content end, excluding the trailing "\n":
      // lineStarts[line + 1] points one past the newline, so clamping endOffset
      // to it leaves a zero-width segment (an empty <span class="mark">) at the
      // end of a non-final line. The final line has no trailing newline.
      const lineEnd = line + 1 < lineStarts.length ? lineStarts[line + 1] - 1 : textLength;
      const start = Math.max(item.startOffset, lineStart) - lineStart;
      const end = Math.min(item.endOffset, lineEnd) - lineStart;
      if (end > start) {
        const parts = byLine.get(line) || [];
        parts.push({ ...item, start, end });
        byLine.set(line, parts);
      }
    }
  }
  return byLine;
}

// Convert every span's codepoint offsets to UTF-16 offsets in one forward pass
// over the text, instead of rescanning from the start for each offset (which was
// O(spans × textLength)). Offsets past the text clamp to its UTF-16 length, and
// non-positive offsets map to 0, matching the previous per-offset behavior.
export function convertSpansToUtf16(text: string, spans: any[], offsetSpace: "utf16" | "codepoint"): any[] {
  if (offsetSpace === "utf16") return spans;
  const wanted = new Set<number>();
  for (const span of spans) {
    if (Number.isInteger(span.startOffset)) wanted.add(span.startOffset);
    if (Number.isInteger(span.endOffset)) wanted.add(span.endOffset);
  }
  const sorted = [...wanted].sort((a, b) => a - b);
  const map = new Map<number, number>();
  let codePoints = 0;
  let utf16 = 0;
  let i = 0;
  for (const char of text) {
    // utf16 is the UTF-16 length of the first `codePoints` codepoints, i.e. the
    // UTF-16 offset where codepoint `codePoints` begins.
    while (i < sorted.length && sorted[i] <= codePoints) map.set(sorted[i++], utf16);
    utf16 += char.length;
    codePoints += 1;
  }
  while (i < sorted.length) map.set(sorted[i++], utf16);
  return spans.map((span) => ({
    ...span,
    startOffset: map.get(span.startOffset) ?? span.startOffset,
    endOffset: map.get(span.endOffset) ?? span.endOffset,
  }));
}
