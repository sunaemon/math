// Pure per-line segment geometry for the source panes, extracted from
// source-render.ts so the boundary splitting and covering-span precedence — the
// churn-prone part: the narrowest span wins, and a booklink mark outranks a skip
// overlay — is dependency-free and unit testable. A "span" is any object with
// numeric `start`/`end` column offsets within a line, plus `spanLength`/`index`
// used to break covering ties. The functions are generic over the span shape so
// callers keep their own richer mark/skip/token records on each segment.

export interface LineSpan {
  start: number;
  end: number;
  index?: number;
  spanLength?: number;
  [key: string]: unknown;
}

export interface LineSegment<T extends LineSpan = LineSpan> {
  start: number;
  end: number;
  mark: T | null;
  skip: T | null;
  token: T | null;
}

// The narrowest span covering [start, end), ties broken by lower index. A segment
// is wholly inside or outside each span because the line is split at every span
// boundary, so containment is exactly `range.start <= start && end <= range.end`.
function narrowestCover<T extends LineSpan>(ranges: T[], start: number, end: number): T | null {
  return (
    ranges
      .filter((range) => range.start <= start && end <= range.end)
      .sort((a, b) => (a.spanLength ?? 0) - (b.spanLength ?? 0) || (a.index ?? 0) - (b.index ?? 0))[0] || null
  );
}

// Split a line of length `lineLength` at every mark/skip/token boundary into
// elementary intervals, each tagged with its covering mark, skip, and token. All
// three are constant within an interval, since the line is split at every boundary.
export function lineSegments<T extends LineSpan>(
  lineLength: number,
  marks: T[],
  skips: T[],
  tokens: T[],
): LineSegment<T>[] {
  const boundaries = new Set<number>([0, lineLength]);
  for (const span of [...marks, ...skips, ...tokens]) {
    boundaries.add(span.start);
    boundaries.add(span.end);
  }
  const points = [...boundaries].sort((a, b) => a - b);
  const segments: LineSegment<T>[] = [];
  for (let i = 0; i + 1 < points.length; i += 1) {
    const start = points[i];
    const end = points[i + 1];
    if (end <= start) continue;
    segments.push({
      start,
      end,
      mark: narrowestCover(marks, start, end),
      skip: narrowestCover(skips, start, end),
      token: tokens.find((range) => range.start <= start && end <= range.end) || null,
    });
  }
  return segments;
}

// The covering-span identity a segment is grouped under: a booklink mark
// (`m<entry>`) wins over a skip overlay (`s<index>`), so a formalized statement
// nested in skipped prose still reads as the booklink.
export function wrapperKey(segment: { mark: LineSpan | null; skip: LineSpan | null }): string | null {
  if (segment.mark) return `m${segment.mark.index}`;
  if (segment.skip) return `s${segment.skip.index}`;
  return null;
}
