// Syntax-highlight data for the formalization viewer.
//
// Highlight spans and Lean fold ranges are a pure function of a source file's
// text, so they are computed on the Node side with the vendored tree-sitter
// grammars (server/highlight-core.ts): the live server answers
// `highlight-cache/<path>.json` requests on demand, and a static distribution
// ships pregenerated files at the same URLs (server/highlight-cache.ts). The
// browser only fetches and validates that JSON — it never loads the
// tree-sitter runtime or grammars. Missing or malformed data degrades to
// plain text, as a failed parse used to.
//
// Each entry is {"version": 1, "sha256": ..., "spans": [[start, end, cls],
// ...], "folds": [[start, end], ...]} with UTF-16 offsets into the source
// text; spans are sorted and non-overlapping.

export interface HighlightSpan {
  startOffset: number;
  endOffset: number;
  cls: string;
}
export interface HighlightFold {
  startOffset: number;
  endOffset: number;
}
export interface HighlightData {
  spans: HighlightSpan[];
  folds: HighlightFold[];
}

export function languageForPath(path: string | null | undefined): "lean" | "markdown" | null {
  if (!path) return null;
  if (path.endsWith(".lean")) return "lean";
  if (path.endsWith(".md")) return "markdown";
  return null;
}

function isOffsetPair(value: unknown): value is [number, number] {
  return (
    Array.isArray(value) &&
    value.length === 2 &&
    Number.isFinite(value[0]) &&
    Number.isFinite(value[1]) &&
    value[0] >= 0 &&
    value[1] >= value[0]
  );
}

// Validate one highlight-cache payload. Never throws: anything unexpected
// yields empty data, so a stale or corrupt cache file renders plain text
// instead of breaking the pane.
export function parseHighlightData(value: unknown): HighlightData {
  const data: HighlightData = { spans: [], folds: [] };
  if (!value || typeof value !== "object") return data;
  const { spans, folds } = value as { spans?: unknown; folds?: unknown };
  if (Array.isArray(spans)) {
    for (const item of spans) {
      if (Array.isArray(item) && item.length === 3 && isOffsetPair([item[0], item[1]]) && typeof item[2] === "string")
        data.spans.push({ startOffset: item[0], endOffset: item[1], cls: item[2] });
    }
  }
  if (Array.isArray(folds)) {
    for (const item of folds) {
      if (isOffsetPair(item)) data.folds.push({ startOffset: item[0], endOffset: item[1] });
    }
  }
  return data;
}
