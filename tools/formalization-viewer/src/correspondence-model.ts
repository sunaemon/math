// Report offsets count Unicode code points. Never apply them as JS UTF-16
// indices, or apply canonical English offsets to translated Markdown.
export interface FormulaEvidence {
  index: number;
  line: number;
  start: number;
  end: number;
  bodyStart: number;
  pdfTag?: string;
  book: string;
  syntax?: unknown;
  context?: string;
  lean?: string;
  inferredType?: string;
  typeStatus: string;
  typeReason?: string;
  variables: Array<Record<string, any>>;
  expressionFragments?: Array<Record<string, any>>;
  semanticExpressions?: Array<{ fragmentIndex: number | null; supported: boolean; ast?: unknown; reason?: string }>;
  operators: Array<Record<string, any>>;
}

export interface CorrespondenceReport {
  status: "current" | "stale" | "unavailable" | "error";
  source?: string;
  report?: string;
  reasons?: string[];
  reason?: string;
  coverage?: { interpretationUnits: number; operators: { tracedOperators: number } };
  formulas: FormulaEvidence[];
}

export function nearestFormula(rows: FormulaEvidence[], offset: number): number {
  if (!rows.length) return -1;
  const covering = rows.findIndex((row) => row.start <= offset && offset < row.end);
  if (covering >= 0) return covering;
  const following = rows.findIndex((row) => row.start >= offset);
  return following >= 0 ? following : rows.length - 1;
}

export function sourcePieces(row: FormulaEvidence, start: number, end: number): [string, string, string] {
  const codepoints = Array.from(row.book);
  const begin = Math.max(0, Math.min(codepoints.length, start - row.bodyStart));
  const stop = Math.max(begin, Math.min(codepoints.length, end - row.bodyStart));
  return [codepoints.slice(0, begin).join(""), codepoints.slice(begin, stop).join(""), codepoints.slice(stop).join("")];
}
