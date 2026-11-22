import type { FormulaEvidence } from "./correspondence-model.js";

// A Lean occurrence can correspond to several book formulas. Preserve every
// edge when overlapping ranges are split into non-overlapping DOM segments.
export interface FormulaLinkSpan {
  start: number;
  end: number;
  tags: string[];
  wholeTags?: string[];
}
export function formulaLinkSegments(spans: FormulaLinkSpan[]): FormulaLinkSpan[] {
  const valid = spans.filter(
    (span) => Number.isInteger(span.start) && Number.isInteger(span.end) && span.start >= 0 && span.end > span.start,
  );
  const points = [...new Set(valid.flatMap((span) => [span.start, span.end]))].sort((a, b) => a - b);
  const result: FormulaLinkSpan[] = [];
  for (let i = 0; i + 1 < points.length; i++) {
    const start = points[i],
      end = points[i + 1];
    const tags = [
      ...new Set(valid.filter((span) => span.start <= start && end <= span.end).flatMap((span) => span.tags)),
    ].sort();
    if (!tags.length) continue;
    const classified = valid.some((span) => span.wholeTags !== undefined);
    const wholeTags = [
      ...new Set(
        valid.filter((span) => span.start <= start && end <= span.end).flatMap((span) => span.wholeTags ?? []),
      ),
    ]
      .filter((tag) => tags.includes(tag))
      .sort();
    const previous = result.at(-1);
    if (
      previous?.end === start &&
      JSON.stringify(previous.tags) === JSON.stringify(tags) &&
      JSON.stringify(previous.wholeTags ?? []) === JSON.stringify(wholeTags)
    )
      previous.end = end;
    else result.push({ start, end, tags, ...(classified ? { wholeTags } : {}) });
  }
  return result;
}

// This classifies the extent of already verified operator evidence, not a new
// semantic match. A partial operator cannot acquire whole-expression styling
// just because other matched operators occur elsewhere in the same declaration.
export function formulaRangeCoverage(
  row: Pick<FormulaEvidence, "book" | "bodyStart" | "operators">,
  operatorStart: number,
): "whole" | "partial" {
  const begin = row.bodyStart + Array.from(row.book).length - Array.from(row.book.trimStart()).length;
  const end = row.bodyStart + Array.from(row.book.trimEnd()).length;
  const roots = row.operators.filter(
    (operator) =>
      operator.operatorStart === operatorStart &&
      operator.start <= begin &&
      end <= operator.end &&
      operator.sourceExpression?.trim() === row.book.trim() &&
      operator.calls?.length === 1,
  );
  return roots.length === 1 ? "whole" : "partial";
}
