import assert from "node:assert/strict";
import test from "node:test";
import { taggedFormulaRects } from "./formula-geometry.ts";
import { formulaLineSpans } from "./source-offsets.ts";
import type { CorrespondenceReport } from "./correspondence-model.ts";

test("formula overlays retain Unicode locations, split lines and reject stale or mismatching text", () => {
  const text = "😀 $x+\ny$";
  const report = { status: "current", formulas: [{ index: 7, bodyStart: 3, book: "x+\ny" }] } as CorrespondenceReport;
  const lines = formulaLineSpans(text, report);
  assert.equal(lines.get(0)![0].start, 4);
  assert.equal(lines.get(1)![0].start, 0);
  assert.equal(lines.get(0)![0].index, 7);
  assert.equal(formulaLineSpans(text, { ...report, status: "stale" }).size, 0);
  assert.equal(formulaLineSpans("entirely different translated source", report).size, 0);
});
test("PDF overlays use balanced source tags, not identical adjacent rendered text", () => {
  const glyph = (x: number) => ({ str: "x", width: 4, height: 10, fontName: "f", transform: [10, 0, 0, 10, x, 20] });
  const content = {
    styles: { f: { ascent: 0.8, descent: -0.2 } },
    items: [
      glyph(1),
      { type: "beginMarkedContent", tag: "BookFormula-source-3" },
      glyph(10),
      { type: "endMarkedContent" },
      glyph(30),
      { type: "beginMarkedContent", tag: "BookFormula-source-9" },
      glyph(40),
      { type: "endMarkedContent" },
    ],
  };
  const boxes = taggedFormulaRects(content, [1, 0, 0, -1, 0, 100]);
  assert.deepEqual(boxes.get("BookFormula-source-3"), [{ left: 10, right: 14, top: 72, bottom: 82 }]);
  assert.deepEqual(boxes.get("BookFormula-source-9"), [{ left: 40, right: 44, top: 72, bottom: 82 }]);
  assert.equal(boxes.size, 2);
});
