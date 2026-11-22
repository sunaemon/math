import assert from "node:assert/strict";
import test from "node:test";
import { nearestFormula, sourcePieces, type FormulaEvidence } from "./correspondence-model.ts";

const row = { start: 8, end: 16, bodyStart: 10, book: "😀x+日", index: 0 } as FormulaEvidence;
test("correspondence spans use Unicode codepoints and retain argument order", () => {
  assert.deepEqual(sourcePieces(row, 11, 12), ["😀", "x", "+日"]);
  assert.deepEqual(sourcePieces(row, 10, 11), ["", "😀", "x+日"]);
  assert.deepEqual(sourcePieces(row, 0, 99), ["", "😀x+日", ""]);
});
test("formula navigation prefers the containing formula and handles gaps and empty chapters", () => {
  const rows = [row, { ...row, start: 30, end: 40 }];
  assert.equal(nearestFormula(rows, 9), 0);
  assert.equal(nearestFormula(rows, 20), 1);
  assert.equal(nearestFormula(rows, 50), 1);
  assert.equal(nearestFormula([], 10), -1);
});
