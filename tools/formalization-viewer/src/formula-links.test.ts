import assert from "node:assert/strict";
import test from "node:test";
import { formulaLinkSegments, formulaRangeCoverage } from "./formula-links.ts";

test("overlapping original Lean occurrences retain every corresponding formula", () => {
  assert.deepEqual(
    formulaLinkSegments([
      { start: 0, end: 5, tags: ["a"] },
      { start: 2, end: 7, tags: ["b"] },
    ]),
    [
      { start: 0, end: 2, tags: ["a"] },
      { start: 2, end: 5, tags: ["a", "b"] },
      { start: 5, end: 7, tags: ["b"] },
    ],
  );
});
test("link segments merge identical neighbors without crossing gaps or accepting invalid spans", () => {
  assert.deepEqual(
    formulaLinkSegments([
      { start: 0, end: 2, tags: ["a", "a"] },
      { start: 2, end: 4, tags: ["a"] },
      { start: 5, end: 6, tags: ["a"] },
      { start: -1, end: 8, tags: ["bad"] },
      { start: 4, end: 4, tags: ["bad"] },
    ]),
    [
      { start: 0, end: 4, tags: ["a"] },
      { start: 5, end: 6, tags: ["a"] },
    ],
  );
});

test("partial ranges never become whole-expression evidence by overlap or adjacency", () => {
  assert.deepEqual(
    formulaLinkSegments([
      { start: 0, end: 2, tags: ["a"], wholeTags: [] },
      { start: 2, end: 4, tags: ["a"], wholeTags: [] },
      { start: 5, end: 7, tags: ["a"], wholeTags: [] },
    ]),
    [
      { start: 0, end: 4, tags: ["a"], wholeTags: [] },
      { start: 5, end: 7, tags: ["a"], wholeTags: [] },
    ],
  );
  assert.deepEqual(
    formulaLinkSegments([
      { start: 0, end: 4, tags: ["a"], wholeTags: [] },
      { start: 2, end: 4, tags: ["a"], wholeTags: ["a"] },
    ]),
    [
      { start: 0, end: 2, tags: ["a"], wholeTags: [] },
      { start: 2, end: 4, tags: ["a"], wholeTags: ["a"] },
    ],
  );
});
test("whole-expression styling requires one verified root operator spanning the exact source formula", () => {
  const row = {
    book: "\n d(x,y) / (1+d(x,y))\n",
    bodyStart: 20,
    operators: [
      { operatorStart: 21, start: 21, end: 27, sourceExpression: "d(x,y)", calls: [{}] },
      { operatorStart: 28, start: 21, end: 41, sourceExpression: "d(x,y) / (1+d(x,y))", calls: [{}] },
    ],
  };
  row.operators[1].end = row.bodyStart + Array.from(row.book.trimEnd()).length;
  assert.equal(formulaRangeCoverage(row, 21), "partial");
  assert.equal(formulaRangeCoverage(row, 28), "whole");
  assert.equal(formulaRangeCoverage(row, 99), "partial");
  assert.equal(formulaRangeCoverage({ ...row, operators: [{ ...row.operators[1], calls: [{}, {}] }] }, 28), "partial");
  assert.equal(formulaRangeCoverage({ ...row, operators: [{ ...row.operators[1], end: 27 }] }, 28), "partial");
});
