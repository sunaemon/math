// Unit tests for the pure offset/line/span math behind the source panes. Run
// with `node --test`. These pin the off-by-one boundaries the viewer's mark and
// fold rendering depend on: line-start tables, offset->line binary search,
// per-line span bucketing (with the trailing-newline exclusion), and codepoint
// -> UTF-16 offset conversion across surrogate pairs.

import { test } from "node:test";
import assert from "node:assert/strict";
import { buildLineStarts, offsetToLine, bucketByLine, convertSpansToUtf16 } from "./source-offsets.ts";

test("buildLineStarts records the start of every line", () => {
  assert.deepEqual(buildLineStarts(""), [0]);
  assert.deepEqual(buildLineStarts("abc"), [0]);
  assert.deepEqual(buildLineStarts("a\nbb\n"), [0, 2, 5]);
  assert.deepEqual(buildLineStarts("\n"), [0, 1]);
  assert.deepEqual(buildLineStarts("a\n\nb"), [0, 2, 3]);
});

test("offsetToLine maps an offset to its 0-based line", () => {
  const starts = buildLineStarts("a\nbb\n"); // [0, 2, 5]
  assert.equal(offsetToLine(starts, 0), 0);
  assert.equal(offsetToLine(starts, 1), 0); // still on line 0 (the '\n')
  assert.equal(offsetToLine(starts, 2), 1); // first char of line 1
  assert.equal(offsetToLine(starts, 4), 1);
  assert.equal(offsetToLine(starts, 5), 2);
  assert.equal(offsetToLine(starts, 999), 2); // past end clamps to last line
  assert.equal(offsetToLine(starts, -1), 0); // before start clamps to line 0
});

test("bucketByLine splits a span across the lines it covers", () => {
  // "abcd\nefgh": lineStarts [0, 5], textLength 9.
  const starts = buildLineStarts("abcd\nefgh");
  const byLine = bucketByLine(starts, 9, [{ startOffset: 2, endOffset: 7, id: "x" }]);
  assert.deepEqual([...byLine.keys()].sort(), [0, 1]);
  // line 0: "cd" -> [2,4); line 1: "ef" -> [0,2), each carrying the item fields.
  assert.deepEqual(byLine.get(0), [{ startOffset: 2, endOffset: 7, id: "x", start: 2, end: 4 }]);
  assert.deepEqual(byLine.get(1), [{ startOffset: 2, endOffset: 7, id: "x", start: 0, end: 2 }]);
});

test("bucketByLine excludes the trailing newline (no phantom next-line segment)", () => {
  const starts = buildLineStarts("abcd\nefgh"); // [0, 5]
  // A span that runs up to and through the '\n' at offset 4 stays on line 0.
  const byLine = bucketByLine(starts, 9, [{ startOffset: 0, endOffset: 5 }]);
  assert.deepEqual([...byLine.keys()], [0]);
  assert.deepEqual(byLine.get(0), [{ startOffset: 0, endOffset: 5, start: 0, end: 4 }]);
});

test("bucketByLine skips invalid and non-integer spans", () => {
  const starts = buildLineStarts("abcd"); // [0]
  const byLine = bucketByLine(starts, 4, [
    { startOffset: 2, endOffset: 2 }, // zero-width
    { startOffset: 3, endOffset: 1 }, // inverted
    { startOffset: 0.5, endOffset: 3 }, // non-integer start
    { startOffset: 1, endOffset: 3 }, // the one valid span
  ]);
  assert.equal(byLine.size, 1);
  assert.deepEqual(byLine.get(0), [{ startOffset: 1, endOffset: 3, start: 1, end: 3 }]);
});

test("convertSpansToUtf16 is identity when offsets are already UTF-16", () => {
  const spans = [{ startOffset: 1, endOffset: 3 }];
  assert.equal(convertSpansToUtf16("a😀b", spans, "utf16"), spans); // same reference, untouched
});

test("convertSpansToUtf16 leaves pure-ASCII codepoint offsets unchanged", () => {
  const out = convertSpansToUtf16("abcde", [{ startOffset: 1, endOffset: 4 }], "codepoint");
  assert.deepEqual(out, [{ startOffset: 1, endOffset: 4 }]);
});

test("convertSpansToUtf16 widens offsets across a surrogate pair", () => {
  // "a😀b": 😀 is 1 codepoint but 2 UTF-16 units. Codepoint offsets: a=[0,1),
  // 😀=[1,2), b=[2,3). UTF-16: a=[0,1), 😀=[1,3), b=[3,4).
  const text = "a😀b";
  assert.deepEqual(convertSpansToUtf16(text, [{ startOffset: 1, endOffset: 2 }], "codepoint"), [
    { startOffset: 1, endOffset: 3 },
  ]);
  assert.deepEqual(convertSpansToUtf16(text, [{ startOffset: 0, endOffset: 3 }], "codepoint"), [
    { startOffset: 0, endOffset: 4 },
  ]);
});

test("convertSpansToUtf16 clamps an out-of-range offset to the UTF-16 length", () => {
  const text = "a😀b"; // UTF-16 length 4
  assert.deepEqual(convertSpansToUtf16(text, [{ startOffset: 2, endOffset: 99 }], "codepoint"), [
    { startOffset: 3, endOffset: 4 },
  ]);
});
