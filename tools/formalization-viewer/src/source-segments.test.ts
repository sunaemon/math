// Unit tests for the source-pane segment geometry. Run with `node --test`.
// These pin the rendering behavior the recent booklink/skip-overlay fixes were
// about: a line splits at every span boundary, the narrowest span covers a
// segment (ties → lower index), mark and skip are tracked independently, and a
// booklink mark outranks a skip when both cover a segment.

import { test } from "node:test";
import assert from "node:assert/strict";
import { lineSegments, wrapperKey, type LineSpan, type LineSegment } from "./source-segments.ts";

const span = (start: number, end: number, index: number): LineSpan => ({
  start,
  end,
  index,
  spanLength: end - start,
});

// Compact a segment list to [start, end, markIndex|null, skipIndex|null, hasToken].
function summary(segments: LineSegment[]) {
  return segments.map((s) => [s.start, s.end, s.mark?.index ?? null, s.skip?.index ?? null, s.token != null]);
}

test("an empty line is one bare segment", () => {
  assert.deepEqual(summary(lineSegments(5, [], [], [])), [[0, 5, null, null, false]]);
});

test("a mark splits the line into before / covered / after", () => {
  assert.deepEqual(summary(lineSegments(5, [span(1, 3, 0)], [], [])), [
    [0, 1, null, null, false],
    [1, 3, 0, null, false],
    [3, 5, null, null, false],
  ]);
});

test("the narrowest mark covers an overlapped segment", () => {
  const wide = span(0, 4, 0); // spanLength 4
  const narrow = span(1, 2, 1); // spanLength 1, nested inside wide
  assert.deepEqual(summary(lineSegments(4, [wide, narrow], [], [])), [
    [0, 1, 0, null, false], // only wide covers here
    [1, 2, 1, null, false], // both cover; narrower (index 1) wins
    [2, 4, 0, null, false], // only wide covers here
  ]);
});

test("equal-width covering spans break the tie on lower index", () => {
  assert.deepEqual(summary(lineSegments(2, [span(0, 2, 1), span(0, 2, 0)], [], [])), [[0, 2, 0, null, false]]);
});

test("mark and skip are tracked independently on the same segment", () => {
  const mark = span(0, 2, 0);
  const skip = span(0, 4, 0);
  assert.deepEqual(summary(lineSegments(4, [mark], [skip], [])), [
    [0, 2, 0, 0, false], // covered by both the mark and the skip
    [2, 4, null, 0, false], // mark ended; still inside the skip
  ]);
});

test("a covering token is recorded on its segment", () => {
  assert.deepEqual(summary(lineSegments(4, [], [], [span(0, 2, 0)])), [
    [0, 2, null, null, true],
    [2, 4, null, null, false],
  ]);
});

test("wrapperKey: mark outranks skip, then skip, then nothing", () => {
  assert.equal(wrapperKey({ mark: span(0, 1, 3), skip: null }), "m3");
  assert.equal(wrapperKey({ mark: null, skip: span(0, 1, 5) }), "s5");
  assert.equal(wrapperKey({ mark: span(0, 1, 1), skip: span(0, 1, 2) }), "m1");
  assert.equal(wrapperKey({ mark: null, skip: null }), null);
});
