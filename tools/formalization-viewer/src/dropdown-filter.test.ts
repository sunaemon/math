// Unit tests for the custom dropdown's option filtering and highlight clamping.
// Run with `node --test`.

import { test } from "node:test";
import assert from "node:assert/strict";
import { filterOptionIndices, clampIndex } from "./dropdown-filter.ts";

const OPTIONS = [
  { label: "Polish Spaces", value: "polish-spaces" },
  { label: "Cantor–Baire Space", value: "cantor-baire" },
  { label: "", value: "fallback.md" },
];

test("a blank or whitespace query keeps every option in order", () => {
  assert.deepEqual(filterOptionIndices(OPTIONS, ""), [0, 1, 2]);
  assert.deepEqual(filterOptionIndices(OPTIONS, "   "), [0, 1, 2]);
});

test("filtering is a case-insensitive substring match on the label", () => {
  assert.deepEqual(filterOptionIndices(OPTIONS, "cant"), [1]);
  assert.deepEqual(filterOptionIndices(OPTIONS, "SPACE"), [0, 1]);
});

test("filtering falls back to the value when the label is blank", () => {
  assert.deepEqual(filterOptionIndices(OPTIONS, "fallback"), [2]);
});

test("a query that matches nothing yields no indices", () => {
  assert.deepEqual(filterOptionIndices(OPTIONS, "zzz"), []);
});

test("clampIndex keeps a highlight within [0, length - 1]", () => {
  assert.equal(clampIndex(5, 3), 3);
  assert.equal(clampIndex(5, 9), 4);
  assert.equal(clampIndex(5, -2), 0);
  assert.equal(clampIndex(1, 0), 0);
});

test("clampIndex collapses to 0 for an empty or invalid list length", () => {
  assert.equal(clampIndex(0, 3), 0);
  assert.equal(clampIndex(-1, 2), 0);
});
