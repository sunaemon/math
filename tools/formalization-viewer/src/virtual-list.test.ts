import test from "node:test";
import assert from "node:assert/strict";
import { listWindow, MARKER_ROW_HEIGHT as row } from "./virtual-list.ts";

test("large menus mount only the visible viewport and one screen on either side", () => {
  const count = 10000,
    height = row * 8,
    top = row * 5000;
  const window = listWindow(count, top, height);
  assert.deepEqual([window.start, window.end], [4992, 5016]);
  assert.equal(window.before + (window.end - window.start) * row + window.after, count * row);
});
test("opening at the end and filtering to a small list clamps the scroll position", () => {
  const end = listWindow(10000, row * 10000, row * 8);
  assert.equal(end.end, 10000);
  assert.equal(end.top, row * 9992);
  const filtered = listWindow(3, end.top, row * 8);
  assert.deepEqual([filtered.start, filtered.end, filtered.top], [0, 3, 0]);
  assert.deepEqual([listWindow(0, 100, row * 8).start, listWindow(0, 100, row * 8).end], [0, 0]);
});
