import assert from "node:assert/strict";
import { test } from "node:test";
import { WheelChapterPull, WHEEL_GESTURE_GAP } from "./chapter-pull-gesture.ts";

test("ordinary scrolling and its momentum cannot turn a chapter upon reaching an edge", () => {
  const gesture = new WheelChapterPull();
  assert.equal(gesture.push(300, null, 0).turn, false);
  assert.deepEqual(gesture.push(300, 1, 50), { progress: 0, turn: false });
  assert.equal(gesture.push(300, 1, 100).turn, false);
  assert.equal(gesture.push(120, 1, 100 + WHEEL_GESTURE_GAP + 1).turn, true);
});

test("an intentional pull accumulates a threshold and turns only once per gesture", () => {
  const gesture = new WheelChapterPull();
  assert.equal(gesture.push(50, 1, 0).turn, false);
  assert.equal(gesture.push(60, 1, 30).turn, true);
  assert.deepEqual(gesture.push(500, 1, 60), { progress: 0, turn: false });
});

test("top pulls go backwards, while reversal, missing neighbors, and blocked loads cancel a pull", () => {
  const gesture = new WheelChapterPull();
  assert.equal(gesture.push(-120, -1, 0).turn, true);
  assert.equal(gesture.push(120, null, 1000).turn, false);
  assert.equal(gesture.push(50, 1, 2000).progress > 0, true);
  assert.equal(gesture.push(-120, -1, 2030).turn, false);
  assert.equal(gesture.push(120, 1, 2060).turn, false);
  gesture.block(3000);
  assert.equal(gesture.push(120, 1, 3050).turn, false);
  assert.equal(gesture.push(120, 1, 4000).turn, true);
});
