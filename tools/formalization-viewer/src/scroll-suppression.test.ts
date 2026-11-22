import { test } from "node:test";
import assert from "node:assert/strict";
import { ScrollSuppression } from "./scroll-suppression.ts";

test("navigation replaces suppression and cancels a previous release", () => {
  const timers: { run: () => void; ms: number; cancelled: boolean }[] = [];
  let changed = 0;
  const guard = new ScrollSuppression(
    (run, ms) => {
      const timer = { run, ms, cancelled: false };
      timers.push(timer);
      return () => {
        timer.cancelled = true;
      };
    },
    () => {
      changed++;
    },
  );
  guard.begin(["pdf", "lean"]);
  guard.releaseAfter();
  assert.equal(timers[0].ms, 300);
  guard.begin(["md"]);
  assert.equal(timers[0].cancelled, true);
  assert.deepEqual([...guard.panes], ["md"]);
  guard.releaseAfter();
  timers[1].run();
  assert.equal(guard.panes.size, 0);
  assert.equal(changed, 3);
});

test("PDF links extend the shared window to 1200ms and retain other suppressed panes", () => {
  const timers: { run: () => void; ms: number; cancelled: boolean }[] = [];
  const guard = new ScrollSuppression(
    (run, ms) => {
      const timer = { run, ms, cancelled: false };
      timers.push(timer);
      return () => {
        timer.cancelled = true;
      };
    },
    () => {},
  );
  guard.begin(["lean"]);
  guard.releaseAfter();
  guard.hold("pdf");
  assert.equal(timers[0].cancelled, true);
  assert.equal(timers[1].ms, 1200);
  assert.deepEqual([...guard.panes], ["lean", "pdf"]);
  timers[1].run();
  assert.equal(guard.panes.size, 0);
});
