import { test } from "node:test";
import assert from "node:assert/strict";
import { Recovery } from "./recovery.ts";

test("recovery coalesces timers and requests while an attempt is in flight", async () => {
  const timers: { run: () => Promise<void>; ms: number }[] = [];
  let finish!: (ok: boolean) => void;
  let count = 0;
  const recovery = new Recovery(
    () => {
      count++;
      return new Promise((resolve) => {
        finish = resolve;
      });
    },
    (run, ms) => {
      timers.push({ run, ms });
    },
  );
  recovery.schedule();
  recovery.schedule();
  assert.equal(timers.length, 1);
  assert.equal(timers[0].ms, 1000);
  const attempt = timers.shift()!.run();
  recovery.schedule();
  assert.equal(timers.length, 0);
  assert.equal(count, 1);
  finish(false);
  await attempt;
  assert.equal(timers[0].ms, 2000);
  const retry = timers.shift()!.run();
  finish(true);
  await retry;
  assert.equal(timers.length, 0);
  recovery.schedule();
  assert.equal(timers[0].ms, 1000);
});

test("recovery caps backoff, and a rejected attempt still schedules one retry", async () => {
  const timers: { run: () => Promise<void>; ms: number }[] = [];
  const recovery = new Recovery(
    async () => false,
    (run, ms) => {
      timers.push({ run, ms });
    },
  );
  recovery.schedule();
  for (let i = 1; i <= 20; i++) {
    const timer = timers.shift()!;
    assert.equal(timer.ms, Math.min(15000, i * 1000));
    await timer.run();
    assert.equal(timers.length, 1);
  }
  const failures: (() => Promise<void>)[] = [];
  new Recovery(
    async () => {
      throw new Error("offline");
    },
    (run) => {
      failures.push(run);
    },
  ).schedule();
  await failures.shift()!();
  assert.equal(failures.length, 1);
});
