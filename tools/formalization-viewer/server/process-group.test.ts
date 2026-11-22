import assert from "node:assert/strict";
import { spawn, type ChildProcess } from "node:child_process";
import test from "node:test";

import { terminate } from "./process-group.ts";

function alive(pid: number): boolean {
  try {
    process.kill(pid, 0);
    return true;
  } catch {
    return false;
  }
}

async function waitFor(predicate: () => boolean, ms: number): Promise<boolean> {
  const deadline = Date.now() + ms;
  while (Date.now() < deadline) {
    if (predicate()) return true;
    await new Promise((resolve) => setTimeout(resolve, 25));
  }
  return predicate();
}

function killQuietly(proc: ChildProcess, extraPid?: number): void {
  if (proc.pid !== undefined) {
    try {
      process.kill(-proc.pid, "SIGKILL");
    } catch {
      /* group already gone */
    }
  }
  if (extraPid !== undefined) {
    try {
      process.kill(extraPid, "SIGKILL");
    } catch {
      /* already gone */
    }
  }
}

// Spawn a detached leader (its own process group) running `script`; the
// script prints the pid of a same-group grandchild on its first stdout line.
function spawnLeader(script: string): { proc: ChildProcess; grandchildPid: Promise<number> } {
  const proc = spawn(process.execPath, ["-e", script], {
    detached: true,
    stdio: ["ignore", "pipe", "ignore"],
  });
  const grandchildPid = new Promise<number>((resolve, reject) => {
    let buffer = "";
    proc.stdout!.on("data", (chunk) => {
      buffer += chunk;
      const pid = Number(buffer.split("\n")[0]);
      if (Number.isInteger(pid) && pid > 0) resolve(pid);
    });
    proc.once("error", reject);
  });
  return { proc, grandchildPid };
}

const SLEEPER = "setTimeout(() => {}, 30000)";

test("terminate reaps a grandchild whose leader already exited", async () => {
  const { proc, grandchildPid } = spawnLeader(`
    const { spawn } = require("node:child_process");
    const child = spawn(process.execPath, ["-e", ${JSON.stringify(SLEEPER)}], { stdio: "ignore" });
    child.unref();
    console.log(child.pid);
    setTimeout(() => {}, 50);
  `);
  const pid = await grandchildPid;
  try {
    assert.ok(await waitFor(() => proc.exitCode !== null, 5000), "leader should exit on its own");
    assert.ok(alive(pid), "grandchild should outlive its leader");
    await terminate(proc, 2000);
    assert.ok(await waitFor(() => !alive(pid), 3000), "grandchild must not survive terminate");
  } finally {
    killQuietly(proc, pid);
  }
});

test("terminate escalates to SIGKILL for a member that ignores SIGTERM", async () => {
  // The grandchild prints its pid only after its SIGTERM handler is
  // installed (the leader forwards the line), so the escalation path is
  // exercised deterministically rather than racing the handler install.
  const { proc, grandchildPid } = spawnLeader(`
    const { spawn } = require("node:child_process");
    const child = spawn(process.execPath, ["-e", "process.on('SIGTERM', () => {}); console.log(process.pid); setTimeout(() => {}, 30000)"], { stdio: ["ignore", "pipe", "ignore"] });
    child.stdout.pipe(process.stdout);
    setTimeout(() => {}, 30000);
  `);
  const pid = await grandchildPid;
  try {
    assert.ok(alive(pid));
    const started = Date.now();
    await terminate(proc, 300);
    const elapsed = Date.now() - started;
    assert.ok(await waitFor(() => !alive(pid), 3000), "SIGTERM-ignoring member must be SIGKILLed");
    assert.ok(elapsed >= 250, "the grace period must elapse before SIGKILL (no early give-up)");
    assert.ok(proc.exitCode !== null || proc.signalCode !== null, "leader should be gone");
  } finally {
    killQuietly(proc, pid);
  }
});

test("terminate returns promptly when the tree dies on SIGTERM", async () => {
  const proc = spawn(process.execPath, ["-e", SLEEPER], {
    detached: true,
    stdio: ["ignore", "ignore", "ignore"],
  });
  try {
    const started = Date.now();
    await terminate(proc);
    assert.ok(Date.now() - started < 3000, "the common path must not wait out the grace period");
    assert.ok(proc.pid !== undefined && !alive(proc.pid));
  } finally {
    killQuietly(proc);
  }
});
