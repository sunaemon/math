// Process-group termination shared by the Lean bridge, the cache generator's
// Lean server, and the file watcher.
//
// Each child is spawned `detached` (its own process group) so a signal to the
// group reaps the whole tree — e.g. the `lean` child under `lake env`, not just
// the `lake` wrapper, which would otherwise be orphaned after every build.

import type { ChildProcess } from "node:child_process";

export function killGroup(proc: ChildProcess, signal: NodeJS.Signals): void {
  if (proc.pid === undefined) return;
  try {
    process.kill(-proc.pid, signal);
  } catch {
    try {
      proc.kill(signal);
    } catch {
      /* already gone */
    }
  }
}

export function waitExit(proc: ChildProcess, ms: number): Promise<boolean> {
  if (proc.pid === undefined || proc.exitCode !== null || proc.signalCode !== null) return Promise.resolve(true);
  return new Promise((resolve) => {
    const timer = setTimeout(() => {
      proc.off("exit", onExit);
      resolve(false);
    }, ms);
    function onExit(): void {
      clearTimeout(timer);
      resolve(true);
    }
    proc.once("exit", onExit);
  });
}

// Whether any process still belongs to the group led by `pgid`. Signal 0
// only probes for existence; an ESRCH means the group has no members left.
// On platforms without POSIX process groups the probe always fails, which
// degrades the group waits below to watching the leader alone.
function groupAlive(pgid: number): boolean {
  try {
    process.kill(-pgid, 0);
    return true;
  } catch {
    return false;
  }
}

// Wait until the leader has exited *and* every member of its process group
// is gone. Watching only the leader is not enough: a wrapper such as
// `lake env` exits promptly on SIGTERM while the real `lean` under it can
// linger, and a leader that died on its own can leave its group behind.
export function waitGroupExit(proc: ChildProcess, ms: number): Promise<boolean> {
  if (proc.pid === undefined) return Promise.resolve(true);
  const pgid = proc.pid;
  return new Promise((resolve) => {
    const deadline = Date.now() + ms;
    const timer = setInterval(check, 25);
    function cleanup(): void {
      clearInterval(timer);
      proc.off("exit", check);
    }
    function check(): void {
      const leaderGone = proc.exitCode !== null || proc.signalCode !== null;
      if (leaderGone && !groupAlive(pgid)) {
        cleanup();
        resolve(true);
      } else if (Date.now() >= deadline) {
        cleanup();
        resolve(false);
      }
    }
    proc.on("exit", check);
    check();
  });
}

// Stop a subprocess and the process group it leads, then reap it so no orphan
// survives. The group is signalled even when the leader has already exited:
// its members can outlive it (the real server under a short-lived wrapper).
// Best-effort: a process tree that has already fully exited is a no-op.
export async function terminate(proc: ChildProcess | null, graceMs = 5000): Promise<void> {
  if (proc === null || proc.pid === undefined) return;
  killGroup(proc, "SIGTERM");
  if (await waitGroupExit(proc, graceMs)) return;
  killGroup(proc, "SIGKILL");
  await waitGroupExit(proc, graceMs);
}
