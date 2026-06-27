// Process-group termination shared by the Lean bridge, the cache generator's
// Lean server, and the file watcher.
//
// Each child is spawned `detached` (its own process group) so a signal to the
// group reaps the whole tree — e.g. the `lean` child under `lake env`, not just
// the `lake` wrapper, which would otherwise be orphaned after every build.

import type { ChildProcess } from "node:child_process";

export function killGroup(proc: ChildProcess, signal: NodeJS.Signals): void {
  try {
    process.kill(-proc.pid!, signal);
  } catch {
    try {
      proc.kill(signal);
    } catch {
      /* already gone */
    }
  }
}

export function waitExit(proc: ChildProcess, ms: number): Promise<boolean> {
  if (proc.exitCode !== null || proc.signalCode !== null) return Promise.resolve(true);
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

// Stop a subprocess and the process group it leads, then reap it so no orphan
// survives. Best-effort: a process that has already exited is a no-op.
export async function terminate(proc: ChildProcess | null): Promise<void> {
  if (proc === null || proc.exitCode !== null || proc.signalCode !== null) return;
  killGroup(proc, "SIGTERM");
  if (await waitExit(proc, 5000)) return;
  killGroup(proc, "SIGKILL");
  await waitExit(proc, 5000);
}
