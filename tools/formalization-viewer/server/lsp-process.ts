import { spawn, type ChildProcessByStdio } from "node:child_process";
import type { Writable, Readable } from "node:stream";

export type LeanProc = ChildProcessByStdio<Writable, Readable, null>;
export type SpawnLean = (root: string) => LeanProc;

// A dedicated process group keeps the lake wrapper and its Lean child together.
export const spawnLean: SpawnLean = (root) =>
  spawn("lake", ["env", "lean", "--server"], {
    cwd: root,
    stdio: ["pipe", "pipe", "ignore"],
    detached: true,
  });
