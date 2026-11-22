import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import os from "node:os";
import test from "node:test";
import { LeanServer } from "./lean-server.ts";
import type { LeanProc } from "./lsp-process.ts";
import { terminate } from "./process-group.ts";

test("the cache client closes and reaps a server with a negative frame length", async () => {
  let child!: LeanProc;
  const server = new LeanServer(os.tmpdir(), (root) => {
    child = spawn(
      process.execPath,
      ["-e", "process.stdout.write('Content-Length: -1\\r\\n\\r\\n'); process.stdin.resume()"],
      {
        cwd: root,
        stdio: ["pipe", "pipe", "ignore"],
        detached: true,
      },
    );
    return child;
  });
  try {
    await assert.rejects(server.waitResponse(1, 5), /closed unexpectedly/);
  } finally {
    await server.shutdown();
    await terminate(child);
  }
  assert.ok(child.exitCode !== null || child.signalCode !== null);
});
