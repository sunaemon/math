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

test("closing a cached document releases its diagnostics and notifies Lean", async () => {
  const server = new LeanServer(os.tmpdir(), () =>
    spawn(process.execPath, ["-e", "process.stdin.resume()"], {
      stdio: ["pipe", "pipe", "ignore"],
      detached: true,
    }),
  );
  try {
    const messages: unknown[] = [];
    server.notify = (method, params) => {
      messages.push({ method, params });
    };
    const uri = "file:///example.lean";
    server.diagnostics.set(uri, [{ message: "old diagnostics" }]);
    server.closeDocument(uri);
    assert.deepEqual(messages, [{ method: "textDocument/didClose", params: { textDocument: { uri } } }]);
    assert.equal(server.diagnostics.has(uri), false);
  } finally {
    await server.shutdown();
  }
});
