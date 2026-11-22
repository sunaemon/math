import assert from "node:assert/strict";
import { spawn, type ChildProcess } from "node:child_process";
import { once } from "node:events";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import test from "node:test";
import { FileWatcher } from "./file-watcher.ts";
import { terminate } from "./process-group.ts";

test("a missing build directory is covered by its existing parent at cold startup", async () => {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), "file-watcher-cold-")));
  fs.mkdirSync(path.join(root, "book/src"), { recursive: true });
  let args: string[] = [];
  const watcher = new FileWatcher(root, ["book/src", "book/build"], new Map(), undefined, {
    spawn: (cwd, flags) => {
      args = flags;
      return spawn(process.execPath, ["-e", "setInterval(() => {}, 1000)"], {
        cwd,
        stdio: ["ignore", "pipe", "ignore"],
        detached: true,
      });
    },
  });
  try {
    watcher.ensure();
    const watched = args.flatMap((arg, i) => (arg === "--watch" ? [args[i + 1]] : []));
    assert.deepEqual(watched, [path.join(root, "book")]);
  } finally {
    await watcher.shutdown();
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test("a crashed watcher restarts while subscribers remain and shutdown reaps it", async () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "file-watcher-retry-"));
  fs.mkdirSync(path.join(root, "src"));
  const children: ChildProcess[] = [];
  let changed!: () => void;
  const change = new Promise<void>((resolve) => {
    changed = resolve;
  });
  const events: string[] = [];
  const watcher = new FileWatcher(root, ["src"], new Map(), () => changed(), {
    retryMs: 1,
    spawn: (cwd) => {
      const event = JSON.stringify({
        tags: [{ kind: "path", filetype: "file", absolute: path.join(root, "src/chapter.md") }],
      });
      const script =
        children.length === 0
          ? "process.exit(1)"
          : `process.stdout.write(${JSON.stringify(event + "\n")}); setInterval(() => {}, 1000)`;
      const child = spawn(process.execPath, ["-e", script], {
        cwd,
        stdio: ["ignore", "pipe", "ignore"],
        detached: true,
      });
      children.push(child);
      return child;
    },
  });
  watcher.subscribe({ put: (message) => events.push(message) });
  const timer = setTimeout(() => changed(), 5000);
  try {
    watcher.ensure();
    await change;
    assert.equal(children.length, 2);
    assert.deepEqual(
      events.map((event) => JSON.parse(event).path),
      ["src/chapter.md"],
    );
  } finally {
    clearTimeout(timer);
    await watcher.shutdown();
    await Promise.all(children.map(terminate));
    fs.rmSync(root, { recursive: true, force: true });
  }
  assert.ok(children.every((child) => child.exitCode !== null || child.signalCode !== null));
});

test("shutdown cancels a pending watcher retry", async () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "file-watcher-stop-"));
  fs.mkdirSync(path.join(root, "src"));
  const children: ChildProcess[] = [];
  const watcher = new FileWatcher(root, ["src"], new Map(), undefined, {
    retryMs: 30,
    spawn: (cwd) => {
      const child = spawn(process.execPath, ["-e", "process.exit(1)"], {
        cwd,
        stdio: ["ignore", "pipe", "ignore"],
        detached: true,
      });
      children.push(child);
      return child;
    },
  });
  watcher.subscribe({ put() {} });
  try {
    watcher.ensure();
    await once(children[0], "exit");
    await watcher.shutdown();
    await new Promise((resolve) => setTimeout(resolve, 60));
    assert.equal(children.length, 1);
  } finally {
    await watcher.shutdown();
    await Promise.all(children.map(terminate));
    fs.rmSync(root, { recursive: true, force: true });
  }
});
