import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { test, mock } from "node:test";
import { atomicWrite } from "./file-output.ts";

test("atomic output retains the previous JSON if publication fails", () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "atomic-output-"));
  const target = path.join(root, "cache.json");
  try {
    atomicWrite(target, '{"complete":1}');
    mock.method(fs, "renameSync", () => {
      throw new Error("publication interrupted");
    });
    assert.throws(() => atomicWrite(target, '{"complete":2}'), /interrupted/);
    assert.deepEqual(JSON.parse(fs.readFileSync(target, "utf-8")), { complete: 1 });
    assert.deepEqual(fs.readdirSync(root), ["cache.json"]);
    mock.restoreAll();
    atomicWrite(target, '{"complete":2}');
    assert.deepEqual(JSON.parse(fs.readFileSync(target, "utf-8")), { complete: 2 });
  } finally {
    mock.restoreAll();
    fs.rmSync(root, { recursive: true, force: true });
  }
});
