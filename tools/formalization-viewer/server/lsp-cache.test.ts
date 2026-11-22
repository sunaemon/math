import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import test from "node:test";
import { CacheKeys, parseArgs, generate } from "./lsp-cache.ts";

test("closure cache keys preserve previous values and read shared imports once", () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "lsp-key-"));
  try {
    const a = path.join(root, "A.lean"),
      b = path.join(root, "B.lean");
    fs.writeFileSync(a, "import B\n\ndef a := 1\n");
    fs.writeFileSync(b, "def b := 2\n");
    const reads: string[] = [];
    const keys = new CacheKeys(root, "pins", (file) => {
      reads.push(file);
      return fs.readFileSync(file);
    });
    // Captured from the previous implementation before memoization: changing
    // these would invalidate unchanged, expensive Lean elaboration caches.
    assert.equal(keys.key(a), "fa2eda7f8c70cfb721579297434dd0e8ba4fbb51fa3d3d397c101a8e0c4197b3");
    assert.equal(keys.key(b), "38e58732ca0657ebf71dd39d0ccbf90436e781cb4e5c31016ce54baa1e6e0588");
    assert.deepEqual(reads.sort(), [a, b]);
    fs.writeFileSync(b, "def b := 3\n");
    assert.notEqual(new CacheKeys(root, "pins").key(a), keys.key(a));
    fs.writeFileSync(b, "import A\ndef b := 3\n");
    assert.equal(new CacheKeys(root, "pins").key(a), new CacheKeys(root, "pins").key(b));
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test("cache CLI rejects absent values, unknown options and invalid deadlines", () => {
  for (const option of ["--root", "--project-dir", "--out", "--elab-timeout"]) {
    assert.throws(() => parseArgs([option]), /requires a value/);
    assert.throws(() => parseArgs([option, "--out"]), /requires a value/);
  }
  for (const value of ["NaN", "Infinity", "0", "-1", "2junk"]) {
    assert.throws(() => parseArgs(["--elab-timeout", value]), /positive finite/);
  }
  assert.throws(() => parseArgs(["--unknown"]), /Unknown option/);
  assert.equal(parseArgs(["--elab-timeout", "1.5"]).elabTimeout, 1.5);
  assert.deepEqual(parseArgs(["--", "--literal-file.lean"]).files, ["--literal-file.lean"]);
});

test("cache generation rejects escaping targets before opening a Lean server or writing output", async () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "cache-target-"));
  try {
    fs.mkdirSync(path.join(root, "book/lean"), { recursive: true });
    const output = path.join(root, "cache");
    await assert.rejects(generate(root, "book", output, [path.join(root, "outside.lean")]), /outside the project/);
    await assert.rejects(generate(root, "..", output, []), /top-level name/);
    await assert.rejects(generate(root, "book", output, [], NaN), /positive and finite/);
    assert.throws(() => parseArgs(["--project-dir", "../outside"]), /top-level project name/);
    assert.equal(fs.existsSync(output), false);
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});
