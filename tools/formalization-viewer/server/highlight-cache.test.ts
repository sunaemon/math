import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { generate, HighlightService, type HighlightFile } from "./highlight-cache.ts";
import type { Manifest } from "./projects.ts";

function fakeProject(root: string): Manifest {
  const dir = path.join(root, "book");
  fs.mkdirSync(path.join(dir, "src"), { recursive: true });
  fs.mkdirSync(path.join(dir, "lean"), { recursive: true });
  fs.writeFileSync(path.join(dir, "src", "a.md"), "# Title\n\nSome $x$ math.\n");
  fs.writeFileSync(path.join(dir, "lean", "B.lean"), "/-@ booklink: x -/\ntheorem b : True := trivial\n");
  fs.writeFileSync(path.join(dir, "src", "skip.txt"), "not a source");
  return { dir: "book", mount: "/book", served: { src: ["md"], lean: ["lean"] } };
}

test("generate writes per-file highlight JSON keyed by source hash and skips unchanged files", async () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "highlight-cache-"));
  const project = fakeProject(root);
  const out = path.join(root, "book", "build", "highlight-cache");
  assert.equal(await generate(root, project, out), 2);
  const md = JSON.parse(fs.readFileSync(path.join(out, "src", "a.md.json"), "utf-8")) as HighlightFile;
  assert.equal(md.version, 1);
  assert.match(md.sha256, /^[0-9a-f]{64}$/);
  assert.ok(md.spans.length > 0);
  assert.deepEqual(md.folds, []);
  const lean = JSON.parse(fs.readFileSync(path.join(out, "lean", "B.lean.json"), "utf-8")) as HighlightFile;
  assert.equal(lean.folds.length, 1);
  assert.equal(await generate(root, project, out), 0);
  fs.appendFileSync(path.join(root, "book", "src", "a.md"), "More prose.\n");
  assert.equal(await generate(root, project, out), 1);
});

test("HighlightService computes on demand, memoizes, and rejects unknown files", async () => {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), "highlight-service-")));
  const project = fakeProject(root);
  const service = new HighlightService(root);
  const first = await service.get(project, "src/a.md");
  assert.ok(first && first.spans.length > 0);
  assert.equal(await service.get(project, "src/a.md"), first);
  assert.equal(await service.get(project, "src/missing.md"), null);
  assert.equal(await service.get(project, "src/skip.txt"), null);
});
