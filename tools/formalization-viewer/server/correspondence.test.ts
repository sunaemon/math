import assert from "node:assert/strict";
import test from "node:test";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { CorrespondenceService } from "./correspondence.ts";

test("correspondence adapter rejects paths and handles repositories without a registry", async () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "viewer-correspondence-"));
  try {
    const service = new CorrespondenceService(root);
    for (const source of ["/etc/passwd.md", "book/../private.md", "book/chapter.lean", "book\\..\\private.md"])
      await assert.rejects(service.read(source));
    assert.deepEqual(await service.read("book/chapter.md"), { status: "unavailable", formulas: [] });
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test("concurrent inspection is shared beyond five seconds and ignores unrelated builds", async (t) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "viewer-correspondence-"));
  try {
    fs.mkdirSync(path.join(root, "tools/chapter-correspondence"), { recursive: true });
    fs.writeFileSync(
      path.join(root, "tools/chapter-correspondence/viewer.py"),
      `from pathlib import Path
import json
p=Path('count'); n=int(p.read_text())+1 if p.exists() else 1; p.write_text(str(n)); print(json.dumps({'count':n}))
`,
    );
    const service = new CorrespondenceService(root);
    let now = 1000;
    t.mock.method(Date, "now", () => now);
    const [first, second] = await Promise.all([service.read("book/chapter.md"), service.read("book/chapter.md")]);
    assert.deepEqual(first, { count: 1 });
    assert.deepEqual(second, first);
    now += 60000;
    service.invalidate("book/build/book-debug.pdf");
    assert.deepEqual(await service.read("book/chapter.md"), first);
    assert.deepEqual(await service.read("book/chapter.md", true), { count: 2 });
    assert.deepEqual(await service.read("book/chapter.md"), first);
    service.invalidate();
    assert.deepEqual(await service.read("book/chapter.md"), { count: 3 });
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test("cache tracks source, rules, validation reports and compiled Lean dependencies without a watch event", async () => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "viewer-correspondence-"));
  try {
    fs.mkdirSync(path.join(root, "tools/chapter-correspondence"), { recursive: true });
    fs.mkdirSync(path.join(root, "book"));
    const source = path.join(root, "book/chapter.md");
    const dependency = path.join(root, "dependency.olean");
    fs.writeFileSync(source, "original");
    fs.writeFileSync(dependency, "original");
    fs.writeFileSync(
      path.join(root, "tools/chapter-correspondence/viewer.py"),
      `from pathlib import Path
import json
p=Path('count'); n=int(p.read_text())+1 if p.exists() else 1; p.write_text(str(n)); print(json.dumps({'count':n,'_cacheInputs':[str(Path('dependency.olean').resolve())]}))
`,
    );
    const service = new CorrespondenceService(root);
    assert.deepEqual(await service.read("book/chapter.md"), { count: 1 });
    assert.deepEqual(await service.read("book/chapter.md"), { count: 1 });
    fs.writeFileSync(source, "changed source");
    assert.deepEqual(await service.read("book/chapter.md"), { count: 2 });
    fs.writeFileSync(dependency, "changed compiled dependency");
    assert.deepEqual(await service.read("book/chapter.md"), { count: 3 });
    fs.mkdirSync(path.join(root, "tools/book-filter"));
    fs.writeFileSync(path.join(root, "tools/book-filter/Rule.hs"), "changed rule");
    assert.deepEqual(await service.read("book/chapter.md"), { count: 4 });
    const report = path.join(root, "build/validation/correspondence-new/report.json");
    fs.mkdirSync(path.dirname(report), { recursive: true });
    fs.writeFileSync(report, "{}");
    assert.deepEqual(await service.read("book/chapter.md"), { count: 5 });
    fs.writeFileSync(report, '{"passed":true}');
    assert.deepEqual(await service.read("book/chapter.md"), { count: 6 });
    assert.deepEqual(await service.read("book/chapter.md"), { count: 6 });
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});
