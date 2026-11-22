import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import test from "node:test";

import { chapterTitles } from "./chapter-titles.ts";
import type { Manifest } from "./projects.ts";

const project: Manifest = { mount: "/book", dir: "book", bookManifest: "book.json", pdf: "book.pdf" };

test("chapterTitles memoizes until a chapter changes", () => {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), "viewer-titles-")));
  try {
    fs.mkdirSync(path.join(root, "book"), { recursive: true });
    fs.writeFileSync(
      path.join(root, "book", "book.json"),
      JSON.stringify({ chapters: ["book/ch1.md", "book/ch2.md"] }),
    );
    fs.writeFileSync(path.join(root, "book", "ch1.md"), "# One\n\nFirst chapter.\n");
    const ch2 = path.join(root, "book", "ch2.md");
    fs.writeFileSync(ch2, "# Two\n\nSecond chapter.\n");

    const first = chapterTitles(root, project);
    assert.deepEqual(first, { ch1: "One", ch2: "Two" });
    assert.equal(chapterTitles(root, project), first, "unchanged inputs reuse the titles");

    fs.writeFileSync(ch2, "# Two, Revised\n\nSecond chapter.\n");
    const later = new Date(Date.now() + 5000);
    fs.utimesSync(ch2, later, later);
    const second = chapterTitles(root, project);
    assert.notEqual(second, first, "a chapter edit rebuilds");
    assert.equal(second.ch2, "Two, Revised");
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});
