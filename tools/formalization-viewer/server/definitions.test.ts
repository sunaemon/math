import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import test from "node:test";

import { bookDefinitionRegistry } from "./definitions.ts";
import type { Manifest } from "./projects.ts";

const project: Manifest = { mount: "/book", dir: "book", bookManifest: "book.json", pdf: "book.pdf" };

function bookFixture(root: string): void {
  fs.mkdirSync(path.join(root, "book"), { recursive: true });
  fs.writeFileSync(path.join(root, "book", "book.json"), JSON.stringify({ chapters: ["book/ch1.md", "book/ch2.md"] }));
  fs.writeFileSync(path.join(root, "book", "ch1.md"), "# One\n\nFirst chapter.\n");
  fs.writeFileSync(path.join(root, "book", "ch2.md"), "# Two\n\nSecond chapter.\n");
}

function bumpMtime(file: string): void {
  const later = new Date(Date.now() + 5000);
  fs.utimesSync(file, later, later);
}

test("bookDefinitionRegistry memoizes until an input changes", () => {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), "viewer-definitions-")));
  try {
    bookFixture(root);
    const first = bookDefinitionRegistry(root, project);
    assert.deepEqual(Object.keys(first.sourceHashes).sort(), ["book/ch1.md", "book/ch2.md"]);
    assert.equal(bookDefinitionRegistry(root, project), first, "unchanged inputs reuse the registry");

    const ch1 = path.join(root, "book", "ch1.md");
    fs.writeFileSync(ch1, "# One\n\nFirst chapter, revised.\n");
    bumpMtime(ch1);
    const second = bookDefinitionRegistry(root, project);
    assert.notEqual(second, first, "a chapter edit rebuilds");
    assert.notEqual(second.sourceHashes["book/ch1.md"], first.sourceHashes["book/ch1.md"]);
    assert.equal(bookDefinitionRegistry(root, project), second);

    // An aux file appearing after a PDF build also invalidates (the section
    // aliases are read from the aux files).
    fs.mkdirSync(path.join(root, "book", "build"), { recursive: true });
    fs.writeFileSync(path.join(root, "book", "build", "book.aux"), "");
    const third = bookDefinitionRegistry(root, project);
    assert.notEqual(third, second, "an aux file appearing rebuilds");
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});

test("bookDefinitionRegistry inverts term and section uses into usedBy", () => {
  const root = fs.realpathSync(fs.mkdtempSync(path.join(os.tmpdir(), "viewer-definitions-")));
  try {
    fs.mkdirSync(path.join(root, "book"), { recursive: true });
    fs.writeFileSync(
      path.join(root, "book", "book.json"),
      JSON.stringify({ chapters: ["book/ch1.md", "book/ch2.md"] }),
    );
    fs.writeFileSync(
      path.join(root, "book", "ch1.md"),
      [
        "# One {#sec:one}",
        "",
        "## Groups {#sec:groups}",
        "",
        "A \\termdefine{group} is a set with an operation.",
        "The \\termuse{group} notion recurs in §{sec:groups}.",
        "",
      ].join("\n"),
    );
    fs.writeFileSync(
      path.join(root, "book", "ch2.md"),
      [
        "# Two {#sec:two}",
        "",
        "Every \\termuse{group} here is a \\termuse{group} again, as §{sec:groups} showed.",
        "",
        "Later, \\termuseas{group}{groups} appear once more.",
        "",
      ].join("\n"),
    );
    const registry = bookDefinitionRegistry(root, project);
    const term = registry.entries["term-def-group"];
    assert.ok(term, "the term entry exists");
    // The ch1 use sits in the term's own defining paragraph and is excluded;
    // the two ch2 uses in one paragraph collapse into a single item.
    assert.equal(term.usedBy?.length, 2);
    assert.equal(term.usedBy?.[0].file, "book/ch2.md");
    assert.equal(term.usedBy?.[0].section, "Two");
    assert.match(term.usedBy?.[0].excerpt ?? "", /Every/);
    assert.match(term.usedBy?.[1].excerpt ?? "", /Later/);
    const section = registry.entries["sec:groups"];
    assert.ok(section, "the section entry exists");
    // The ch1 § reference sits in the section's own opening block and is
    // excluded; only the ch2 reference remains.
    assert.equal(section.usedBy?.length, 1);
    assert.equal(section.usedBy?.[0].file, "book/ch2.md");
  } finally {
    fs.rmSync(root, { recursive: true, force: true });
  }
});
