import test from "node:test";
import assert from "node:assert/strict";
import { previewStartPage } from "./pdf-preview.ts";

test("chapter previews omit part dividers and parity padding before the first chapter", async () => {
  const page = { num: 15, gen: 0 };
  const doc = {
    numPages: 20,
    getOutline: async () => [{ dest: "part.1", items: [{ dest: "chapter.1", items: [{ dest: "section.1.1" }] }] }],
    getDestination: async (name: string) => (name === "chapter.1" ? [page] : [0]),
    getPageIndex: async (ref: unknown) => {
      assert.equal(ref, page);
      return 2;
    },
  };
  assert.equal(await previewStartPage(doc, "/book-preview-polish-spaces.pdf"), 3);
  assert.equal(await previewStartPage(doc, "/book-preview-polish-spaces-dark.pdf?v=2"), 3);
});

test("a folio-only leading page is skipped and front matter already on page one stays visible", async () => {
  const doc = (index: number) => ({
    numPages: 6,
    getOutline: async () => [{ dest: "chapter*.2" }],
    getDestination: async () => [index],
  });
  assert.equal(await previewStartPage(doc(1), "book-preview-chapter.pdf"), 2);
  assert.equal(await previewStartPage(doc(0), "book-preview-preface.pdf"), 1);
});

test("full-book renders retain their opening pages without consulting chapter outlines", async () => {
  const doc = {
    getOutline: () => {
      throw new Error("must not be called");
    },
  };
  for (const path of ["book-debug.pdf", "book-debug-dark.pdf", "book.pdf"])
    assert.equal(await previewStartPage(doc, path), 1);
});

test("contents previews skip parity padding even without an outline entry", async () => {
  const doc = (index: number) => ({
    numPages: 19,
    getOutline: async () => null,
    getDestinations: async () => ({ "Doc-Start": [0], "chapter*.1": [index] }),
    getDestination: async () => [index],
  });
  for (const path of ["book-preview-_contents.pdf", "book-preview-_contents-dark.pdf?v=2"]) {
    assert.equal(await previewStartPage(doc(1), path), 2);
    assert.equal(await previewStartPage(doc(0), path), 1);
    assert.equal(await previewStartPage(doc(99), path), 1);
    assert.equal(await previewStartPage(doc(1), path, () => false), 1);
  }
});

test("contents previews prefer local anchors to inherited bookmarks for absent chapters", async () => {
  const doc = {
    numPages: 19,
    getOutline: async () => [{ dest: "chapter*.2", items: [{ dest: "chapter.1" }] }],
    getDestinations: async () => ({ "Doc-Start": [0], "chapter*.1": [1] }),
    getDestination: async (name: string) => (name === "chapter*.1" ? [1] : null),
  };
  assert.equal(await previewStartPage(doc, "book-preview-_contents.pdf"), 2);
  assert.equal(await previewStartPage(doc, "book-preview-_contents-dark.pdf?v=2"), 2);
});

test("contents resolves its heading directly when pdf.js returns an empty destination map", async () => {
  const doc = {
    numPages: 19,
    getOutline: async () => null,
    getDestinations: async () => ({}),
    getDestination: async (name: string) => (name === "chapter*.1" ? [1] : null),
  };
  assert.equal(await previewStartPage(doc, "book-preview-_contents.pdf"), 2);
});

test("missing, invalid and stale chapter destinations conservatively retain the first page", async () => {
  const doc = {
    numPages: 3,
    getOutline: async () => [{ dest: "chapter.1" }],
    getDestination: async () => [99],
  };
  assert.equal(await previewStartPage(doc, "book-preview-chapter.pdf"), 1);
  assert.equal(await previewStartPage(doc, "book-preview-chapter.pdf", () => false), 1);
  assert.equal(await previewStartPage({ ...doc, getOutline: async () => null }, "book-preview-chapter.pdf"), 1);
});

test("chapter anchor resolution skips unrelated chapters while full documents retain all sources", async () => {
  const { pdfIncludesSource } = await import("./pdf-preview.ts");
  for (const pdf of [
    "book-preview-cantor-baire-space.pdf",
    "book-preview-cantor-baire-space-dark.pdf?v=2",
    "book-layout-a5-10pt-preview-cantor-baire-space.pdf",
  ]) {
    assert.equal(pdfIncludesSource(pdf, "/book/src/cantor-baire-space.md"), true);
    assert.equal(pdfIncludesSource(pdf, "/book/src/preface.md"), false);
    assert.equal(pdfIncludesSource(pdf, undefined), true);
  }
  assert.equal(pdfIncludesSource("book-debug.pdf", "/book/src/preface.md"), true);
  assert.equal(pdfIncludesSource("book-preview-_index.pdf", "/book/src/_index.md"), true);
});
