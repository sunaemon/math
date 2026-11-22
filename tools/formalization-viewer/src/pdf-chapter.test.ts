import test from "node:test";
import assert from "node:assert/strict";
import { destinationChapter, termTarget, preferredDestination } from "./pdf-chapter.ts";

test("terms and notation retain distinct definition and index targets", () => {
  for (const [prefix, key] of [
    ["term", "polish-space"],
    ["notation", "BaireSpace"],
  ]) {
    for (const role of ["def", "index"]) {
      const target = termTarget(`${prefix}-${role}-${key}`)!;
      assert.equal(target.definition, `${prefix}-def-${key}`);
      assert.equal(target.references, `${prefix}-index-${key}`);
    }
    const index = `${prefix}-index-${key}`;
    assert.equal(preferredDestination(index, true), `${prefix}-def-${key}`);
    assert.equal(preferredDestination(index, false), index);
  }
  for (const other of [null, [], "ref-Kechris1995", "sec:polish-spaces", "term-index-"]) {
    assert.equal(termTarget(other), null);
  }
  assert.equal(preferredDestination("sec:polish-spaces", true), "sec:polish-spaces");
});

test("cross-chapter references use full-document chapter boundaries and prefer definitions", async () => {
  const destinations: Record<string, any> = {
    "chapter.1": [0, null, 0, 700],
    "chapter.2": [5, null, 0, 700],
    "sec:target": [6, null, 0, 400],
    "term-index-example": [20, null, 0, 600],
    "term-def-example": [1, null, 0, 500],
  };
  const doc = {
    getOutline: async () => [{ dest: "chapter.1" }, { dest: "chapter.2" }],
    getDestination: async (name: string) => destinations[name] ?? null,
  };
  const anchors = { first: "sec:first", second: "sec:second" };
  assert.equal(await destinationChapter(doc, "sec:target", anchors), "second");
  assert.equal(await destinationChapter(doc, "term-index-example", anchors), "first");
  assert.equal(await destinationChapter(doc, "missing", anchors), null);
});

test("references and index destinations resolve to their own previews without changing term definition routing", async () => {
  const destinations: Record<string, any> = {
    "chapter.1": [0, null, 0, 700],
    "section*.20": [10, null, 0, 700],
    "chapter*.21": [15, null, 0, 700],
    "term-index-example": [12, null, 0, 600],
    "term-def-example": [1, null, 0, 500],
    "ref-example": [16, null, 0, 400],
    "notation-index-other": [11, null, 0, 500],
  };
  const doc = {
    getOutline: async () => [
      { dest: "chapter.1", title: "Chapter" },
      { dest: "section*.20", title: "Index" },
      { dest: "chapter*.21", title: "References" },
    ],
    getDestination: async (name: string) => destinations[name] ?? null,
  };
  const chapters = { first: "Chapter" };
  const sections = { _index: "Index", _bibliography: "References" };
  assert.equal(await destinationChapter(doc, "ref-example", chapters, sections), "_bibliography");
  assert.equal(await destinationChapter(doc, "notation-index-other", chapters, sections), "_index");
  assert.equal(await destinationChapter(doc, "term-index-example", chapters, sections), "first");
  assert.equal(await destinationChapter(doc, "term-index-example", chapters, sections, false), "_index");
});
