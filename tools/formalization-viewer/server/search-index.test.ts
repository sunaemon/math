import assert from "node:assert/strict";
import test from "node:test";
import { searchRecords, searchText } from "./search-index.ts";
test("search indexes visible Japanese prose, semantic terms and source lines", () => {
  const text =
    "# 章 {#sec:chapter}\n\n<!-- private note -->\n\nこれは\\termdefine{可算稠密集合}です。\n\n`LeanName` is searchable.\n";
  const records = searchRecords("book/chapter.md", text);
  assert.ok(records.every((record) => !record.text.includes("private note")));
  const hit = records.find((record) => record.text.includes("可算稠密集合"))!;
  assert.equal(hit.line, 5);
  assert.equal(hit.title, "章");
  assert.equal(hit.language, "ja");
  assert.ok(records.some((record) => record.text.includes("LeanName")));
  assert.equal(searchText("a & b < c"), "a & b < c");
});
test("search skips hidden notation metadata without moving source line offsets", () => {
  const records = searchRecords(
    "book/a.md",
    "# Chapter\n\n\\begin{mathmeta}\n  \\vars{PrivateMetadata}{hidden}\n\\end{mathmeta}\n\nVisible prose.\n",
  );
  assert.ok(records.every((record) => !record.text.includes("PrivateMetadata")));
  assert.equal(records.find((record) => record.text.includes("Visible prose"))?.line, 7);
  assert.ok(searchText("\\begin{theorem*}[Named theorem] Content.\\end{theorem*}").includes("Named theorem"));
});
