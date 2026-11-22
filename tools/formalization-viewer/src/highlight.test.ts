import test from "node:test";
import assert from "node:assert/strict";
import { languageForPath, parseHighlightData } from "./highlight.ts";

test("languageForPath classifies viewer sources", () => {
  assert.equal(languageForPath("src/a.md"), "markdown");
  assert.equal(languageForPath("lean/B.lean"), "lean");
  assert.equal(languageForPath("build/x.tex"), null);
  assert.equal(languageForPath(null), null);
  assert.equal(languageForPath(""), null);
});

test("parseHighlightData validates cache payloads without throwing", () => {
  assert.deepEqual(parseHighlightData(null), { spans: [], folds: [] });
  assert.deepEqual(parseHighlightData("junk"), { spans: [], folds: [] });
  assert.deepEqual(parseHighlightData({}), { spans: [], folds: [] });
  const data = parseHighlightData({
    version: 1,
    sha256: "x",
    spans: [
      [0, 5, "tok-keyword"],
      [3, 2, "tok-type"],
      ["a", 1, "tok-type"],
      [0, 1, 42],
      [0, 1],
    ],
    folds: [[2, 9], [9, 2], "x"],
  });
  assert.deepEqual(data.spans, [{ startOffset: 0, endOffset: 5, cls: "tok-keyword" }]);
  assert.deepEqual(data.folds, [{ startOffset: 2, endOffset: 9 }]);
});
