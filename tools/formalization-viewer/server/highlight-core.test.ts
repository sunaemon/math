import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { computeHighlightData, languageForPath, type HighlightData } from "./highlight-core.ts";

const here = path.dirname(fileURLToPath(import.meta.url));
const fixture = (name: string) => fs.readFileSync(path.join(here, "..", "fixtures", name), "utf-8");

function assertWellFormed(data: HighlightData, text: string): void {
  let prevEnd = 0;
  for (const span of data.spans) {
    assert.ok(span.startOffset >= prevEnd, "spans are sorted and non-overlapping");
    assert.ok(span.endOffset > span.startOffset && span.endOffset <= text.length);
    assert.match(span.cls, /^tok-/);
    prevEnd = span.endOffset;
  }
}

test("languageForPath classifies viewer sources", () => {
  assert.equal(languageForPath("src/a.md"), "markdown");
  assert.equal(languageForPath("lean/B.lean"), "lean");
  assert.equal(languageForPath("build/x.tex"), null);
  assert.equal(languageForPath(null), null);
  assert.equal(languageForPath(""), null);
});

test("Lean highlights and booklink folds are computed on the Node side", async () => {
  const text = fixture("simple.lean");
  const data = await computeHighlightData(text, "lean");
  assertWellFormed(data, text);
  assert.ok(data.spans.length > 0);
  const commentAt = text.indexOf("-- Lean filler");
  assert.ok(
    data.spans.some((s) => s.cls === "tok-comment" && s.startOffset <= commentAt && commentAt < s.endOffset),
    "line comments are tok-comment",
  );
  const theoremAt = text.indexOf("theorem alpha_theorem");
  assert.ok(
    data.spans.some((s) => s.cls === "tok-keyword" && s.startOffset <= theoremAt && theoremAt + 7 <= s.endOffset),
    "theorem is tok-keyword",
  );
  // The fixture carries exactly three /-@ booklink blocks, and all of them fold.
  assert.equal(data.folds.length, 3);
  for (const fold of data.folds) {
    const slice = text.slice(fold.startOffset, fold.endOffset);
    assert.ok(slice.startsWith("/-@") && slice.endsWith("-/"), `fold covers a booklink block: ${slice.slice(0, 20)}`);
  }
});

test("Markdown highlights include headings and the LaTeX overlay", async () => {
  const text = fixture("simple.md");
  const data = await computeHighlightData(text, "markdown");
  assertWellFormed(data, text);
  assert.deepEqual(data.folds, []);
  const headingAt = text.indexOf("Simple Booklink Fixture");
  assert.ok(
    data.spans.some((s) => s.cls === "tok-heading" && s.startOffset <= headingAt && headingAt < s.endOffset),
    "heading text is tok-heading",
  );
  const beginAt = text.indexOf("\\begin{theorem*}");
  assert.ok(
    data.spans.some((s) => s.cls === "tok-keyword" && s.startOffset === beginAt),
    "\\begin is tok-keyword",
  );
  const envAt = text.indexOf("theorem*}");
  assert.ok(
    data.spans.some((s) => s.cls === "tok-type" && s.startOffset <= envAt && envAt < s.endOffset),
    "environment name is tok-type",
  );

  const md = "# T\n\nMath $x$ here.\n\n<!-- hidden -->\n";
  const crafted = await computeHighlightData(md, "markdown");
  const commentAt = md.indexOf("<!--");
  assert.ok(
    crafted.spans.some((s) => s.cls === "tok-comment" && s.startOffset <= commentAt && commentAt < s.endOffset),
    "HTML comments are tok-comment",
  );
  const dollarAt = md.indexOf("$x$");
  assert.ok(
    crafted.spans.some((s) => s.cls === "tok-operator" && s.startOffset === dollarAt),
    "math delimiters are tok-operator",
  );
});
