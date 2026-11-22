import { test } from "node:test";
import assert from "node:assert/strict";
import { canonicalPdfPath, layoutPdfPath, pdfLayout } from "./pdf-layout.ts";
import { themedPdfPath } from "./pdf-theme.ts";
import { PDF_PAPER_KEY, PDF_FONT_SIZE_KEY, sharedPreference, withSharedPreferences } from "./session-store.ts";

test("layout paths compose with themes and retain canonical chapter identity", () => {
  for (const suffix of ["debug", "preview-polish-spaces", "preview-_index"]) {
    const original = `/book/build/book-${suffix}.pdf`;
    const variant = layoutPdfPath(original, "b6", "12");
    assert.equal(variant, `/book/build/book-layout-b6-12pt-${suffix}.pdf`);
    assert.equal(canonicalPdfPath(variant), original);
    assert.deepEqual(pdfLayout(variant), { paper: "b6", font: "12" });
    assert.equal(layoutPdfPath(variant, "b6", "12"), variant);
    assert.equal(layoutPdfPath(variant, "default", "default"), original);
    assert.equal(layoutPdfPath(themedPdfPath(original, true), "b6", "12"), themedPdfPath(variant, true));
  }
  assert.equal(layoutPdfPath("/book/book.pdf", "b6", "12"), "/book/book.pdf");
  assert.equal(layoutPdfPath("/book/book-debug.pdf", "$(bad)", "99"), "/book/book-debug.pdf");
});

test("page and font choices survive shared URLs and reject unknown values", () => {
  const search = withSharedPreferences("?marker=somewhere", { [PDF_PAPER_KEY]: "b5", [PDF_FONT_SIZE_KEY]: "11" });
  assert.equal(sharedPreference(search, PDF_PAPER_KEY), "b5");
  assert.equal(sharedPreference(search, PDF_FONT_SIZE_KEY), "11");
  assert.equal(new URLSearchParams(search).get("marker"), "somewhere");
  assert.equal(sharedPreference("?v=1&paper=evil", PDF_PAPER_KEY), null);
  assert.equal(sharedPreference("?v=1&fontSize=100", PDF_FONT_SIZE_KEY), null);
});
