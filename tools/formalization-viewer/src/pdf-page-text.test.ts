import test from "node:test";
import assert from "node:assert/strict";
import { pdfPageText } from "./pdf-page-text.ts";

test("layout, highlights and selection share one marked-content extraction per page", async () => {
  let reads = 0;
  const text = { items: [{ str: "Text" }, { type: "beginMarkedContent" }], styles: {} };
  const page = {
    getTextContent: async (options: unknown) => {
      assert.deepEqual(options, { includeMarkedContent: true });
      reads++;
      return text;
    },
  };
  const results = await Promise.all([pdfPageText(page), pdfPageText(page), pdfPageText(page)]);
  assert.ok(results.every((result) => result === text));
  assert.equal(reads, 1);
  assert.notEqual(await pdfPageText({ getTextContent: async () => ({ items: [] }) }), text);
});

test("interrupted page text extraction can be retried", async () => {
  let reads = 0;
  const page = {
    getTextContent: async () => {
      if (++reads === 1) throw new Error("interrupted");
      return { items: [] };
    },
  };
  await assert.rejects(pdfPageText(page), /interrupted/);
  assert.deepEqual(await pdfPageText(page), { items: [] });
});
