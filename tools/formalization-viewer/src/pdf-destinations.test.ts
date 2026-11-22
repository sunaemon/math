import test from "node:test";
import assert from "node:assert/strict";
import { pdfDestination } from "./pdf-destinations.ts";

test("concurrent marker lookups read the name tree once and keep document caches separate", async () => {
  let reads = 0;
  const destination = [17, { name: "XYZ" }, 0, 100, null];
  const doc = {
    getDestination: async () => null,
    getDestinations: async () => {
      reads++;
      return { "booklink-entry-1": destination };
    },
  };
  const results = await Promise.all(Array.from({ length: 1000 }, () => pdfDestination(doc, "booklink-entry-1")));
  assert.ok(results.every((result) => result === destination));
  assert.equal(await pdfDestination(doc, "missing"), null);
  assert.equal(await pdfDestination(doc, "toString"), null);
  assert.equal(reads, 1);
  const peer = { getDestinations: async () => ({ "booklink-entry-1": [42] }) };
  assert.deepEqual(await pdfDestination(peer, "booklink-entry-1"), [42]);
});

test("a failed name-tree request can be retried", async () => {
  let reads = 0;
  const doc = {
    getDestinations: async () => {
      if (++reads === 1) throw new Error("interrupted");
      return { chapter: [0] };
    },
  };
  await assert.rejects(pdfDestination(doc, "chapter"), /interrupted/);
  assert.deepEqual(await pdfDestination(doc, "chapter"), [0]);
});

test("anchors omitted from the enumerated tree remain searchable and share fallback requests", async () => {
  let reads = 0;
  const doc = {
    getDestinations: async () => ({}),
    getDestination: async (name: string) => {
      reads++;
      return name === "chapter" ? [3] : null;
    },
  };
  assert.deepEqual(await Promise.all([pdfDestination(doc, "chapter"), pdfDestination(doc, "chapter")]), [[3], [3]]);
  assert.equal(reads, 1);
  assert.equal(await pdfDestination(doc, "missing"), null);
});
