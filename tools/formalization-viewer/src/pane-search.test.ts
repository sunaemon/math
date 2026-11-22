import assert from "node:assert/strict";
import test from "node:test";
import { findInLines, findInPdf } from "./pane-search.ts";
test("pane search preserves lines, normalizes width/case, and limits results", () => {
  assert.deepEqual(
    findInLines("first\nＦＯＯ bar\nfoo baz", "foo").map((hit) => hit.line),
    [2, 3],
  );
  assert.equal(findInLines("x\nx\nx", "x", 2).length, 2);
  assert.deepEqual(findInLines("x", " "), []);
});
test("PDF search spans Japanese text items and retains page and line geometry", async () => {
  const doc = { numPages: 2, getPage: async (number: number) => ({ number, view: [0, 0, 100, 100] }) };
  const hits = await findInPdf(
    doc,
    "可算稠密",
    () => true,
    async (page: any) => ({
      items: [
        { str: "可算", transform: [1, 0, 0, 1, 0, 80] },
        { str: "稠密集合", transform: [1, 0, 0, 1, 10, 80] },
        { str: String(page.number), transform: [1, 0, 0, 1, 20, 80] },
      ],
    }),
  );
  assert.deepEqual(
    hits.map((hit) => hit.page),
    [1, 2],
  );
  assert.ok(Math.abs(hits[0].fraction! - 0.2) < 1e-10);
  let calls = 0;
  await findInPdf(
    doc,
    "x",
    () => false,
    async () => {
      calls++;
      return { items: [] };
    },
  );
  assert.equal(calls, 0);
});

test("prefetch targets distinct result pages ahead and behind, bounded to three", async () => {
  const { nearbyHitPages } = await import("./pane-search.ts");
  const hits = [1, 1, 2, 2, 4, 4, 7, 9].map((page) => ({ title: "", excerpt: "", page }));
  assert.deepEqual(nearbyHitPages(hits, 2), [4, 7, 1]);
  assert.deepEqual(nearbyHitPages(hits, 0), [2, 4]);
  assert.deepEqual(nearbyHitPages(hits, 7), [7]);
  assert.deepEqual(nearbyHitPages([], 0), []);
});

test("PDF batches resume inside a page without rescanning or skipping matches", async () => {
  const { PaneSearchSession, pdfHits } = await import("./pane-search.ts");
  let pages = 0;
  const doc = {
    numPages: 1,
    getPage: async () => {
      pages++;
      return { view: [0, 0, 100, 100] };
    },
  };
  const session = new PaneSearchSession(
    pdfHits(
      doc,
      "x",
      () => true,
      async () => ({ items: [{ str: "x ".repeat(450), transform: [1, 0, 0, 1, 0, 80] }] }),
    ),
    () => true,
  );
  await Promise.all([session.loadMore(), session.loadMore()]);
  assert.equal(session.hits.length, 200);
  assert.equal(session.hasMore, true);
  await session.loadMore();
  assert.equal(session.hits.length, 400);
  assert.equal(session.hasMore, true);
  await session.loadMore();
  assert.equal(session.hits.length, 450);
  assert.equal(session.hasMore, false);
  assert.equal(pages, 1);
});

test("line batches have no overlap and exactly 200 matches are reported as complete", async () => {
  const { PaneSearchSession, lineHits } = await import("./pane-search.ts");
  const session = new PaneSearchSession(lineHits("x\n".repeat(525), "x"), () => true);
  await session.loadMore();
  await session.loadMore();
  await session.loadMore();
  assert.deepEqual(
    session.hits.map((hit) => hit.line),
    Array.from({ length: 525 }, (_, i) => i + 1),
  );
  assert.equal(session.hasMore, false);
  const exact = new PaneSearchSession(lineHits("x\n".repeat(200), "x"), () => true);
  await exact.loadMore();
  assert.equal(exact.hits.length, 200);
  assert.equal(exact.hasMore, false);
});

test("canceling while a batch is pending discards its results", async () => {
  const { PaneSearchSession } = await import("./pane-search.ts");
  let current = true;
  let release!: () => void;
  const wait = new Promise<void>((resolve) => {
    release = resolve;
  });
  async function* hits() {
    await wait;
    yield { title: "old", excerpt: "old" };
  }
  const session = new PaneSearchSession(hits(), () => current);
  const pending = session.loadMore();
  current = false;
  release();
  await pending;
  assert.deepEqual(session.hits, []);
});
