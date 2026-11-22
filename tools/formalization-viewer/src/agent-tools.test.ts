import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import { viewerAgentTools, type ViewerAgentAdapter } from "./agent-tools.ts";

const catalog = JSON.parse(fs.readFileSync(new URL("../ai-catalog.json", import.meta.url), "utf8"));
function fixture() {
  let selected = -1,
    reads = 0;
  const entries = [
    {
      lean: {
        source: "/repo/book/lean/A.lean",
        declName: "example",
        declKind: "theorem",
        markerLine: 5,
        markerEndLine: 8,
        declLine: 9,
        declEndLine: 12,
      },
      booklink: { target: "prose", excerpt: "A quoted mathematical claim." },
      match: { status: "matched", source: "/repo/book/src/a.md", startLine: 20, endLine: 24 },
      texMatch: { status: "matched", source: "/repo/book/build/a.tex", startLine: 100, endLine: 110, entry: 7 },
    },
  ];
  const adapter: ViewerAgentAdapter = {
    state: () => ({ marker: selected === 0 ? "example" : null }),
    entries: () => entries,
    markerId: () => "example",
    markerIndex: (id) => (id === "example" ? 0 : null),
    path: (source) => (source ?? "").replace("/repo/book/", ""),
    sources: () => ["src/a.md", "lean/A.lean", "build/a.tex"],
    readSource: async () => {
      reads++;
      return "first\nsecond\nthird";
    },
    pdfLocation: () => ({ destination: "booklink-entry-7", page: 3 }),
    navigate: async (index) => {
      selected = index;
    },
    search: async (query, limit) => ({ query, limit, hits: [] }),
  };
  const tools = viewerAgentTools(catalog.entries[0].data.tools, adapter);
  const call = (name: string, args: unknown, signal?: AbortSignal) =>
    tools.find((tool) => tool.name === name)!.execute(args, { signal });
  return { call, adapter, reads: () => reads, selected: () => selected };
}
test("catalog-backed tools expose source and Lean correspondence without local filesystem roots", async () => {
  const { call } = fixture();
  const marker: any = await call("get_marker", { marker: "example" });
  assert.equal(marker.lean.source, "lean/A.lean");
  assert.equal(marker.lean.declarationStartLine, 9);
  assert.equal(marker.lean.markerStartLine, 5);
  assert.equal(marker.book.startLine, 20);
  assert.equal(marker.pdf.destination, "booklink-entry-7");
  assert.equal(JSON.stringify(marker).includes("/repo"), false);
  for (const line of [6, 10])
    assert.equal(((await call("find_markers_for_location", { source: "lean/A.lean", line })) as any).total, 1);
  assert.equal(((await call("find_markers_for_location", { source: "lean/A.lean", line: 30 })) as any).total, 0);
  assert.equal(((await call("list_markers", { query: "mathematical", limit: 1 })) as any).markers[0].marker, "example");
});
test("agent source reads validate exposed paths, bounded lines and unexpected arguments", async () => {
  const { call, reads } = fixture();
  assert.deepEqual(((await call("read_source", { source: "src/a.md", startLine: 2, endLine: 3 })) as any).lines, [
    { line: 2, text: "second" },
    { line: 3, text: "third" },
  ]);
  await assert.rejects(call("read_source", { source: "../../secret" }), /not exposed/);
  await assert.rejects(call("read_source", { source: "src/a.md", endLine: 201 }), /200/);
  await assert.rejects(call("search_book", { query: "x", limit: 51 }), /limit/);
  await assert.rejects(call("get_viewer_state", { credentials: true }), /arguments/);
  await assert.rejects(call("get_marker", { marker: "missing" }), /Unknown marker/);
  assert.equal(reads(), 1);
});
test("navigation updates the UI adapter and canceled calls do not navigate", async () => {
  const { call, selected } = fixture();
  const controller = new AbortController();
  controller.abort();
  await assert.rejects(call("navigate_marker", { marker: "example" }, controller.signal), { name: "AbortError" });
  assert.equal(selected(), -1);
  await call("navigate_marker", { marker: "example" });
  assert.equal(selected(), 0);
  assert.deepEqual(await call("get_viewer_state", {}), { marker: "example" });
});
