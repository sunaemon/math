import { test } from "node:test";
import assert from "node:assert/strict";

import { BookBuilder } from "./book-builder.ts";
import type { Manifest } from "./projects.ts";

const MANIFEST: Manifest = {
  mount: "/bk",
  dir: "bk",
  served: { src: ["md", "json"], build: ["pdf", "json"] },
  pdf: "build/bk-debug.pdf",
  sourceMap: "build/bk-sourcemap.json",
};

// Drive BookBuilder against a harmless build command so notify() spawns `true`
// (exit 0, args ignored) instead of a real `make`. env is read in the
// constructor, so set/restore it around each builder.
function withBuilder(
  env: Record<string, string | undefined>,
  body: (builder: BookBuilder, logs: string[]) => Promise<void>,
): Promise<void> {
  const saved = { ...process.env };
  Object.assign(process.env, { BOOKLINK_MAKE: "true", BOOKLINK_AUTOBUILD_DEBOUNCE_MS: "5", ...env });
  const logs: string[] = [];
  const builder = new BookBuilder(process.cwd(), [MANIFEST], (m) => logs.push(m));
  return body(builder, logs).finally(async () => {
    await builder.shutdown();
    process.env = saved;
  });
}

async function waitFor(predicate: () => boolean, timeoutMs = 1000): Promise<void> {
  const start = Date.now();
  while (!predicate()) {
    if (Date.now() - start > timeoutMs) throw new Error("timed out waiting for condition");
    await new Promise((r) => setTimeout(r, 5));
  }
}

const spawned = (logs: string[]): string[] => logs.filter((m) => m.startsWith("book-builder: true "));
const finished = (logs: string[]): string[] => logs.filter((m) => m.includes("build finished"));

test("with no selection, a Markdown change builds the debug PDF + source map", () =>
  withBuilder({}, async (builder, logs) => {
    builder.notify("bk/src/polish-space-book/x.md");
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-debug.pdf bk/build/bk-sourcemap.json"]);
  }));

test("a release selection builds only the source map (release is never auto-built)", () =>
  withBuilder({}, async (builder, logs) => {
    builder.setSelection("s1", "bk/build/bk-book.pdf");
    builder.notify("bk/src/a.md");
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-sourcemap.json"]);
  }));

test("a chapter-preview selection builds that one preview PDF + source map", () =>
  withBuilder({}, async (builder, logs) => {
    builder.setSelection("s1", "bk/build/bk-preview-polish-spaces.pdf");
    builder.notify("bk/src/a.md");
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), [
      "book-builder: true bk/build/bk-preview-polish-spaces.pdf bk/build/bk-sourcemap.json",
    ]);
  }));

test("switching selection to a different PDF rebuilds that target", () =>
  withBuilder({ BOOKLINK_AUTOBUILD_DEBOUNCE_MS: "10" }, async (builder, logs) => {
    builder.setSelection("s1", "bk/build/bk-debug.pdf"); // initial: records only, no build
    builder.setSelection("s1", "bk/build/bk-preview-cantor-baire-space.pdf"); // change: rebuilds the preview
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), [
      "book-builder: true bk/build/bk-preview-cantor-baire-space.pdf bk/build/bk-sourcemap.json",
    ]);
  }));

test("a preview selection whose chapter is not a plain identifier is dropped (no make-target injection)", () =>
  withBuilder({}, async (builder, logs) => {
    // The chapter component becomes the make stem ($*), which the preview recipe
    // interpolates into a shell-evaluated LuaLaTeX command. A selection carrying
    // shell metacharacters must never reach `make`; it is dropped, leaving only
    // the fixed source-map target.
    builder.setSelection("s1", "bk/build/bk-preview-$(touch pwned).pdf");
    builder.notify("bk/src/a.md");
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-sourcemap.json"]);
  }));

test("a project-relative selection (missing the dir prefix) is ignored, falling back to debug", () =>
  withBuilder({}, async (builder, logs) => {
    // The client must report a repo-relative path ("bk/build/..."). A
    // project-relative one ("build/...") matches no job prefix, so the selection
    // is dropped and the build resolves to the debug-PDF default, not the diff.
    builder.setSelection("s1", "build/bk-diff.pdf");
    builder.notify("bk/src/a.md");
    await waitFor(() => finished(logs).length === 1);
    assert.deepEqual(spawned(logs), ["book-builder: true bk/build/bk-debug.pdf bk/build/bk-sourcemap.json"]);
  }));

test("non-Markdown and out-of-tree changes do not build", () =>
  withBuilder({}, async (builder, logs) => {
    builder.notify("bk/build/bk-debug.tex"); // build output, not a source
    builder.notify("bk/lean/Foo.lean"); // a Lean source, not Markdown
    builder.notify("other/src/x.md"); // a different project's source
    await new Promise((r) => setTimeout(r, 40));
    assert.equal(spawned(logs).length, 0);
  }));

test("rapid saves within the debounce window coalesce into one build", () =>
  withBuilder({ BOOKLINK_AUTOBUILD_DEBOUNCE_MS: "30" }, async (builder, logs) => {
    builder.notify("bk/src/a.md");
    builder.notify("bk/src/b.md");
    builder.notify("bk/src/a.md");
    await waitFor(() => finished(logs).length === 1);
    await new Promise((r) => setTimeout(r, 40));
    assert.equal(spawned(logs).length, 1);
  }));

test("BOOKLINK_AUTOBUILD=0 disables auto-building", () =>
  withBuilder({ BOOKLINK_AUTOBUILD: "0" }, async (builder, logs) => {
    builder.notify("bk/src/a.md");
    await new Promise((r) => setTimeout(r, 40));
    assert.equal(spawned(logs).length, 0);
  }));
