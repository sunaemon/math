// Unit tests for the copy-TeX shortcut's pure decision logic. Run with
// `node --test`. These pin the source-selection contract (the pane the reader
// last selected a marker in wins; peer requires a peer map and its pane still
// displayed) and the peer-path derivation used to fetch the peer document's
// tex from its own mount.

import { test } from "node:test";
import assert from "node:assert/strict";
import { copyTexSource, peerTexRelativePath } from "./copy-tex.ts";

test("copyTexSource follows a marker selected in the peer PDF pane", () => {
  assert.equal(copyTexSource(true, "peer", ["md", "pdf", "pdf-peer"]), "peer");
  assert.equal(copyTexSource(true, "peer", ["tex", "pdf-peer"]), "peer");
});

test("copyTexSource follows a marker selected in any project pane", () => {
  assert.equal(copyTexSource(true, "project", ["md", "pdf", "pdf-peer"]), "project");
  assert.equal(copyTexSource(true, "project", ["pdf-peer"]), "project");
});

test("copyTexSource reverts to the project when the peer pane is hidden or has no map", () => {
  assert.equal(copyTexSource(true, "peer", ["md", "lean", "tex", "pdf"]), "project");
  assert.equal(copyTexSource(false, "peer", ["md", "pdf", "pdf-peer"]), "project");
  assert.equal(copyTexSource(true, "peer", []), "project");
});

test("peerTexRelativePath strips the map root and the peer project dir", () => {
  // The shape the ja mount actually serves: absolute sourcemap paths, peer dir
  // "polish-space", yielding a path relative to the peer mount.
  assert.equal(
    peerTexRelativePath("/repo/polish-space/build/polish-space-book-debug.tex", "/repo", "polish-space"),
    "build/polish-space-book-debug.tex",
  );
});

test("peerTexRelativePath leaves already-relative paths and foreign roots intact", () => {
  assert.equal(peerTexRelativePath("build/book.tex", "", "polish-space"), "build/book.tex");
  assert.equal(peerTexRelativePath("/elsewhere/build/book.tex", "/repo", "polish-space"), "elsewhere/build/book.tex");
  // A trailing slash on the peer dir does not break the strip.
  assert.equal(peerTexRelativePath("polish-space/build/book.tex", "", "polish-space/"), "build/book.tex");
});
