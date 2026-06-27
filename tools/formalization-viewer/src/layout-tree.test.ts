// Unit tests for the pure pane-layout tree algebra. Run with `node --test`.
// These pin the invariants the drag-and-drop / persistence glue in app.ts relies
// on: splits collapse to a single child when a leaf is removed, same-direction
// nesting flattens, and validateTree rejects unknown or duplicated panes and
// repairs ratios.

import { test } from "node:test";
import assert from "node:assert/strict";
import {
  PANE_NAMES,
  defaultTree,
  makeSplit,
  treeLeaves,
  treeKind,
  validateTree,
  removeLeaf,
  replaceLeaf,
  flattenSameDir,
  addLeaf,
} from "./layout-tree.ts";

test("makeSplit: empty -> null, single -> bare leaf, many -> split with unit ratios", () => {
  assert.equal(makeSplit("row", []), null);
  assert.deepEqual(makeSplit("row", ["pdf"]), { pane: "pdf" });
  assert.deepEqual(makeSplit("row", ["pdf", "md"]), {
    dir: "row",
    children: [{ pane: "pdf" }, { pane: "md" }],
    ratios: [1, 1],
  });
});

test("defaultTree is a row of every pane except tex", () => {
  assert.deepEqual(
    treeLeaves(defaultTree()),
    PANE_NAMES.filter((p) => p !== "tex"),
  );
});

test("treeLeaves collects pane names in order", () => {
  assert.deepEqual(treeLeaves(null), []);
  assert.deepEqual(treeLeaves({ pane: "md" }), ["md"]);
  assert.deepEqual(treeLeaves(makeSplit("col", ["pdf", "md", "lean"])), ["pdf", "md", "lean"]);
});

test("treeKind classifies leaf rows/cols and nested splits", () => {
  assert.equal(treeKind(null), "columns");
  assert.equal(treeKind({ pane: "pdf" }), "columns");
  assert.equal(treeKind(makeSplit("row", ["pdf", "md"])), "columns");
  assert.equal(treeKind(makeSplit("col", ["pdf", "md"])), "rows");
  const nested = {
    dir: "row" as const,
    children: [{ pane: "pdf" }, makeSplit("col", ["md", "lean"])!],
    ratios: [1, 1],
  };
  assert.equal(treeKind(nested), "others");
});

test("validateTree accepts known panes and rejects unknown ones", () => {
  assert.equal(validateTree(null), null);
  assert.deepEqual(validateTree({ pane: "pdf" }), { pane: "pdf" });
  assert.equal(validateTree({ pane: "bogus" }), null);
  assert.equal(validateTree({ dir: "diag", children: [{ pane: "pdf" }] }), null);
  assert.equal(validateTree({ dir: "row", children: "nope" }), null);
});

test("validateTree drops duplicate panes and collapses to a single survivor", () => {
  assert.deepEqual(validateTree({ dir: "row", children: [{ pane: "pdf" }, { pane: "pdf" }] }), { pane: "pdf" });
});

test("validateTree repairs ratios: bad length -> all ones, non-positive -> 1", () => {
  assert.deepEqual(validateTree({ dir: "row", children: [{ pane: "pdf" }, { pane: "md" }], ratios: [2, 3] }), {
    dir: "row",
    children: [{ pane: "pdf" }, { pane: "md" }],
    ratios: [2, 3],
  });
  assert.deepEqual(validateTree({ dir: "row", children: [{ pane: "pdf" }, { pane: "md" }], ratios: [0, -4] }), {
    dir: "row",
    children: [{ pane: "pdf" }, { pane: "md" }],
    ratios: [1, 1],
  });
  assert.deepEqual(validateTree({ dir: "row", children: [{ pane: "pdf" }, { pane: "md" }], ratios: [9] }), {
    dir: "row",
    children: [{ pane: "pdf" }, { pane: "md" }],
    ratios: [1, 1],
  });
});

test("removeLeaf collapses a split that falls to one child", () => {
  assert.equal(removeLeaf({ pane: "pdf" }, "pdf"), null);
  assert.deepEqual(removeLeaf({ pane: "pdf" }, "md"), { pane: "pdf" });
  assert.deepEqual(removeLeaf(makeSplit("row", ["pdf", "md"]), "md"), { pane: "pdf" });
});

test("removeLeaf keeps the surviving children's ratios", () => {
  const tree = {
    dir: "row" as const,
    children: [{ pane: "pdf" }, { pane: "md" }, { pane: "lean" }],
    ratios: [5, 6, 7],
  };
  assert.deepEqual(removeLeaf(tree, "md"), {
    dir: "row",
    children: [{ pane: "pdf" }, { pane: "lean" }],
    ratios: [5, 7],
  });
});

test("replaceLeaf swaps a target leaf and leaves others alone", () => {
  assert.deepEqual(replaceLeaf({ pane: "pdf" }, "pdf", { pane: "md" }), { pane: "md" });
  assert.deepEqual(replaceLeaf({ pane: "pdf" }, "lean", { pane: "md" }), { pane: "pdf" });
  assert.deepEqual(replaceLeaf(makeSplit("row", ["pdf", "md"]), "md", { pane: "lean" }), {
    dir: "row",
    children: [{ pane: "pdf" }, { pane: "lean" }],
    ratios: [1, 1],
  });
});

test("addLeaf appends, wrapping a bare leaf into a row", () => {
  assert.deepEqual(addLeaf(null, "pdf"), { pane: "pdf" });
  assert.deepEqual(addLeaf({ pane: "pdf" }, "md"), {
    dir: "row",
    children: [{ pane: "pdf" }, { pane: "md" }],
    ratios: [1, 1],
  });
  assert.deepEqual(addLeaf({ dir: "row", children: [{ pane: "pdf" }, { pane: "md" }], ratios: [2, 3] }, "lean"), {
    dir: "row",
    children: [{ pane: "pdf" }, { pane: "md" }, { pane: "lean" }],
    ratios: [2, 3, 1],
  });
});

test("flattenSameDir merges nested same-direction splits but not cross-direction", () => {
  const sameDir = {
    dir: "row" as const,
    children: [{ pane: "pdf" }, { dir: "row" as const, children: [{ pane: "md" }, { pane: "lean" }], ratios: [1, 1] }],
    ratios: [1, 1],
  };
  assert.deepEqual(flattenSameDir(sameDir), {
    dir: "row",
    children: [{ pane: "pdf" }, { pane: "md" }, { pane: "lean" }],
    ratios: [1, 1, 1],
  });

  const crossDir = {
    dir: "row" as const,
    children: [{ pane: "pdf" }, { dir: "col" as const, children: [{ pane: "md" }, { pane: "lean" }], ratios: [1, 1] }],
    ratios: [1, 1],
  };
  assert.deepEqual(flattenSameDir(crossDir), crossDir);
});
