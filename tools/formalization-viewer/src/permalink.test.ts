// Unit tests for the permalink encoding. Run with `node --test`. These pin the
// contract a shared link depends on: ids come from the Lean declaration name
// (not the shifting entry index), namesakes are disambiguated by ordinal, and
// rewriting the position leaves every other query parameter alone.

import { test } from "node:test";
import assert from "node:assert/strict";
import { markerId, markerIndex, readLocationParams, withLocationParams } from "./permalink.ts";

const entry = (declName?: string) => (declName ? { lean: { declName } } : {});

// The shape the polish-space sourcemap actually has: mostly unique declaration
// names, with a statement/proof pair sharing one name.
const ENTRIES = [
  entry("IsSeparableByCountableDense"),
  entry("closed_subspace_polish"),
  entry("open_subspace_polish"),
  entry("closed_subspace_polish"),
  entry(),
];

test("markerId names an entry by its declaration, with an ordinal only when shared", () => {
  assert.equal(markerId(ENTRIES, 0), "IsSeparableByCountableDense");
  assert.equal(markerId(ENTRIES, 2), "open_subspace_polish");
  assert.equal(markerId(ENTRIES, 1), "closed_subspace_polish~1");
  assert.equal(markerId(ENTRIES, 3), "closed_subspace_polish~2");
});

test("markerId falls back to a positional id for an entry with no declaration", () => {
  assert.equal(markerId(ENTRIES, 4), "@4");
  assert.equal(markerId(ENTRIES, 9), "");
});

test("markerIndex resolves the ids markerId produces", () => {
  for (const index of ENTRIES.keys()) {
    assert.equal(markerIndex(ENTRIES, markerId(ENTRIES, index)), index, `round trip for entry ${index}`);
  }
});

test("markerIndex survives links made before or after the markers moved", () => {
  // A link written when the name was unique still lands on the declaration.
  assert.equal(markerIndex(ENTRIES, "closed_subspace_polish"), 1);
  // An ordinal past the end of a still-present name falls back to its first
  // entry rather than failing: the declaration is what was asked for.
  assert.equal(markerIndex(ENTRIES, "closed_subspace_polish~7"), 1);
});

test("markerIndex reports an id this book does not have", () => {
  assert.equal(markerIndex(ENTRIES, "renamed_since_the_link"), null);
  assert.equal(markerIndex(ENTRIES, "@9"), null);
  assert.equal(markerIndex(ENTRIES, ""), null);
  assert.equal(markerIndex([], "closed_subspace_polish"), null);
});

test("withLocationParams rewrites the position and preserves the other params", () => {
  assert.equal(
    withLocationParams("?pdf=build%2Fbook-debug.pdf&debug", { marker: "closed_subspace_polish~2", skip: null }),
    "?pdf=build%2Fbook-debug.pdf&debug=&marker=closed_subspace_polish~2",
  );
  assert.equal(withLocationParams("", { marker: "foo", skip: null }), "?marker=foo");
});

test("withLocationParams keeps a marker and a skip from coexisting", () => {
  const marked = withLocationParams("", { marker: "foo", skip: null });
  assert.equal(withLocationParams(marked, { marker: null, skip: "polish-spaces-72" }), "?skip=polish-spaces-72");
  assert.equal(withLocationParams(marked, { marker: null, skip: null }), "");
});

test("readLocationParams reads back what withLocationParams wrote", () => {
  const search = withLocationParams("?pdf=x", { marker: "closed_subspace_polish~2", skip: null });
  assert.deepEqual(readLocationParams(search), { marker: "closed_subspace_polish~2", skip: null });
  assert.deepEqual(readLocationParams("?skip=polish-spaces-72"), { marker: null, skip: "polish-spaces-72" });
  assert.deepEqual(readLocationParams(""), { marker: null, skip: null });
});

test("batch marker IDs match stable URL identities including duplicate ordinals", async () => {
  const { markerIds } = await import("./permalink.ts");
  const entries = [{ lean: { declName: "same" } }, { lean: { declName: "other" } }, { lean: { declName: "same" } }, {}];
  assert.deepEqual(
    markerIds(entries),
    entries.map((_, index) => markerId(entries, index)),
  );
});
