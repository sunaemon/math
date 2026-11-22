// Unit tests for the per-project reading session. Run with `node --test`. These
// pin the merge/clear semantics navigation relies on, the tolerance for stale or
// corrupt stored JSON, and the requirement that unavailable storage degrades to
// an empty session instead of throwing.

import { test } from "node:test";
import assert from "node:assert/strict";
import {
  readSession,
  writeSession,
  sessionKey,
  sharedPreference,
  withSharedPreferences,
  PDF_MODE_KEY,
  removeUrlManagedStorage,
  type StorageLike,
} from "./session-store.ts";

function fakeStorage(initial: Record<string, string> = {}): StorageLike & { data: Record<string, string> } {
  const data = { ...initial };
  return {
    data,
    getItem: (key) => data[key] ?? null,
    setItem: (key, value) => {
      data[key] = value;
    },
    removeItem: (key) => {
      delete data[key];
    },
    key: (index) => Object.keys(data)[index] ?? null,
    get length() {
      return Object.keys(data).length;
    },
  };
}

const KEY = sessionKey("/polish-space");

test("versioned URLs share layout and PDF mode while preserving position links", () => {
  const key = "formalization-viewer-layout-v2";
  const layout = JSON.stringify({ tree: { dir: "row", children: [{ pane: "md" }, { pane: "pdf" }], ratios: [3, 1] } });
  const search = withSharedPreferences("?marker=example~2&pdf=book.pdf&debug", {
    [key]: layout,
    [PDF_MODE_KEY]: "full",
    "formalization-viewer-code-font": "monaco",
    "formalization-viewer-appearance-mode": "dark",
  });
  const params = new URLSearchParams(search);
  assert.equal(params.get("v"), "1");
  assert.equal(params.get("marker"), "example~2");
  assert.equal(params.get("pdf"), "book.pdf");
  assert.ok(search.includes("layout=row(md:3,pdf:1)"), search);
  assert.equal(sharedPreference(search, key), layout);
  assert.equal(sharedPreference(search, PDF_MODE_KEY), "full");
  assert.equal(params.has("font"), false);
  assert.equal(params.has("theme"), false);
  assert.equal(sharedPreference("?v=1&font=monaco", "formalization-viewer-code-font"), null);
});

test("default chapter mode and default layout are omitted from the URL", () => {
  const key = "formalization-viewer-layout-v2";
  const layout = JSON.stringify({ tree: { pane: "md" } });
  const params = new URLSearchParams(
    withSharedPreferences(
      "?v=1&pdfMode=full&layout=old&marker=example",
      {
        [key]: layout,
        [PDF_MODE_KEY]: "chapter",
      },
      { [key]: layout },
    ),
  );
  assert.equal(params.has("layout"), false);
  assert.equal(params.has("pdfMode"), false);
  assert.equal(params.get("marker"), "example");
});

test("compact layouts represent nested directions, pane order, ratios and focus", () => {
  const key = "formalization-viewer-layout-v2";
  const tree = {
    dir: "row",
    children: [{ pane: "pdf" }, { dir: "col", children: [{ pane: "md" }, { pane: "lean" }], ratios: [1, 1] }],
    ratios: [3, 2],
  };
  const search = withSharedPreferences("?marker=example", { [key]: JSON.stringify({ tree, maximized: "pdf" }) });
  assert.ok(search.includes("layout=row(pdf:3,col(md,lean):2)"), search);
  assert.equal(new URLSearchParams(search).get("focus"), "pdf");
  assert.deepEqual(JSON.parse(sharedPreference(search, key)!), { tree, maximized: "pdf" });
});

test("maximizing the default tree writes only focus and restoring removes it", () => {
  const key = "formalization-viewer-layout-v2";
  const tree = { dir: "row", children: [{ pane: "pdf" }, { pane: "md" }], ratios: [1, 1] };
  const defaults = { [key]: JSON.stringify({ tree }) };
  const search = withSharedPreferences("?v=1", { [key]: JSON.stringify({ tree, maximized: "pdf" }) }, defaults);
  assert.equal(search, "?v=1&focus=pdf");
  assert.deepEqual(JSON.parse(sharedPreference(search, key)!), { maximized: "pdf" });
  assert.equal(withSharedPreferences(search, defaults, defaults), "?v=1");
});

test("JSON links are read and rewritten without changing v=1 or losing unrelated parameters", () => {
  const key = "formalization-viewer-layout-v2";
  const layout = JSON.stringify({ tree: { pane: "md" }, maximized: "md" });
  const legacy = `?v=1&layout=${encodeURIComponent(layout)}&marker=example~2&custom=a%26b%23c`;
  assert.equal(sharedPreference(legacy, key), layout);
  const rewritten = withSharedPreferences(legacy, { [PDF_MODE_KEY]: "full" });
  assert.ok(rewritten.includes("layout=md"), rewritten);
  assert.equal(new URLSearchParams(rewritten).get("focus"), "md");
  assert.equal(new URLSearchParams(rewritten).get("custom"), "a&b#c");
  assert.equal(new URLSearchParams(rewritten).get("v"), "1");
  assert.deepEqual(JSON.parse(sharedPreference(rewritten, key)!), JSON.parse(layout));
});

test("drag ratios become small proportional integers and equal ratios disappear", () => {
  const key = "formalization-viewer-layout-v2";
  const layout = (ratios: number[]) =>
    JSON.stringify({ tree: { dir: "row", children: [{ pane: "pdf" }, { pane: "md" }], ratios } });
  assert.ok(withSharedPreferences("", { [key]: layout([0.75, 0.25]) }).includes("layout=row(pdf:3,md:1)"));
  assert.ok(withSharedPreferences("", { [key]: layout([3, 3]) }).includes("layout=row(pdf,md)"));
  const search = withSharedPreferences("", { [key]: layout([1 / 3, 2 / 3]) });
  const tree = JSON.parse(sharedPreference(search, key)!).tree;
  assert.ok(Math.abs(tree.ratios[0] / tree.ratios[1] - 0.5) < 0.0002);
});

test("malformed compact layouts cannot produce partial trees or consume unbounded nesting", () => {
  const key = "formalization-viewer-layout-v2";
  for (const layout of [
    "row()",
    "row(pdf,)",
    "row(pdf,md",
    "row(pdf,pdf)",
    "row(pdf:0,md)",
    "row(pdf:-1,md)",
    "row(pdf:Infinity,md)",
    "pdf:3",
    "pdf)extra",
    "row(".repeat(30) + "pdf" + ")".repeat(30),
    "x".repeat(8193),
  ]) {
    assert.equal(sharedPreference(`?v=1&layout=${encodeURIComponent(layout)}`, key), null, layout);
  }
  assert.equal(sharedPreference("?v=1&layout=pdf&focus=bad%26value", key), null);
});

test("migration removes URL-owned storage without removing reader or appearance state", () => {
  const storage = fakeStorage({
    "formalization-viewer-layout-v2": '{"tree":{"pane":"lean"}}',
    [PDF_MODE_KEY]: "full",
    [KEY]: JSON.stringify({ pdf: "book-debug.pdf", md: "chapter.md", marker: "example" }),
    "formalization-viewer-code-font": "monaco",
  });
  removeUrlManagedStorage(storage);
  assert.equal(storage.getItem("formalization-viewer-layout-v2"), null);
  assert.equal(storage.getItem(PDF_MODE_KEY), null);
  assert.deepEqual(JSON.parse(storage.getItem(KEY)!), { md: "chapter.md", marker: "example" });
  assert.equal(storage.getItem("formalization-viewer-code-font"), "monaco");
});

test("unknown URL versions and malformed layouts are not reinterpreted", () => {
  const key = "formalization-viewer-layout-v2";
  const future = "?v=2&layout=future-format&marker=example";
  assert.equal(sharedPreference(future, key), null);
  assert.equal(withSharedPreferences(future, { [key]: '{"tree":{"pane":"md"}}' }), future);
  assert.equal(sharedPreference("?v=1&layout=not-json", key), null);
  assert.equal(sharedPreference("?v=1&layout=[]", key), null);
  assert.equal(sharedPreference("?layout={}", key), null);
});

test("sessionKey scopes the session to the project mount", () => {
  assert.notEqual(sessionKey("/polish-space"), sessionKey("/polish-space-ja"));
  assert.ok(sessionKey("").length > 0, "a mountless project still needs a key");
});

test("writeSession merges into what is stored and clears on an explicit null", () => {
  const storage = fakeStorage();
  writeSession(storage, KEY, { marker: "closed_subspace_polish~2", lean: "lean/Example.lean" });
  const withFile = writeSession(storage, KEY, { md: "src/book/polish-spaces.md" });
  assert.equal(withFile.marker, "closed_subspace_polish~2", "an absent field keeps its stored value");
  assert.equal(withFile.lean, "lean/Example.lean");
  assert.equal(withFile.md, "src/book/polish-spaces.md");

  // Moving to a skip clears the marker position, and back again clears the skip.
  const skipped = writeSession(storage, KEY, { marker: null, skip: "polish-spaces-72", skipProgress: 0.5 });
  assert.deepEqual([skipped.marker, skipped.skip, skipped.skipProgress], [null, "polish-spaces-72", 0.5]);
  const marked = writeSession(storage, KEY, { marker: "open_subspace_polish", skip: null, skipProgress: null });
  assert.deepEqual([marked.marker, marked.skip], ["open_subspace_polish", null]);
  assert.equal(marked.lean, "lean/Example.lean", "the position write leaves the open documents alone");
});

test("readSession returns an empty session for missing, corrupt, or foreign values", () => {
  assert.equal(readSession(fakeStorage(), KEY).marker, null);
  assert.equal(readSession(fakeStorage({ [KEY]: "{not json" }), KEY).marker, null);
  assert.equal(readSession(fakeStorage({ [KEY]: "[1,2,3]" }), KEY).marker, null);
  // Wrong types from an older/hand-edited value must not reach navigation.
  const wrongTypes = readSession(fakeStorage({ [KEY]: '{"marker":42,"skipProgress":"half","md":""}' }), KEY);
  assert.deepEqual([wrongTypes.marker, wrongTypes.skipProgress, wrongTypes.md], [null, null, null]);
});

test("a viewer whose storage is unavailable still gets a session", () => {
  const blocked: StorageLike = {
    getItem: () => {
      throw new Error("storage disabled");
    },
    setItem: () => {
      throw new Error("storage disabled");
    },
  };
  assert.equal(readSession(blocked, KEY).marker, null);
  assert.equal(writeSession(blocked, KEY, { marker: "foo" }).marker, "foo");
  assert.equal(readSession(null, KEY).marker, null);
});

test("browser preferences survive disabled storage, including a throwing property getter", async () => {
  const { browserStorage, readPreference, writePreference } = await import("./session-store.ts");
  const previous = Object.getOwnPropertyDescriptor(globalThis, "localStorage");
  try {
    Object.defineProperty(globalThis, "localStorage", {
      configurable: true,
      get() {
        throw new Error("denied");
      },
    });
    assert.equal(browserStorage(), null);
    assert.equal(readPreference("layout"), null);
    assert.doesNotThrow(() => writePreference("layout", "value"));
  } finally {
    if (previous) Object.defineProperty(globalThis, "localStorage", previous);
    else Reflect.deleteProperty(globalThis, "localStorage");
  }
});
