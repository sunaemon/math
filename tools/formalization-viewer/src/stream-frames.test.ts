// Unit tests for the pure SSE-frame parsers and the build-select request
// builder. Run with `node --test`.

import { test } from "node:test";
import assert from "node:assert/strict";
import { parseWatchPath, parseBuildStatus, selectPdfRequest } from "./stream-frames.ts";

test("parseWatchPath returns the path for a well-formed frame", () => {
  assert.equal(parseWatchPath('{"path":"src/a.md"}'), "src/a.md");
});

test("parseWatchPath rejects missing, blank, non-string paths and bad JSON", () => {
  assert.equal(parseWatchPath("{}"), null);
  assert.equal(parseWatchPath('{"path":""}'), null);
  assert.equal(parseWatchPath('{"path":5}'), null);
  assert.equal(parseWatchPath("not json"), null);
  assert.equal(parseWatchPath("null"), null);
});

test("parseBuildStatus returns the validated status, preserving extra fields", () => {
  assert.deepEqual(parseBuildStatus('{"dir":"polish-space","state":"building"}'), {
    dir: "polish-space",
    state: "building",
  });
  assert.deepEqual(parseBuildStatus('{"dir":"d","state":"done","pct":42}'), {
    dir: "d",
    state: "done",
    pct: 42,
  });
});

test("parseBuildStatus rejects missing/wrong-typed fields and bad JSON", () => {
  assert.equal(parseBuildStatus('{"dir":"d"}'), null);
  assert.equal(parseBuildStatus('{"state":"done"}'), null);
  assert.equal(parseBuildStatus('{"dir":1,"state":"done"}'), null);
  assert.equal(parseBuildStatus("not json"), null);
  assert.equal(parseBuildStatus("null"), null);
});

test("selectPdfRequest builds the POST target and body", () => {
  assert.deepEqual(selectPdfRequest("?session=x", "polish-space/build/a.pdf"), {
    url: "/build/select?session=x",
    body: '{"pdf":"polish-space/build/a.pdf"}',
  });
});

test("selectPdfRequest returns null for a blank path", () => {
  assert.equal(selectPdfRequest("?session=x", ""), null);
});
