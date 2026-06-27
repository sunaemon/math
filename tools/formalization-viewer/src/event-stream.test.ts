// Unit tests for the multiplexed SSE event stream. Run with `node --test`.
//
// EventStream holds its connection/handlers/session id as instance fields and
// takes its EventSource as an injected factory, so each test drives a fresh
// `new EventStream({ eventSource })` with a FakeEventSource — no module singleton
// to reset and no global to stub.

import { test } from "node:test";
import assert from "node:assert/strict";
import { EventStream } from "./event-stream.ts";
import { fakeEventSourceFactory } from "./testing/harness.ts";

function makeStream(uuid = "test-id") {
  const sources = fakeEventSourceFactory();
  const stream = new EventStream({ eventSource: sources.factory, randomUuid: () => uuid });
  return { stream, sources };
}

test("derives connId and a URL-encoded sessionQuery from the injected uuid", () => {
  const { stream } = makeStream("abc-123");
  assert.equal(stream.connId, "abc-123");
  assert.equal(stream.sessionQuery, "?session=abc-123");

  const { stream: encoded } = makeStream("a b/c");
  assert.equal(encoded.sessionQuery, "?session=a%20b%2Fc");
});

test("connectStream opens exactly one source at /events and is idempotent", () => {
  const { stream, sources } = makeStream("x");
  const first = stream.connectStream();
  const second = stream.connectStream();
  assert.equal(sources.created.length, 1);
  assert.equal(sources.last().url, "/events?session=x");
  assert.equal(first, second); // memoized promise; no second connection
});

test("delivers a channel event to a handler registered before connect", () => {
  const { stream, sources } = makeStream();
  const got: string[] = [];
  stream.onStreamEvent("watch", (data) => got.push(data));
  stream.connectStream();
  sources.last().emit("watch", '{"path":"a.md"}');
  assert.deepEqual(got, ['{"path":"a.md"}']);
});

test("fans out to every handler on a channel and isolates channels", () => {
  const { stream, sources } = makeStream();
  const watch: string[] = [];
  const watch2: string[] = [];
  const build: string[] = [];
  stream.onStreamEvent("watch", (d) => watch.push(d));
  stream.onStreamEvent("watch", (d) => watch2.push(d));
  stream.onStreamEvent("build", (d) => build.push(d));
  stream.connectStream();
  sources.last().emit("watch", "W");
  assert.deepEqual(watch, ["W"]);
  assert.deepEqual(watch2, ["W"]);
  assert.deepEqual(build, []); // a watch frame must not reach the build channel
});

test("attaches a channel registered after connect", () => {
  const { stream, sources } = makeStream();
  stream.connectStream();
  const got: string[] = [];
  stream.onStreamEvent("lsp", (d) => got.push(d));
  assert.ok(sources.last().hasChannel("lsp"));
  sources.last().emit("lsp", "L");
  assert.deepEqual(got, ["L"]);
});

test("connectStream resolves when the source opens", async () => {
  const { stream, sources } = makeStream();
  let resolved = false;
  const done = stream.connectStream().then(() => {
    resolved = true;
  });
  assert.equal(resolved, false); // pending until open/error
  sources.last().triggerOpen();
  await done;
  assert.equal(resolved, true);
});

test("connectStream resolves on a connection error so a missing bridge never hangs", async () => {
  const { stream, sources } = makeStream();
  let resolved = false;
  const done = stream.connectStream().then(() => {
    resolved = true;
  });
  sources.last().triggerError();
  await done;
  assert.equal(resolved, true);
});

test("open handlers fire reconnect=false first, then reconnect=true after an error", () => {
  const { stream, sources } = makeStream();
  const opens: boolean[] = [];
  stream.onStreamOpen(({ reconnect }) => opens.push(reconnect));
  stream.connectStream();
  sources.last().triggerOpen(); // first connect
  sources.last().triggerError(); // drop
  sources.last().triggerOpen(); // recovery
  assert.deepEqual(opens, [false, true]);
});

test("error handlers fire on a connection error", () => {
  const { stream, sources } = makeStream();
  let errors = 0;
  stream.onStreamError(() => (errors += 1));
  stream.connectStream();
  sources.last().triggerError();
  assert.equal(errors, 1);
});

test("instances are isolated — one stream's handlers never see another's events", () => {
  const a = makeStream("a");
  const b = makeStream("b");
  const gotA: string[] = [];
  a.stream.onStreamEvent("watch", (d) => gotA.push(d));
  a.stream.connectStream();
  b.stream.connectStream();
  b.sources.last().emit("watch", "for-b");
  assert.deepEqual(gotA, []); // b's source is wholly separate
});
