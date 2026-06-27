// Port of tests/test_booklink_lsp_server.py::RequestProvenanceTest. Run with
// `node --test`.

import { test } from "node:test";
import assert from "node:assert/strict";
import { isTrustedRequest } from "./request-trust.ts";

test("accepts loopback same-origin request", () => {
  assert.ok(isTrustedRequest("127.0.0.1:8765", "http://127.0.0.1:8765"));
  assert.ok(isTrustedRequest("localhost:8765", "http://localhost:8765"));
});

test("rejects cross-origin POST source", () => {
  assert.ok(!isTrustedRequest("127.0.0.1:8765", "https://example.test"));
});

test("rejects DNS-rebinding host", () => {
  assert.ok(!isTrustedRequest("attacker.test:8765", "http://attacker.test:8765"));
});

test("rejects loopback origin with mismatched port", () => {
  assert.ok(!isTrustedRequest("127.0.0.1:8765", "http://127.0.0.1:9999"));
  assert.ok(!isTrustedRequest("127.0.0.1:8765", "http://127.0.0.1"));
});

test("accepts a request with no Origin header (same-origin navigation)", () => {
  assert.ok(isTrustedRequest("127.0.0.1:8765", undefined));
});
