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

test("accepts only the configured VPN IP and matching origins", () => {
  const host = "100.102.10.52";
  assert.ok(isTrustedRequest(`${host}:8765`, undefined, host));
  assert.ok(isTrustedRequest(`${host}:8765`, `http://${host}:8765`, host));
  assert.ok(!isTrustedRequest(`${host}:8765`, `http://${host}:9999`, host));
  assert.ok(!isTrustedRequest(`${host}:8765`, "https://attacker.test", host));
  assert.ok(!isTrustedRequest("100.102.10.53:8765", undefined, host));
  assert.ok(!isTrustedRequest("attacker.test:8765", "http://attacker.test:8765", host));
  assert.ok(!isTrustedRequest("127.0.0.1:8765", undefined, host));
  assert.ok(!isTrustedRequest(`${host}:8765`, undefined));
});

test("accepts bracketed IPv6 addresses with a matching origin", () => {
  assert.ok(isTrustedRequest("[::1]:8765", "http://[::1]:8765"));
  assert.ok(isTrustedRequest("[fd7a:115c:a1e0::1]:8765", "http://[fd7a:115c:a1e0::1]:8765", "fd7a:115c:a1e0::1"));
});

test("accepts only the configured DNS name and matching origins", () => {
  const host = "viewer.example.ts.net";
  assert.ok(isTrustedRequest(`${host}:8765`, undefined, host));
  assert.ok(isTrustedRequest(`${host}:8765`, `http://${host}:8765`, host));
  assert.ok(isTrustedRequest(`${host}:8765`, `http://${host}:8765`, host.toUpperCase() + "."));
  assert.ok(!isTrustedRequest(`${host}:8765`, `http://${host}:9999`, host));
  assert.ok(!isTrustedRequest(`${host}:8765`, "https://attacker.test", host));
  for (const other of ["attacker.test", "other.example.ts.net", "127.0.0.1", "100.102.10.52"]) {
    assert.ok(!isTrustedRequest(`${other}:8765`, `http://${other}:8765`, host));
  }
  assert.ok(!isTrustedRequest(`${host}:8765`, undefined));
});
