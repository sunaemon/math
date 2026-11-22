import test from "node:test";
import assert from "node:assert/strict";
import { chatCallbackUrl } from "./chat-callback.ts";

test("OAuth callback relay accepts full and Safari scheme-less addresses", () => {
  const url = "http://127.0.0.1:1455/auth/callback?code=test-code&state=test-state&client_id=issued-client";
  assert.equal(chatCallbackUrl(`  ${url}  `), url);
  assert.equal(chatCallbackUrl(url.slice("http://".length)), url);
  assert.equal(
    chatCallbackUrl("http://127.0.0.1:1455/auth/callback?error=access_denied&state=test"),
    "http://127.0.0.1:1455/auth/callback?error=access_denied&state=test",
  );
});
test("empty, shortened and unrelated URLs get actionable errors without leaking codes", () => {
  for (const input of [
    "",
    "  ",
    "not a URL",
    "http://127.0.0.1",
    "http://127.0.0.1:1455/auth/callback",
    "http://127.0.0.1:1455/auth/callback?code=secret-code&state=…",
    "https://evil.test/auth/callback?code=secret-code&state=test",
    "http://127.0.0.1:1455/other?code=secret-code&state=test",
  ]) {
    assert.throws(
      () => chatCallbackUrl(input),
      (error) => {
        assert.doesNotMatch((error as Error).message, /secret-code|Invalid URL/);
        assert.match((error as Error).message, /URL/);
        return true;
      },
    );
  }
});
