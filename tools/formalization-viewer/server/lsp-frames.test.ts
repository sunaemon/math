import assert from "node:assert/strict";
import test from "node:test";
import { LspFrames } from "./lsp-frames.ts";

function frame(body: string): Buffer {
  return Buffer.from(`Content-Length: ${Buffer.byteLength(body)}\r\n\r\n${body}`);
}

test("LSP frames support split UTF-8 messages and concatenated frames", () => {
  const reader = new LspFrames();
  const first = JSON.stringify({ text: "日本語" });
  const bytes = Buffer.concat([frame(first), frame("{}")]);
  const result = [];
  for (const byte of bytes) result.push(...reader.push(Buffer.from([byte])));
  assert.deepEqual(result, [first, "{}"]);
});

test("invalid, missing or duplicate LSP lengths fail without a backwards cursor", () => {
  for (const header of [
    "Content-Length: -1",
    "Content-Length: 1.5",
    "Content-Length: 1x",
    "Content-Length: NaN",
    "Content-Length: 9007199254740992",
    "Content-Type: application/json",
    "Content-Length: 2\r\nContent-Length: 2",
  ]) {
    assert.throws(() => new LspFrames().push(Buffer.from(`${header}\r\n\r\n{}`)), /LSP Content-Length/, header);
  }
  assert.deepEqual(new LspFrames().push(Buffer.from("Content-Length: 0\r\n\r\n")), [""]);
});
