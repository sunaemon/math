import test from "node:test";
import assert from "node:assert/strict";
import { installStreamIterator } from "../vendor/pdfjs/stream-iterator.mjs";

test("legacy stream readers support PDF async iteration and release their locks", async () => {
  let released = 0,
    cancelled = 0;
  class LegacyStream {
    getReader() {
      let n = 0;
      return {
        read: async () => (n++ ? { done: true } : { done: false, value: "PDF text" }),
        releaseLock: () => released++,
        cancel: async () => {
          cancelled++;
        },
      };
    }
  }
  installStreamIterator(LegacyStream);
  const values = [];
  for await (const value of new LegacyStream() as any) values.push(value);
  assert.deepEqual(values, ["PDF text"]);
  assert.equal(released, 1);
  assert.equal(cancelled, 0);
  for await (const value of new LegacyStream() as any) {
    assert.equal(value, "PDF text");
    break;
  }
  assert.equal(released, 2);
  assert.equal(cancelled, 1);
  const prototype = LegacyStream.prototype as unknown as Record<symbol, unknown>;
  const original = prototype[Symbol.asyncIterator];
  installStreamIterator(LegacyStream);
  assert.equal(prototype[Symbol.asyncIterator], original);
});
