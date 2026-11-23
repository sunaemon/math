// Compatibility for browsers without ReadableStream async iteration.
// Uses the reader API and preserves cancellation and lock release on early exit.
export function installStreamIterator(Stream = globalThis.ReadableStream) {
  if (!Stream || Stream.prototype[Symbol.asyncIterator]) return;
  Object.defineProperty(Stream.prototype, Symbol.asyncIterator, {
    configurable: true,
    writable: true,
    async *value({ preventCancel = false } = {}) {
      const reader = this.getReader();
      let finished = false;
      try {
        for (;;) {
          const result = await reader.read();
          if (result.done) { finished = true; return; }
          yield result.value;
        }
      } finally {
        try { if (!finished && !preventCancel) await reader.cancel(); }
        finally { reader.releaseLock(); }
      }
    },
  });
}
installStreamIterator();
