// In-repo test harness for the viewer's browser modules — no npm dependency, in
// keeping with the project's vendor-everything toolchain. Provides fakes for the
// browser APIs the modules depend on so they can be driven under `node --test`.
//
// This file lives in src/testing/ so neither the esbuild bundle glob
// (src/*.ts, non-recursive) nor the test glob (src/*.test.ts) picks it up; test
// files import it explicitly via "./testing/harness.ts".

// A fake EventSource matching the EventSourceLike slice event-stream.ts depends
// on, plus controls (emit / triggerOpen / triggerError) so a test can drive the
// SSE lifecycle deterministically. Inject it via `new EventStream({ eventSource })`.
export class FakeEventSource {
  readonly url: string;
  onopen: ((event?: unknown) => void) | null = null;
  onerror: ((event?: unknown) => void) | null = null;
  closed = false;
  private readonly listeners = new Map<string, Set<(event: { data: string }) => void>>();

  constructor(url: string) {
    this.url = url;
  }

  addEventListener(type: string, listener: (event: { data: string }) => void): void {
    let set = this.listeners.get(type);
    if (!set) {
      set = new Set();
      this.listeners.set(type, set);
    }
    set.add(listener);
  }

  close(): void {
    this.closed = true;
  }

  // ---- test controls ----
  emit(type: string, data: string): void {
    for (const listener of this.listeners.get(type) || []) listener({ data });
  }
  triggerOpen(): void {
    this.onopen?.();
  }
  triggerError(): void {
    this.onerror?.();
  }
  hasChannel(type: string): boolean {
    return this.listeners.has(type);
  }
}

// An EventStream `eventSource` factory that records every source it creates, so a
// test can assert how many were opened (idempotency) and drive the latest one.
export function fakeEventSourceFactory() {
  const created: FakeEventSource[] = [];
  const factory = (url: string): FakeEventSource => {
    const source = new FakeEventSource(url);
    created.push(source);
    return source;
  };
  return {
    factory,
    created,
    last(): FakeEventSource {
      const source = created[created.length - 1];
      if (!source) throw new Error("no FakeEventSource has been created yet");
      return source;
    },
  };
}
