// Shared per-tab event stream for the formalization viewer.
//
// Browsers cap concurrent HTTP/1.x connections per origin (six in Chrome,
// shared across every tab), and an EventSource pins one connection for its
// lifetime. With separate /lsp/events and /watch/events streams each tab
// pinned two, so a third viewer tab saturated the pool and stalled every
// further request to the bridge, including the LSP handshake. Instead, one
// EventSource per tab subscribes to GET /events, which multiplexes both
// channels as named SSE events ("lsp" and "watch").
//
// The stream also carries the tab's session id: tools/formalization-viewer/server/serve.ts
// gives each session a dedicated Lean server, fully isolating tabs.
//
// The stream is a class with its connection, handlers, and session id held as
// instance fields rather than module-level mutable state, and its EventSource is
// injectable. Production constructs one shared instance (`eventStream`, exported
// below) and uses it throughout; tests construct their own EventStream with a
// fake source, so there is no module singleton to reset and no global to stub.

type StreamHandler = (data: string) => void;
type OpenHandler = (arg: { reconnect: boolean }) => void;

// The slice of EventSource this module depends on, so tests can inject a fake.
export interface EventSourceLike {
  addEventListener(type: string, listener: (event: { data: string }) => void): void;
  onopen: ((event?: unknown) => void) | null;
  onerror: ((event?: unknown) => void) | null;
  close(): void;
}
export type EventSourceFactory = (url: string) => EventSourceLike;

function defaultUuid(): string {
  return (
    globalThis.crypto?.randomUUID?.() || `c${Math.random().toString(36).slice(2)}${Math.random().toString(36).slice(2)}`
  );
}

function defaultEventSource(url: string): EventSourceLike {
  return new EventSource(url) as unknown as EventSourceLike;
}

export interface EventStreamOptions {
  // Defaults to `new EventSource(url)`; injected as a fake in tests.
  eventSource?: EventSourceFactory;
  // Defaults to crypto.randomUUID (with a Math.random fallback); pinned in tests.
  randomUuid?: () => string;
}

export class EventStream {
  readonly connId: string;
  readonly sessionQuery: string;

  private readonly makeSource: EventSourceFactory;
  private readonly handlers = new Map<string, Set<StreamHandler>>();
  private readonly openHandlers = new Set<OpenHandler>();
  private readonly errorHandlers = new Set<() => void>();
  private readonly attachedChannels = new Set<string>();
  private source: EventSourceLike | null = null;
  private openPromise: Promise<void> | null = null;

  constructor(options: EventStreamOptions = {}) {
    this.makeSource = options.eventSource ?? defaultEventSource;
    this.connId = (options.randomUuid ?? defaultUuid)();
    this.sessionQuery = `?session=${encodeURIComponent(this.connId)}`;
  }

  private attachChannel(channel: string): void {
    if (!this.source || this.attachedChannels.has(channel)) return;
    this.attachedChannels.add(channel);
    this.source.addEventListener(channel, (event) => {
      for (const handler of this.handlers.get(channel) || []) handler(event.data);
    });
  }

  onStreamEvent(channel: string, handler: StreamHandler): void {
    let set = this.handlers.get(channel);
    if (!set) {
      set = new Set();
      this.handlers.set(channel, set);
    }
    set.add(handler);
    this.attachChannel(channel);
  }

  // Open handlers fire on every successful (re)connect; `reconnect` is true when
  // the stream recovered from an error, meaning messages may have been missed
  // and the server on the other end may be a different process.
  onStreamOpen(handler: OpenHandler): void {
    this.openHandlers.add(handler);
  }

  onStreamError(handler: () => void): void {
    this.errorHandlers.add(handler);
  }

  // Open the shared stream (idempotent). Resolves once the stream is open, so
  // the bridge has registered this tab before the first request is sent — or on
  // the first connection error, so a missing bridge can never hang the caller.
  connectStream(): Promise<void> {
    if (this.openPromise) return this.openPromise;
    this.openPromise = new Promise<void>((resolve) => {
      const source = this.makeSource("/events" + this.sessionQuery);
      this.source = source;
      for (const channel of this.handlers.keys()) this.attachChannel(channel);
      let settled = false;
      let failed = false;
      const settle = () => {
        if (!settled) {
          settled = true;
          resolve();
        }
      };
      source.onopen = () => {
        const reconnect = failed;
        failed = false;
        settle();
        for (const handler of this.openHandlers) handler({ reconnect });
      };
      source.onerror = () => {
        failed = true;
        settle();
        for (const handler of this.errorHandlers) handler();
      };
    });
    return this.openPromise;
  }
}

// The single tab-wide stream the app uses throughout. Tests do not touch this;
// they construct their own EventStream with an injected fake source.
export const eventStream = new EventStream();
