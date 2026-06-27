// The Lean LSP bridge and per-session registry for the formalization viewer.
//
// Each browser tab carries its own `session` id and gets a dedicated
// `lake env lean --server`, spawned lazily on first use and reaped a short grace
// period after the tab's event stream closes. This isolates tabs completely: no
// shared document state, no cross-tab id collisions, and one tab's
// reload/restart never disturbs another.
//
// Node runs single-threaded, so the locks the Python original needed are gone:
// any run of synchronous code is atomic, and the only interleavings happen at
// `await` points. The one contract that still matters is that a grace-period
// reaper (a timer) must not tear a bridge down while a send is in flight (the
// send `await`s spawning/writing); the in-flight counter below preserves it.

import { spawn } from "node:child_process";
import type { ChildProcessByStdio } from "node:child_process";
import type { Writable, Readable } from "node:stream";
import { killGroup, terminate } from "./process-group.ts";

// stdio: ["pipe", "pipe", "ignore"] -> stdin/stdout present, stderr ignored.
type LeanProc = ChildProcessByStdio<Writable, Readable, null>;

export interface Sink {
  put(text: string): void;
}

export interface BridgeLike {
  root: string;
  running(): boolean;
  hasClients(): boolean;
  subscribe(sink: Sink): void;
  unsubscribe(sink: Sink): void;
  send(text: string): Promise<void>;
  shutdown(): Promise<void>;
}

function isInitialize(text: string): boolean {
  try {
    const message = JSON.parse(text);
    return message !== null && typeof message === "object" && message.method === "initialize";
  } catch {
    return false;
  }
}

const BRIDGE_CLOSED = JSON.stringify({ jsonrpc: "2.0", method: "$/bridge/closed", params: {} });

export class LeanBridge implements BridgeLike {
  root: string;
  private proc: LeanProc | null = null;
  private epoch = 0;
  private clients = new Set<Sink>();

  constructor(root: string) {
    this.root = root;
  }

  running(): boolean {
    return this.proc !== null && this.proc.exitCode === null && this.proc.signalCode === null;
  }

  private spawnProcess(): void {
    this.epoch += 1;
    const epoch = this.epoch;
    // detached puts the server in its own process group so we can signal the
    // whole tree (lake -> lean) and never orphan the child.
    const proc = spawn("lake", ["env", "lean", "--server"], {
      cwd: this.root,
      stdio: ["pipe", "pipe", "ignore"],
      detached: true,
    });
    this.proc = proc;

    let buffer = Buffer.alloc(0);
    let dead = false;
    // Only announce closure for the still-current server, so an intentional
    // restart does not surface as a crash to the new client.
    const announceClosed = (): void => {
      if (dead) return;
      dead = true;
      if (epoch === this.epoch) this.broadcast(BRIDGE_CLOSED);
    };

    proc.stdout.on("data", (chunk: Buffer) => {
      if (dead) return;
      buffer = Buffer.concat([buffer, chunk]);
      for (;;) {
        const headerEnd = buffer.indexOf("\r\n\r\n");
        if (headerEnd < 0) return;
        let length = 0;
        let malformed = false;
        for (const line of buffer.subarray(0, headerEnd).toString("latin1").split("\r\n")) {
          if (line.toLowerCase().startsWith("content-length:")) {
            const parsed = Number.parseInt(line.slice(line.indexOf(":") + 1).trim(), 10);
            if (Number.isNaN(parsed)) {
              malformed = true;
            } else {
              length = parsed;
            }
          }
        }
        if (malformed) {
          // Treat like a dropped server so clients self-heal.
          announceClosed();
          killGroup(proc, "SIGTERM");
          return;
        }
        const bodyStart = headerEnd + 4;
        if (buffer.length - bodyStart < length) return;
        const body = buffer.subarray(bodyStart, bodyStart + length).toString("utf-8");
        buffer = buffer.subarray(bodyStart + length);
        this.broadcast(body);
      }
    });
    proc.stdout.on("end", announceClosed);
    proc.on("exit", announceClosed);
    proc.on("error", announceClosed);
  }

  private ensure(): void {
    if (!this.running()) this.spawnProcess();
  }

  private async restart(): Promise<void> {
    await terminate(this.proc);
    this.proc = null;
    this.spawnProcess();
  }

  async shutdown(): Promise<void> {
    await terminate(this.proc);
    this.proc = null;
  }

  private broadcast(text: string): void {
    // Iterate a snapshot so a sink that detaches mid-broadcast (clients.delete on
    // a closed connection) cannot disrupt the loop.
    // oxlint-disable-next-line unicorn/no-useless-spread
    for (const sink of [...this.clients]) sink.put(text);
  }

  async send(text: string): Promise<void> {
    // `initialize` is the first message of an LSP session. A reused Lean server
    // rejects a second initialize, so start a fresh server for each one; this
    // makes browser reloads reconnect cleanly.
    if (isInitialize(text)) {
      await this.restart();
    } else {
      this.ensure();
    }
    const proc = this.proc;
    if (proc === null || proc.stdin === null) {
      throw new Error("Lean bridge is not running");
    }
    const data = Buffer.from(text, "utf-8");
    proc.stdin.write(Buffer.concat([Buffer.from(`Content-Length: ${data.length}\r\n\r\n`, "latin1"), data]));
  }

  subscribe(sink: Sink): void {
    this.clients.add(sink);
  }

  unsubscribe(sink: Sink): void {
    this.clients.delete(sink);
  }

  hasClients(): boolean {
    return this.clients.size > 0;
  }
}

type BridgeFactory = (root: string) => BridgeLike;

export class SessionRegistry {
  static readonly GRACE_SECONDS = 30;
  // Backstop against a misbehaving or churning client that cycles through many
  // session ids: each bridge can spawn a heavyweight `lake env lean --server`,
  // so cap how many we keep. The limit is comfortably above any realistic tab
  // count; it only bites when sessions are being created faster than they are
  // reaped. Active sessions are never evicted, so a genuine burst of live tabs
  // can still exceed it — this bounds the idle leak, not legitimate use.
  static readonly MAX_SESSIONS = 32;

  readonly root: string;
  readonly bridges = new Map<string, BridgeLike>();
  readonly reapers = new Map<string, NodeJS.Timeout>();
  readonly inflight = new Map<string, number>();
  private readonly makeBridge: BridgeFactory;

  constructor(root: string, makeBridge: BridgeFactory = (r) => new LeanBridge(r)) {
    this.root = root;
    this.makeBridge = makeBridge;
  }

  // Shut down idle bridges (no clients, no in-flight send) until we are back
  // under the cap, so creating a new session cannot grow the Lean-server count
  // without bound. Iterates in insertion order, so the oldest idle session goes
  // first. A no-op when already under the cap or when every bridge is active.
  private evictIdleSessions(): void {
    if (this.bridges.size < SessionRegistry.MAX_SESSIONS) return;
    for (const [sessionId, bridge] of this.bridges) {
      if (this.bridges.size < SessionRegistry.MAX_SESSIONS) return;
      if (bridge.hasClients() || this.inflight.get(sessionId)) continue;
      this.cancelReaper(sessionId);
      this.bridges.delete(sessionId);
      void bridge.shutdown();
    }
  }

  private getOrCreate(sessionId: string, root?: string): BridgeLike {
    let bridge = this.bridges.get(sessionId);
    if (bridge === undefined) {
      this.evictIdleSessions();
      bridge = this.makeBridge(root ?? this.root);
      this.bridges.set(sessionId, bridge);
    }
    return bridge;
  }

  private cancelReaper(sessionId: string): void {
    const timer = this.reapers.get(sessionId);
    if (timer !== undefined) {
      clearTimeout(timer);
      this.reapers.delete(sessionId);
    }
  }

  private scheduleReap(sessionId: string): void {
    const timer = setTimeout(() => {
      void this.reap(sessionId);
    }, SessionRegistry.GRACE_SECONDS * 1000);
    // A daemon-like timer: it must not keep the process alive on its own.
    timer.unref?.();
    this.reapers.set(sessionId, timer);
  }

  subscribe(sessionId: string, sink: Sink): void {
    this.cancelReaper(sessionId);
    this.getOrCreate(sessionId).subscribe(sink);
  }

  unsubscribe(sessionId: string, sink: Sink): void {
    const bridge = this.bridges.get(sessionId);
    if (bridge === undefined) return;
    bridge.unsubscribe(sink);
    if (!bridge.hasClients() && !this.reapers.has(sessionId)) {
      this.scheduleReap(sessionId);
    }
  }

  async reap(sessionId: string): Promise<void> {
    this.reapers.delete(sessionId);
    const bridge = this.bridges.get(sessionId);
    // A subscriber may have reconnected during the grace window, or a send may
    // be in flight (it awaits outside any lock and reschedules the reaper when
    // it finishes). Either keeps the bridge alive; reaping it now would tear it
    // down mid-write and let the send spawn a fresh, untracked Lean server.
    if (bridge === undefined || bridge.hasClients() || this.inflight.get(sessionId)) {
      return;
    }
    this.bridges.delete(sessionId);
    await bridge.shutdown();
  }

  running(sessionId: string): boolean {
    const bridge = this.bridges.get(sessionId);
    return bridge !== undefined ? bridge.running() : false;
  }

  async send(sessionId: string, text: string, root?: string): Promise<void> {
    const bridge = this.getOrCreate(sessionId, root);
    // The bridge may have been created by an earlier /events subscribe with the
    // default root; correct it before the lazy spawn (the first send) so
    // `lake env lean --server` runs in this session's project lake dir.
    if (root !== undefined && !bridge.running()) bridge.root = root;
    // Treat the send as activity: cancel any pending reaper and mark the session
    // in-flight so a reaper that has already fired skips the shutdown (see reap)
    // instead of tearing the bridge down mid-write. The finally reschedules it.
    this.cancelReaper(sessionId);
    this.inflight.set(sessionId, (this.inflight.get(sessionId) ?? 0) + 1);
    try {
      await bridge.send(text);
    } finally {
      const remaining = (this.inflight.get(sessionId) ?? 1) - 1;
      if (remaining > 0) {
        this.inflight.set(sessionId, remaining);
      } else {
        this.inflight.delete(sessionId);
        // A send may arrive for a session with no event stream (the tab never
        // subscribed, or is already gone); without a reaper such a bridge would
        // leak its Lean server until shutdown.
        if (!bridge.hasClients() && !this.reapers.has(sessionId)) {
          this.scheduleReap(sessionId);
        }
      }
    }
  }

  async shutdownAll(): Promise<void> {
    const bridges = [...this.bridges.values()];
    for (const timer of this.reapers.values()) clearTimeout(timer);
    this.bridges.clear();
    this.reapers.clear();
    this.inflight.clear();
    await Promise.all(bridges.map((bridge) => bridge.shutdown()));
  }
}
