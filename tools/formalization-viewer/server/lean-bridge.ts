// The Lean LSP bridge and per-session registry for the formalization viewer.
//
// Each browser tab carries its own `session` id and gets a dedicated
// `lake env lean --server`, spawned lazily on first use and reaped a short grace
// period after the tab's event stream closes. This isolates tabs completely: no
// shared document state, no cross-tab id collisions, and one tab's
// reload/restart never disturbs another.
//
// Sends and lifecycle changes share one queue: a restart must finish reaping
// the previous process before another send can spawn or write to its successor.

import { killGroup, terminate } from "./process-group.ts";
import { LspFrames } from "./lsp-frames.ts";
import { spawnLean, type LeanProc, type SpawnLean } from "./lsp-process.ts";

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
  private usable = false;
  private pending: Promise<void> = Promise.resolve();
  private readonly spawnServer: SpawnLean;
  private clients = new Set<Sink>();

  constructor(root: string, spawnServer: SpawnLean = spawnLean) {
    this.root = root;
    this.spawnServer = spawnServer;
  }

  running(): boolean {
    return this.usable && this.proc !== null && this.proc.exitCode === null && this.proc.signalCode === null;
  }

  private async spawnProcess(): Promise<void> {
    this.epoch += 1;
    const epoch = this.epoch;
    const proc = this.spawnServer(this.root);
    this.proc = proc;
    this.usable = false;
    const frames = new LspFrames();
    let dead = false;
    const announceClosed = (): void => {
      if (dead) return;
      dead = true;
      if (this.proc === proc) {
        this.usable = false;
        // A failed spawn has no process to reap. A closed stdout can still
        // belong to a live child; retain that handle until shutdown/restart.
        if (proc.pid === undefined || proc.exitCode !== null || proc.signalCode !== null) this.proc = null;
      }
      if (epoch === this.epoch) this.broadcast(BRIDGE_CLOSED);
    };
    proc.stdout.on("data", (chunk: Buffer) => {
      if (dead) return;
      try {
        for (const body of frames.push(chunk)) this.broadcast(body);
      } catch {
        announceClosed();
        killGroup(proc, "SIGTERM");
      }
    });
    proc.stdout.on("end", announceClosed);
    proc.stdin.on("error", announceClosed);
    proc.on("exit", announceClosed);
    proc.on("error", announceClosed);
    await new Promise<void>((resolve, reject) => {
      proc.once("spawn", () => {
        if (dead) return reject(new Error("Lean bridge closed during startup"));
        this.usable = true;
        resolve();
      });
      proc.once("error", reject);
    });
  }

  private async stopProcess(): Promise<void> {
    this.epoch += 1;
    const proc = this.proc;
    this.proc = null;
    this.usable = false;
    await terminate(proc);
  }

  private enqueue(action: () => Promise<void>): Promise<void> {
    const result = this.pending.then(action);
    // A failed send must not poison the queue for the next reconnect attempt.
    this.pending = result.catch(() => {});
    return result;
  }

  shutdown(): Promise<void> {
    return this.enqueue(() => this.stopProcess());
  }

  private broadcast(text: string): void {
    // Iterate a snapshot so a sink that detaches mid-broadcast (clients.delete on
    // a closed connection) cannot disrupt the loop.
    // oxlint-disable-next-line unicorn/no-useless-spread
    for (const sink of [...this.clients]) sink.put(text);
  }

  send(text: string): Promise<void> {
    return this.enqueue(async () => {
      if (isInitialize(text) || !this.running()) {
        await this.stopProcess();
        await this.spawnProcess();
      }
      const proc = this.proc;
      if (proc === null || !this.running()) throw new Error("Lean bridge is not running");
      const data = Buffer.from(text, "utf-8");
      const framed = Buffer.concat([Buffer.from(`Content-Length: ${data.length}\r\n\r\n`, "latin1"), data]);
      await new Promise<void>((resolve, reject) => {
        proc.stdin.write(framed, (error) => (error ? reject(error) : resolve()));
      });
    });
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
    if (root !== undefined && root !== bridge.root) {
      if (bridge.running() || this.inflight.get(sessionId)) {
        throw new Error("LSP session belongs to another project; create a new session");
      }
      bridge.root = root;
    }
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
