// Port of tests/test_booklink_lsp_server.py::SessionRegistryRaceTest. Run with
// `node --test`.
//
// These exercise the concurrency contract around SessionRegistry.send and the
// grace-period reaper without spawning real `lake env lean --server` processes:
// a stub bridge stands in for LeanBridge and records spawn/shutdown calls, and a
// gated send lets the test drive the exact interleaving the production race
// depends on. On Node the interleaving happens at `await` points rather than
// across threads, but the contract is identical.

import { test } from "node:test";
import assert from "node:assert/strict";
import { SessionRegistry } from "./lean-bridge.ts";
import type { BridgeLike, Sink } from "./lean-bridge.ts";

const ROOT = "/repo";

// Stand-in for LeanBridge. Tracks shutdowns and an optional gate so a send can
// be held mid-flight; `send` re-spawns when called after a shutdown, which is
// exactly the orphaned-server leak the registry must prevent.
class StubBridge implements BridgeLike {
  root: string;
  clients = new Set<Sink>();
  shutdowns = 0;
  spawns = 1; // a live server at construction
  gate = false; // when true, send blocks until openGate()
  entered: Promise<void>;
  private enteredResolve!: () => void;
  private gatePromise: Promise<void>;
  private gateResolve!: () => void;

  constructor(root: string) {
    this.root = root;
    this.entered = new Promise((resolve) => (this.enteredResolve = resolve));
    this.gatePromise = new Promise((resolve) => (this.gateResolve = resolve));
  }

  hasClients(): boolean {
    return this.clients.size > 0;
  }
  subscribe(sink: Sink): void {
    this.clients.add(sink);
  }
  unsubscribe(sink: Sink): void {
    this.clients.delete(sink);
  }
  running(): boolean {
    return this.shutdowns === 0;
  }
  openGate(): void {
    this.gateResolve();
  }

  async send(_text: string): Promise<void> {
    this.enteredResolve();
    if (this.gate) await this.gatePromise;
    // ensure()/restart() inside the real send would spawn a fresh server here if
    // the bridge had been shut down underneath it.
    if (this.shutdowns) this.spawns += 1;
  }

  async shutdown(): Promise<void> {
    this.shutdowns += 1;
  }
}

function newRegistry(): SessionRegistry {
  return new SessionRegistry(ROOT, (root) => new StubBridge(root));
}

function clearReapers(reg: SessionRegistry): void {
  for (const timer of reg.reapers.values()) clearTimeout(timer);
}

test("send during a pending reap does not orphan the bridge", async () => {
  const reg = newRegistry();
  const sid = "s";
  const bridge = new StubBridge(ROOT);
  reg.bridges.set(sid, bridge);
  // Simulate a pending reaper from a closed event stream.
  reg.reapers.set(
    sid,
    setTimeout(() => {}, 60000),
  );
  bridge.gate = true;

  const sending = reg.send(sid, "msg");
  // send registers the in-flight marker synchronously before awaiting bridge.send.
  await bridge.entered;

  // The grace timer fires now, mid-send.
  await reg.reap(sid);

  // The bridge must survive: not shut down, still registered, not respawned.
  assert.equal(bridge.shutdowns, 0);
  assert.equal(reg.bridges.get(sid), bridge);

  bridge.openGate();
  await sending;

  assert.equal(bridge.shutdowns, 0);
  assert.equal(bridge.spawns, 1);
  // With no clients, the completed send reschedules the reaper.
  assert.ok(reg.reapers.has(sid));
  assert.ok(!reg.inflight.has(sid));
  clearReapers(reg);
});

test("creating sessions past the cap evicts idle ones but spares active ones", async () => {
  const reg = newRegistry();
  const cap = SessionRegistry.MAX_SESSIONS;

  // Fill to the cap. The first session is held active (a live client); the rest
  // subscribe then unsubscribe with the SAME sink (Set identity) so they end up
  // with no clients, i.e. idle eviction candidates.
  reg.subscribe("active", { put() {} });
  for (let i = 0; i < cap - 1; i += 1) {
    const sink: Sink = { put() {} };
    reg.subscribe(`idle-${i}`, sink);
    reg.unsubscribe(`idle-${i}`, sink);
  }
  clearReapers(reg);
  assert.equal(reg.bridges.size, cap);

  const active = reg.bridges.get("active") as StubBridge;

  // One more session triggers eviction of an idle bridge to stay under the cap.
  await reg.send("overflow", "msg");

  assert.ok(reg.bridges.size <= cap, "stays within the session cap");
  assert.ok(reg.bridges.has("overflow"), "the new session is created");
  assert.ok(reg.bridges.has("active"), "an active session is never evicted");
  assert.equal(active.shutdowns, 0, "the active bridge is not shut down");
  clearReapers(reg);
});

test("send without an event stream schedules a reap", async () => {
  const reg = newRegistry();
  const sid = "lonely";
  await reg.send(sid, "msg");
  assert.ok(reg.bridges.has(sid));
  assert.ok(reg.reapers.has(sid));
  assert.ok(!reg.inflight.has(sid));
  clearReapers(reg);
});

test("overlapping sends reap only after the last completes", async () => {
  const reg = newRegistry();
  const sid = "busy";
  const bridge = new StubBridge(ROOT);
  reg.bridges.set(sid, bridge);
  bridge.gate = true;

  const sends = [reg.send(sid, "m"), reg.send(sid, "m"), reg.send(sid, "m")];
  await bridge.entered;
  assert.equal(reg.inflight.get(sid), 3);

  // A reap mid-flight is a no-op; bridge stays alive.
  await reg.reap(sid);
  assert.equal(bridge.shutdowns, 0);
  assert.equal(reg.bridges.get(sid), bridge);

  bridge.openGate();
  await Promise.all(sends);
  assert.ok(!reg.inflight.has(sid));
  assert.ok(reg.reapers.has(sid));
  assert.equal(bridge.shutdowns, 0);
  clearReapers(reg);
});
