// Minimal Lean LSP client for the formalization viewer infoview.
//
// Talks to tools/formalization-viewer/server/serve.ts: the "lsp" channel of the shared
// event stream (event-stream.ts) carries JSON-RPC messages from `lake env
// lean --server` (server -> browser), and a fetch POST forwards each
// request/notification (browser -> server). Only the few methods the infoview
// needs are implemented: initialize, didOpen, the Lean custom goal queries
// ($/lean/plainGoal, $/lean/plainTermGoal), and tracking of
// publishDiagnostics.
//
// Everything degrades gracefully: if the bridge endpoint is absent (the viewer
// was started with plain http.server, no Lean), connect() resolves to null and
// the infoview shows an "unavailable" notice instead of failing.

// connId is the tab's session id: sent as ?session=<connId> on every /lsp
// call so the bridge gives this tab its own dedicated Lean server, fully
// isolating tabs from each other. It also prefixes JSON-RPC ids (string ids,
// which Lean echoes verbatim) as defence in depth.
import { eventStream } from "./event-stream.js";

type Pending = { resolve: (value: any) => void; reject: (reason?: any) => void };
type LspInfo = { rootUri: string; rootPath?: string; running?: boolean; static?: boolean };
type DiagnosticsHandler = (uri: string, diagnostics: any[]) => void;
type StatusHandler = (status: string) => void;

interface Lsp {
  info: LspInfo | null;
  connId: string;
  projectQuery: string;
  nextId: number;
  pending: Map<string, Pending>;
  diagnostics: Map<string, any[]>;
  openVersions: Map<string, number>;
  ready: boolean;
  onDiagnostics: DiagnosticsHandler | null;
  onStatus: StatusHandler | null;
  healAttempts?: number;
  healTimer?: ReturnType<typeof setTimeout> | null;
  healing?: boolean;
}

const lsp: Lsp = {
  info: null,
  connId: eventStream.connId,
  projectQuery: "",
  nextId: 1,
  pending: new Map(), // namespaced id -> {resolve, reject}
  diagnostics: new Map(), // uri -> diagnostics[]
  openVersions: new Map(), // uri -> version
  ready: false,
  onDiagnostics: null,
  onStatus: null,
};

// Static mode: instead of a live `lake env lean --server` bridge, answers come
// from pregenerated per-file caches (tools/formalization-viewer/server/lsp-cache.ts). Each
// cache samples goal/termGoal/hover once per symbol; a position lookup takes
// the latest sampled column at or before the cursor, so any in-token position
// resolves to the answer recorded at the token start.
interface StaticLsp {
  enabled: boolean;
  urlFor: ((repoPath: string) => string) | null;
  byUri: Map<string, Promise<any>>;
}

const staticLsp: StaticLsp = {
  enabled: false,
  urlFor: null, // repoPath -> cache URL
  byUri: new Map(), // uri -> Promise<cache|null>
};

function loadStaticCache(uri: string, repoPath: string) {
  const urlFor = staticLsp.urlFor;
  if (!urlFor) return Promise.resolve(null);
  let cached = staticLsp.byUri.get(uri);
  if (!cached) {
    cached = (async () => {
      try {
        const response = await fetch(urlFor(repoPath));
        if (!response.ok) return null;
        return await response.json();
      } catch (_error) {
        return null;
      }
    })();
    staticLsp.byUri.set(uri, cached);
  }
  return cached;
}

// slot: 1 = plainGoal, 2 = plainTermGoal, 3 = hover (sample = [col, g, t, h]).
async function staticLookup(uri: string, line: number, character: number, slot: number) {
  if (!staticLsp.byUri.has(uri)) return null;
  const cache = await staticLsp.byUri.get(uri);
  const row = cache?.lines?.[line];
  if (!row || !row.length) return null;
  let found = row[0];
  for (const sample of row) {
    if (sample[0] > character) break;
    found = sample;
  }
  const index = found[slot];
  if (index < 0) return null;
  const table = slot === 1 ? cache.goals : slot === 2 ? cache.termGoals : cache.hovers;
  return table?.[index] ?? null;
}

function post(message: any) {
  // projectQuery tells the server which project's lake dir to spawn the Lean
  // server in (the first send spawns it); without it the bridge would fall back
  // to the default project's root.
  return fetch("/lsp/send" + eventStream.sessionQuery + lsp.projectQuery, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(message),
  });
}

function notify(method: string, params: any): void {
  // Notifications are fire-and-forget: no caller awaits them. Swallow transport
  // failures (e.g. the bridge dropped mid-session) here so they do not surface
  // as unhandled promise rejections; the heal loop re-establishes session and
  // document state on the next reconnect.
  post({ jsonrpc: "2.0", method, params }).catch((error) => {
    console.warn(`[booklink] LSP notify ${method} failed:`, error);
  });
}

function requestRaw(method: string, params: any) {
  const id = `${lsp.connId}:${lsp.nextId++}`;
  const promise = new Promise<any>((resolve, reject) => {
    lsp.pending.set(id, { resolve, reject });
  });
  post({ jsonrpc: "2.0", id, method, params }).catch((error) => {
    const entry = lsp.pending.get(id);
    if (entry) {
      lsp.pending.delete(id);
      entry.reject(error);
    }
  });
  return { id, promise };
}

function requestWithTimeout(method: string, params: any, ms: number) {
  return new Promise<any>((resolve, reject) => {
    let settled = false;
    const { id, promise } = requestRaw(method, params);
    const timer = setTimeout(() => {
      if (!settled) {
        settled = true;
        // Drop the still-pending entry so it cannot leak when the response
        // never arrives (e.g. the Lean server dropped without a close event).
        lsp.pending.delete(id);
        reject(new Error(`${method} timed out`));
      }
    }, ms);
    promise.then(
      (result) => {
        if (!settled) {
          settled = true;
          clearTimeout(timer);
          resolve(result);
        }
      },
      (error) => {
        if (!settled) {
          settled = true;
          clearTimeout(timer);
          reject(error);
        }
      },
    );
  });
}

// Server -> client requests we acknowledge with an empty result; everything
// else gets a "method not found" reply (see handleMessage). These are
// capability/progress notifications-as-requests that expect only an ack.
const SERVER_REQUEST_ACKS = new Set([
  "window/workDoneProgress/create",
  "client/registerCapability",
  "client/unregisterCapability",
  "workspace/semanticTokens/refresh",
  "workspace/codeLens/refresh",
  "workspace/diagnostic/refresh",
  "workspace/inlayHint/refresh",
]);

function handleMessage(message: any) {
  if (message.id !== undefined && lsp.pending.has(message.id)) {
    const entry = lsp.pending.get(message.id);
    lsp.pending.delete(message.id);
    if (entry) {
      if (message.error) entry.reject(new Error(message.error.message || "LSP error"));
      else entry.resolve(message.result);
    }
    return;
  }
  // A message carrying both an id and a method that is not one of our pending
  // requests is a server -> client request. Per JSON-RPC every request needs a
  // response, or the server can stall waiting for one. We implement none of
  // these capabilities, so acknowledge the ones that expect an empty result and
  // reject the rest with "method not found" rather than leaving them hanging.
  if (message.id !== undefined && typeof message.method === "string") {
    if (SERVER_REQUEST_ACKS.has(message.method)) {
      post({ jsonrpc: "2.0", id: message.id, result: null }).catch(() => {});
    } else {
      post({
        jsonrpc: "2.0",
        id: message.id,
        error: { code: -32601, message: `method not found: ${message.method}` },
      }).catch(() => {});
    }
    return;
  }
  if (message.method === "textDocument/publishDiagnostics") {
    const { uri, diagnostics } = message.params;
    lsp.diagnostics.set(uri, diagnostics || []);
    lsp.onDiagnostics?.(uri, diagnostics || []);
    return;
  }
  if (message.method === "$/bridge/closed") {
    lsp.ready = false;
    lsp.onStatus?.("closed");
    scheduleHeal();
  }
}

// After the event stream recovers from an error, the bridge may be a
// different process than the one this tab ran its handshake against (the
// viewer server was restarted, or the session was reaped while offline). Ask
// the bridge whether this session's Lean server is still alive; if not, run a
// fresh handshake. A transient socket blip with the session intact keeps the
// Lean server's elaboration state untouched.
async function resyncAfterReconnect() {
  if (!lsp.ready) return; // the handshake/heal path is already driving recovery
  try {
    const response = await fetch("/lsp/info" + eventStream.sessionQuery + lsp.projectQuery);
    if (response.ok && (await response.json()).running) {
      lsp.onStatus?.("ready");
      return;
    }
  } catch (_error) {
    // Treat an unreachable bridge like a lost session: heal with backoff.
  }
  lsp.ready = false;
  scheduleHeal();
}

function connectEvents() {
  eventStream.onStreamEvent("lsp", (data: string) => {
    try {
      handleMessage(JSON.parse(data));
    } catch (_error) {
      // Ignore malformed frames.
    }
  });
  eventStream.onStreamError(() => {
    lsp.onStatus?.("reconnecting");
  });
  eventStream.onStreamOpen(({ reconnect }) => {
    if (reconnect) resyncAfterReconnect();
  });
  // Resolve once the stream is open so the bridge has registered this client
  // before we send the first request (otherwise a fast response can be missed);
  // a transient connect error also resolves, never hanging the handshake.
  return eventStream.connectStream();
}

// Run (or re-run) the LSP handshake against a fresh server. On failure or a
// dropped server, retry with backoff so the viewer self-heals.
// Returns true on a successful handshake, false on failure. Retry scheduling is
// the caller's job (scheduleHeal): this keeps the heal callback the single owner
// of the backoff loop, so a failure never schedules a retry while another heal
// body is mid-flight.
async function handshake(): Promise<boolean> {
  if (!lsp.info) return true; // nothing to connect to; treat as done, do not retry
  lsp.ready = false;
  lsp.onStatus?.("connecting");
  try {
    await requestWithTimeout(
      "initialize",
      {
        processId: null,
        rootUri: lsp.info.rootUri,
        capabilities: {
          textDocument: { publishDiagnostics: {}, hover: { contentFormat: ["markdown", "plaintext"] } },
        },
      },
      30000,
    );
    notify("initialized", {});
    lsp.ready = true;
    lsp.healAttempts = 0;
    lsp.onStatus?.("ready");
    return true;
  } catch (error) {
    lsp.ready = false;
    console.warn("[booklink] Lean LSP handshake failed:", error);
    lsp.onStatus?.("error");
    return false;
  }
}

function scheduleHeal() {
  // A timer pending OR a heal body already running both count as healing in
  // progress. Clearing healTimer at the start of the callback must not open a
  // window for a second concurrent heal body (which would clear pending /
  // openVersions out from under the in-flight handshake); the `healing` flag
  // keeps the heal loop single-flight across the await.
  if (lsp.healTimer || lsp.healing) return;
  lsp.healAttempts = (lsp.healAttempts || 0) + 1;
  const delay = Math.min(15000, 1000 * lsp.healAttempts);
  lsp.healTimer = setTimeout(async () => {
    lsp.healTimer = null;
    lsp.healing = true;
    // A reconnect spawns a fresh server: drop stale request and document state.
    for (const entry of lsp.pending.values()) entry.reject(new Error("LSP reconnecting"));
    lsp.pending.clear();
    lsp.openVersions.clear();
    lsp.onStatus?.("reconnecting");
    let ok = false;
    try {
      ok = await handshake();
    } finally {
      lsp.healing = false;
    }
    // Schedule the next backoff attempt only after this body has released the
    // `healing` guard, so the retry is sequential rather than concurrent.
    if (!ok) scheduleHeal();
  }, delay);
}

export function uriForRepoPath(repoPath: string): string | null {
  if (!lsp.info) return null;
  return `${lsp.info.rootUri}/${repoPath.replace(/^\/+/, "")}`;
}

interface ConnectLeanLspOptions {
  onDiagnostics?: DiagnosticsHandler | null;
  onStatus?: StatusHandler | null;
  staticCacheUrlFor?: ((repoPath: string) => string) | null;
  projectDir?: string | null;
}

// Connect to the bridge and run the LSP handshake. Resolves to the bridge info
// object, or null if the bridge is unavailable. With `staticCacheUrlFor` set,
// no bridge is contacted: every query is answered from the static cache.
export async function connectLeanLsp(
  { onDiagnostics, onStatus, staticCacheUrlFor, projectDir } = {} as ConnectLeanLspOptions,
): Promise<LspInfo | null> {
  lsp.onDiagnostics = onDiagnostics ?? null;
  lsp.onStatus = onStatus ?? null;
  // The bridge serves every project; name ours so /lsp/info reports the LSP
  // root this project's repo-relative paths resolve against.
  lsp.projectQuery = projectDir ? `&project=${encodeURIComponent(projectDir)}` : "";
  if (staticCacheUrlFor) {
    staticLsp.enabled = true;
    staticLsp.urlFor = staticCacheUrlFor;
    lsp.info = { rootUri: "booklink-cache:/", rootPath: "/", running: true, static: true };
    lsp.ready = true;
    onStatus?.("static");
    return lsp.info;
  }
  let info: LspInfo | null = null;
  try {
    const response = await fetch("/lsp/info" + eventStream.sessionQuery + lsp.projectQuery);
    if (response.ok) info = await response.json();
  } catch (_error) {
    info = null;
  }
  if (!info) {
    onStatus?.("unavailable");
    return null;
  }
  lsp.info = info;
  await connectEvents();
  // handshake() no longer self-schedules; drive the first retry here so an
  // initial failure still self-heals with backoff.
  if (!(await handshake())) scheduleHeal();
  return info;
}

export function isReady() {
  return lsp.ready;
}

// Open (or re-sync) a Lean document by repo-relative path. Lean keeps multiple
// documents open; each unique URI is opened once, later edits bump the version.
// In static mode this kicks off the cache fetch and replays its diagnostics.
export function openDocument(repoPath: string, text: string): string | null {
  const uri = uriForRepoPath(repoPath);
  if (!uri || !lsp.ready) return uri;
  if (staticLsp.enabled) {
    loadStaticCache(uri, repoPath)
      .then((cache) => {
        const diagnostics = cache?.diagnostics || [];
        lsp.diagnostics.set(uri, diagnostics);
        lsp.onDiagnostics?.(uri, diagnostics);
      })
      .catch((error) => {
        console.warn("[booklink] static cache load failed for", repoPath, error);
      });
    return uri;
  }
  if (!lsp.openVersions.has(uri)) {
    lsp.openVersions.set(uri, 1);
    notify("textDocument/didOpen", {
      textDocument: { uri, languageId: "lean", version: 1, text },
    });
  }
  return uri;
}

// Push a new version of an already-open document (or open it if it is not yet
// open) so the Lean server re-elaborates after the file changed on disk.
export function changeDocument(repoPath: string, text: string): string | null {
  const uri = uriForRepoPath(repoPath);
  if (!uri || !lsp.ready) return uri;
  if (staticLsp.enabled) return openDocument(repoPath, text);
  if (!lsp.openVersions.has(uri)) {
    lsp.openVersions.set(uri, 1);
    notify("textDocument/didOpen", {
      textDocument: { uri, languageId: "lean", version: 1, text },
    });
    return uri;
  }
  const version = (lsp.openVersions.get(uri) ?? 0) + 1;
  lsp.openVersions.set(uri, version);
  notify("textDocument/didChange", {
    textDocument: { uri, version },
    contentChanges: [{ text }],
  });
  return uri;
}

export function diagnosticsFor(uri: string) {
  return lsp.diagnostics.get(uri) || [];
}

// Goal state at a position: { goals: string[], rendered?: string } or null.
export async function plainGoal(uri: string | null, line: number, character: number) {
  if (!uri || !lsp.ready) return null;
  if (staticLsp.enabled) return staticLookup(uri, line, character, 1);
  try {
    return await requestWithTimeout(
      "$/lean/plainGoal",
      { textDocument: { uri }, position: { line, character } },
      15000,
    );
  } catch (_error) {
    return null;
  }
}

// Expected-type / term goal at a position: { goal: string, range } or null.
export async function plainTermGoal(uri: string | null, line: number, character: number) {
  if (!uri || !lsp.ready) return null;
  if (staticLsp.enabled) return staticLookup(uri, line, character, 2);
  try {
    return await requestWithTimeout(
      "$/lean/plainTermGoal",
      { textDocument: { uri }, position: { line, character } },
      15000,
    );
  } catch (_error) {
    return null;
  }
}

// Hover at a position: { contents: MarkupContent|..., range? } or null.
export async function hover(uri: string | null, line: number, character: number) {
  if (!uri || !lsp.ready) return null;
  if (staticLsp.enabled) return staticLookup(uri, line, character, 3);
  try {
    return await requestWithTimeout(
      "textDocument/hover",
      { textDocument: { uri }, position: { line, character } },
      15000,
    );
  } catch (_error) {
    return null;
  }
}
