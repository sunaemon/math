#!/usr/bin/env node
// Static file server for the formalization viewer plus a Lean LSP bridge.
//
// Serves the repository over HTTP like `python -m http.server` and adds a bridge
// to a `lake env lean --server` subprocess so the viewer's infoview pane can
// show live Lean goal state and diagnostics:
//
//   GET  /lsp/info?session=ID   -> {rootUri, rootPath, running}
//   GET  /events?session=ID     -> Server-Sent Events stream multiplexing two
//                                  named channels: `event: lsp` carries JSON-RPC
//                                  messages from the Lean server, `event: watch`
//                                  carries file-watch notifications.
//   POST /lsp/send?session=ID   -> forward one JSON-RPC message to the Lean
//                                  server (browser -> server).
//
// The two channels share one stream because browsers cap concurrent HTTP/1.x
// connections per origin and an EventSource pins one for its lifetime. The
// legacy single-channel `/lsp/events` and `/watch/events` endpoints remain for
// stale tabs running cached viewer JS.
//
// Each browser tab carries its own `session` id and gets a dedicated Lean
// server, spawned lazily on first use and reaped a short grace period after the
// tab's event stream closes. `lake` must be on PATH (run via mise/elan).

import http from "node:http";
import type { IncomingMessage, ServerResponse } from "node:http";
import fs from "node:fs";
import path from "node:path";
import crypto from "node:crypto";
import { spawn } from "node:child_process";

import { Projects } from "./projects.ts";
import type { Manifest } from "./projects.ts";
import { SessionRegistry } from "./lean-bridge.ts";
import type { Sink } from "./lean-bridge.ts";
import { FileWatcher } from "./file-watcher.ts";
import { BookBuilder } from "./book-builder.ts";
import { isTrustedRequest } from "./request-trust.ts";
import { repoVersion, attachLicenseText, appendVendorComponents, katexMacros, macrosTexPath } from "./repo-version.ts";

const ROOT = fs.realpathSync(process.env.BOOKLINK_ROOT ?? process.cwd());
// Requested port; 0 means "let the OS assign a free port". The bound port is
// read back from the listening socket below.
const PORT = (() => {
  const parsed = Number.parseInt(process.env.BOOKLINK_VIEWER_PORT ?? "8765", 10);
  return Number.isNaN(parsed) ? 8765 : parsed;
})();

const projects = new Projects(ROOT, process.env.BOOKLINK_PROJECT ?? "");
const sessions = new SessionRegistry(projects.defaultLspRoot);

// Build-status fan-out: book-builder reports {dir,state} on build start/finish;
// relay it on the "build" SSE channel so the viewer can show a "Building…"
// indicator. `buildingDirs` is the live set, replayed to each new subscriber so
// a tab opened mid-build still shows the indicator.
const buildClients = new Set<Sink>();
const buildingDirs = new Set<string>();
function broadcastBuild(status: { dir: string; state: string }): void {
  if (status.state === "building") buildingDirs.add(status.dir);
  else buildingDirs.delete(status.dir);
  const payload = JSON.stringify(status);
  const sinks = [...buildClients];
  for (const sink of sinks) sink.put(payload);
}

// Rebuild a book's debug PDF + viewer source map when its Markdown source
// changes; the regenerated build/ files reload the panes through the watcher.
const builder = new BookBuilder(
  ROOT,
  projects.projects,
  (m) => process.stderr.write(`${m}\n`),
  (status) => broadcastBuild(status),
);
const watcher = new FileWatcher(ROOT, projects.watchDirs, projects.watchAliases, (rel) => builder.notify(rel));

const MIME: Record<string, string> = {
  ".html": "text/html",
  ".js": "text/javascript",
  ".mjs": "text/javascript",
  ".css": "text/css",
  ".json": "application/json",
  ".map": "application/json",
  ".md": "text/markdown",
  ".txt": "text/plain",
  ".lean": "text/plain",
  ".scm": "text/plain",
  ".ts": "text/plain",
  ".tex": "application/x-tex",
  ".pdf": "application/pdf",
  ".svg": "image/svg+xml",
  ".wasm": "application/wasm",
  ".woff2": "font/woff2",
  ".woff": "font/woff",
  ".ico": "image/x-icon",
  ".png": "image/png",
  ".jpg": "image/jpeg",
  ".jpeg": "image/jpeg",
  ".gif": "image/gif",
};

const POST_BODY_LIMIT = 16 * 1024 * 1024;

function safeDecode(s: string): string {
  try {
    return decodeURIComponent(s);
  } catch {
    return s.replace(/%[0-9a-fA-F]{2}/g, (m) => {
      try {
        return decodeURIComponent(m);
      } catch {
        return m;
      }
    });
  }
}

function sendError(res: ServerResponse, status: number, message: string): void {
  if (res.writableEnded) return;
  res.writeHead(status, { "Content-Type": "text/plain; charset=utf-8" });
  res.end(message);
}

function sendJson(res: ServerResponse, obj: unknown, status = 200): void {
  if (res.writableEnded) return;
  const data = JSON.stringify(obj);
  res.writeHead(status, {
    "Content-Type": "application/json",
    "Content-Length": Buffer.byteLength(data),
  });
  res.end(data);
}

function noStoreRoute(route: string): boolean {
  return /(\.js|\.css|\.html|\.map|\/)$/.test(route);
}

// --- viewer build version ---------------------------------------------------
//
// A fingerprint of the viewer's own browser assets (the esbuild outputs under
// build/, plus the root index.html/styles.css). The client embeds the version
// it loaded with (injected into index.html below) and re-checks this endpoint on
// reconnect and tab focus; a mismatch means an esbuild rebuild landed while the
// page was stale, so it reloads. This is the safety net behind the file-watch
// reload: even if a watch event is missed (SSE drop, coalesced event, a build
// raced after the page loaded), the next focus self-heals instead of leaving the
// reader on stale JS. Fingerprint is mtime+size, not content hash, so it stays a
// cheap stat sweep over a handful of files.
const VIEWER_DIR_ABS = path.join(ROOT, "tools", "formalization-viewer");
const VIEWER_BUILD_DIR = path.join(VIEWER_DIR_ABS, "build");

function viewerBuildVersion(): string {
  const parts: string[] = [];
  const stamp = (file: string) => {
    try {
      const st = fs.statSync(file);
      parts.push(`${path.basename(file)}:${Math.floor(st.mtimeMs)}:${st.size}`);
    } catch {
      // A missing file (e.g. before the first build) just drops out of the
      // fingerprint; it reappears once written and changes the version then.
    }
  };
  stamp(path.join(VIEWER_DIR_ABS, "index.html"));
  stamp(path.join(VIEWER_DIR_ABS, "styles.css"));
  try {
    for (const name of fs.readdirSync(VIEWER_BUILD_DIR).sort()) {
      if (name.endsWith(".js") || name.endsWith(".css")) stamp(path.join(VIEWER_BUILD_DIR, name));
    }
  } catch {
    // No build dir yet; the index.html/styles.css stamps still version the page.
  }
  return crypto.createHash("sha1").update(parts.join("\n")).digest("hex").slice(0, 16);
}

function sendText(res: ServerResponse, text: string): void {
  if (res.writableEnded) return;
  res.writeHead(200, {
    "Content-Type": "text/plain; charset=utf-8",
    "Content-Length": Buffer.byteLength(text),
    "Cache-Control": "no-store",
  });
  res.end(text);
}

// Serve the viewer's index.html with the current build version injected, so the
// running page knows exactly which build it loaded and can detect a newer one.
// Read-and-rewrite rather than stream because it is one small file.
function serveViewerIndex(res: ServerResponse): void {
  let html: string;
  try {
    html = fs.readFileSync(path.join(VIEWER_DIR_ABS, "index.html"), "utf-8");
  } catch {
    return sendError(res, 404, "Not Found");
  }
  const meta = `<meta name="viewer-build-version" content="${viewerBuildVersion()}">`;
  const injected = html.includes("</head>") ? html.replace("</head>", `  ${meta}\n</head>`) : `${meta}\n${html}`;
  res.writeHead(200, {
    "Content-Type": "text/html; charset=utf-8",
    "Content-Length": Buffer.byteLength(injected),
    "Cache-Control": "no-store",
  });
  res.end(injected);
}

// --- static file serving ----------------------------------------------------

function serveStatic(req: IncomingMessage, res: ServerResponse, urlPath: string): void {
  const rel = safeDecode(urlPath);
  let fsPath = path.join(ROOT, rel);
  const within = path.relative(ROOT, fsPath);
  if (within.startsWith("..") || path.isAbsolute(within)) {
    return sendError(res, 404, "Not Found");
  }
  if (urlPath.endsWith("/")) fsPath = path.join(fsPath, "index.html");

  // The viewer's own index.html is served with the build version injected so the
  // page can detect a later rebuild and self-reload; GET only (HEAD keeps the
  // plain streamed path, which still 200s for probes).
  if (req.method === "GET" && path.resolve(fsPath) === path.join(VIEWER_DIR_ABS, "index.html")) {
    return serveViewerIndex(res);
  }

  let stat: fs.Stats;
  try {
    stat = fs.statSync(fsPath);
  } catch {
    return sendError(res, 404, "Not Found");
  }
  if (stat.isDirectory()) return sendError(res, 404, "Not Found");

  // The lexical check above operates on the requested path, but statSync and
  // createReadStream follow symlinks. Resolve the real path and re-check it is
  // inside ROOT. Legitimate served trees are symlinks to other locations within
  // the repo (the chapter excerpt shares the full book's src/, tex/, and lean/),
  // so those still resolve under ROOT; a symlink escaping the repo (e.g. to
  // /etc/passwd) is rejected here.
  let realPath: string;
  try {
    realPath = fs.realpathSync(fsPath);
  } catch {
    return sendError(res, 404, "Not Found");
  }
  const realWithin = path.relative(ROOT, realPath);
  if (realWithin.startsWith("..") || path.isAbsolute(realWithin)) {
    return sendError(res, 404, "Not Found");
  }

  const lastModified = stat.mtime.toUTCString();
  const ims = req.headers["if-modified-since"];
  if (typeof ims === "string") {
    const imsTime = Date.parse(ims);
    if (!Number.isNaN(imsTime) && Math.floor(stat.mtimeMs / 1000) <= Math.floor(imsTime / 1000)) {
      res.writeHead(304);
      return void res.end();
    }
  }

  const headers: Record<string, string | number> = {
    "Content-Type": MIME[path.extname(fsPath).toLowerCase()] ?? "application/octet-stream",
    "Content-Length": stat.size,
    "Last-Modified": lastModified,
  };
  // Dev server: serve the viewer's own assets uncached so an esbuild rebuild —
  // and the page reload the file-watch triggers — loads the new JS/CSS.
  if (noStoreRoute(urlPath.split("?")[0])) headers["Cache-Control"] = "no-store";

  res.writeHead(200, headers);
  if (req.method === "HEAD") return void res.end();
  const stream = fs.createReadStream(fsPath);
  stream.on("error", () => res.destroy());
  res.on("close", () => stream.destroy());
  stream.pipe(res);
}

// --- SSE streaming ----------------------------------------------------------

class ResSink implements Sink {
  private readonly res: ServerResponse;
  private readonly channel: string | null;

  constructor(res: ServerResponse, channel: string | null) {
    this.res = res;
    this.channel = channel;
  }

  put(text: string): void {
    if (this.res.writableEnded) return;
    let frame = this.channel ? `event: ${this.channel}\n` : "";
    // JSON-RPC messages are single-line, but split defensively so a stray
    // newline can never break SSE record framing.
    for (const line of text.split("\n")) frame += `data: ${line}\n`;
    frame += "\n";
    this.res.write(frame);
  }
}

function startSse(res: ServerResponse, cleanup: () => void): void {
  res.on("error", () => {});
  // The stream has no length and ends when the connection closes, so it must not
  // promise keep-alive.
  res.writeHead(200, {
    "Content-Type": "text/event-stream",
    "Cache-Control": "no-cache",
    Connection: "close",
  });
  const ping = setInterval(() => {
    if (!res.writableEnded) res.write(": ping\n\n");
  }, 15000);
  ping.unref?.();
  res.on("close", () => {
    clearInterval(ping);
    cleanup();
  });
}

function streamCombined(req: IncomingMessage, res: ServerResponse, sessionId: string): void {
  // LSP responses and watch notifications arrive on one stream, tagged with
  // their SSE event name. The Lean server itself is spawned by the first
  // /lsp/send (initialize); here we only register this tab's sinks.
  watcher.ensure();
  const lspSink = new ResSink(res, "lsp");
  const watchSink = new ResSink(res, "watch");
  const buildSink = new ResSink(res, "build");
  startSse(res, () => {
    sessions.unsubscribe(sessionId, lspSink);
    watcher.unsubscribe(watchSink);
    buildClients.delete(buildSink);
    builder.clearSelection(sessionId);
  });
  sessions.subscribe(sessionId, lspSink);
  watcher.subscribe(watchSink);
  buildClients.add(buildSink);
  // Replay in-flight builds so a tab opened mid-build shows the indicator.
  for (const dir of buildingDirs) buildSink.put(JSON.stringify({ dir, state: "building" }));
}

function streamLspLegacy(res: ServerResponse, sessionId: string): void {
  const sink = new ResSink(res, null);
  startSse(res, () => sessions.unsubscribe(sessionId, sink));
  sessions.subscribe(sessionId, sink);
}

function streamWatchLegacy(res: ServerResponse): void {
  watcher.ensure();
  const sink = new ResSink(res, null);
  startSse(res, () => watcher.unsubscribe(sink));
  watcher.subscribe(sink);
}

// --- manifest ---------------------------------------------------------------

function sendManifest(res: ServerResponse, meta: Manifest): void {
  // Serve the project's manifest with a freshly enumerated "pdfs" list so the
  // viewer only offers PDFs that exist right now.
  let data: Record<string, unknown>;
  try {
    data = JSON.parse(fs.readFileSync(path.join(ROOT, meta.dir, "manifest.json"), "utf-8"));
  } catch {
    return sendError(res, 404, "Not Found");
  }
  data.pdfs = projects.projectPdfList(meta);
  data.version = repoVersion(ROOT);
  if (data.license) {
    appendVendorComponents(ROOT, data.license);
    attachLicenseText(ROOT, data.license);
  }
  data.katexMacros = katexMacros(macrosTexPath(ROOT, meta.dir));
  sendJson(res, data);
}

// --- request handling -------------------------------------------------------

function sessionIdOf(url: URL): string {
  return url.searchParams.get("session") ?? "";
}

function projectRootOf(url: URL): string {
  const projectDir = url.searchParams.get("project") ?? projects.defaultProject.dir;
  return projects.lspRoots.get(projectDir) ?? projects.defaultLspRoot;
}

function readBody(req: IncomingMessage, limit: number): Promise<string> {
  return new Promise((resolve, reject) => {
    const declared = Number.parseInt(req.headers["content-length"] ?? "", 10);
    if (!Number.isNaN(declared) && (declared < 0 || declared > limit)) {
      reject(Object.assign(new Error("request body too large"), { code: 413 }));
      return;
    }
    let size = 0;
    const chunks: Buffer[] = [];
    req.on("data", (chunk: Buffer) => {
      size += chunk.length;
      if (size > limit) {
        reject(Object.assign(new Error("request body too large"), { code: 413 }));
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });
    req.on("end", () => resolve(Buffer.concat(chunks).toString("utf-8")));
    req.on("error", reject);
  });
}

async function handlePost(req: IncomingMessage, res: ServerResponse, route: string, url: URL): Promise<void> {
  if (route !== "/lsp/send" && route !== "/build/select") return sendError(res, 404, "Not Found");
  try {
    const body = await readBody(req, POST_BODY_LIMIT);
    if (route === "/build/select") {
      // The tab tells us which rendered PDF it is showing so the auto-build
      // resolves its target from that selection.
      const pdf = (() => {
        try {
          const parsed = JSON.parse(body) as { pdf?: unknown };
          return typeof parsed.pdf === "string" ? parsed.pdf : "";
        } catch {
          return "";
        }
      })();
      if (pdf) builder.setSelection(sessionIdOf(url), pdf);
      sendJson(res, { ok: true });
      return;
    }
    await sessions.send(sessionIdOf(url), body, projectRootOf(url));
    sendJson(res, { ok: true });
  } catch (error) {
    if ((error as { code?: number }).code === 413) {
      sendJson(res, { ok: false, error: "request body too large" }, 413);
    } else {
      sendJson(res, { ok: false, error: String((error as Error).message ?? error) }, 500);
    }
  }
}

function handleGet(req: IncomingMessage, res: ServerResponse, route: string, url: URL): void {
  if (route === "/projects.json") {
    // The book selector in the viewer lists every served project.
    return sendJson(
      res,
      projects.projects.map((meta) => ({ name: meta.name ?? meta.dir, dir: meta.dir, mount: meta.mount })),
    );
  }
  if (route === "/viewer-version") {
    // The live-reload safety net: the page compares this against the version it
    // loaded with and reloads on a mismatch (see src/reload-guard.ts).
    return sendText(res, viewerBuildVersion());
  }
  if (route === "/events" || route.startsWith("/lsp/") || route.startsWith("/watch/")) {
    if (route === "/events") return streamCombined(req, res, sessionIdOf(url));
    if (route === "/lsp/info") {
      const projectDir = url.searchParams.get("project") ?? projects.defaultProject.dir;
      const lspRoot = projects.lspRoots.get(projectDir);
      if (lspRoot === undefined) return sendJson(res, { error: `unknown project: ${projectDir}` }, 404);
      return sendJson(res, {
        rootUri: `file://${lspRoot}`,
        rootPath: lspRoot,
        running: sessions.running(sessionIdOf(url)),
      });
    }
    if (route === "/lsp/events") return streamLspLegacy(res, sessionIdOf(url));
    if (route === "/watch/events") return streamWatchLegacy(res);
    return sendError(res, 404, "Not Found");
  }
  if (route === "/" || projects.mounts.has(route)) {
    res.writeHead(302, {
      Location: `${route === "/" ? projects.defaultMount : route}/`,
      "Content-Length": "0",
    });
    return void res.end();
  }
  for (const meta of projects.byMount) {
    if (route === `${meta.mount}/manifest.json`) return sendManifest(res, meta);
  }
  const rewritten = projects.applyMount(route);
  if (!projects.isAllowedPath(rewritten)) return sendError(res, 403, "Forbidden");
  serveStatic(req, res, rewritten);
}

function handle(req: IncomingMessage, res: ServerResponse): void {
  // Per-request isolation, matching Python's ThreadingHTTPServer: a browser that
  // drops an SSE stream or cancels a range request resets the connection, which
  // surfaces as an error on req/res. Swallow those here so one dropped
  // connection cannot become an uncaught exception that takes the server down.
  req.on("error", () => {});
  res.on("error", () => {});
  try {
    const host = req.headers.host;
    const origin = Array.isArray(req.headers.origin) ? req.headers.origin[0] : req.headers.origin;
    if (!isTrustedRequest(host, origin)) return sendError(res, 403, "Forbidden");

    const url = new URL(req.url ?? "/", "http://127.0.0.1");
    const route = (req.url ?? "/").split("?", 1)[0].split("#", 1)[0];

    if (req.method === "POST") {
      void handlePost(req, res, route, url);
      return;
    }
    if (req.method === "GET" || req.method === "HEAD") {
      if (req.method === "HEAD") {
        const rewritten = projects.applyMount(route);
        if (!projects.isAllowedPath(rewritten)) return sendError(res, 403, "Forbidden");
        return serveStatic(req, res, rewritten);
      }
      return handleGet(req, res, route, url);
    }
    sendError(res, 405, "Method Not Allowed");
  } catch (error) {
    // A bug in routing/serving one request must not kill the process.
    process.stderr.write(`[viewer] request error: ${(error as Error)?.stack ?? error}\n`);
    try {
      sendError(res, 500, "Internal Server Error");
    } catch {
      /* headers already sent (e.g. mid-stream): nothing more to do */
    }
  }
}

// --- startup ----------------------------------------------------------------

function openBrowser(url: string): void {
  const flag = (process.env.BOOKLINK_OPEN_BROWSER ?? "1").trim().toLowerCase();
  if (["0", "false", "no", ""].includes(flag)) return;
  // Defer so the first request is accepted promptly; never let a missing browser
  // take down the server.
  setTimeout(() => {
    const cmd = process.platform === "darwin" ? "open" : "xdg-open";
    try {
      const child = spawn(cmd, [url], { stdio: "ignore", detached: true });
      child.on("error", () => {});
      child.unref();
    } catch {
      /* ignore */
    }
  }, 300).unref?.();
}

// Browsers routinely drop SSE streams and cancel range requests (tab close,
// EventSource reconnect, PDF preview); those surface as connection resets and
// are expected, not server faults. Keep the process alive on them (and log, but
// do not exit, on anything else) so a single bad request never bricks the viewer
// — the safety net behind the per-request try/catch in handle().
const IGNORED_ERRNO = new Set(["ECONNRESET", "EPIPE", "ECONNABORTED", "ERR_STREAM_DESTROYED"]);
function installProcessGuards(): void {
  process.on("uncaughtException", (error: NodeJS.ErrnoException) => {
    if (error && IGNORED_ERRNO.has(error.code ?? "")) return;
    process.stderr.write(`[viewer] uncaught exception: ${error?.stack ?? error}\n`);
  });
  process.on("unhandledRejection", (reason) => {
    process.stderr.write(`[viewer] unhandled rejection: ${(reason as Error)?.stack ?? reason}\n`);
  });
}

function main(): void {
  installProcessGuards();
  const server = http.createServer(handle);
  server.on("clientError", (_err, socket) => socket.destroy());
  server.keepAliveTimeout = 120000;
  server.listen(PORT, "127.0.0.1", () => {
    const address = server.address();
    const port = typeof address === "object" && address !== null ? address.port : PORT;
    for (const meta of projects.projects) {
      process.stdout.write(`Formalization viewer: http://127.0.0.1:${port}${meta.mount}/\n`);
    }
    process.stdout.write(`Lean LSP bridge: serving ${ROOT}\n`);
    openBrowser(`http://127.0.0.1:${port}${projects.defaultMount}/`);
  });

  let shuttingDown = false;
  const shutdown = async (): Promise<void> => {
    if (shuttingDown) return;
    shuttingDown = true;
    watcher.shutdown();
    await builder.shutdown();
    await sessions.shutdownAll();
    process.exit(0);
  };
  process.on("SIGINT", () => void shutdown());
  process.on("SIGTERM", () => void shutdown());
}

main();
