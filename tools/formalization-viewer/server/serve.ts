#!/usr/bin/env node
import { preloadViewerModules } from "./module-preload.ts";
import { CorrespondenceService } from "./correspondence.ts";
import { ensureSearchIndex } from "./search-index.ts";
import { bookReferences } from "./references.ts";
import { fixedMath } from "./mathml.ts";
import { bookDefinitionRegistry } from "./definitions.ts";
import { HighlightService } from "./highlight-cache.ts";
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
import { pathToFileURL } from "node:url";
import crypto from "node:crypto";
import { spawn } from "node:child_process";

import { Projects, VIEWER_DIR } from "./projects.ts";
import type { Manifest } from "./projects.ts";
import { SessionRegistry } from "./lean-bridge.ts";
import type { Sink } from "./lean-bridge.ts";
import { FileWatcher } from "./file-watcher.ts";
import { BuildLogSockets } from "./build-log-socket.ts";
import { BookBuilder } from "./book-builder.ts";
import { chapterTitles } from "./chapter-titles.ts";
import { isTrustedRequest } from "./request-trust.ts";
import { isIP } from "node:net";
import { lookup } from "node:dns/promises";
import { createGzip, gzipSync } from "node:zlib";
import { pipeline } from "node:stream";
import { repoVersion, attachLicenseText, appendVendorComponents, katexMacros, macrosTexPath } from "./repo-version.ts";

const ROOT = fs.realpathSync(process.env.BOOKLINK_ROOT ?? process.cwd());
const HOST = (process.env.BOOKLINK_VIEWER_HOST ?? "127.0.0.1").trim().replace(/\.+$/, "").toLowerCase();
if (!HOST) throw new Error("BOOKLINK_VIEWER_HOST must not be empty");
const BIND_ADDRESS = isIP(HOST) ? HOST : (await lookup(HOST)).address;
if (BIND_ADDRESS === "0.0.0.0" || BIND_ADDRESS === "::") {
  throw new Error("BOOKLINK_VIEWER_HOST must resolve to a specific local IP address");
}
const URL_HOST = HOST.includes(":") ? `[${HOST}]` : HOST;
// Requested port; 0 means "let the OS assign a free port". The bound port is
// read back from the listening socket below.
const PORT = (() => {
  const parsed = Number.parseInt(process.env.BOOKLINK_VIEWER_PORT ?? "8765", 10);
  return Number.isNaN(parsed) ? 8765 : parsed;
})();

const projects = new Projects(ROOT, process.env.BOOKLINK_PROJECT ?? "");
const highlightService = new HighlightService(ROOT);
const correspondenceService = new CorrespondenceService(ROOT);
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

// Rebuild a book's debug PDF + viewer source map when its Markdown or Lean
// source changes; the regenerated build/ files reload the panes through the
// watcher.
const buildLogs = new BuildLogSockets(HOST);
const builder = new BookBuilder(
  ROOT,
  projects.projects,
  (m) => process.stderr.write(`${m}\n`),
  (status) => broadcastBuild(status),
  (dir, text, reset) => buildLogs.publish(dir, text, reset),
);
const watcher = new FileWatcher(ROOT, projects.watchDirs, projects.watchAliases, (rel) => {
  correspondenceService.invalidate(rel);
  builder.notify(rel);
});

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

function acceptsGzip(header: string | undefined): boolean {
  let wildcard = false;
  for (const item of (header ?? "").toLowerCase().split(",")) {
    const [coding, ...parameters] = item.trim().split(";");
    const quality = parameters.find((parameter) => parameter.trim().startsWith("q="));
    const accepted = quality === undefined || Number(quality.trim().slice(2)) > 0;
    if (coding === "gzip") return accepted;
    if (coding === "*") wildcard = accepted;
  }
  return wildcard;
}

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
  res.end(res.req.method === "HEAD" ? undefined : message);
}

function sendJson(res: ServerResponse, obj: unknown, status = 200, revalidate = false): void {
  if (res.writableEnded) return;
  const data = JSON.stringify(obj);
  if (revalidate && status === 200) {
    const etag = `W/"${crypto.createHash("sha256").update(data).digest("hex")}"`;
    res.setHeader("ETag", etag);
    res.setHeader("Cache-Control", "no-cache");
    if (
      String(res.req.headers["if-none-match"] ?? "")
        .split(",")
        .map((tag) => tag.trim())
        .includes(etag)
    ) {
      res.writeHead(304);
      return void res.end();
    }
  }
  res.writeHead(status, {
    "Content-Type": "application/json",
    "Content-Length": Buffer.byteLength(data),
  });
  res.end(res.req.method === "HEAD" ? undefined : data);
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
  res.end(res.req.method === "HEAD" ? undefined : text);
}

// Serve the viewer's index.html with the current build version injected, so the
// running page knows exactly which build it loaded and can detect a newer one.
let viewerIndex: { version: string; html: string; gzip?: Buffer } | undefined;

function serveViewerIndex(res: ServerResponse): void {
  const version = viewerBuildVersion();
  if (viewerIndex?.version !== version) {
    let html: string;
    try {
      html = fs.readFileSync(path.join(VIEWER_DIR_ABS, "index.html"), "utf-8");
    } catch {
      return sendError(res, 404, "Not Found");
    }
    html = preloadViewerModules(html, VIEWER_DIR_ABS);
    const meta = `<meta name="viewer-build-version" content="${version}">`;
    viewerIndex = {
      version,
      html: html.includes("</head>") ? html.replace("</head>", `  ${meta}\n</head>`) : `${meta}\n${html}`,
    };
  }
  const index = viewerIndex;
  const gzip = acceptsGzip(res.req.headers["accept-encoding"]);
  res.writeHead(200, {
    "Content-Type": "text/html; charset=utf-8",
    ...(gzip ? { "Content-Encoding": "gzip" } : { "Content-Length": Buffer.byteLength(index.html) }),
    Vary: "Accept-Encoding",
    "Cache-Control": "no-cache",
  });
  res.end(res.req.method === "HEAD" ? undefined : gzip ? (index.gzip ??= gzipSync(index.html)) : index.html);
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
  // page can detect a later rebuild and self-reload. HEAD uses that same
  // representation and content length while omitting the body.
  if (
    (req.method === "GET" || req.method === "HEAD") &&
    path.resolve(fsPath) === path.join(VIEWER_DIR_ABS, "index.html")
  ) {
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

  // Stream large text assets through gzip without buffering the whole source
  // map in memory. PDFs and already-compressed binary assets stay unchanged.
  const contentType =
    path.basename(fsPath) === "ai-catalog.json"
      ? "application/ai-catalog+json"
      : (MIME[path.extname(fsPath).toLowerCase()] ?? "application/octet-stream");
  const compressible =
    stat.size >= 1024 &&
    (contentType.startsWith("text/") ||
      ["application/json", "application/ai-catalog+json", "application/x-tex", "image/svg+xml"].includes(contentType));
  if (compressible) res.setHeader("Vary", "Accept-Encoding");
  const gzip = compressible && acceptsGzip(req.headers["accept-encoding"]);
  const lastModified = stat.mtime.toUTCString();
  const etag = `W/"${stat.size.toString(16)}-${stat.mtimeMs.toString(16)}-${stat.ctimeMs.toString(16)}"`;
  res.setHeader("ETag", etag);
  const inm = req.headers["if-none-match"];
  if (typeof inm === "string" && (inm === "*" || inm.split(",").some((tag) => tag.trim() === etag))) {
    res.writeHead(304);
    return void res.end();
  }
  const ims = inm === undefined ? req.headers["if-modified-since"] : undefined;
  if (typeof ims === "string") {
    const imsTime = Date.parse(ims);
    if (!Number.isNaN(imsTime) && Math.floor(stat.mtimeMs / 1000) <= Math.floor(imsTime / 1000)) {
      res.writeHead(304);
      return void res.end();
    }
  }

  const headers: Record<string, string | number> = {
    "Content-Type": contentType,
    "Last-Modified": lastModified,
  };
  if (gzip) headers["Content-Encoding"] = "gzip";
  else headers["Content-Length"] = stat.size;
  // Dev server: serve the viewer's own assets uncached so an esbuild rebuild —
  // and the page reload the file-watch triggers — loads the new JS/CSS.
  if (noStoreRoute(urlPath.split("?")[0])) headers["Cache-Control"] = "no-store";

  res.writeHead(200, headers);
  if (req.method === "HEAD") return void res.end();
  const stream = fs.createReadStream(realPath);
  // pipeline tears down every stream on cancellation or read/compression error.
  if (gzip) pipeline(stream, createGzip(), res, () => {});
  else pipeline(stream, res, () => {});
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
  if (res.req.method === "HEAD") {
    res.end();
    return;
  }
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
  data.chapterTitles = chapterTitles(ROOT, meta);
  data.version = repoVersion(ROOT);
  if (data.license) {
    appendVendorComponents(ROOT, data.license);
    attachLicenseText(ROOT, data.license);
  }
  data.definitionRegistry = bookDefinitionRegistry(ROOT, meta);
  data.references = bookReferences(ROOT, meta);
  data.katexMacros = katexMacros(macrosTexPath(ROOT, meta.dir));
  data.fixedMath = fixedMath(
    ROOT,
    path.join(meta.dir, String(meta.sourceMap)),
    data.katexMacros as Record<string, string>,
  );
  sendJson(res, data, 200, true);
}

// --- highlight cache ----------------------------------------------------------

// Precomputed tree-sitter highlight data (server/highlight-cache.ts). A static
// distribution ships the same URLs as files; here they are computed on demand
// and memoized by source hash, so an edit recomputes exactly one file.
function serveHighlightData(res: ServerResponse, meta: Manifest, rel: string): void {
  highlightService
    .get(meta, rel)
    .then((data) => {
      if (!data) return sendError(res, 404, "Not Found");
      sendJson(res, data);
    })
    .catch((error: Error) => {
      process.stderr.write(`[viewer] highlight request failed: ${error?.stack ?? error}\n`);
      sendError(res, 500, "Internal Server Error");
    });
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
      req.pause();
      reject(Object.assign(new Error("request body too large"), { code: 413 }));
      return;
    }
    let size = 0;
    const chunks: Buffer[] = [];
    req.on("data", (chunk: Buffer) => {
      size += chunk.length;
      if (size > limit) {
        reject(Object.assign(new Error("request body too large"), { code: 413 }));
        chunks.length = 0;
        req.pause();
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
      res.setHeader("Connection", "close");
      res.once("finish", () => req.destroy());
      sendJson(res, { ok: false, error: "request body too large" }, 413);
    } else {
      sendJson(res, { ok: false, error: String((error as Error).message ?? error) }, 500);
    }
  }
}

function handleGet(req: IncomingMessage, res: ServerResponse, route: string, url: URL): void {
  if (route === "/.well-known/ai-catalog.json") return serveStatic(req, res, `${VIEWER_DIR}/ai-catalog.json`);
  if (route === "/projects.json") {
    // The book selector in the viewer lists every served project.
    return sendJson(
      res,
      projects.projects.map((meta) => ({
        name: meta.name ?? meta.dir,
        selectorLabel: meta.selectorLabel,
        dir: meta.dir,
        mount: meta.mount,
      })),
    );
  }
  if (route === "/viewer-version") {
    // The live-reload safety net: the page compares this against the version it
    // loaded with and reloads on a mismatch (see src/reload-guard.ts).
    return sendText(res, viewerBuildVersion());
  }
  if (route === "/events" || route.startsWith("/lsp/") || route.startsWith("/watch/")) {
    if (req.method === "HEAD" && ["/events", "/lsp/events", "/watch/events"].includes(route)) {
      return startSse(res, () => {});
    }
    if (route === "/events") return streamCombined(req, res, sessionIdOf(url));
    if (route === "/lsp/info") {
      const projectDir = url.searchParams.get("project") ?? projects.defaultProject.dir;
      const lspRoot = projects.lspRoots.get(projectDir);
      if (lspRoot === undefined) return sendJson(res, { error: `unknown project: ${projectDir}` }, 404);
      return sendJson(res, {
        rootUri: pathToFileURL(lspRoot).href,
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
      Location: `${route === "/" ? projects.defaultMount : route}/${url.search}`,
      "Content-Length": "0",
    });
    return void res.end();
  }
  for (const meta of projects.byMount) {
    if (route === `${meta.mount}/correspondence.json` || route === `${meta.mount}/correspondence-lean.json`) {
      const source = url.searchParams.get("source") ?? "";
      if (!source.startsWith(`${meta.dir}/`) || !source.endsWith(".md") || !projects.isAllowedPath(`/${source}`))
        return sendError(res, 404, "Not Found");
      res.setHeader("Cache-Control", "no-cache");
      void correspondenceService
        .read(source, route.endsWith("/correspondence-lean.json"))
        .then((data) => sendJson(res, data, 200, true))
        .catch((error) => {
          console.error("[viewer] correspondence", error);
          sendJson(res, { status: "error", reason: "inspection-failed", formulas: [] }, 503);
        });
      return;
    }
    if (route === `${meta.mount}/manifest.json`) return sendManifest(res, meta);
  }
  for (const meta of projects.byMount) {
    const prefix = `${meta.mount}/pagefind/`;
    if (!route.startsWith(prefix)) continue;
    const asset = safeDecode(route.slice(prefix.length));
    if (!/^[a-zA-Z0-9_.-]+(?:\/[a-zA-Z0-9_.-]+)*$/.test(asset) || asset.split("/").includes(".."))
      return sendError(res, 404, "Not Found");
    void ensureSearchIndex(ROOT, meta)
      .then((directory) => {
        if (!directory) return sendError(res, 404, "Not Found");
        serveStatic(req, res, `/${path.relative(ROOT, path.join(directory, asset)).split(path.sep).join("/")}`);
      })
      .catch((error) => {
        console.error("[viewer] search index", error);
        sendError(res, 503, "Search index unavailable");
      });
    return;
  }
  for (const meta of projects.byMount) {
    const prefix = `${meta.mount}/highlight-cache/`;
    if (route.startsWith(prefix) && route.endsWith(".json")) {
      // Authorize the encoded path, as for static files: both consumers decode once.
      const rel = route.slice(prefix.length, -".json".length);
      if (!projects.isAllowedPath(`/${meta.dir}/${rel}`)) return sendError(res, 404, "Not Found");
      return void serveHighlightData(res, meta, safeDecode(rel));
    }
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
    if (!isTrustedRequest(host, origin, HOST)) return sendError(res, 403, "Forbidden");

    const url = new URL(req.url ?? "/", "http://127.0.0.1");
    const route = (req.url ?? "/").split("?", 1)[0].split("#", 1)[0];

    if (req.method === "POST") {
      void handlePost(req, res, route, url);
      return;
    }
    if (req.method === "GET" || req.method === "HEAD") {
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
  server.on("upgrade", (req, socket, head) => {
    buildLogs.upgrade(req, socket, head, (dir) => {
      if (!projects.projects.some((meta) => meta.dir === dir)) return null;
      let fd: number | undefined;
      try {
        fd = fs.openSync(path.join(ROOT, dir, "build/viewer-build.log"), "r");
        const size = fs.fstatSync(fd).size;
        const buffer = Buffer.alloc(Math.min(size, 1024 * 1024));
        fs.readSync(fd, buffer, 0, buffer.length, size - buffer.length);
        return buffer.toString("utf8");
      } catch {
        return "";
      } finally {
        if (fd !== undefined) fs.closeSync(fd);
      }
    });
  });
  server.on("clientError", (_err, socket) => socket.destroy());
  server.keepAliveTimeout = 120000;
  server.listen(PORT, BIND_ADDRESS, () => {
    const address = server.address();
    const port = typeof address === "object" && address !== null ? address.port : PORT;
    for (const meta of projects.projects) {
      process.stdout.write(`Formalization viewer: http://${URL_HOST}:${port}${meta.mount}/\n`);
    }
    process.stdout.write(`Lean LSP bridge: serving ${ROOT}\n`);
    openBrowser(`http://${URL_HOST}:${port}${projects.defaultMount}/`);
  });

  let shuttingDown = false;
  const shutdown = async (): Promise<void> => {
    if (shuttingDown) return;
    shuttingDown = true;
    // The watchexec supervisor waits for this process to exit before it can
    // restart the server, so a cleanup step that throws or hangs must never
    // keep the process alive: exit on any path, and force-exit on a timeout.
    const failsafe = setTimeout(() => process.exit(1), 15000);
    failsafe.unref();
    try {
      await watcher.shutdown();
      await builder.shutdown();
      await sessions.shutdownAll();
    } finally {
      process.exit(0);
    }
  };
  process.on("SIGINT", () => void shutdown());
  process.on("SIGTERM", () => void shutdown());
}

main();
