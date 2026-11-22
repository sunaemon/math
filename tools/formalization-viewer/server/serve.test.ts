import assert from "node:assert/strict";
import { request } from "node:http";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { gunzipSync } from "node:zlib";
import test from "node:test";
import { startViewerServer, type ViewerServer } from "../e2e/viewer-server.ts";

const SERVER_SOURCE = fileURLToPath(new URL(".", import.meta.url));

function fixture(): { root: string; base: string } {
  const base = fs.mkdtempSync(path.join(os.tmpdir(), "viewer-http-"));
  const root = path.join(base, "checkout with # %");
  const server = path.join(root, "tools/formalization-viewer/server");
  fs.mkdirSync(server, { recursive: true });
  // Keep the production entry point and all its authored dependencies together.
  for (const file of fs.readdirSync(SERVER_SOURCE)) {
    if (file.endsWith(".ts") && !file.endsWith(".test.ts"))
      fs.copyFileSync(path.join(SERVER_SOURCE, file), path.join(server, file));
  }
  const shared = path.join(root, "tools/formalization-viewer/src");
  fs.mkdirSync(shared, { recursive: true });
  for (const file of [
    "pdf-theme.ts",
    "link-preview.ts",
    "definition-registry.ts",
    "pdf-layout.ts",
    "math-source.ts",
    "katex-compat.ts",
    "definition-render.ts",
    "package.json",
  ])
    fs.copyFileSync(path.join(SERVER_SOURCE, "../src", file), path.join(shared, file));
  fs.cpSync(path.join(SERVER_SOURCE, "../vendor"), path.join(root, "tools/formalization-viewer/vendor"), {
    recursive: true,
  });
  fs.writeFileSync(path.join(root, "tools/formalization-viewer/index.html"), "<head></head><body>viewer</body>");
  fs.mkdirSync(path.join(root, "book/src"), { recursive: true });
  fs.writeFileSync(
    path.join(root, "book/manifest.json"),
    JSON.stringify({ mount: "/book", dir: "book", served: { src: ["md"] } }),
  );
  fs.writeFileSync(path.join(root, "book/src/chapter.md"), "source text");
  return { root: fs.realpathSync(root), base };
}

test("live HTTP routes give HEAD the GET headers, encode LSP roots, and close oversized requests", async () => {
  const { root, base } = fixture();
  let server: ViewerServer | undefined;
  try {
    server = await startViewerServer(root, "book");
    const baseUrl = server.baseUrl;
    const sharedSearch = "?v=1&layout=%7B%22tree%22%3A%7B%22pane%22%3A%22md%22%7D%7D&marker=example";
    for (const route of ["/", "/book"]) {
      const redirect = await fetch(baseUrl + route + sharedSearch, { redirect: "manual" });
      assert.equal(redirect.headers.get("location"), "/book/" + sharedSearch);
    }
    for (const route of ["/", "/book/", "/projects.json", "/book/manifest.json", "/book/src/chapter.md"]) {
      const get = await fetch(baseUrl + route, { redirect: "manual" });
      const body = await get.text();
      const head = await fetch(baseUrl + route, { method: "HEAD", redirect: "manual" });
      assert.equal(head.status, get.status, route);
      assert.equal(head.headers.get("location"), get.headers.get("location"), route);
      assert.equal(head.headers.get("content-type"), get.headers.get("content-type"), route);
      assert.equal(await head.text(), "", route);
      if (get.headers.has("content-length"))
        assert.equal(Number(head.headers.get("content-length")), Buffer.byteLength(body), route);
    }
    const info = (await (await fetch(baseUrl + "/lsp/info?project=book")).json()) as { rootUri: string };
    assert.equal(info.rootUri, pathToFileURL(path.join(root, "book")).href);
    assert.equal((await fetch(baseUrl + "/events", { method: "HEAD" })).status, 200);
    const rejected = await new Promise<{ status: number; connection: string | undefined }>((resolve, reject) => {
      const req = request(
        baseUrl + "/lsp/send",
        {
          method: "POST",
          headers: { "Content-Length": String(16 * 1024 * 1024 + 1) },
        },
        (res) => {
          res.resume();
          res.once("end", () => resolve({ status: res.statusCode!, connection: res.headers.connection }));
        },
      );
      req.once("error", reject);
      req.end();
    });
    assert.deepEqual(rejected, { status: 413, connection: "close" });
    assert.equal((await fetch(baseUrl + "/projects.json")).status, 200);
  } finally {
    await server?.stop();
    fs.rmSync(base, { recursive: true, force: true });
  }
});

test("large source maps negotiate gzip, preserve bytes, and keep HEAD and cache headers consistent", async () => {
  const { root, base } = fixture();
  let server: ViewerServer | undefined;
  const data = Buffer.from(JSON.stringify({ entries: Array(2000).fill({ title: "日本語のソース", line: 123 }) }));
  fs.mkdirSync(path.join(root, "book/build"));
  fs.writeFileSync(path.join(root, "book/build/map.json"), data);
  fs.writeFileSync(path.join(root, "book/build/book.pdf"), data);
  fs.writeFileSync(
    path.join(root, "book/manifest.json"),
    JSON.stringify({ mount: "/book", dir: "book", served: { src: ["md"], build: ["json", "pdf"] } }),
  );
  try {
    server = await startViewerServer(root, "book");
    const baseUrl = server.baseUrl;
    const raw = (route: string, headers: Record<string, string> = {}, method = "GET") =>
      new Promise<{ status: number; headers: import("node:http").IncomingHttpHeaders; body: Buffer }>(
        (resolve, reject) => {
          const req = request(baseUrl + route, { headers, method }, (res) => {
            const chunks: Buffer[] = [];
            res.on("data", (chunk: Buffer) => chunks.push(chunk));
            res.on("error", reject);
            res.on("end", () =>
              resolve({ status: res.statusCode!, headers: res.headers, body: Buffer.concat(chunks) }),
            );
          });
          req.on("error", reject);
          req.end();
        },
      );
    const html = await raw("/book/", { "Accept-Encoding": "gzip" });
    assert.equal(html.headers["content-encoding"], "gzip");
    assert.equal(html.headers.vary, "Accept-Encoding");
    assert.match(gunzipSync(html.body).toString(), /viewer-build-version/);
    const htmlHead = await raw("/book/", { "Accept-Encoding": "gzip" }, "HEAD");
    assert.equal(htmlHead.headers["content-encoding"], "gzip");
    assert.equal(htmlHead.body.length, 0);
    fs.writeFileSync(
      path.join(root, "tools/formalization-viewer/index.html"),
      "<head></head><body>updated viewer</body>",
    );
    const updated = await raw("/book/", { "Accept-Encoding": "gzip" });
    assert.match(gunzipSync(updated.body).toString(), /updated viewer/);
    assert.notDeepEqual(updated.body, html.body);
    const route = "/book/build/map.json";
    const compressed = await raw(route, { "Accept-Encoding": "gzip, deflate, br" });
    assert.equal(compressed.status, 200);
    assert.equal(compressed.headers["content-encoding"], "gzip");
    assert.equal(compressed.headers.vary, "Accept-Encoding");
    assert.equal(compressed.headers["content-length"], undefined);
    assert.deepEqual(gunzipSync(compressed.body), data);
    assert.ok(compressed.body.length < data.length / 2);
    for (const encoding of ["", "identity", "gzip;q=0, *;q=1", "br"]) {
      const plain = await raw(route, { "Accept-Encoding": encoding });
      assert.equal(plain.headers["content-encoding"], undefined, encoding);
      assert.equal(Number(plain.headers["content-length"]), data.length);
      assert.equal(plain.headers.vary, "Accept-Encoding");
      assert.deepEqual(plain.body, data);
    }
    for (const encoding of ["*", "br, gzip;q=0.5"]) {
      assert.equal((await raw(route, { "Accept-Encoding": encoding })).headers["content-encoding"], "gzip");
    }
    const head = await raw(route, { "Accept-Encoding": "gzip" }, "HEAD");
    for (const name of ["content-encoding", "content-type", "content-length", "vary", "last-modified"]) {
      assert.equal(head.headers[name], compressed.headers[name], name);
    }
    assert.equal(head.body.length, 0);
    const cached = await raw(route, {
      "Accept-Encoding": "gzip",
      "If-Modified-Since": compressed.headers["last-modified"]!,
    });
    assert.equal(cached.status, 304);
    assert.equal(cached.headers.vary, "Accept-Encoding");
    assert.equal(cached.body.length, 0);
    const validated = await raw(route, { "If-None-Match": String(compressed.headers.etag) });
    assert.equal(validated.status, 304);
    fs.writeFileSync(path.join(root, "book/build/map.json"), Buffer.from('{"updated":true}'));
    const changed = await raw(route, {
      "If-None-Match": String(compressed.headers.etag),
      "If-Modified-Since": compressed.headers["last-modified"]!,
    });
    assert.equal(changed.status, 200);
    assert.notEqual(changed.headers.etag, compressed.headers.etag);
    const manifest = await raw("/book/manifest.json");
    assert.equal(manifest.headers["cache-control"], "no-cache");
    assert.equal((await raw("/book/manifest.json", { "If-None-Match": String(manifest.headers.etag) })).status, 304);
    const pdf = await raw("/book/build/book.pdf", { "Accept-Encoding": "gzip" });
    assert.equal(pdf.headers["content-encoding"], undefined);
    assert.deepEqual(pdf.body, data);
    const small = await raw("/book/src/chapter.md", { "Accept-Encoding": "gzip" });
    assert.equal(small.headers["content-encoding"], undefined);
    assert.equal(small.body.toString(), "source text");
    // Browser fetch transparently decodes the negotiated response.
    assert.deepEqual(await (await fetch(baseUrl + route)).json(), { updated: true });
  } finally {
    await server?.stop();
    fs.rmSync(base, { recursive: true, force: true });
  }
});

test("startup failures include the child diagnostic and cleanup does not wait for readiness timeout", async () => {
  const { root, base } = fixture();
  fs.writeFileSync(path.join(root, "book/manifest.json"), "invalid json");
  try {
    await assert.rejects(startViewerServer(root, "book"), /invalid JSON/);
  } finally {
    fs.rmSync(base, { recursive: true, force: true });
  }
});

test("a cold viewer serves sources before selection and stays responsive during the requested build", async () => {
  const { root, base } = fixture();
  const saved = { ...process.env };
  let server: ViewerServer | undefined;
  let logSocket: WebSocket | undefined;
  try {
    fs.writeFileSync(
      path.join(root, "book/manifest.json"),
      JSON.stringify({
        mount: "/book",
        dir: "book",
        served: { src: ["md"], build: ["pdf", "json"] },
        pdf: "build/book-debug.pdf",
        sourceMap: "build/book-sourcemap.json",
      }),
    );
    const command = path.join(root, "fake-make");
    fs.writeFileSync(
      command,
      '#!/bin/sh\nset -e\necho live-build-output\nprintf "%s\\n" "$@" > requested\nwhile [ ! -f continue ]; do sleep 0.02; done\n' +
        'echo live-build-diagnostic >&2\nmkdir -p book/build\nprintf "test PDF" > book/build/book-debug.pdf\nprintf "{}" > book/build/book-sourcemap.json\n',
      { mode: 0o755 },
    );
    Object.assign(process.env, {
      BOOKLINK_MAKE: command,
      BOOKLINK_AUTOBUILD: "1",
      BOOKLINK_AUTOBUILD_DEBOUNCE_MS: "1",
    });
    server = await startViewerServer(root, "book");
    const url = server.baseUrl;
    assert.equal((await fetch(url + "/book/")).status, 200);
    assert.equal(await (await fetch(url + "/book/src/chapter.md")).text(), "source text");
    assert.equal(fs.existsSync(path.join(root, "requested")), false);
    assert.equal((await fetch(url + "/book/build/book-debug.pdf")).status, 404);
    logSocket = new WebSocket(url.replace(/^http/, "ws") + "/build/log?dir=book");
    let streamed = "";
    logSocket.addEventListener("message", (event) => {
      const message = JSON.parse(String(event.data)) as { text: string; reset: boolean };
      streamed = (message.reset ? "" : streamed) + message.text;
    });
    await new Promise<void>((resolve, reject) => {
      logSocket!.addEventListener("open", () => resolve(), { once: true });
      logSocket!.addEventListener("error", reject, { once: true });
    });
    const waitForLog = async (text: string): Promise<void> => {
      const deadline = Date.now() + 5000;
      while (!streamed.includes(text)) {
        assert.ok(Date.now() < deadline, `waiting for pushed log: ${text}`);
        await new Promise((resolve) => setTimeout(resolve, 10));
      }
    };
    const selection = await fetch(url + "/build/select?session=cold", {
      method: "POST",
      body: JSON.stringify({ pdf: "book/build/book-debug.pdf" }),
    });
    assert.equal(selection.status, 200);
    const waitFor = async (file: string): Promise<void> => {
      const deadline = Date.now() + 5000;
      while (!fs.existsSync(path.join(root, file))) {
        assert.ok(Date.now() < deadline, `waiting for ${file}`);
        await new Promise((resolve) => setTimeout(resolve, 10));
      }
    };
    await waitFor("requested");
    await waitForLog("live-build-output");
    assert.equal(
      fs.readFileSync(path.join(root, "requested"), "utf8"),
      "book/build/book-debug.pdf\nbook/build/book-sourcemap.json\n",
    );
    assert.equal(await (await fetch(url + "/book/src/chapter.md")).text(), "source text");
    fs.writeFileSync(path.join(root, "continue"), "");
    await waitFor("book/build/book-sourcemap.json");
    await waitForLog("live-build-diagnostic");
    await waitForLog("finished (exit 0)");
    assert.equal(await (await fetch(url + "/book/build/book-debug.pdf")).text(), "test PDF");
  } finally {
    logSocket?.close();
    await server?.stop();
    process.env = saved;
    fs.rmSync(base, { recursive: true, force: true });
  }
});

test("highlight authorization decodes URL paths exactly once, like static serving", async () => {
  const { root, base } = fixture();
  let server: ViewerServer | undefined;
  try {
    fs.mkdirSync(path.join(root, "book/%73rc"));
    fs.writeFileSync(path.join(root, "book/%73rc/hidden.md"), "outside the served source directory");
    fs.writeFileSync(path.join(root, "book/src/literal%73.md"), "# A literal percent filename");
    server = await startViewerServer(root, "book");
    for (const method of ["GET", "HEAD"]) {
      const rejected = await fetch(server.baseUrl + "/book/highlight-cache/%2573rc/hidden.md.json", { method });
      assert.equal(rejected.status, 404);
      assert.equal((await fetch(server.baseUrl + "/book/%2573rc/hidden.md", { method })).status, 403);
    }
    for (const rel of ["%73rc/chapter.md", "src/literal%2573.md"]) {
      const highlighted = await fetch(server.baseUrl + "/book/highlight-cache/" + rel + ".json");
      assert.equal(highlighted.status, 200, rel);
      assert.equal(((await highlighted.json()) as { version: number }).version, 1);
      assert.equal((await fetch(server.baseUrl + "/book/" + rel)).status, 200, rel);
    }
  } finally {
    await server?.stop();
    fs.rmSync(base, { recursive: true, force: true });
  }
});
