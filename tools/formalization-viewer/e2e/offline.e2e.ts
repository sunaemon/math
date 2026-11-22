import { test } from "node:test";
import assert from "node:assert/strict";
import { createServer } from "node:http";
import { readFileSync } from "node:fs";
import { CdpBrowser } from "./cdp.ts";

test("first visit caches reading assets, refreshes online, and reloads offline", async (t) => {
  let revision = 1;
  const html = `<!doctype html><link rel="stylesheet" href="style.css">
    <body><script type="module">
    import {initOffline} from './build/offline.js';
    await initOffline();
    document.body.dataset.revision = await (await fetch('manifest.json',{cache:'no-store'})).text();
    </script>`;
  const server = createServer((req, res) => {
    const route = new URL(req.url!, "http://localhost").pathname;
    if (route === "/book/offline-worker.js") {
      res.setHeader("Content-Type", "text/javascript");
      res.end(readFileSync(new URL("../offline-worker.js", import.meta.url)));
    } else if (/^\/book\/build\/[a-zA-Z0-9_-]+\.js$/.test(route)) {
      // Browser entries can import shared chunks; the fixture serves the same
      // flat module directory as the live server and static export.
      try {
        const file = route.slice("/book/build/".length);
        const script = readFileSync(new URL(`../build/${file}`, import.meta.url));
        res.setHeader("Content-Type", "text/javascript");
        res.end(script);
      } catch {
        res.writeHead(404);
        res.end("missing module");
      }
    } else if (route === "/book/manifest.json") {
      res.end(String(revision));
    } else if (route === "/book/book.pdf") {
      if (req.headers.range) res.writeHead(206, { "Content-Range": "bytes 0-3/8" });
      res.end(req.headers.range ? "part" : "full-pdf");
    } else if (route === "/book/style.css") {
      res.setHeader("Content-Type", "text/css");
      res.end("body {color: green}");
    } else if (route === "/book/" || route === "/book/index.html") {
      res.setHeader("Content-Type", "text/html");
      res.end(html);
    } else {
      res.writeHead(404);
      res.end("missing");
    }
  });
  await new Promise<void>((resolve) => server.listen(0, "127.0.0.1", resolve));
  t.after(() => {
    server.closeAllConnections();
    server.close();
  });
  const address = server.address();
  assert.ok(address && typeof address !== "string");
  const url = `http://127.0.0.1:${address.port}/book/`;
  const browser = await CdpBrowser.launch();
  t.after(() => browser.close());
  const tab = await browser.newPage();
  await tab.navigate(url);
  await tab.waitFor("document.body.dataset.revision === '1'");
  assert.equal(await tab.evaluate("fetch('book.pdf?viewer-cache=1').then(r=>r.text())"), "full-pdf");
  assert.equal(
    await tab.evaluate("fetch('book.pdf?viewer-cache=1',{headers:{Range:'bytes=0-3'}}).then(r=>r.status)"),
    206,
  );
  revision = 2;
  assert.equal(await tab.evaluate("fetch('manifest.json').then(r=>r.text())"), "2");
  await tab.evaluate("fetch('missing.json').then(r=>r.status)");
  await tab.waitFor(`(async()=>{const c=await caches.open('formalization-viewer:/book/:v1');
    return !!(await c.match(location.origin+'/book/build/offline.js')) && !!(await c.match(location.origin+'/book/style.css'));})()`);
  server.closeAllConnections();
  await new Promise<void>((resolve) => server.close(() => resolve()));
  await tab.navigate(url + "?marker=another#passage");
  await tab.waitFor("document.body.dataset.revision === '2'");
  assert.equal(
    await tab.evaluate("fetch('book.pdf?viewer-cache=99',{headers:{Range:'bytes=0-3'}}).then(r=>r.text())"),
    "full-pdf",
  );
  assert.equal(await tab.evaluate("fetch('missing.json').then(()=>false,()=>true)"), true);
  assert.equal(await tab.evaluate("fetch('/other/manifest.json').then(()=>false,()=>true)"), true);
  assert.equal(await tab.evaluate("fetch('manifest.json',{method:'POST'}).then(()=>false,()=>true)"), true);
});
