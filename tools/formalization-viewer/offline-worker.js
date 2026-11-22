// Mounted beside index.html so each book has its own cache and scope.
const base = new URL(self.registration.scope);
const prefix = `formalization-viewer:${base.pathname}:`;
const cacheName = `${prefix}v1`;
const shell = new URL("index.html", base).href;

function eligible(request) {
  const url = new URL(request.url);
  return (
    request.method === "GET" &&
    url.origin === base.origin &&
    url.pathname.startsWith(base.pathname) &&
    (request.mode === "navigate" ||
      /\.(?:html|css|js|mjs|json|wasm|scm|woff2?|ttf|pdf|md|lean|bib|tex|pagefind|pf_meta|pf_index|pf_fragment|pf_filter)$/.test(
        url.pathname,
      ))
  );
}

self.addEventListener("install", (event) => {
  event.waitUntil(
    (async () => {
      const cache = await caches.open(cacheName);
      await cache.add(new Request(shell, { cache: "reload" }));
      await self.skipWaiting();
    })(),
  );
});
self.addEventListener("activate", (event) => {
  event.waitUntil(
    (async () => {
      for (const name of await caches.keys()) {
        if (name.startsWith(prefix) && name !== cacheName) await caches.delete(name);
      }
      await self.clients.claim();
    })(),
  );
});

async function respond(request) {
  const url = new URL(request.url);
  if (url.pathname.endsWith(".pdf")) url.searchParams.delete("viewer-cache");
  const key = request.mode === "navigate" ? shell : url.href;
  // Cache Storage may be unavailable or full. Reading must still work online.
  const cache = await caches.open(cacheName).catch(() => null);
  try {
    const response = await fetch(request);
    // Partial PDF responses must never replace a complete document.
    if (response.status === 200 && response.type !== "opaque" && !response.redirected) {
      await cache?.put(key, response.clone()).catch(() => {});
    }
    return response;
  } catch (error) {
    // A complete cached PDF is also a valid response to a Range request.
    const saved = await cache?.match(key).catch(() => undefined);
    if (saved) return saved;
    throw error;
  }
}
self.addEventListener("fetch", (event) => {
  if (eligible(event.request)) event.respondWith(respond(event.request));
});
