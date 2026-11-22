import { trustedScriptURL } from "./safe-script-url.js";
// Start before loading book data, then replay assets downloaded before the
// first worker took control. This makes the first visit useful offline too.
async function registerOffline(): Promise<void> {
  if (!isSecureContext || !("serviceWorker" in navigator)) return;
  const base = new URL("./", location.href);
  await navigator.serviceWorker.register(trustedScriptURL(new URL("offline-worker.js", base)), {
    scope: base.pathname,
    updateViaCache: "none",
  });
  await navigator.serviceWorker.ready;
  if (!navigator.serviceWorker.controller) {
    await new Promise<void>((resolve) => {
      navigator.serviceWorker.addEventListener("controllerchange", () => resolve(), { once: true });
      if (navigator.serviceWorker.controller) resolve();
    });
  }
  const assets = performance.getEntriesByType("resource").map((entry) => entry.name);
  // Noncritical replay runs in the background; book loading can proceed.
  void Promise.allSettled(
    assets
      .filter((name) => {
        const url = new URL(name);
        return (
          url.origin === base.origin &&
          url.pathname.startsWith(base.pathname) &&
          /\.(?:js|mjs|css|woff2?|wasm)$/.test(url.pathname)
        );
      })
      .map((url) => fetch(url).then((response) => response.body?.cancel())),
  );
}

export async function initOffline(): Promise<void> {
  let timer: ReturnType<typeof setTimeout> | undefined;
  try {
    await Promise.race([
      registerOffline(),
      new Promise<void>((resolve) => {
        timer = setTimeout(resolve, 3000);
      }),
    ]);
  } finally {
    clearTimeout(timer);
  }
}
