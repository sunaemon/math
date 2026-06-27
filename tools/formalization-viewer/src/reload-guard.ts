// Live-reload safety net for the formalization viewer.
//
// The fast path for picking up an esbuild rebuild is the file-watch event:
// build/*.js changes, a `watch` SSE frame arrives, and app.ts reloads the page.
// But that path can miss a rebuild — the SSE stream dropped and reconnected, the
// OS coalesced the event, or a build finished after the page had already loaded.
// When that happens the reader is stranded on stale JS until they reload by hand
// (the recurring "I had to reload" papercut).
//
// This module closes the gap with a version check. The server injects the build
// it served into index.html (<meta name="viewer-build-version">) and exposes the
// current build at GET /viewer-version. We re-check that endpoint whenever the
// tab is likely stale — on SSE reconnect and whenever the tab regains focus — and
// reload if it no longer matches what we loaded. So even if every watch event is
// missed, the moment the reader looks at the viewer it self-heals.
//
// Degrades to a no-op when there is no version meta or the endpoint 404s (e.g. a
// static dist export with no live server): nothing to compare against, so the
// page simply never auto-reloads.

import { eventStream } from "./event-stream.js";

function loadedVersion(): string | null {
  const meta = document.querySelector('meta[name="viewer-build-version"]');
  const content = meta?.getAttribute("content")?.trim();
  return content ? content : null;
}

let baseline: string | null = null;
let reloading = false;
let inFlight: Promise<void> | null = null;

// Fetch the server's current build version and reload if it differs from the one
// this page loaded with. Coalesces concurrent calls and never reloads twice.
export function checkForNewBuild(): Promise<void> {
  if (reloading || baseline === null) return Promise.resolve();
  if (inFlight) return inFlight;
  inFlight = fetch("/viewer-version", { cache: "no-store" })
    .then((res) => (res.ok ? res.text() : null))
    .then((current) => {
      const version = current?.trim();
      // Only reload on a definite, different version. A failed/empty fetch (a
      // brief server blip, a static export) must not trigger a reload loop.
      if (version && version !== baseline) {
        reloading = true;
        window.location.reload();
      }
    })
    .catch(() => {
      // Network/endpoint error: leave the page as-is and try again next trigger.
    })
    .finally(() => {
      inFlight = null;
    });
  return inFlight;
}

// Wire the version check to the moments a stale page is most likely to be
// noticed: SSE reconnect (events may have been missed while disconnected) and
// the tab regaining focus/visibility (the reader returning to the viewer).
export function installReloadGuard(): void {
  baseline = loadedVersion();
  if (baseline === null) return; // no version to compare against; stay a no-op.

  eventStream.onStreamOpen(({ reconnect }) => {
    if (reconnect) void checkForNewBuild();
  });

  document.addEventListener("visibilitychange", () => {
    if (document.visibilityState === "visible") void checkForNewBuild();
  });
  window.addEventListener("focus", () => void checkForNewBuild());
}
