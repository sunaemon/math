// Build-status client for the formalization viewer.
//
// Subscribes to the "build" channel of the shared event stream, on which
// tools/formalization-viewer/server/serve.ts relays { dir, state } records when
// the server's book-builder starts and finishes an auto-build triggered by a
// Markdown edit (state: "building" | "done" | "failed"). The viewer uses these
// to show a "Building…" indicator while the debug PDF and source map regenerate.
//
// Degrades silently when the bridge/builder is absent (plain static serving):
// the stream simply never delivers build events.

import { eventStream } from "./event-stream.js";
import { parseBuildStatus, selectPdfRequest, type BuildStatus } from "./stream-frames.js";

export type { BuildStatus };

// Tell the server which rendered PDF this tab is showing (repo-relative path) so
// the auto-build resolves its target from the selection. Fire-and-forget: a
// missing builder/bridge just means the POST is ignored.
export function reportSelectedPdf(repoRelPath: string) {
  const request = selectPdfRequest(eventStream.sessionQuery, repoRelPath);
  if (!request) return;
  fetch(request.url, {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: request.body,
  }).catch(() => {
    // Ignore: the builder is optional (e.g. static serving).
  });
}

export function connectBuildStatus(onStatus: (status: BuildStatus) => void, onReconnect?: () => void) {
  eventStream.onStreamEvent("build", (data: string) => {
    const status = parseBuildStatus(data);
    if (status) onStatus(status);
  });
  // The server drops a session's recorded selection when its stream closes, so
  // after a reconnect (server restart, dev rebuild, network blip) re-report the
  // viewed PDF; otherwise the auto-build silently reverts to the debug default.
  if (onReconnect) eventStream.onStreamOpen(({ reconnect }) => reconnect && onReconnect());
  eventStream.connectStream();
}
