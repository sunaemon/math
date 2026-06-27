// Live-reload client for the formalization viewer.
//
// Subscribes to the "watch" channel of the shared event stream, on which
// tools/formalization-viewer/server/serve.ts relays native filesystem events (watchexec:
// inotify on Linux, FSEvents on macOS) as { path } records with
// repository-relative paths. The viewer uses these to re-render the
// Markdown/Lean/TeX panes and reload the PDF on change.
//
// Degrades silently when the bridge/watcher is absent (plain static serving):
// the stream simply never delivers watch events.

import { eventStream } from "./event-stream.js";
import { parseWatchPath } from "./stream-frames.js";

export function connectFileWatch(onChange: (path: string) => void) {
  eventStream.onStreamEvent("watch", (data: string) => {
    const path = parseWatchPath(data);
    if (path) onChange(path);
  });
  eventStream.connectStream();
}
