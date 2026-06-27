// Launch the real viewer server (tools/formalization-viewer/server/serve.ts) for
// the E2E tests — the live HTTP + SSE bridge, not the static dist (which is a
// plain file server with no /events stream or LSP). Spawned with the current
// Node (which inherits mise's PATH, so serve.ts can find lake/watchexec) on an
// ephemeral port with the browser auto-open disabled.

import { spawn, type ChildProcess } from "node:child_process";
import path from "node:path";
import { freePort, waitForHttp } from "./util.ts";

export interface ViewerServer {
  baseUrl: string;
  port: number;
  stop: () => void;
}

export async function startViewerServer(repoRoot: string, project: string): Promise<ViewerServer> {
  const port = await freePort();
  const serve = path.join(repoRoot, "tools", "formalization-viewer", "server", "serve.ts");
  const proc: ChildProcess = spawn(process.execPath, [serve], {
    cwd: repoRoot,
    env: {
      ...process.env,
      BOOKLINK_ROOT: repoRoot,
      BOOKLINK_PROJECT: project,
      BOOKLINK_VIEWER_PORT: String(port),
      BOOKLINK_OPEN_BROWSER: "0",
    },
    stdio: "ignore",
  });
  await waitForHttp(`http://127.0.0.1:${port}/`);
  return {
    baseUrl: `http://127.0.0.1:${port}`,
    port,
    stop: () => {
      try {
        // SIGTERM (not SIGKILL): serve.ts's signal handler reaps its Lean LSP
        // bridges and the watchexec file watcher, so they are not orphaned.
        proc.kill("SIGTERM");
      } catch {
        // already exited
      }
    },
  };
}
