// Launch the real viewer server (tools/formalization-viewer/server/serve.ts) for
// the E2E tests — the live HTTP + SSE bridge, not the static dist (which is a
// plain file server with no /events stream or LSP). Spawned with the current
// Node (which inherits mise's PATH, so serve.ts can find lake/watchexec) on an
// ephemeral port with the browser auto-open disabled.

import { spawn, type ChildProcess } from "node:child_process";
import path from "node:path";
import { waitExit, killGroup } from "../server/process-group.ts";
import { freePort, waitForHttp } from "./util.ts";

export interface ViewerServer {
  baseUrl: string;
  port: number;
  stop: () => Promise<void>;
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
      BOOKLINK_AUTOBUILD: process.env.BOOKLINK_AUTOBUILD ?? "0",
    },
    stdio: ["ignore", "ignore", "pipe"],
    detached: true,
  });
  let diagnostics = "";
  proc.stderr?.on("data", (chunk: Buffer) => {
    diagnostics = (diagnostics + chunk.toString("utf-8")).slice(-32768);
  });
  let stopping: Promise<void> | null = null;
  const stop = (): Promise<void> => {
    if (stopping) return stopping;
    stopping = (async () => {
      if (proc.pid === undefined || proc.exitCode !== null || proc.signalCode !== null) return;
      proc.kill("SIGTERM");
      // serve.ts has a 15-second failsafe for reaping its detached children.
      if (await waitExit(proc, 16000)) return;
      killGroup(proc, "SIGKILL");
      if (!(await waitExit(proc, 1000))) throw new Error("Viewer did not exit after SIGKILL");
    })();
    return stopping;
  };
  const controller = new AbortController();
  const failed = new Promise<never>((_resolve, reject) => {
    proc.once("error", reject);
    proc.once("close", (code, signal) => reject(new Error(`Viewer exited before readiness (${code ?? signal})`)));
  });
  try {
    await Promise.race([waitForHttp(`http://127.0.0.1:${port}/`, 25000, controller.signal), failed]);
  } catch (error) {
    await stop();
    throw new Error(`${(error as Error).message}\n${diagnostics}`);
  } finally {
    controller.abort();
  }
  return { baseUrl: `http://127.0.0.1:${port}`, port, stop };
}
