// Small shared helpers for the browser-driven E2E harness: a sleep, an
// ephemeral-port allocator, and an HTTP readiness poll. No npm dependency.

import net from "node:net";

export const sleep = (ms: number): Promise<void> => new Promise((resolve) => setTimeout(resolve, ms));

// Bind :0 to let the OS pick a free port, then hand it back. The brief close
// race (another process grabbing it before we listen) is acceptable for tests.
export function freePort(): Promise<number> {
  return new Promise((resolve, reject) => {
    const server = net.createServer();
    server.on("error", reject);
    server.listen(0, "127.0.0.1", () => {
      const address = server.address();
      const port = typeof address === "object" && address ? address.port : 0;
      server.close(() => resolve(port));
    });
  });
}

export async function waitForHttp(url: string, timeoutMs = 25000): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    try {
      const response = await fetch(url);
      if (response.status > 0) return;
    } catch {
      // not listening yet
    }
    await sleep(200);
  }
  throw new Error(`timed out waiting for ${url}`);
}
