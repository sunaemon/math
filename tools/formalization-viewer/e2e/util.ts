// Small shared helpers for the browser-driven E2E harness: a sleep, an
// ephemeral-port allocator, and an HTTP readiness poll. No npm dependency.

import { usablePort } from "../server/free-port.ts";

export const sleep = (ms: number): Promise<void> => new Promise((resolve) => setTimeout(resolve, ms));

// Bind :0 to let the OS pick a free port, then hand it back. The brief close
// race (another process grabbing it before we listen) is acceptable for tests.
export function freePort(): Promise<number> {
  return usablePort(0);
}

export async function waitForHttp(url: string, timeoutMs = 25000, signal?: AbortSignal): Promise<void> {
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    signal?.throwIfAborted();
    try {
      const response = await fetch(url, { signal, redirect: "manual" });
      if (response.status > 0) return;
    } catch {
      // not listening yet
    }
    await sleep(200);
  }
  throw new Error(`timed out waiting for ${url}`);
}
