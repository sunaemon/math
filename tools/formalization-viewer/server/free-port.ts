#!/usr/bin/env node
// Print a usable TCP port on BOOKLINK_VIEWER_HOST (127.0.0.1 by default).
//
// Given a preferred port as argv[2] (0 or empty means "any"), bind it if it is
// free and echo it back; if it is already in use, fall back to an OS-assigned
// free port instead. The Makefile's formalization-viewer target resolves the
// viewer port through this once before launching, so a second viewer instance
// (or a stale listener on the preferred port) does not fail to bind a hardcoded
// port.
//
// There is an inherent race: the port is released here and re-bound by the
// server a moment later. Node's listen() sets SO_REUSEADDR and this is a
// developer tool, so the window is acceptable.

import { createServer } from "node:net";
import path from "node:path";
import { pathToFileURL } from "node:url";
import type { AddressInfo } from "node:net";

function bind(port: number, host: string): Promise<number | null> {
  return new Promise((resolve) => {
    const server = createServer();
    server.once("error", () => resolve(null));
    server.listen({ port, host, exclusive: true }, () => {
      const assigned = (server.address() as AddressInfo).port;
      server.close(() => resolve(assigned));
    });
  });
}

export async function usablePort(preferred: number, host = "127.0.0.1"): Promise<number> {
  if (preferred) {
    const bound = await bind(preferred, host);
    if (bound !== null) return bound;
  }
  const any = await bind(0, host);
  if (any === null) throw new Error(`Unable to allocate a port on ${host}`);
  return any;
}

async function main(): Promise<void> {
  const arg = process.argv[2] ?? "";
  const parsed = Number.parseInt(arg, 10);
  const preferred = Number.isNaN(parsed) ? 0 : parsed;
  process.stdout.write(`${await usablePort(preferred, process.env.BOOKLINK_VIEWER_HOST)}\n`);
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  void main();
}
