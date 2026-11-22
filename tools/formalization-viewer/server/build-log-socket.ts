// Outbound-only WebSocket transport for build logs; no application input is accepted.
import { createHash } from "node:crypto";
import type { IncomingMessage } from "node:http";
import type { Duplex } from "node:stream";
import { isTrustedRequest } from "./request-trust.ts";

const LIMIT = 1024 * 1024;

function frame(opcode: number, payload: Buffer): Buffer {
  const header = Buffer.alloc(payload.length < 126 ? 2 : payload.length <= 65535 ? 4 : 10);
  header[0] = 0x80 | opcode;
  if (header.length === 2) header[1] = payload.length;
  else if (header.length === 4) {
    header[1] = 126;
    header.writeUInt16BE(payload.length, 2);
  } else {
    header[1] = 127;
    header.writeBigUInt64BE(BigInt(payload.length), 2);
  }
  return Buffer.concat([header, payload]);
}

export class BuildLogSockets {
  private readonly bindHost: string;

  constructor(bindHost = "127.0.0.1") {
    this.bindHost = bindHost;
  }

  private readonly logs = new Map<string, string>();
  private readonly clients = new Map<string, Set<Duplex>>();

  publish(dir: string, text: string, reset: boolean): void {
    this.logs.set(dir, ((reset ? "" : (this.logs.get(dir) ?? "")) + text).slice(-LIMIT));
    for (const socket of this.clients.get(dir) ?? []) this.send(socket, { text, reset });
  }

  private send(socket: Duplex, message: { text: string; reset: boolean }): void {
    // A stalled browser must never hold up make or accumulate an unbounded queue.
    if (socket.writableLength > 2 * LIMIT) return void socket.destroy();
    socket.write(frame(1, Buffer.from(JSON.stringify(message))));
  }

  upgrade(req: IncomingMessage, socket: Duplex, head: Buffer, snapshot: (dir: string) => string | null): void {
    let url: URL;
    try {
      url = new URL(req.url ?? "/", "http://localhost");
    } catch {
      socket.end("HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\n");
      return;
    }
    const dir = url.searchParams.get("dir") ?? "";
    const key = req.headers["sec-websocket-key"];
    if (
      url.pathname !== "/build/log" ||
      !isTrustedRequest(req.headers.host, req.headers.origin, this.bindHost) ||
      req.method !== "GET" ||
      req.headers.upgrade?.toLowerCase() !== "websocket" ||
      req.headers["sec-websocket-version"] !== "13" ||
      typeof key !== "string" ||
      !/^[A-Za-z0-9+/]{22}==$/.test(key)
    ) {
      socket.end("HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\n");
      return;
    }
    const saved = snapshot(dir);
    if (saved === null) {
      socket.end("HTTP/1.1 404 Not Found\r\nConnection: close\r\n\r\n");
      return;
    }
    const accept = createHash("sha1")
      .update(key + "258EAFA5-E914-47DA-95CA-C5AB0DC85B11")
      .digest("base64");
    socket.write(
      `HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ${accept}\r\n\r\n`,
    );
    let clients = this.clients.get(dir);
    if (!clients) this.clients.set(dir, (clients = new Set()));
    clients.add(socket);
    socket.on("error", () => socket.destroy());
    socket.on("close", () => {
      clients.delete(socket);
      if (!clients.size) this.clients.delete(dir);
    });
    this.send(socket, { text: this.logs.get(dir) ?? saved.slice(-LIMIT), reset: true });
    // Browsers only send close/pong here. Parse masked control frames, including
    // split/coalesced packets; reject data frames and excessive input immediately.
    let pending = Buffer.alloc(0);
    const receive = (chunk: Buffer) => {
      pending = Buffer.concat([pending, chunk]);
      while (pending.length >= 2) {
        const opcode = pending[0] & 15;
        const length = pending[1] & 127;
        if (pending[0] !== (0x80 | opcode) || !(pending[1] & 128) || length > 125 || ![8, 9, 10].includes(opcode)) {
          socket.destroy();
          return;
        }
        if (pending.length < 6 + length) return;
        const payload = Buffer.from(pending.subarray(6, 6 + length));
        for (let i = 0; i < length; i++) payload[i] ^= pending[2 + (i % 4)];
        pending = pending.subarray(6 + length);
        if (opcode === 8) {
          socket.end(frame(8, Buffer.alloc(0)));
          return;
        }
        if (opcode === 9) socket.write(frame(10, payload));
      }
    };
    socket.on("data", receive);
    if (head.length) receive(head);
  }
}
