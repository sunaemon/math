import { PassThrough } from "node:stream";
import type { IncomingMessage } from "node:http";
import assert from "node:assert/strict";
import http from "node:http";
import { once } from "node:events";
import test from "node:test";
import { BuildLogSockets } from "./build-log-socket.ts";

test("WebSocket replays logs, pushes output, resets builds and recovers on reconnect", async () => {
  const logs = new BuildLogSockets();
  const server = http.createServer();
  server.on("upgrade", (req, socket, head) => {
    logs.upgrade(req, socket, head, (dir) => (dir === "book" ? "saved output\n" : null));
  });
  server.listen(0, "127.0.0.1");
  await once(server, "listening");
  const address = server.address();
  assert.ok(address && typeof address !== "string");
  const url = `ws://127.0.0.1:${address.port}/build/log?dir=book`;
  const sockets: WebSocket[] = [];
  const connect = () => {
    const socket = new WebSocket(url);
    sockets.push(socket);
    return socket;
  };
  const next = (socket: WebSocket) =>
    new Promise<{ text: string; reset: boolean }>((resolve, reject) => {
      socket.addEventListener("message", (event) => resolve(JSON.parse(String(event.data))), { once: true });
      socket.addEventListener("error", reject, { once: true });
    });
  try {
    const socket = connect();
    assert.deepEqual(await next(socket), { text: "saved output\n", reset: true });
    let message = next(socket);
    logs.publish("other-book", "invisible", false);
    logs.publish("book", "日本語 stdout\n", false);
    assert.deepEqual(await message, { text: "日本語 stdout\n", reset: false });
    message = next(socket);
    logs.publish("book", "", true);
    assert.deepEqual(await message, { text: "", reset: true });
    message = next(socket);
    logs.publish("book", "stderr: failed\n", false);
    assert.deepEqual(await message, { text: "stderr: failed\n", reset: false });
    const closed = new Promise<void>((resolve) => socket.addEventListener("close", () => resolve(), { once: true }));
    socket.close();
    await closed;
    const reconnected = connect();
    assert.deepEqual(await next(reconnected), { text: "stderr: failed\n", reset: true });
    message = next(reconnected);
    logs.publish("book", "x".repeat(70000), true);
    assert.equal((await message).text.length, 70000);
    logs.publish("book", "x".repeat(2 * 1024 * 1024), true);
    const bounded = connect();
    assert.equal((await next(bounded)).text.length, 1024 * 1024);
  } finally {
    await Promise.all(
      sockets
        .filter((socket) => socket.readyState !== WebSocket.CLOSED)
        .map(
          (socket) =>
            new Promise<void>((resolve) => {
              socket.addEventListener("close", () => resolve(), { once: true });
              socket.close();
            }),
        ),
    );
    await new Promise<void>((resolve) => server.close(() => resolve()));
  }
});

test("WebSocket rejects cross-origin upgrades and unknown books", async () => {
  const logs = new BuildLogSockets();
  const server = http.createServer();
  server.on("upgrade", (req, socket, head) => logs.upgrade(req, socket, head, () => null));
  server.listen(0, "127.0.0.1");
  await once(server, "listening");
  const address = server.address();
  assert.ok(address && typeof address !== "string");
  try {
    for (const [origin, status] of [
      ["https://example.com", 400],
      [`http://127.0.0.1:${address.port}`, 404],
    ] as const) {
      const result = await new Promise<number | undefined>((resolve, reject) => {
        const req = http.request(
          {
            host: "127.0.0.1",
            port: address.port,
            path: "/build/log?dir=unknown",
            headers: {
              Origin: origin,
              Connection: "Upgrade",
              Upgrade: "websocket",
              "Sec-WebSocket-Version": "13",
              "Sec-WebSocket-Key": "dGhlIHNhbXBsZSBub25jZQ==",
            },
          },
          (res) => {
            res.resume();
            resolve(res.statusCode);
          },
        );
        req.on("error", reject);
        req.end();
      });
      assert.equal(result, status);
    }
  } finally {
    await new Promise<void>((resolve) => server.close(() => resolve()));
  }
});

test("malformed upgrade URLs return 400 without invoking the snapshot", async () => {
  const socket = new PassThrough();
  let response = "";
  socket.on("data", (chunk) => {
    response += chunk;
  });
  const ended = once(socket, "end");
  new BuildLogSockets().upgrade({ url: "http://[", headers: {} } as IncomingMessage, socket, Buffer.alloc(0), () => {
    assert.fail("invalid URL must not reach the snapshot");
  });
  await ended;
  assert.match(response, /^HTTP\/1.1 400 Bad Request/);
});
