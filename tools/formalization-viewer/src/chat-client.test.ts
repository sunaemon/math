import test from "node:test";
import assert from "node:assert/strict";
import crypto from "node:crypto";
import { BrowserChat, verifyChatIdentity, openaiEvents } from "./chat-client.ts";

const { privateKey, publicKey } = crypto.generateKeyPairSync("rsa", { modulusLength: 2048 });
const key = { ...publicKey.export({ format: "jwk" }), kid: "test-key", alg: "RS256", use: "sig" };
const sign = (claims: object) => {
  const encode = (data: unknown) => Buffer.from(JSON.stringify(data)).toString("base64url");
  const source = `${encode({ alg: "RS256", kid: key.kid })}.${encode(claims)}`;
  return `${source}.${crypto.sign("RSA-SHA256", Buffer.from(source), privateKey).toString("base64url")}`;
};
const claims = () => ({
  iss: "https://auth.openai.com",
  aud: "issued-client",
  sub: "reader",
  email: "reader@example.test",
  nonce: "nonce",
  exp: Math.floor(Date.now() / 1000) + 3600,
  iat: Math.floor(Date.now() / 1000),
});
function memoryStore(): Storage {
  const values = new Map<string, string>();
  return {
    getItem: (key) => values.get(key) ?? null,
    setItem: (key, value) => {
      values.set(key, value);
    },
    removeItem: (key) => {
      values.delete(key);
    },
    clear: () => values.clear(),
    key: (index) => [...values.keys()][index] ?? null,
    get length() {
      return values.size;
    },
  };
}
const sse = (events: object[]) =>
  new Response(events.map((event) => `data: ${JSON.stringify(event)}\n\n`).join(""), {
    headers: { "Content-Type": "text/event-stream" },
  });

test("browser verifies ID-token signatures and rejects wrong identity claims or unknown keys", async () => {
  assert.equal((await verifyChatIdentity(sign(claims()), "issued-client", "nonce", [key])).sub, "reader");
  for (const change of [
    { iss: "https://evil.test" },
    { aud: "other" },
    { nonce: "other" },
    { exp: 0 },
    { sub: "" },
    { aud: ["issued-client", "other"], azp: "other" },
  ])
    await assert.rejects(verifyChatIdentity(sign({ ...claims(), ...change }), "issued-client", "nonce", [key]));
  const bad = sign(claims()).split(".");
  bad[1] = Buffer.from(JSON.stringify({ ...claims(), sub: "attacker" })).toString("base64url");
  await assert.rejects(verifyChatIdentity(bad.join("."), "issued-client", "nonce", [key]), /署名/);
  await assert.rejects(verifyChatIdentity(sign(claims()), "issued-client", "nonce", []), /公開鍵/);
});

test("browser-only OAuth relays the callback, validates PKCE and persists only in the browser tab", async () => {
  const store = memoryStore();
  let authorization: URL;
  let exchange: URLSearchParams | undefined;
  let tokenCalls = 0;
  const request: typeof fetch = async (url, init) => {
    assert.ok(
      String(url).startsWith("https://auth.openai.com/") || String(url).startsWith("https://api.openai.com/v1/"),
    );
    assert.equal(init?.credentials, "omit");
    if (String(url).endsWith("/oauth/token")) {
      tokenCalls++;
      const body = init?.body as URLSearchParams;
      exchange = body;
      assert.equal(body.get("client_id"), "issued-client");
      assert.equal(body.get("redirect_uri"), authorization.searchParams.get("redirect_uri"));
      assert.equal(
        crypto.createHash("sha256").update(body.get("code_verifier")!).digest("base64url"),
        authorization.searchParams.get("code_challenge"),
      );
      return Response.json({
        access_token: "test-access",
        token_type: "Bearer",
        expires_in: 3600,
        scope: "chatgpt.tokens.use.direct resource.invoke",
        id_token: sign({ ...claims(), nonce: authorization.searchParams.get("nonce") }),
      });
    }
    if (String(url).endsWith("/models"))
      return Response.json({
        models: [
          { slug: "gpt-example", display_name: "Example", visibility: "list" },
          { slug: "hidden", visibility: "hide" },
        ],
      });
    throw new Error("Unexpected endpoint");
  };
  const client = new BrowserChat([key], store, request);
  authorization = new URL((await client.begin()).url);
  assert.equal(authorization.searchParams.get("client_id"), "dynamic_agent_client");
  assert.ok(!authorization.searchParams.get("scope")!.includes("offline_access"));
  const callback = new URL(authorization.searchParams.get("redirect_uri")!);
  callback.search = new URLSearchParams({
    code: "test-code",
    state: "incorrect",
    client_id: "issued-client",
  }).toString();
  await assert.rejects(client.complete(callback.href), /一致しません/);
  assert.equal(client.status().pending, true);
  callback.searchParams.set("state", authorization.searchParams.get("state")!);
  // A page reload retains the pending transaction and PKCE verifier.
  const restored = new BrowserChat([key], store, request);
  await restored.complete(callback.href);
  assert.ok(exchange);
  assert.equal(restored.status().provider, "chatgpt");
  assert.doesNotMatch(JSON.stringify(restored.status()), /test-access/);
  assert.deepEqual(await restored.models(), [{ id: "gpt-example", name: "Example" }]);
  const saved = JSON.parse(store.getItem("viewer-chat-profile-v1")!);
  assert.equal(saved.refresh, undefined);
  assert.equal(saved.idToken, undefined);
  saved.expires = 0;
  store.setItem("viewer-chat-profile-v1", JSON.stringify(saved));
  const expired = new BrowserChat([key], store, request);
  assert.equal(expired.status().provider, null);
  await assert.rejects(expired.models(), /接続してください/);
  assert.equal(tokenCalls, 1);
  const again = new URL((await expired.begin()).url);
  assert.equal(again.searchParams.get("client_id"), "dynamic_agent_client");
  assert.equal(again.searchParams.get("id_token_hint"), null);
  expired.disconnect();
  assert.equal(expired.status().provider, null);
  assert.equal(store.length, 0);
});

test("browser API keys never persist and inference goes directly to OpenAI with terminal event checks", async () => {
  const store = memoryStore();
  let payload: any;
  let mode = "complete";
  const requests: string[] = [];
  const client = new BrowserChat([], store, async (url, init) => {
    requests.push(String(url));
    assert.equal(init?.credentials, "omit");
    assert.ok(init);
    assert.equal((init.headers as Record<string, string>).Authorization, "Bearer test-api-key-12345");
    if (String(url).endsWith("/models")) return Response.json({ data: [{ id: "gpt-example" }, { id: "tts-example" }] });
    payload = JSON.parse(init?.body as string);
    if (mode === "failed")
      return sse([
        { type: "response.output_text.delta", delta: "partial" },
        { type: "response.failed", response: { error: { code: "usage_limit" } } },
      ]);
    if (mode === "cut") return sse([{ type: "response.output_text.delta", delta: "partial" }]);
    return sse([{ type: "response.output_text.delta", delta: "数式 $x=1$." }, { type: "response.completed" }]);
  });
  client.setApiKey("test-api-key-12345");
  assert.equal(store.length, 0);
  assert.equal(new BrowserChat([], store).status().provider, null);
  assert.deepEqual(await client.models(), [{ id: "gpt-example", name: "gpt-example" }]);
  const messages = [{ role: "user" as const, content: "What does this mean?" }];
  let answer = "";
  for await (const delta of client.respond("gpt-example", messages, new AbortController().signal)) answer += delta;
  assert.equal(answer, "数式 $x=1$.");
  assert.equal(payload.store, false);
  assert.equal(payload.stream, true);
  assert.deepEqual(payload.input, messages);
  const collect = async () => {
    for await (const _ of client.respond("gpt-example", messages, new AbortController().signal)) {
      /* consume */
    }
  };
  mode = "failed";
  await assert.rejects(collect(), /usage_limit/);
  mode = "cut";
  await assert.rejects(collect(), /完了する前/);
  assert.ok(requests.every((url) => url.startsWith("https://api.openai.com/v1/")));
  client.disconnect();
  await assert.rejects(collect(), /接続/);
});

test("browser SSE parser preserves split UTF-8 and trailing terminal events", async () => {
  const bytes = new TextEncoder().encode(
    'data: {"type":"response.output_text.delta","delta":"数式"}\r\n\r\ndata: {"type":"response.completed"}',
  );
  const stream = new ReadableStream<Uint8Array>({
    start(controller) {
      for (let i = 0; i < bytes.length; i += 3) controller.enqueue(bytes.slice(i, i + 3));
      controller.close();
    },
  });
  const events = [];
  for await (const event of openaiEvents(stream)) events.push(event);
  assert.equal(events[0].delta, "数式");
  assert.equal(events[1].type, "response.completed");
});

test("cancelled browser sign-in cannot replace a new API connection", async () => {
  const store = memoryStore();
  let finish!: (value: Response) => void;
  const client = new BrowserChat(
    [key],
    store,
    () =>
      new Promise((resolve) => {
        finish = resolve;
      }),
  );
  const auth = new URL((await client.begin()).url),
    callback = new URL(auth.searchParams.get("redirect_uri")!);
  callback.search = new URLSearchParams({
    state: auth.searchParams.get("state")!,
    code: "test-code",
    client_id: "issued-client",
  }).toString();
  const pending = client.complete(callback.href);
  client.setApiKey("new-test-api-key-12345");
  finish(
    Response.json({
      access_token: "old-access",
      refresh_token: "old-refresh",
      expires_in: 3600,
      token_type: "Bearer",
      scope: "resource.invoke chatgpt.tokens.use.direct",
      id_token: sign({ ...claims(), nonce: auth.searchParams.get("nonce") }),
    }),
  );
  await assert.rejects(pending, /取り消され/);
  assert.equal(client.status().provider, "api");
  assert.equal(store.length, 0);
});

test("a network failure at the token exchange keeps the login attempt retryable", async () => {
  const store = memoryStore();
  let authorization: URL;
  let tokenCalls = 0;
  const client = new BrowserChat([key], store, async (url) => {
    if (String(url).endsWith("/oauth/token")) {
      tokenCalls++;
      if (tokenCalls === 1) throw new TypeError("fetch failed");
      return Response.json({
        access_token: "test-access",
        token_type: "Bearer",
        expires_in: 3600,
        scope: "chatgpt.tokens.use.direct resource.invoke",
        id_token: sign({ ...claims(), nonce: authorization.searchParams.get("nonce") }),
      });
    }
    throw new Error("Unexpected endpoint");
  });
  authorization = new URL((await client.begin()).url);
  const callback = new URL(authorization.searchParams.get("redirect_uri")!);
  callback.search = new URLSearchParams({
    code: "test-code",
    state: authorization.searchParams.get("state")!,
    client_id: "issued-client",
  }).toString();
  await assert.rejects(client.complete(callback.href), /直接接続できません/);
  assert.equal(client.status().pending, true, "the attempt survives a failure before the provider answered");
  // The same callback URL completes once the network is back.
  await client.complete(callback.href);
  assert.equal(client.status().provider, "chatgpt");
  assert.equal(tokenCalls, 2);
});

test("a 5xx from the token endpoint keeps the login attempt retryable", async () => {
  const store = memoryStore();
  let authorization: URL;
  let tokenCalls = 0;
  const client = new BrowserChat([key], store, async (url) => {
    if (String(url).endsWith("/oauth/token")) {
      tokenCalls++;
      if (tokenCalls === 1) return Response.json({ error: "temporarily_unavailable" }, { status: 503 });
      return Response.json({
        access_token: "test-access",
        token_type: "Bearer",
        expires_in: 3600,
        scope: "chatgpt.tokens.use.direct resource.invoke",
        id_token: sign({ ...claims(), nonce: authorization.searchParams.get("nonce") }),
      });
    }
    throw new Error("Unexpected endpoint");
  });
  authorization = new URL((await client.begin()).url);
  const callback = new URL(authorization.searchParams.get("redirect_uri")!);
  callback.search = new URLSearchParams({
    code: "test-code",
    state: authorization.searchParams.get("state")!,
    client_id: "issued-client",
  }).toString();
  await assert.rejects(client.complete(callback.href), /OpenAI HTTP 503/);
  assert.equal(client.status().pending, true, "the attempt survives a server error");
  await client.complete(callback.href);
  assert.equal(client.status().provider, "chatgpt");
  assert.equal(tokenCalls, 2);
});

test("a rejected exchange consumes the attempt and a retry reports it as used, not expired", async () => {
  const store = memoryStore();
  let authorization: URL;
  const client = new BrowserChat([key], store, async (url) => {
    if (String(url).endsWith("/oauth/token")) return Response.json({ error: "invalid_grant" }, { status: 400 });
    throw new Error("Unexpected endpoint");
  });
  authorization = new URL((await client.begin()).url);
  const callback = new URL(authorization.searchParams.get("redirect_uri")!);
  callback.search = new URLSearchParams({
    code: "test-code",
    state: authorization.searchParams.get("state")!,
    client_id: "issued-client",
  }).toString();
  await assert.rejects(client.complete(callback.href), /OpenAI HTTP 400/);
  assert.equal(client.status().pending, false, "a rejection spends the attempt");
  await assert.rejects(client.complete(callback.href), /使用済み/);
});

test("disconnect removes the persisted host ID and the next login generates a new one", async () => {
  const local = memoryStore();
  const previous = Object.getOwnPropertyDescriptor(globalThis, "localStorage");
  Object.defineProperty(globalThis, "localStorage", { configurable: true, value: local });
  try {
    const client = new BrowserChat([key], memoryStore());
    const first = new URL((await client.begin()).url).searchParams.get("ext_agent_host_id");
    assert.ok(first);
    client.disconnect();
    assert.equal(local.getItem("viewer-chat-host-id"), null);
    const second = new URL((await client.begin()).url).searchParams.get("ext_agent_host_id");
    assert.ok(second);
    assert.notEqual(first, second);
    Object.defineProperty(globalThis, "localStorage", {
      configurable: true,
      get: () => {
        throw new Error("blocked");
      },
    });
    assert.doesNotThrow(() => client.disconnect());
    assert.equal(client.status().pending, false);
  } finally {
    if (previous) Object.defineProperty(globalThis, "localStorage", previous);
    else Reflect.deleteProperty(globalThis, "localStorage");
  }
});

test("untrusted JSON parser failures use readable errors without response contents", async () => {
  const client = new BrowserChat([], memoryStore(), async () => new Response("<html>private-provider-detail</html>"));
  client.setApiKey("test-api-key-12345");
  await assert.rejects(client.models(), /^Error: OpenAI の応答を読み取れませんでした/);
  for (const ending of ["", "\n\n"]) {
    const stream = new ReadableStream<Uint8Array>({
      start(controller) {
        controller.enqueue(new TextEncoder().encode("data: {private-provider-detail" + ending));
        controller.close();
      },
    });
    await assert.rejects(async () => {
      for await (const _ of openaiEvents(stream)) {
        /* consume */
      }
    }, /^Error: チャットの応答を読み取れませんでした/);
    assert.equal(stream.locked, false);
  }
  for (const header of ["bad-json", "null", "[]"]) {
    const token = Buffer.from(header).toString("base64url") + ".e30.signature";
    await assert.rejects(
      verifyChatIdentity(token, "issued-client", "nonce", [key]),
      /^Error: ID トークンの形式が不正です/,
    );
  }
});

test("ID-token times allow bounded clock skew and reject malformed or future issuance", async () => {
  const now = Math.floor(Date.now() / 1000);
  for (const times of [
    { iat: now - 3600, exp: now - 120 },
    { iat: now + 120, nbf: now + 120, exp: now + 3600 },
  ])
    assert.equal(
      (await verifyChatIdentity(sign({ ...claims(), ...times }), "issued-client", "nonce", [key])).sub,
      "reader",
    );
  for (const times of [
    { exp: now - 240 },
    { iat: now + 240 },
    { nbf: now + 240 },
    { iat: undefined },
    { iat: "today" },
    { nbf: "tomorrow" },
    { iat: now + 100, exp: now + 50 },
  ])
    await assert.rejects(verifyChatIdentity(sign({ ...claims(), ...times }), "issued-client", "nonce", [key]));
});
