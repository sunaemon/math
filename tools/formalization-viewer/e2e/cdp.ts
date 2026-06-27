// A minimal Chrome DevTools Protocol client for the viewer E2E tests, built on
// Node's global WebSocket and fetch (no npm dependency, no browser-driver
// library). It launches a headless Chrome, attaches to a fresh page target, and
// exposes just enough to drive the SPA: navigate, evaluate JS in the page, poll
// for a condition, and observe the network requests the page makes (so the live
// SSE/LSP connections can be asserted).

import { spawn, type ChildProcess } from "node:child_process";
import { existsSync, mkdtempSync, rmSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { freePort, sleep, waitForHttp } from "./util.ts";

// Locate a Chrome/Chromium binary: $CHROME / $CHROME_PATH first, then the usual
// macOS and Linux install paths. Throws a clear error if none is found.
export function findChrome(): string {
  const candidates = [
    process.env.CHROME,
    process.env.CHROME_PATH,
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    "/Applications/Chromium.app/Contents/MacOS/Chromium",
    "/usr/bin/google-chrome",
    "/usr/bin/google-chrome-stable",
    "/usr/bin/chromium",
    "/usr/bin/chromium-browser",
  ].filter((candidate): candidate is string => typeof candidate === "string" && candidate.length > 0);
  for (const candidate of candidates) {
    if (existsSync(candidate)) return candidate;
  }
  throw new Error(`Chrome/Chromium not found; set CHROME=/path/to/chrome. Tried:\n  ${candidates.join("\n  ")}`);
}

type CdpResult = Record<string, unknown>;
interface Pending {
  resolve: (result: CdpResult) => void;
  reject: (error: Error) => void;
}

export class CdpBrowser {
  private nextId = 0;
  private readonly pending = new Map<number, Pending>();
  private readonly pages = new Map<string, CdpPage>();
  private readonly proc: ChildProcess;
  private readonly ws: WebSocket;
  private readonly userDataDir: string;

  private constructor(proc: ChildProcess, ws: WebSocket, userDataDir: string) {
    this.proc = proc;
    this.ws = ws;
    this.userDataDir = userDataDir;
    ws.onmessage = (event: MessageEvent) => this.dispatch(String(event.data));
  }

  static async launch(): Promise<CdpBrowser> {
    const chrome = findChrome();
    const port = await freePort();
    const userDataDir = mkdtempSync(path.join(os.tmpdir(), "viewer-e2e-chrome-"));
    const proc = spawn(
      chrome,
      [
        `--remote-debugging-port=${port}`,
        `--user-data-dir=${userDataDir}`,
        // Recent Chrome rejects CDP WebSocket connections without an allowed
        // origin; the debugging port is loopback-only here, so allow any.
        "--remote-allow-origins=*",
        "--headless=new",
        "--no-first-run",
        "--no-default-browser-check",
        "--disable-gpu",
        "--disable-dev-shm-usage",
        "--disable-extensions",
        "about:blank",
      ],
      { stdio: "ignore" },
    );
    await waitForHttp(`http://127.0.0.1:${port}/json/version`);
    const version = (await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()) as {
      webSocketDebuggerUrl: string;
    };
    const ws = new WebSocket(version.webSocketDebuggerUrl);
    await new Promise<void>((resolve, reject) => {
      ws.onopen = () => resolve();
      ws.onerror = () => reject(new Error("failed to open the CDP WebSocket"));
    });
    return new CdpBrowser(proc, ws, userDataDir);
  }

  private dispatch(data: string): void {
    const message = JSON.parse(data) as {
      id?: number;
      error?: { message: string };
      result?: CdpResult;
      method?: string;
      params?: unknown;
      sessionId?: string;
    };
    if (typeof message.id === "number") {
      const pending = this.pending.get(message.id);
      if (!pending) return;
      this.pending.delete(message.id);
      if (message.error) pending.reject(new Error(message.error.message));
      else pending.resolve(message.result ?? {});
      return;
    }
    if (message.sessionId && message.method) {
      this.pages.get(message.sessionId)?.handleEvent(message.method, message.params);
    }
  }

  send(method: string, params: Record<string, unknown> = {}, sessionId?: string): Promise<CdpResult> {
    const id = ++this.nextId;
    return new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
      this.ws.send(JSON.stringify({ id, method, params, sessionId }));
    });
  }

  async newPage(): Promise<CdpPage> {
    const { targetId } = (await this.send("Target.createTarget", { url: "about:blank" })) as { targetId: string };
    const { sessionId } = (await this.send("Target.attachToTarget", { targetId, flatten: true })) as {
      sessionId: string;
    };
    const page = new CdpPage(this, sessionId);
    this.pages.set(sessionId, page);
    await page.init();
    return page;
  }

  async close(): Promise<void> {
    try {
      this.ws.close();
    } catch {
      // already closed
    }
    try {
      this.proc.kill("SIGKILL");
    } catch {
      // already exited
    }
    try {
      rmSync(this.userDataDir, { recursive: true, force: true });
    } catch {
      // best effort
    }
  }
}

export class CdpPage {
  private readonly requestUrls: string[] = [];
  private readonly browser: CdpBrowser;
  private readonly sessionId: string;

  constructor(browser: CdpBrowser, sessionId: string) {
    this.browser = browser;
    this.sessionId = sessionId;
  }

  async init(): Promise<void> {
    await this.browser.send("Page.enable", {}, this.sessionId);
    await this.browser.send("Runtime.enable", {}, this.sessionId);
    await this.browser.send("Network.enable", {}, this.sessionId);
  }

  handleEvent(method: string, params: unknown): void {
    if (method === "Network.requestWillBeSent") {
      const url = (params as { request?: { url?: string } }).request?.url;
      if (url) this.requestUrls.push(url);
    }
  }

  async navigate(url: string): Promise<void> {
    await this.browser.send("Page.navigate", { url }, this.sessionId);
    await this.waitFor("document.readyState === 'complete'", { timeout: 20000 });
  }

  // Evaluate a JS expression in the page and return its (JSON-serializable) value.
  async evaluate<T = unknown>(expression: string): Promise<T> {
    const evaluation = (await this.browser.send(
      "Runtime.evaluate",
      { expression, returnByValue: true, awaitPromise: true },
      this.sessionId,
    )) as {
      result: { value: T };
      exceptionDetails?: { exception?: { description?: string }; text?: string };
    };
    if (evaluation.exceptionDetails) {
      const detail = evaluation.exceptionDetails;
      throw new Error(`page evaluate failed: ${detail.exception?.description ?? detail.text ?? "unknown error"}`);
    }
    return evaluation.result.value;
  }

  // Poll an expression until it is truthy, or throw on timeout.
  async waitFor(expression: string, opts: { timeout?: number; interval?: number } = {}): Promise<void> {
    const timeout = opts.timeout ?? 10000;
    const interval = opts.interval ?? 100;
    const deadline = Date.now() + timeout;
    let lastError: unknown;
    while (Date.now() < deadline) {
      try {
        if (await this.evaluate<boolean>(`!!(${expression})`)) return;
      } catch (error) {
        lastError = error;
      }
      await sleep(interval);
    }
    throw new Error(`waitFor timed out: ${expression}${lastError ? ` (last error: ${String(lastError)})` : ""}`);
  }

  // The URLs the page has requested so far (including the EventSource stream).
  requests(): string[] {
    return [...this.requestUrls];
  }

  async waitForRequest(substring: string, timeoutMs = 10000): Promise<string> {
    const deadline = Date.now() + timeoutMs;
    while (Date.now() < deadline) {
      const hit = this.requestUrls.find((url) => url.includes(substring));
      if (hit) return hit;
      await sleep(100);
    }
    throw new Error(`no network request matched: ${substring}`);
  }
}
