// A `lake env lean --server` client with LSP framing, used by the static cache
// generator. Tracks request responses, per-file diagnostics, and per-file
// elaboration progress (`$/lean/fileProgress` with an empty processing list).
//
// The Python original used a condition variable; here a list of one-shot waiter
// callbacks, woken on every inbound message, plays the same role on Node's
// single-threaded loop.

import { killGroup, terminate } from "./process-group.ts";
import { LspFrames } from "./lsp-frames.ts";
import { spawnLean, type LeanProc, type SpawnLean } from "./lsp-process.ts";

export interface JsonRpcMessage {
  id?: number | string;
  method?: string;
  params?: Record<string, unknown>;
  result?: unknown;
  error?: unknown;
}

export class LeanServer {
  private readonly proc: LeanProc;
  private nextId = 1;
  readonly responses = new Map<number, JsonRpcMessage>();
  readonly diagnostics = new Map<string, unknown[]>();
  private readonly progressDone = new Set<string>();
  private closed = false;
  private waiters: Array<() => void> = [];

  constructor(root: string, spawnServer: SpawnLean = spawnLean) {
    this.proc = spawnServer(root);
    this.startReader();
  }

  private wake(): void {
    const waiters = this.waiters;
    this.waiters = [];
    for (const w of waiters) w();
  }

  private waitChange(ms: number): Promise<void> {
    return new Promise((resolve) => {
      let done = false;
      const finish = (): void => {
        if (done) return;
        done = true;
        clearTimeout(timer);
        resolve();
      };
      const timer = setTimeout(finish, ms);
      this.waiters.push(finish);
    });
  }

  private startReader(): void {
    const frames = new LspFrames();
    const onEnd = (): void => {
      this.closed = true;
      this.wake();
    };
    this.proc.stdout.on("data", (chunk: Buffer) => {
      if (this.closed) return;
      let messages: string[];
      try {
        messages = frames.push(chunk);
      } catch {
        onEnd();
        killGroup(this.proc, "SIGTERM");
        return;
      }
      for (const body of messages) {
        let message: JsonRpcMessage;
        try {
          message = JSON.parse(body);
        } catch {
          continue;
        }
        this.dispatch(message);
      }
    });
    this.proc.stdout.on("end", onEnd);
    this.proc.on("exit", onEnd);
    this.proc.on("error", onEnd);
    this.proc.stdin.on("error", onEnd);
  }

  private dispatch(message: JsonRpcMessage): void {
    if (message.id !== undefined && (message.result !== undefined || message.error !== undefined)) {
      this.responses.set(message.id as number, message);
    } else if (message.method === "textDocument/publishDiagnostics") {
      const params = (message.params ?? {}) as { uri?: string; diagnostics?: unknown[] };
      if (params.uri !== undefined) this.diagnostics.set(params.uri, params.diagnostics ?? []);
    } else if (message.method === "$/lean/fileProgress") {
      const params = (message.params ?? {}) as { textDocument?: { uri?: string }; processing?: unknown[] };
      const uri = params.textDocument?.uri;
      if (uri !== undefined) {
        if (params.processing && params.processing.length) this.progressDone.delete(uri);
        else this.progressDone.add(uri);
      }
    }
    this.wake();
  }

  private send(message: JsonRpcMessage): void {
    const data = Buffer.from(JSON.stringify(message), "utf-8");
    this.proc.stdin.write(Buffer.concat([Buffer.from(`Content-Length: ${data.length}\r\n\r\n`, "latin1"), data]));
  }

  notify(method: string, params: Record<string, unknown>): void {
    this.send({ jsonrpc: "2.0", method, params } as JsonRpcMessage);
  }

  request(method: string, params: Record<string, unknown>): number {
    const id = this.nextId++;
    this.send({ jsonrpc: "2.0", id, method, params } as JsonRpcMessage);
    return id;
  }

  // Pop and return {id: message} for whichever of `ids` have answered, waiting
  // until at least one has.
  async takeResponses(ids: Iterable<number>, timeoutS: number): Promise<Map<number, JsonRpcMessage>> {
    const deadline = Date.now() + timeoutS * 1000;
    for (;;) {
      const ready = new Map<number, JsonRpcMessage>();
      for (const id of ids) {
        const message = this.responses.get(id);
        if (message !== undefined) {
          ready.set(id, message);
          this.responses.delete(id);
        }
      }
      if (ready.size) return ready;
      if (this.closed) throw new Error("lean server closed unexpectedly");
      const remaining = deadline - Date.now();
      if (remaining <= 0) throw new Error(`no response from lean server within ${timeoutS}s`);
      await this.waitChange(Math.min(remaining, 1000));
    }
  }

  async waitResponse(id: number, timeoutS: number): Promise<JsonRpcMessage> {
    return (await this.takeResponses([id], timeoutS)).get(id)!;
  }

  async initialize(rootUri: string): Promise<void> {
    const id = this.request("initialize", {
      processId: null,
      rootUri,
      capabilities: {
        textDocument: {
          publishDiagnostics: {},
          hover: { contentFormat: ["markdown", "plaintext"] },
        },
      },
    });
    await this.waitResponse(id, 120);
    this.notify("initialized", {});
  }

  async openAndElaborate(uri: string, text: string, timeoutS: number): Promise<void> {
    this.notify("textDocument/didOpen", {
      textDocument: { uri, languageId: "lean", version: 1, text },
    });
    const deadline = Date.now() + timeoutS * 1000;
    while (!this.progressDone.has(uri)) {
      if (this.closed) throw new Error("lean server closed during elaboration");
      const remaining = deadline - Date.now();
      if (remaining <= 0) throw new Error(`${uri}: elaboration did not finish within ${timeoutS}s`);
      await this.waitChange(Math.min(remaining, 1000));
    }
    // Trailing diagnostics can arrive just after the final progress event.
    await new Promise((resolve) => setTimeout(resolve, 500));
  }

  diagnosticsFor(uri: string): unknown[] {
    return this.diagnostics.get(uri) ?? [];
  }

  async shutdown(): Promise<void> {
    await terminate(this.proc);
  }
}
