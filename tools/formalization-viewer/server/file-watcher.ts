// File-watch fan-out for the formalization viewer.
//
// Watches the source/build trees with watchexec (native inotify on Linux,
// FSEvents on macOS) and relays repo-relative changed paths to SSE clients. The
// viewer uses these to live-reload the Markdown/Lean/TeX panes and the PDF.
// Degrades to a no-op stream if watchexec is not on PATH.
//
// A changed file may be known under several repo-relative names when projects
// share trees via symlinks, and watchexec reports whichever side of a symlink
// its watch root happened to resolve to. Every event is therefore expanded to
// its full equivalence class over the alias map (both directions, to a fixed
// point) before use.
//
// An optional `onChange` tap is invoked with each path in that class. The
// server uses it to auto-rebuild a book's viewer artifacts when its Markdown
// or Lean source changes; the regenerated build/ files then flow back as
// ordinary watch events that reload the panes.

import { spawn } from "node:child_process";
import type { ChildProcessByStdio } from "node:child_process";
import type { Readable } from "node:stream";
import fs from "node:fs";
import path from "node:path";
import type { Sink } from "./lean-bridge.ts";
import { terminate } from "./process-group.ts";

// md/lean/tex/pdf are the rendered panes; json covers the booklink source map
// and the chapter manifest; js/css/html are the viewer's own assets, whose
// change triggers a full page reload.
const EXTENSIONS = "md,lean,pdf,tex,json,js,css,html";

interface WatchTag {
  kind?: string;
  filetype?: string;
  absolute?: string;
}

type WatchProc = ChildProcessByStdio<null, Readable, null>;
interface WatchOptions {
  spawn?: (root: string, args: string[]) => WatchProc;
  retryMs?: number;
}

export class FileWatcher {
  private readonly root: string;
  private readonly watchDirs: string[];
  private readonly aliases: Map<string, string>;
  private readonly onChange?: (rel: string) => void;
  private proc: WatchProc | null = null;
  private stopped = false;
  private retry: NodeJS.Timeout | null = null;
  private retryMs: number;
  private readonly initialRetryMs: number;
  private readonly spawnWatch: (root: string, args: string[]) => WatchProc;
  private clients = new Set<Sink>();

  constructor(
    root: string,
    watchDirs: string[],
    aliases: Map<string, string>,
    onChange?: (rel: string) => void,
    options: WatchOptions = {},
  ) {
    this.root = root;
    this.watchDirs = watchDirs;
    this.aliases = aliases;
    this.onChange = onChange;
    this.initialRetryMs = options.retryMs ?? 500;
    this.retryMs = this.initialRetryMs;
    this.spawnWatch =
      options.spawn ??
      ((cwd, args) =>
        spawn("watchexec", args, {
          cwd,
          stdio: ["ignore", "pipe", "ignore"],
          detached: true,
        }));
  }

  ensure(): void {
    if (this.stopped) return;
    if (this.proc !== null && this.proc.exitCode === null && this.proc.signalCode === null) return;
    const resolved: Array<{ dir: string; real: string }> = [];
    for (const name of this.watchDirs) {
      let dir = path.join(this.root, name);
      // Lazy builds may not have created build/ yet. Watch its nearest existing
      // ancestor so the first artifacts and subsequent updates are still seen.
      while (!fs.existsSync(dir) && dir !== this.root && dir.startsWith(this.root + path.sep)) {
        dir = path.dirname(dir);
      }
      let real: string;
      try {
        real = fs.realpathSync(dir);
        if (!fs.statSync(dir).isDirectory()) continue;
      } catch {
        continue;
      }
      resolved.push({ dir, real });
    }
    // Keep a minimal cover of the realpaths: drop a dir whose realpath equals
    // or lies under another watched dir's (symlinked shared trees, and the
    // real parents of per-file symlink targets), so no events arrive twice.
    resolved.sort((a, b) => a.real.length - b.real.length);
    const watched: string[] = [];
    const kept: string[] = [];
    for (const { dir, real } of resolved) {
      if (kept.some((k) => real === k || real.startsWith(k + path.sep))) continue;
      kept.push(real);
      watched.push("--watch", dir);
    }
    if (watched.length === 0) return;

    let proc: ChildProcessByStdio<null, Readable, null>;
    try {
      // --no-vcs-ignore so the gitignored build/ PDFs are still watched.
      proc = this.spawnWatch(this.root, [
        "--only-emit-events",
        "--emit-events-to=json-stdio",
        "--no-vcs-ignore",
        "--exts",
        EXTENSIONS,
        ...watched,
      ]);
    } catch {
      this.proc = null; // watchexec unavailable; live reload is disabled.
      return;
    }
    // ENOENT (watchexec not on PATH) surfaces asynchronously as an 'error'.
    proc.on("error", () => {
      if (this.proc === proc) this.proc = null;
    });
    proc.on("exit", () => {
      if (this.proc !== proc) return;
      this.proc = null;
      if (this.stopped || !this.clients.size || this.retry !== null) return;
      this.retry = setTimeout(() => {
        this.retry = null;
        if (this.clients.size) this.ensure();
      }, this.retryMs);
      this.retry.unref();
      this.retryMs = Math.min(this.retryMs * 2, 30000);
    });
    this.proc = proc;

    let buffer = "";
    proc.stdout.on("data", (chunk: Buffer) => {
      if (this.stopped || this.proc !== proc) return;
      this.retryMs = this.initialRetryMs;
      buffer += chunk.toString("utf-8");
      let newline: number;
      while ((newline = buffer.indexOf("\n")) >= 0) {
        const raw = buffer.slice(0, newline);
        buffer = buffer.slice(newline + 1);
        this.handleEvent(raw);
      }
    });
  }

  private handleEvent(raw: string): void {
    if (!raw.trim()) return;
    let event: { tags?: WatchTag[] };
    try {
      event = JSON.parse(raw);
    } catch {
      return;
    }
    for (const tag of event.tags ?? []) {
      if (tag.kind === "path" && tag.filetype === "file") {
        const rel = this.relpath(tag.absolute ?? "");
        if (rel) {
          const paths = this.equivalents(rel);
          for (const p of paths) this.onChange?.(p);
          this.broadcast(paths);
        }
      }
    }
  }

  // All repo-relative names of the changed file: the reported path closed over
  // the alias map in both directions (an event may arrive under the symlinked
  // or the real name, and a real name may have several aliases).
  private equivalents(rel: string): string[] {
    const paths = new Set<string>([rel]);
    let grew = true;
    while (grew) {
      grew = false;
      for (const [real, alias] of this.aliases) {
        // Iterate a snapshot: the loop body grows `paths`.
        // oxlint-disable-next-line unicorn/no-useless-spread
        for (const p of [...paths]) {
          for (const [from, to] of [
            [real, alias],
            [alias, real],
          ]) {
            if (p.startsWith(from) && !paths.has(to + p.slice(from.length))) {
              paths.add(to + p.slice(from.length));
              grew = true;
            }
          }
        }
      }
    }
    return [...paths].sort();
  }

  private relpath(absolute: string): string | null {
    const prefix = this.root + path.sep;
    return absolute.startsWith(prefix) ? absolute.slice(prefix.length) : null;
  }

  private broadcast(paths: string[]): void {
    const targets = [...this.clients];
    for (const p of paths) {
      const payload = JSON.stringify({ path: p });
      for (const sink of targets) sink.put(payload);
    }
  }

  async shutdown(): Promise<void> {
    this.stopped = true;
    if (this.retry !== null) clearTimeout(this.retry);
    this.retry = null;
    const proc = this.proc;
    this.proc = null;
    await terminate(proc);
  }

  subscribe(sink: Sink): void {
    this.clients.add(sink);
  }

  unsubscribe(sink: Sink): void {
    this.clients.delete(sink);
  }
}
