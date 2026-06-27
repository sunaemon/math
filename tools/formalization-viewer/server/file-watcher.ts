// File-watch fan-out for the formalization viewer.
//
// Watches the source/build trees with watchexec (native inotify on Linux,
// FSEvents on macOS) and relays repo-relative changed paths to SSE clients. The
// viewer uses these to live-reload the Markdown/Lean/TeX panes and the PDF.
// Degrades to a no-op stream if watchexec is not on PATH.
//
// An optional `onChange` tap is invoked with each real repo-relative changed
// path (before alias fan-out). The server uses it to auto-rebuild a book's
// viewer artifacts when its Markdown source changes; the regenerated build/
// files then flow back as ordinary watch events that reload the panes.

import { spawn } from "node:child_process";
import type { ChildProcessByStdio } from "node:child_process";
import type { Readable } from "node:stream";
import fs from "node:fs";
import path from "node:path";
import type { Sink } from "./lean-bridge.ts";
import { killGroup } from "./process-group.ts";

// md/lean/tex/pdf are the rendered panes; json covers the booklink source map
// and the chapter manifest; js/css/html are the viewer's own assets, whose
// change triggers a full page reload.
const EXTENSIONS = "md,lean,pdf,tex,json,js,css,html";

interface WatchTag {
  kind?: string;
  filetype?: string;
  absolute?: string;
}

export class FileWatcher {
  private readonly root: string;
  private readonly watchDirs: string[];
  private readonly aliases: Map<string, string>;
  private readonly onChange?: (rel: string) => void;
  private proc: ChildProcessByStdio<null, Readable, null> | null = null;
  private clients = new Set<Sink>();

  constructor(root: string, watchDirs: string[], aliases: Map<string, string>, onChange?: (rel: string) => void) {
    this.root = root;
    this.watchDirs = watchDirs;
    this.aliases = aliases;
    this.onChange = onChange;
  }

  ensure(): void {
    if (this.proc !== null && this.proc.exitCode === null && this.proc.signalCode === null) return;
    const watched: string[] = [];
    const seen = new Set<string>();
    for (const name of this.watchDirs) {
      const dir = path.join(this.root, name);
      let real: string;
      try {
        real = fs.realpathSync(dir);
      } catch {
        continue;
      }
      // Symlinked shared trees resolve to an already-watched dir.
      if (!fs.statSync(dir).isDirectory() || seen.has(real)) continue;
      seen.add(real);
      watched.push("--watch", dir);
    }
    if (watched.length === 0) return;

    let proc: ChildProcessByStdio<null, Readable, null>;
    try {
      // --no-vcs-ignore so the gitignored build/ PDFs are still watched.
      proc = spawn(
        "watchexec",
        ["--only-emit-events", "--emit-events-to=json-stdio", "--no-vcs-ignore", "--exts", EXTENSIONS, ...watched],
        { cwd: this.root, stdio: ["ignore", "pipe", "ignore"], detached: true },
      );
    } catch {
      this.proc = null; // watchexec unavailable; live reload is disabled.
      return;
    }
    // ENOENT (watchexec not on PATH) surfaces asynchronously as an 'error'.
    proc.on("error", () => {
      if (this.proc === proc) this.proc = null;
    });
    this.proc = proc;

    let buffer = "";
    proc.stdout.on("data", (chunk: Buffer) => {
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
          this.onChange?.(rel);
          this.broadcast(rel);
        }
      }
    }
  }

  private relpath(absolute: string): string | null {
    const prefix = this.root + path.sep;
    return absolute.startsWith(prefix) ? absolute.slice(prefix.length) : null;
  }

  private broadcast(rel: string): void {
    const paths = new Set<string>([rel]);
    for (const [realPrefix, aliasPrefix] of this.aliases) {
      if (rel.startsWith(realPrefix)) paths.add(aliasPrefix + rel.slice(realPrefix.length));
    }
    const targets = [...this.clients];
    for (const p of [...paths].sort()) {
      const payload = JSON.stringify({ path: p });
      for (const sink of targets) sink.put(payload);
    }
  }

  shutdown(): void {
    const proc = this.proc;
    this.proc = null;
    if (proc === null || proc.exitCode !== null || proc.signalCode !== null) return;
    killGroup(proc, "SIGTERM");
  }

  subscribe(sink: Sink): void {
    this.clients.add(sink);
  }

  unsubscribe(sink: Sink): void {
    this.clients.delete(sink);
  }
}
