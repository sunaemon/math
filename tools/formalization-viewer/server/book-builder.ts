// Auto-rebuild a book's viewer artifacts when its Markdown or Lean source
// changes.
//
// The file watcher reports every changed repo-relative path; this consumer
// notices changes under a project's served Markdown/Lean source trees
// (`src/**.md`, `lean/**.lean` — Lean files carry the booklink markers the
// source map is derived from) and runs that project's `make` build so the
// rendered panes refresh. The regenerated build/ files then flow back through
// the same watcher as ordinary change events. Only Markdown and Lean source
// changes trigger a build, so the build's own TeX/PDF/JSON output never
// re-triggers it.
//
// Watch events report real paths, while a project may share another book's
// source tree through symlinks (a whole dir, or per-file links to individual
// chapters/Lean files). Each job's trigger prefixes therefore include the
// realpath-resolved targets of any symlinks in its served trees, so an edit to
// the canonical file also rebuilds every project that links to it.
//
// The target is resolved from the PDF the viewer currently shows (clients report
// their selection via setSelection): the debug PDF and its source map, or a
// per-chapter preview PDF — whichever is selected. The release PDF is never
// auto-built. The source map is always rebuilt so the marker overlays on the
// Markdown/Lean/TeX panes track the edit even when no PDF is. With no reported
// selection the debug PDF is the default, matching the viewer's default view.
// A session viewing a project that displays another project's PDF as its peer
// pane (manifest "parallelPdf") also keeps that peer PDF fresh: without this,
// editing the canonical book while only the translated book is open leaves the
// peer pane's PDF stale, with band destinations that no longer match the map.
// The implied peer PDF mirrors the session's own selection kind — a chapter
// preview implies the peer book's preview of the same chapter, anything else
// the peer debug PDF — matching the client, whose peer pane follows the
// primary pane's document kind.
//
// Builds are debounced and coalesced: every project dirtied within the window
// is built by a single `make` invocation with the union of their targets,
// because separate concurrent makes can resolve overlapping targets (a book's
// debug PDF doubles as another book's peer-pane PDF) and would race on them.
// A save (or a selection change) during an in-flight build queues exactly one
// follow-up batch.
//
// Controlled by the environment:
//   BOOKLINK_AUTOBUILD=0              disable auto-building entirely
//   BOOKLINK_MAKE=<cmd>              build executable (default "make"); a single
//                                   program name, run without a shell, so it
//                                   cannot embed arguments (no "make -j4")
//   BOOKLINK_AUTOBUILD_DEBOUNCE_MS  shared batch debounce (default 400)
//   BOOKLINK_AUTOBUILD_MAX_WAIT_MS  maximum wait during continuous edits (default 3000)

import { spawn } from "node:child_process";
import type { ChildProcess } from "node:child_process";
import fs from "node:fs";
import { lightPdfPath, themedPdfPath } from "../src/pdf-theme.ts";
import { canonicalPdfPath, pdfLayout, layoutPdfPath } from "../src/pdf-layout.ts";
import path from "node:path";
import type { Manifest } from "./projects.ts";
import { terminate } from "./process-group.ts";

interface BuildJob {
  dir: string;
  // Repo-relative prefixes whose .md/.lean changes fire this job: the served
  // source trees plus the realpath-resolved targets of symlinks inside them
  // (dir prefixes end in "/"; a per-file symlink target is the file path).
  triggers: string[];
  // Repo-relative "<dir>/" prefix used to attribute a selected PDF to this job.
  buildPrefix: string;
  // make targets (repo-relative); null when the manifest omits the artifact.
  sourceMap: string | null;
  pdfTarget: string | null; // debug PDF (manifest "pdf")
  // Repo-relative "<dir>/build/<stem>-preview-" prefix of the per-chapter
  // preview PDFs; a selected path under it is built as-is (the chapter the tab
  // is viewing). Null when there is no debug PDF to derive the stem from.
  previewPrefix: string | null;
}

// Trigger prefixes for one served source tree: the project-local prefix plus
// the realpath-resolved prefixes of the tree itself and of any symlinked
// entries inside it. Missing dirs (e.g. in tests) keep just the local prefix;
// targets outside the repo root are ignored; symlinked dirs are not descended
// into (their own project's triggers cover them, and this avoids cycles).
function triggerPrefixes(root: string, dir: string, sub: string): string[] {
  const prefixes = new Set<string>([`${dir}/${sub}/`]);
  const top = path.join(root, dir, sub);
  const add = (absolute: string, isDir: boolean): void => {
    const rel = path.relative(root, absolute);
    if (rel === "" || rel.startsWith("..") || path.isAbsolute(rel)) return;
    prefixes.add(isDir ? `${rel}/` : rel);
  };
  try {
    add(fs.realpathSync(top), true);
  } catch {
    return [...prefixes];
  }
  const stack = [top];
  while (stack.length) {
    const current = stack.pop()!;
    let entries: fs.Dirent[];
    try {
      entries = fs.readdirSync(current, { withFileTypes: true });
    } catch {
      continue;
    }
    for (const entry of entries) {
      const full = path.join(current, entry.name);
      if (entry.isSymbolicLink()) {
        try {
          const real = fs.realpathSync(full);
          add(real, fs.statSync(real).isDirectory());
        } catch {
          continue;
        }
      } else if (entry.isDirectory()) {
        stack.push(full);
      }
    }
  }
  return [...prefixes];
}

function jobFor(root: string, meta: Manifest): BuildJob | null {
  const triggers: string[] = [];
  for (const [sub, exts] of Object.entries(meta.served ?? {})) {
    // Excerpts can serve generated Markdown. Their outputs must not trigger
    // another build; symlinked original sources under src/ supply the triggers.
    if (sub === "build" || sub.startsWith("build/")) continue;
    if (Array.isArray(exts) && (exts.includes("md") || exts.includes("lean")))
      triggers.push(...triggerPrefixes(root, meta.dir, sub));
  }
  const target = (key: string): string | null => {
    const value = meta[key];
    return typeof value === "string" && value ? `${meta.dir}/${value}` : null;
  };
  const sourceMap = target("sourceMap");
  const pdfTarget = target("pdf");
  if (triggers.length === 0 || (!sourceMap && !pdfTarget)) return null;
  // "<dir>/build/<stem>-debug.pdf" -> "<dir>/build/<stem>-preview-".
  const previewPrefix = pdfTarget?.endsWith("-debug.pdf")
    ? `${pdfTarget.slice(0, -"-debug.pdf".length)}-preview-`
    : null;
  return { dir: meta.dir, triggers, buildPrefix: `${meta.dir}/`, sourceMap, pdfTarget, previewPrefix };
}

export type BuildState = "building" | "done" | "failed";

// Reported when a project's auto-build starts and finishes; the server relays it
// to clients so the viewer can show a "Building…" indicator.
export interface BuildStatus {
  dir: string;
  state: BuildState;
}

export class BookBuilder {
  private readonly root: string;
  private readonly make: string;
  private readonly debounceMs: number;
  private readonly maxWaitMs: number;
  private readonly enabled: boolean;
  private readonly jobs: BuildJob[];
  // Peer-pane links: a selection under ownerPrefix implies a peer-project PDF
  // (named by the owner's manifest "parallelPdf"). The peer pane mirrors the
  // owner selection's document kind — an owner chapter-preview selection
  // implies the peer book's preview of the same chapter, anything else the
  // peer debug PDF — so both preview prefixes ride along (null when either
  // book has no debug PDF to derive a stem from).
  private readonly peerLinks: Array<{
    ownerPrefix: string;
    target: string;
    ownerPreviewPrefix: string | null;
    targetPreviewPrefix: string | null;
  }>;
  private readonly log: (msg: string) => void;
  private readonly onStatus: (status: BuildStatus) => void;
  private readonly onLog: (dir: string, text: string, reset: boolean) => void;
  // Dirty projects awaiting the debounced batch build. A change to a shared
  // source tree marks several projects dirty at once; they are built by ONE
  // `make` invocation with the union of their targets, because separate
  // concurrent makes can resolve overlapping targets (a project's own debug
  // PDF is another project's peer-pane PDF) and would race on them.
  private readonly dirty = new Set<BuildJob>();
  private timer: ReturnType<typeof setTimeout> | null = null;
  private dirtySince: number | null = null;
  private running: ChildProcess | null = null;
  private pending = false;
  // sessionId -> repo-relative path of the PDF that session is viewing.
  private readonly selections = new Map<string, string>();
  private shuttingDown = false;

  constructor(
    root: string,
    manifests: Manifest[],
    log: (msg: string) => void = (m) => process.stderr.write(`${m}\n`),
    onStatus: (status: BuildStatus) => void = () => {},
    onLog: (dir: string, text: string, reset: boolean) => void = () => {},
  ) {
    this.root = fs.realpathSync(root);
    this.log = log;
    this.onStatus = onStatus;
    this.onLog = onLog;
    this.enabled = (process.env.BOOKLINK_AUTOBUILD ?? "1") !== "0";
    this.make = process.env.BOOKLINK_MAKE || "make";
    const ms = Number.parseInt(process.env.BOOKLINK_AUTOBUILD_DEBOUNCE_MS ?? "", 10);
    this.debounceMs = Number.isFinite(ms) && ms >= 0 ? ms : 400;
    const max = Number.parseInt(process.env.BOOKLINK_AUTOBUILD_MAX_WAIT_MS ?? "", 10);
    this.maxWaitMs = Number.isFinite(max) && max >= 0 ? max : 3000;
    this.jobs = manifests.map((meta) => jobFor(this.root, meta)).filter((j): j is BuildJob => j !== null);
    this.peerLinks = manifests.flatMap((meta) => {
      const peer = meta.parallelPdf as { dir?: unknown; path?: unknown } | undefined;
      if (!peer || typeof peer.dir !== "string" || typeof peer.path !== "string" || !peer.path) return [];
      const target = `${peer.dir}/${peer.path.replace(/^\/+/, "")}`;
      const ownerPdf = typeof meta.pdf === "string" && meta.pdf ? `${meta.dir}/${meta.pdf}` : null;
      const previewPrefix = (pdf: string | null): string | null =>
        pdf?.endsWith("-debug.pdf") ? `${pdf.slice(0, -"-debug.pdf".length)}-preview-` : null;
      return [
        {
          ownerPrefix: `${meta.dir}/`,
          target,
          ownerPreviewPrefix: previewPrefix(ownerPdf),
          targetPreviewPrefix: previewPrefix(target),
        },
      ];
    });
  }

  // Called for each real repo-relative changed path. Schedules a debounced
  // rebuild of every project whose Markdown or Lean source tree contains the
  // file, directly or through a symlink.
  notify(rel: string): void {
    if (!this.enabled || !(rel.endsWith(".md") || rel.endsWith(".lean"))) return;
    for (const job of this.jobs) {
      if (job.triggers.some((t) => rel.startsWith(t))) this.schedule(job);
    }
  }

  // Record which PDF a session is viewing (repo-relative path). A change to a
  // different PDF, including the initial report, schedules its artifacts after
  // the server is already serving the UI. make checks freshness of cached files.
  setSelection(session: string, pdf: string): void {
    if (!this.enabled || !pdf) return;
    const prev = this.selections.get(session);
    this.selections.set(session, pdf);
    if (prev !== pdf) {
      const job = this.jobs.find((j) => pdf.startsWith(j.buildPrefix));
      if (job) this.schedule(job);
      // A selection change can also change the peer-implied target (debug vs
      // same-chapter preview); rebuild the peer project too, so the mirrored
      // document exists by the time the peer pane loads it.
      for (const link of this.peerLinks) {
        if (!pdf.startsWith(link.ownerPrefix)) continue;
        const peerJob = this.jobs.find((j) => link.target.startsWith(j.buildPrefix));
        if (peerJob) this.schedule(peerJob);
      }
    }
  }

  clearSelection(session: string): void {
    this.selections.delete(session);
  }

  // The make targets to build for a project, resolved from the PDFs its viewers
  // currently show. The source map is always included; the debug or diff PDF is
  // added per selection; the release PDF (or any other) is never auto-built.
  private resolveTargets(job: BuildJob): string[] {
    const out = new Set<string>();
    // Selections in a project whose peer pane shows this project's PDF imply a
    // PDF here, mirroring the owner selection's document kind: an owner
    // chapter-preview selection implies this book's preview of the same
    // chapter, anything else the debug PDF. Computed first so implied targets
    // stand in for the no-selection debug default — the peer pane tracks
    // canonical-source edits even when no session views this project directly,
    // without dragging in a debug build nobody is looking at.
    const implied = new Set<string>();
    for (const link of this.peerLinks) {
      if (!link.target.startsWith(job.buildPrefix)) continue;
      for (const sel of this.selections.values()) {
        if (!sel.startsWith(link.ownerPrefix)) continue;
        const light = canonicalPdfPath(lightPdfPath(sel));
        const layout = pdfLayout(sel);
        const chapter =
          link.ownerPreviewPrefix &&
          link.targetPreviewPrefix &&
          light.startsWith(link.ownerPreviewPrefix) &&
          light.endsWith(".pdf")
            ? light.slice(link.ownerPreviewPrefix.length, -".pdf".length)
            : null;
        // The chapter component becomes part of a make target, so it passes the
        // same plain-identifier guard as the selection handling below.
        const target =
          chapter && /^[A-Za-z0-9_-]+$/.test(chapter) ? `${link.targetPreviewPrefix}${chapter}.pdf` : link.target;
        implied.add(layoutPdfPath(themedPdfPath(target, lightPdfPath(sel) !== sel), layout.paper, layout.font));
      }
    }
    const sels = [...this.selections.values()].filter((p) => p.startsWith(job.buildPrefix));
    if (sels.length === 0) {
      if (job.pdfTarget && implied.size === 0) out.add(job.pdfTarget);
    } else {
      for (const sel of sels) {
        const light = canonicalPdfPath(lightPdfPath(sel));
        if (job.pdfTarget && light === job.pdfTarget) out.add(sel);
        // A per-chapter preview PDF is built as-is: the make rule renders that one
        // chapter via \includeonly. The chapter component becomes the make target
        // stem ($*), which the Makefile preview recipe interpolates into a
        // shell-evaluated LuaLaTeX command, so a selection like
        // "...-preview-$(cmd).pdf" would be a command-injection vector. Admit the
        // selection only when the chapter is a plain identifier — anything else
        // (the value comes from a client-reported POST /build/select) is dropped.
        else if (job.previewPrefix && light.startsWith(job.previewPrefix) && light.endsWith(".pdf")) {
          const chapter = light.slice(job.previewPrefix.length, -".pdf".length);
          if (/^[A-Za-z0-9_-]+$/.test(chapter)) out.add(sel);
        }
      }
    }
    for (const target of implied) out.add(target);
    if (job.sourceMap) out.add(job.sourceMap);
    return [...out];
  }

  private schedule(job: BuildJob): void {
    this.dirty.add(job);
    this.dirtySince ??= Date.now();
    const wait = Math.min(this.debounceMs, Math.max(0, this.maxWaitMs - (Date.now() - this.dirtySince)));
    if (this.timer) clearTimeout(this.timer);
    this.timer = setTimeout(() => {
      this.timer = null;
      this.dirtySince = null;
      this.run();
    }, wait);
  }

  private run(): void {
    // One build at a time; a change mid-build queues a single follow-up batch.
    if (this.running) {
      this.pending = true;
      return;
    }
    if (this.timer) clearTimeout(this.timer);
    this.timer = null;
    this.dirtySince = null;
    const dirs: string[] = [];
    const targets = new Set<string>();
    for (const job of this.dirty) {
      const resolved = this.resolveTargets(job);
      if (resolved.length === 0) continue;
      dirs.push(job.dir);
      for (const target of resolved) targets.add(target);
    }
    this.dirty.clear();
    if (targets.size === 0) return;
    let proc: ChildProcess;
    const logFiles: number[] = [];
    const writeBuildLog = (chunk: Buffer | string): void => {
      const data = typeof chunk === "string" ? Buffer.from(chunk) : chunk;
      for (const fd of logFiles) fs.writeSync(fd, data);
      for (const dir of dirs) this.onLog(dir, data.toString("utf8"), false);
    };
    const closeBuildLogs = (): void => {
      for (const fd of logFiles.splice(0)) fs.closeSync(fd);
    };
    try {
      // Keep diagnostics even when the viewer was started in a detached terminal.
      // Each affected project gets the complete coalesced build's output, since
      // a failure in a shared prerequisite can break more than one pane.
      for (const dir of dirs) {
        const buildDir = path.join(this.root, dir, "build");
        fs.mkdirSync(buildDir, { recursive: true });
        logFiles.push(fs.openSync(path.join(buildDir, "viewer-build.log"), "w"));
      }
      for (const dir of dirs) this.onLog(dir, "", true);
      writeBuildLog(`${this.make} ${[...targets].join(" ")}\n`);
      // detached so terminate() can reap the whole make subtree (pandoc, lualatex)
      // on shutdown; tee output to the server terminal and persistent build logs.
      proc = spawn(this.make, [...targets], {
        cwd: this.root,
        stdio: ["ignore", "pipe", "pipe"],
        detached: true,
      });
    } catch (error) {
      closeBuildLogs();
      this.log(`book-builder: failed to spawn '${this.make}': ${(error as Error).message}`);
      for (const dir of dirs) this.onStatus({ dir, state: "failed" });
      return;
    }
    proc.stdout!.setEncoding("utf8");
    proc.stderr!.setEncoding("utf8");
    proc.stdout!.on("data", (chunk: string) => {
      writeBuildLog(chunk);
      process.stdout.write(chunk);
    });
    proc.stderr!.on("data", (chunk: string) => {
      writeBuildLog(chunk);
      process.stderr.write(chunk);
    });
    this.running = proc;
    this.log(`book-builder: ${this.make} ${[...targets].join(" ")}`);
    for (const dir of dirs) this.onStatus({ dir, state: "building" });
    let settled = false;
    const finish = (message: string, ok: boolean): void => {
      if (settled) return;
      settled = true;
      writeBuildLog(`\nbuild ${message}\n`);
      closeBuildLogs();
      if (this.running !== proc) return;
      this.running = null;
      this.log(`book-builder: ${dirs.join(" ")} build ${message}`);
      // shutdown() terminates in-flight builds with SIGTERM; that exit is a
      // cancellation, not a failure, so do not flash "failed" at clients on the
      // way out (and do not requeue a pending build that will never run).
      if (this.shuttingDown) return;
      // A queued rebuild keeps the indicator on: report "done"/"failed" only
      // for projects with nothing further pending.
      const requeue = this.pending || this.dirty.size > 0;
      this.pending = false;
      for (const dir of dirs) {
        if (!(requeue && [...this.dirty].some((j) => j.dir === dir))) {
          this.onStatus({ dir, state: ok ? "done" : "failed" });
        }
      }
      if (requeue) this.run();
    };
    // close follows exit and the final stdout/stderr data, so the saved log is
    // complete before reporting success/failure or starting the queued build.
    proc.on("close", (code, signal) =>
      finish(signal ? `killed (${signal})` : `finished (exit ${code})`, !signal && code === 0),
    );
    proc.on("error", (error) => finish(`error: ${error.message}`, false));
  }

  async shutdown(): Promise<void> {
    this.shuttingDown = true;
    if (this.timer) clearTimeout(this.timer);
    this.timer = null;
    this.dirtySince = null;
    this.dirty.clear();
    this.pending = false;
    this.selections.clear();
    if (this.running) await terminate(this.running);
    this.running = null;
  }
}
