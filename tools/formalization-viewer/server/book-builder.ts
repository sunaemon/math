// Auto-rebuild a book's viewer artifacts when its Markdown source changes.
//
// The file watcher reports every changed repo-relative path; this consumer
// notices changes under a project's served Markdown source tree (`src/**.md`)
// and runs that project's `make` build so the rendered panes refresh. The
// regenerated build/ files then flow back through the same watcher as ordinary
// change events. Only Markdown changes trigger a build, so the build's own
// TeX/PDF/JSON output never re-triggers it.
//
// The target is resolved from the PDF the viewer currently shows (clients report
// their selection via setSelection): the debug PDF and its source map, or a
// per-chapter preview PDF — whichever is selected. The release PDF is never
// auto-built. The source map is always rebuilt so the marker overlays on the
// Markdown/Lean/TeX panes track the edit even when no PDF is. With no reported
// selection the debug PDF is the default, matching the viewer's default view.
//
// Builds are debounced per project and coalesced: a save (or a selection change)
// during an in-flight build queues exactly one rebuild afterwards.
//
// Controlled by the environment:
//   BOOKLINK_AUTOBUILD=0              disable auto-building entirely
//   BOOKLINK_MAKE=<cmd>              build executable (default "make"); a single
//                                   program name, run without a shell, so it
//                                   cannot embed arguments (no "make -j4")
//   BOOKLINK_AUTOBUILD_DEBOUNCE_MS  per-project debounce (default 400)

import { spawn } from "node:child_process";
import type { ChildProcess } from "node:child_process";
import type { Manifest } from "./projects.ts";
import { terminate } from "./process-group.ts";

interface BuildJob {
  dir: string;
  // Repo-relative "<dir>/<sub>/" prefixes whose .md changes fire this job.
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

function jobFor(meta: Manifest): BuildJob | null {
  const triggers: string[] = [];
  for (const [sub, exts] of Object.entries(meta.served ?? {})) {
    if (Array.isArray(exts) && exts.includes("md")) triggers.push(`${meta.dir}/${sub}/`);
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
  private readonly enabled: boolean;
  private readonly jobs: BuildJob[];
  private readonly log: (msg: string) => void;
  private readonly onStatus: (status: BuildStatus) => void;
  private readonly timers = new Map<string, ReturnType<typeof setTimeout>>();
  private readonly running = new Map<string, ChildProcess>();
  private readonly pending = new Set<string>();
  // sessionId -> repo-relative path of the PDF that session is viewing.
  private readonly selections = new Map<string, string>();
  private shuttingDown = false;

  constructor(
    root: string,
    manifests: Manifest[],
    log: (msg: string) => void = (m) => process.stderr.write(`${m}\n`),
    onStatus: (status: BuildStatus) => void = () => {},
  ) {
    this.root = root;
    this.log = log;
    this.onStatus = onStatus;
    this.enabled = (process.env.BOOKLINK_AUTOBUILD ?? "1") !== "0";
    this.make = process.env.BOOKLINK_MAKE || "make";
    const ms = Number.parseInt(process.env.BOOKLINK_AUTOBUILD_DEBOUNCE_MS ?? "", 10);
    this.debounceMs = Number.isFinite(ms) && ms >= 0 ? ms : 400;
    this.jobs = manifests.map(jobFor).filter((j): j is BuildJob => j !== null);
  }

  // Called for each real repo-relative changed path. Schedules a debounced
  // rebuild of every project whose Markdown source tree contains the file.
  notify(rel: string): void {
    if (!this.enabled || !rel.endsWith(".md")) return;
    for (const job of this.jobs) {
      if (job.triggers.some((t) => rel.startsWith(t))) this.schedule(job);
    }
  }

  // Record which PDF a session is viewing (repo-relative path). A change to a
  // different PDF rebuilds the newly selected target so the user sees it fresh;
  // the initial report only records the preference (no build on page load).
  setSelection(session: string, pdf: string): void {
    if (!this.enabled || !pdf) return;
    const prev = this.selections.get(session);
    this.selections.set(session, pdf);
    if (prev !== undefined && prev !== pdf) {
      const job = this.jobs.find((j) => pdf.startsWith(j.buildPrefix));
      if (job) this.schedule(job);
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
    const sels = [...this.selections.values()].filter((p) => p.startsWith(job.buildPrefix));
    if (sels.length === 0) {
      if (job.pdfTarget) out.add(job.pdfTarget);
    } else {
      for (const sel of sels) {
        if (job.pdfTarget && sel === job.pdfTarget) out.add(job.pdfTarget);
        // A per-chapter preview PDF is built as-is: the make rule renders that one
        // chapter via \includeonly. The chapter component becomes the make target
        // stem ($*), which the Makefile preview recipe interpolates into a
        // shell-evaluated LuaLaTeX command, so a selection like
        // "...-preview-$(cmd).pdf" would be a command-injection vector. Admit the
        // selection only when the chapter is a plain identifier — anything else
        // (the value comes from a client-reported POST /build/select) is dropped.
        else if (job.previewPrefix && sel.startsWith(job.previewPrefix) && sel.endsWith(".pdf")) {
          const chapter = sel.slice(job.previewPrefix.length, -".pdf".length);
          if (/^[A-Za-z0-9_-]+$/.test(chapter)) out.add(sel);
        }
      }
    }
    if (job.sourceMap) out.add(job.sourceMap);
    return [...out];
  }

  private schedule(job: BuildJob): void {
    const prev = this.timers.get(job.dir);
    if (prev) clearTimeout(prev);
    this.timers.set(
      job.dir,
      setTimeout(() => {
        this.timers.delete(job.dir);
        this.run(job);
      }, this.debounceMs),
    );
  }

  private run(job: BuildJob): void {
    const targets = this.resolveTargets(job);
    if (targets.length === 0) return;
    // One build per project at a time; a change mid-build queues a single rebuild.
    if (this.running.has(job.dir)) {
      this.pending.add(job.dir);
      return;
    }
    let proc: ChildProcess;
    try {
      // detached so terminate() can reap the whole make subtree (pandoc, lualatex)
      // on shutdown; stdio inherited so build progress shows in the server log.
      proc = spawn(this.make, targets, { cwd: this.root, stdio: ["ignore", "inherit", "inherit"], detached: true });
    } catch (error) {
      this.log(`book-builder: failed to spawn '${this.make}' for ${job.dir}: ${(error as Error).message}`);
      return;
    }
    this.running.set(job.dir, proc);
    this.log(`book-builder: ${this.make} ${targets.join(" ")}`);
    this.onStatus({ dir: job.dir, state: "building" });
    const finish = (message: string, ok: boolean): void => {
      if (this.running.get(job.dir) !== proc) return;
      this.running.delete(job.dir);
      this.log(`book-builder: ${job.dir} build ${message}`);
      // shutdown() terminates in-flight builds with SIGTERM; that exit is a
      // cancellation, not a failure, so do not flash "failed" at clients on the
      // way out (and do not requeue a pending build that will never run).
      if (this.shuttingDown) return;
      // A queued rebuild keeps the indicator on: report "done"/"failed" only
      // when nothing further is pending for this project.
      if (this.pending.delete(job.dir)) this.run(job);
      else this.onStatus({ dir: job.dir, state: ok ? "done" : "failed" });
    };
    proc.on("exit", (code, signal) =>
      finish(signal ? `killed (${signal})` : `finished (exit ${code})`, !signal && code === 0),
    );
    proc.on("error", (error) => finish(`error: ${error.message}`, false));
  }

  async shutdown(): Promise<void> {
    this.shuttingDown = true;
    for (const timer of this.timers.values()) clearTimeout(timer);
    this.timers.clear();
    this.pending.clear();
    this.selections.clear();
    await Promise.all([...this.running.values()].map((proc) => terminate(proc)));
    this.running.clear();
  }
}
