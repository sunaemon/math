#!/usr/bin/env node
// Pregenerated syntax-highlight data for the formalization viewer.
//
// For every Markdown or Lean source file a project serves, this records the
// tree-sitter highlight spans and Lean fold ranges the browser used to compute
// itself (see highlight-core.ts), as one JSON file per source file:
//
//   { "version": 1, "sha256": <source hash>,
//     "spans": [[start, end, class], ...], "folds": [[start, end], ...] }
//
// Offsets are UTF-16 code units into the source text. A cache file is keyed by
// the hash of its source, so regeneration only recomputes files whose text
// changed. The live server answers the same `highlight-cache/<path>.json`
// URLs on demand through HighlightService (memoized by source hash), so both
// serving modes present one URL space, mirroring the LSP cache.

import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";
import { CliUsageError, optionValue } from "./cli-values.ts";
import { atomicWrite } from "./file-output.ts";
import { readProject, walkFiles, type Manifest } from "./projects.ts";
import { computeHighlightData, languageForPath, type HighlightData } from "./highlight-core.ts";

export const HIGHLIGHT_CACHE_VERSION = 1;

export interface HighlightFile {
  version: number;
  sha256: string;
  spans: [number, number, string][];
  folds: [number, number][];
}

export function encodeHighlightFile(data: HighlightData, sha256: string): HighlightFile {
  return {
    version: HIGHLIGHT_CACHE_VERSION,
    sha256,
    spans: data.spans.map((span) => [span.startOffset, span.endOffset, span.cls]),
    folds: data.folds.map((fold) => [fold.startOffset, fold.endOffset]),
  };
}

function sha256(bytes: Buffer): string {
  return createHash("sha256").update(bytes).digest("hex");
}

async function highlightFileFor(bytes: Buffer, lang: "lean" | "markdown"): Promise<HighlightFile> {
  return encodeHighlightFile(await computeHighlightData(bytes.toString("utf-8"), lang), sha256(bytes));
}

// Source files of the project that can carry highlights, as project-relative
// POSIX paths — the same enumeration the static distribution copies, narrowed
// to files whose extension the manifest serves and the highlighter knows.
function highlightableFiles(
  root: string,
  project: Manifest,
): { rel: string; full: string; lang: "lean" | "markdown" }[] {
  const projectRoot = path.join(root, project.dir);
  const flat = new Set(project.flat ?? []);
  const found: { rel: string; full: string; lang: "lean" | "markdown" }[] = [];
  for (const [sub, exts] of Object.entries(project.served ?? {})) {
    const allowed = new Set(exts.map((ext) => `.${ext}`));
    const srcDir = path.join(projectRoot, sub);
    try {
      if (!fs.statSync(srcDir).isDirectory()) continue;
    } catch {
      continue;
    }
    for (const full of walkFiles(srcDir)) {
      if (!allowed.has(path.extname(full))) continue;
      if (flat.has(sub) && path.dirname(full) !== srcDir) continue;
      const rel = path.relative(projectRoot, full).split(path.sep).join("/");
      const lang = languageForPath(rel);
      if (lang) found.push({ rel, full, lang });
    }
  }
  return found.sort((a, b) => a.rel.localeCompare(b.rel));
}

// Write highlight JSON for every served source file under outDir, skipping
// files whose recorded source hash is unchanged. Returns the number of files
// (re)generated. A parse failure aborts the build: shipping silently empty
// highlights would hide a broken grammar or query (check_highlights.mjs is
// the matching smoke check).
export async function generate(root: string, project: Manifest, outDir: string): Promise<number> {
  let written = 0;
  for (const { rel, full, lang } of highlightableFiles(root, project)) {
    const bytes = fs.readFileSync(full);
    const dest = path.join(outDir, `${rel}.json`);
    try {
      const existing = JSON.parse(fs.readFileSync(dest, "utf-8")) as HighlightFile;
      if (existing.version === HIGHLIGHT_CACHE_VERSION && existing.sha256 === sha256(bytes)) continue;
    } catch {
      /* no usable cache entry yet */
    }
    fs.mkdirSync(path.dirname(dest), { recursive: true });
    atomicWrite(dest, JSON.stringify(await highlightFileFor(bytes, lang)));
    written += 1;
  }
  return written;
}

// On-demand highlight data for the live server. Results are memoized by
// source hash, so an edit recomputes exactly the changed file on its next
// request. Read failures resolve to null (the route answers 404); parse
// failures degrade to empty data, matching the panes' plain-text fallback.
export class HighlightService {
  private readonly root: string;
  private readonly memo = new Map<string, HighlightFile>();
  private warned = false;

  constructor(root: string) {
    this.root = root;
  }

  async get(project: Manifest, rel: string): Promise<HighlightFile | null> {
    const lang = languageForPath(rel);
    if (!lang) return null;
    const full = path.join(this.root, project.dir, rel);
    let real: string;
    try {
      real = fs.realpathSync(full);
    } catch {
      return null;
    }
    // The route already gates rel through the project's served allowlist; this
    // realpath check keeps a symlinked source from escaping the repository,
    // mirroring serveStatic's containment rule.
    const within = path.relative(this.root, real);
    if (within.startsWith("..") || path.isAbsolute(within)) return null;
    let bytes: Buffer;
    try {
      if (!fs.statSync(real).isFile()) return null;
      bytes = fs.readFileSync(real);
    } catch {
      return null;
    }
    const key = `${project.dir}/${rel}`;
    const hash = sha256(bytes);
    const cached = this.memo.get(key);
    if (cached && cached.sha256 === hash) return cached;
    let data: HighlightData;
    try {
      data = await computeHighlightData(bytes.toString("utf-8"), lang);
    } catch (error) {
      if (!this.warned) {
        this.warned = true;
        process.stderr.write(`[viewer] highlighting unavailable: ${(error as Error)?.message ?? error}\n`);
      }
      data = { spans: [], folds: [] };
    }
    const file = encodeHighlightFile(data, hash);
    this.memo.set(key, file);
    return file;
  }
}

interface CacheArgs {
  root: string;
  project: string;
  out: string | null;
}

export function parseArgs(argv: string[]): CacheArgs {
  const args: CacheArgs = { root: ".", project: "", out: null };
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--root") args.root = optionValue(argv, i++);
    else if (arg === "--project") args.project = optionValue(argv, i++);
    else if (arg === "--out") args.out = optionValue(argv, i++);
    else throw new CliUsageError(`Unknown option: ${arg}`);
  }
  return args;
}

export async function main(argv = process.argv.slice(2)): Promise<void> {
  const args = parseArgs(argv);
  const root = path.resolve(args.root);
  const project = readProject(root, args.project);
  const outDir = args.out ? path.resolve(args.out) : path.join(root, project.dir, "build", "highlight-cache");
  const written = await generate(root, project, outDir);
  process.stdout.write(`highlight-cache: ${written} file(s) generated in ${path.relative(root, outDir)}/\n`);
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  void main().catch((error: Error) => {
    process.stderr.write(`highlight-cache: ${error.message}\n`);
    process.exitCode = error instanceof CliUsageError ? 2 : 1;
  });
}
