#!/usr/bin/env node
// Generate a static Lean LSP response cache for the formalization viewer.
//
// For each Lean source file the viewer can display, this records what the live
// `lake env lean --server` bridge would answer at the cursor positions the
// viewer can ask about: `$/lean/plainGoal`, `$/lean/plainTermGoal`, and
// `textDocument/hover`, plus the file's final diagnostics. Responses are
// constant across a symbol, so positions are sampled once per token (plus column
// 0 of every line) and adjacent samples with identical answers are merged;
// response payloads are interned into shared tables so the cache stays small.
//
// A cache file is keyed by a hash of the Lean source, its transitive in-project
// imports, and the toolchain pins (lean-toolchain, lake-manifest.json,
// lakefile.*). Files whose key is unchanged are skipped, so editing one chapter
// re-elaborates only that chapter and the files that import it.
//
// Columns are UTF-16 code units (LSP positions); an index of -1 means the live
// server answered null at that position. Lookup is "latest sample at or before
// the requested column".

import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { LeanServer } from "./lean-server.ts";

const CACHE_VERSION = 1;
const IMPORT_RE = /^[ \t]*import\s+([\p{L}\p{N}_.«»]+)/gmu;
const TOOLCHAIN_FILES = ["lean-toolchain", "lake-manifest.json", "lakefile.lean", "lakefile.toml"];
const REQUEST_WINDOW = 256;
const REQUEST_TIMEOUT = 120;
const QUERIES = ["$/lean/plainGoal", "$/lean/plainTermGoal", "textDocument/hover"];

type Logger = (message: string) => void;

function isWordChar(ch: string): boolean {
  return /[\p{L}\p{N}\p{M}\p{Pc}'!?.«»]/u.test(ch);
}

// Sample columns for one line: 0 plus each token start, in UTF-16 units.
export function utf16Columns(line: string): number[] {
  const cps = Array.from(line);
  const prefix = [0];
  for (const ch of cps) prefix.push(prefix[prefix.length - 1] + (ch.codePointAt(0)! > 0xffff ? 2 : 1));
  const cols = new Set<number>([0]);
  let i = 0;
  while (i < cps.length) {
    if (/\s/u.test(cps[i])) {
      i += 1;
      continue;
    }
    cols.add(prefix[i]);
    if (isWordChar(cps[i])) {
      while (i < cps.length && isWordChar(cps[i])) i += 1;
    } else {
      i += 1;
    }
  }
  return [...cols].sort((a, b) => a - b);
}

function fileSha256(p: string): string {
  return createHash("sha256").update(fs.readFileSync(p)).digest("hex");
}

function toolchainHash(root: string): string {
  const digest = createHash("sha256");
  for (const name of TOOLCHAIN_FILES) {
    const p = path.join(root, name);
    if (fs.existsSync(p) && fs.statSync(p).isFile()) {
      digest.update(name);
      digest.update(fileSha256(p));
    }
  }
  return digest.digest("hex");
}

// In-project files imported by `p` (module Foo.Bar -> leanSrc/Foo/Bar.lean).
function projectImports(p: string, leanSrc: string): string[] {
  const text = fs.readFileSync(p, "utf-8");
  const deps: string[] = [];
  for (const match of text.matchAll(IMPORT_RE)) {
    const candidate = path.join(leanSrc, ...match[1].split(".")) + ".lean";
    if (fs.existsSync(candidate) && fs.statSync(candidate).isFile()) {
      deps.push(path.resolve(candidate));
    }
  }
  return deps;
}

function stableStringify(value: unknown): string {
  if (value === null || typeof value !== "object") return JSON.stringify(value) ?? "null";
  if (Array.isArray(value)) return `[${value.map(stableStringify).join(",")}]`;
  const obj = value as Record<string, unknown>;
  return `{${Object.keys(obj)
    .sort()
    .map((k) => `${JSON.stringify(k)}:${stableStringify(obj[k])}`)
    .join(",")}}`;
}

// Hash of the file, its transitive in-project imports, and toolchain pins.
function cacheKey(p: string, leanSrc: string, pins: string): string {
  const closure = new Map<string, string>();
  const queue = [path.resolve(p)];
  while (queue.length) {
    const current = queue.pop()!;
    if (closure.has(current)) continue;
    closure.set(current, fileSha256(current));
    queue.push(...projectImports(current, leanSrc));
  }
  const files = [...closure.entries()]
    .map(([abs, hash]) => [path.relative(leanSrc, abs), hash] as [string, string])
    .sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
  return createHash("sha256")
    .update(stableStringify({ version: CACHE_VERSION, pins, files }))
    .digest("hex");
}

// Drop the position-specific `range` from termGoal/hover responses: the viewer
// never reads it, and without it identical answers at different positions dedupe
// into one table entry.
function normalize(slot: number, value: unknown): unknown {
  if (value !== null && typeof value === "object" && (slot === 1 || slot === 2) && "range" in value) {
    const { range: _range, ...rest } = value as Record<string, unknown>;
    return rest;
  }
  return value;
}

function intern(table: unknown[], index: Map<string, number>, value: unknown): number {
  if (value === null || value === undefined) return -1;
  const key = stableStringify(value);
  let i = index.get(key);
  if (i === undefined) {
    i = table.length;
    index.set(key, i);
    table.push(value);
  }
  return i;
}

// Query goal/termGoal/hover at every sample position, pipelined through a
// bounded window of in-flight requests. Returns "line:col" -> [g, t, h].
async function sampleFile(
  server: LeanServer,
  uri: string,
  lines: string[],
  tables: [unknown[], unknown[], unknown[]],
  indexes: [Map<string, number>, Map<string, number>, Map<string, number>],
): Promise<Map<string, [number, number, number]>> {
  const work: Array<[number, number, number, string]> = [];
  lines.forEach((line, lineNo) => {
    for (const col of utf16Columns(line)) {
      QUERIES.forEach((method, slot) => work.push([lineNo, col, slot, method]));
    }
  });
  const results = new Map<string, [number, number, number]>();
  const pending = new Map<number, [number, number, number]>();
  let cursor = 0;
  while (cursor < work.length || pending.size) {
    while (cursor < work.length && pending.size < REQUEST_WINDOW) {
      const [lineNo, col, slot, method] = work[cursor++];
      const rid = server.request(method, {
        textDocument: { uri },
        position: { line: lineNo, character: col },
      });
      pending.set(rid, [lineNo, col, slot]);
    }
    const ready = await server.takeResponses([...pending.keys()], REQUEST_TIMEOUT);
    for (const [rid, message] of ready) {
      const [lineNo, col, slot] = pending.get(rid)!;
      pending.delete(rid);
      const ref = intern(tables[slot], indexes[slot], normalize(slot, message.result ?? null));
      const key = `${lineNo}:${col}`;
      const triple = results.get(key) ?? [-1, -1, -1];
      triple[slot] = ref;
      results.set(key, triple);
    }
  }
  return results;
}

function buildCache(
  relPath: string,
  key: string,
  lines: string[],
  samples: Map<string, [number, number, number]>,
  diagnostics: unknown[],
  tables: [unknown[], unknown[], unknown[]],
): Record<string, unknown> {
  const outLines: Record<string, number[][]> = {};
  lines.forEach((line, lineNo) => {
    const row: number[][] = [];
    let previous: string | null = null;
    for (const col of utf16Columns(line)) {
      const refs = samples.get(`${lineNo}:${col}`) ?? [-1, -1, -1];
      const serialized = refs.join(",");
      if (serialized === previous) continue;
      previous = serialized;
      row.push([col, ...refs]);
    }
    if (row.some((sample) => sample.slice(1).some((ref) => ref !== -1))) {
      outLines[String(lineNo)] = row;
    }
  });
  return {
    version: CACHE_VERSION,
    key,
    path: relPath,
    diagnostics,
    goals: tables[0],
    termGoals: tables[1],
    hovers: tables[2],
    lines: outLines,
  };
}

function discoverLeanFiles(leanSrc: string): string[] {
  const found: string[] = [];
  const seen = new Set<string>();
  const stack = [leanSrc];
  while (stack.length) {
    const dir = stack.pop()!;
    let real: string;
    try {
      real = fs.realpathSync(dir);
    } catch {
      continue;
    }
    if (seen.has(real)) continue;
    seen.add(real);
    let entries: fs.Dirent[];
    try {
      entries = fs.readdirSync(dir, { withFileTypes: true });
    } catch {
      continue;
    }
    for (const entry of entries.sort((a, b) => (a.name < b.name ? -1 : 1))) {
      const full = path.join(dir, entry.name);
      const isDir = entry.isDirectory() || (entry.isSymbolicLink() && safeIsDir(full));
      if (isDir) {
        if (!entry.name.startsWith(".")) stack.push(full);
      } else if (entry.name.endsWith(".lean")) {
        found.push(full);
      }
    }
  }
  return found.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
}

function safeIsDir(p: string): boolean {
  try {
    return fs.statSync(p).isDirectory();
  } catch {
    return false;
  }
}

// Generate caches under outDir; returns {generated, reused} file lists. The Lean
// server is only spawned when at least one cache is stale.
export async function generate(
  root: string,
  projectDir: string,
  outDir: string,
  files: string[] | null = null,
  elabTimeout = 1800,
  log: Logger = (m) => process.stdout.write(`${m}\n`),
): Promise<{ generated: string[]; reused: string[] }> {
  root = path.resolve(root);
  const projectRoot = path.join(root, projectDir);
  const leanSrc = path.join(projectRoot, "lean");
  const targets = files ? files.map((f) => path.resolve(f)) : discoverLeanFiles(leanSrc);
  const pins = toolchainHash(projectRoot);

  const stale: Array<{ p: string; rel: string; outPath: string; key: string }> = [];
  const reused: string[] = [];
  for (const p of targets) {
    const rel = path.relative(projectRoot, p);
    const outPath = path.join(outDir, rel + ".json");
    const key = cacheKey(p, leanSrc, pins);
    let existingKey: string | null = null;
    if (fs.existsSync(outPath)) {
      try {
        existingKey = JSON.parse(fs.readFileSync(outPath, "utf-8")).key ?? null;
      } catch {
        existingKey = null;
      }
    }
    if (existingKey === key) reused.push(rel);
    else stale.push({ p, rel, outPath, key });
  }

  if (reused.length) log(`lsp-cache: ${reused.length} file(s) up to date`);
  if (!stale.length) return { generated: [], reused };

  const server = new LeanServer(projectRoot);
  const generated: string[] = [];
  try {
    await server.initialize(`file://${projectRoot}`);
    for (const { p, rel, outPath, key } of stale) {
      const uri = `file://${p}`;
      const text = fs.readFileSync(p, "utf-8");
      const lines = text.split("\n");
      const started = Date.now();
      log(`lsp-cache: elaborating ${rel} (${lines.length} lines)...`);
      await server.openAndElaborate(uri, text, elabTimeout);
      log(`lsp-cache: sampling ${rel}...`);
      const tables: [unknown[], unknown[], unknown[]] = [[], [], []];
      const indexes: [Map<string, number>, Map<string, number>, Map<string, number>] = [
        new Map(),
        new Map(),
        new Map(),
      ];
      const samples = await sampleFile(server, uri, lines, tables, indexes);
      const diagnostics = server.diagnosticsFor(uri);
      const cache = buildCache(rel, key, lines, samples, diagnostics, tables);
      fs.mkdirSync(path.dirname(outPath), { recursive: true });
      fs.writeFileSync(outPath, JSON.stringify(cache));
      const elapsed = (Date.now() - started) / 1000;
      log(`lsp-cache: wrote ${path.relative(root, outPath)} (${samples.size} samples, ${elapsed.toFixed(1)}s)`);
      generated.push(rel);
    }
  } finally {
    await server.shutdown();
  }
  return { generated, reused };
}

interface CliArgs {
  files: string[];
  root: string;
  projectDir: string;
  out: string | null;
  elabTimeout: number;
}

function parseArgs(argv: string[]): CliArgs {
  const args: CliArgs = { files: [], root: ".", projectDir: "polish-space", out: null, elabTimeout: 1800 };
  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === "--root") args.root = argv[++i];
    else if (arg === "--project-dir") args.projectDir = argv[++i];
    else if (arg === "--out") args.out = argv[++i];
    else if (arg === "--elab-timeout") args.elabTimeout = Number.parseInt(argv[++i], 10);
    else args.files.push(arg);
  }
  return args;
}

async function main(): Promise<void> {
  const args = parseArgs(process.argv.slice(2));
  if (args.out === null) {
    process.stderr.write("lsp-cache: --out is required\n");
    process.exit(2);
  }
  const { generated, reused } = await generate(
    args.root,
    args.projectDir,
    args.out,
    args.files.length ? args.files : null,
    args.elabTimeout,
  );
  process.stdout.write(`lsp-cache: ${generated.length} generated, ${reused.length} reused\n`);
}

if (import.meta.url === `file://${process.argv[1]}`) {
  void main();
}
