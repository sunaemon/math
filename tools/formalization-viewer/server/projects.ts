// Project discovery, mount routing, and the static-serving allowlist for the
// formalization viewer.
//
// The generic viewer is served from VIEWER_DIR; the projects it renders are
// described by <dir>/manifest.json files at the repo root. Every project is
// served at its mount simultaneously; the default project only decides where
// "/" redirects. This module is the Node port of the routing/allowlist logic in
// the former booklink_lsp_server.py.

import fs from "node:fs";
import path from "node:path";

export const VIEWER_DIR = "/tools/formalization-viewer";

export interface Manifest {
  mount: string;
  dir: string;
  name?: string;
  served?: Record<string, string[]>;
  flat?: string[];
  license?: unknown;
  [key: string]: unknown;
}

// --- posix path helpers matching CPython's posixpath semantics -------------

export function posixNormpath(p: string): string {
  if (p === "") return ".";
  let initialSlashes = p.startsWith("/") ? 1 : 0;
  if (initialSlashes && p.startsWith("//") && !p.startsWith("///")) initialSlashes = 2;
  const comps = p.split("/");
  const newComps: string[] = [];
  for (const comp of comps) {
    if (comp === "" || comp === ".") continue;
    if (
      comp !== ".." ||
      (!initialSlashes && newComps.length === 0) ||
      (newComps.length > 0 && newComps[newComps.length - 1] === "..")
    ) {
      newComps.push(comp);
    } else if (newComps.length > 0) {
      newComps.pop();
    }
  }
  const joined = newComps.join("/");
  const result = (initialSlashes ? "/".repeat(initialSlashes) : "") + joined;
  return result || ".";
}

function splitext(p: string): string {
  const base = p.slice(p.lastIndexOf("/") + 1);
  const dot = base.lastIndexOf(".");
  if (dot <= 0) return "";
  let leading = 0;
  while (leading < base.length && base[leading] === ".") leading += 1;
  if (dot < leading) return "";
  return base.slice(dot);
}

function unquote(s: string): string {
  try {
    return decodeURIComponent(s);
  } catch {
    return s.replace(/%[0-9a-fA-F]{2}/g, (m) => {
      try {
        return decodeURIComponent(m);
      } catch {
        return m;
      }
    });
  }
}

function isDir(p: string): boolean {
  try {
    return fs.statSync(p).isDirectory();
  } catch {
    return false;
  }
}

function isFile(p: string): boolean {
  try {
    return fs.statSync(p).isFile();
  } catch {
    return false;
  }
}

// Walk a directory tree following symlinks, guarding against cycles by skipping
// already-visited real directories. Yields absolute file paths.
function* walkFiles(top: string): Generator<string> {
  const seen = new Set<string>();
  const stack = [top];
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
    for (const entry of entries) {
      const full = path.join(dir, entry.name);
      if (entry.isDirectory() || (entry.isSymbolicLink() && isDir(full))) {
        stack.push(full);
      } else if (entry.isFile() || (entry.isSymbolicLink() && isFile(full))) {
        yield full;
      }
    }
  }
}

// --- manifest validation/discovery -----------------------------------------

function validateManifest(p: string, meta: unknown): asserts meta is Manifest {
  if (meta === null || typeof meta !== "object" || Array.isArray(meta)) {
    throw new Error(`${p}: expected a JSON object at the top level.`);
  }
  const mount = (meta as Manifest).mount;
  if (typeof mount !== "string" || !mount.startsWith("/") || mount.replace(/\/+$/, "") === "") {
    throw new Error(`${p}: missing or invalid string field "mount".`);
  }
  const served = (meta as Manifest).served;
  if (served !== undefined && (served === null || typeof served !== "object" || Array.isArray(served))) {
    throw new Error(`${p}: "served" must be an object of subdir -> extensions.`);
  }
}

function readProject(root: string, dirname: string): Manifest {
  const p = path.join(root, dirname, "manifest.json");
  let meta: unknown;
  try {
    meta = JSON.parse(fs.readFileSync(p, "utf-8"));
  } catch (error) {
    throw new Error(`${p}: invalid JSON (${(error as Error).message})`);
  }
  validateManifest(p, meta);
  if (meta.dir === undefined) meta.dir = dirname;
  return meta;
}

function discoverDirnames(root: string): string[] {
  return fs
    .readdirSync(root)
    .filter((entry) => isFile(path.join(root, entry, "manifest.json")))
    .sort();
}

export class Projects {
  readonly root: string;
  readonly projects: Manifest[];
  readonly defaultProject: Manifest;
  readonly byMount: Manifest[];
  readonly mounts: Set<string>;
  readonly defaultMount: string;
  readonly lspRoots: Map<string, string>;
  readonly defaultLspRoot: string;
  readonly manifestUrls: Set<string>;
  readonly watchDirs: string[];
  readonly watchAliases: Map<string, string>;
  private readonly allowedPrefixes: Map<string, Set<string>>;
  private readonly flatPrefixes: Set<string>;

  constructor(root: string, namedProject = "") {
    this.root = root;
    const named = namedProject.trim();
    const dirnames = discoverDirnames(root);
    if (dirnames.length === 0) {
      throw new Error("No project manifest found (expected <dir>/manifest.json under the repo root).");
    }
    if (named && !dirnames.includes(named)) {
      throw new Error(`BOOKLINK_PROJECT=${named}: no ${named}/manifest.json under the repo root.`);
    }
    this.projects = dirnames.map((dirname) => readProject(root, dirname));

    const mountsSeen = new Map<string, string>();
    for (const meta of this.projects) {
      if (mountsSeen.has(meta.mount)) {
        throw new Error(`duplicate mount ${meta.mount}: ${mountsSeen.get(meta.mount)} and ${meta.dir}`);
      }
      mountsSeen.set(meta.mount, meta.dir);
    }

    const defaultDir = named || this.projects[0].dir;
    this.defaultProject = this.projects.find((meta) => meta.dir === defaultDir)!;
    // Longest mount first so routing never confuses mounts that prefix one
    // another (e.g. /polish-space and /polish-space-ch1).
    this.byMount = [...this.projects].sort((a, b) => b.mount.length - a.mount.length);
    this.mounts = new Set(this.projects.map((meta) => meta.mount));
    this.defaultMount = this.defaultProject.mount;

    this.lspRoots = new Map(this.projects.map((meta) => [meta.dir, path.join(root, meta.dir)]));
    this.defaultLspRoot = this.lspRoots.get(this.defaultProject.dir)!;
    this.manifestUrls = new Set(this.projects.map((meta) => `/${meta.dir}/manifest.json`));

    this.allowedPrefixes = new Map();
    this.flatPrefixes = new Set();
    const watchDirs = new Set<string>();
    for (const meta of this.projects) {
      for (const [sub, exts] of Object.entries(meta.served ?? {})) {
        const prefix = `/${meta.dir}/${sub}/`;
        const set = this.allowedPrefixes.get(prefix) ?? new Set<string>();
        for (const ext of exts) set.add(`.${ext}`);
        this.allowedPrefixes.set(prefix, set);
        watchDirs.add(`${meta.dir}/${sub}`);
      }
      for (const sub of meta.flat ?? []) this.flatPrefixes.add(`/${meta.dir}/${sub}/`);
    }
    this.watchDirs = [...[...watchDirs].sort(), "tools/formalization-viewer"];
    this.watchAliases = this.computeWatchAliases();
  }

  // Map realpath prefixes of symlinked served trees back to their project-local
  // form. File-watch events report real paths; tabs of a project that shares
  // another book's trees via symlinks name those files by the symlinked path, so
  // each event is also broadcast under that alias.
  private computeWatchAliases(): Map<string, string> {
    const aliases = new Map<string, string>();
    for (const meta of this.projects) {
      for (const sub of Object.keys(meta.served ?? {})) {
        const top = path.join(this.root, meta.dir, sub);
        if (!isDir(top)) continue;
        const candidates = [top, ...this.collectSubdirs(top)];
        for (const candidate of candidates) {
          let isLink = false;
          try {
            isLink = fs.lstatSync(candidate).isSymbolicLink();
          } catch {
            continue;
          }
          if (isLink && isDir(candidate)) {
            const real = `${path.relative(this.root, fs.realpathSync(candidate))}/`;
            aliases.set(real, `${path.relative(this.root, candidate)}/`);
          }
        }
      }
    }
    return aliases;
  }

  private collectSubdirs(top: string): string[] {
    const dirs: string[] = [];
    const seen = new Set<string>();
    const stack = [top];
    while (stack.length) {
      const dir = stack.pop()!;
      let entries: fs.Dirent[];
      try {
        entries = fs.readdirSync(dir, { withFileTypes: true });
      } catch {
        continue;
      }
      for (const entry of entries) {
        const full = path.join(dir, entry.name);
        if (entry.isDirectory() || (entry.isSymbolicLink() && isDir(full))) {
          let real: string;
          try {
            real = fs.realpathSync(full);
          } catch {
            continue;
          }
          dirs.push(full);
          if (!seen.has(real)) {
            seen.add(real);
            // Only descend into real directories, but still record symlinked
            // dirs (above) so they can be detected as aliases.
            if (entry.isDirectory()) stack.push(full);
          }
        }
      }
    }
    return dirs;
  }

  isAllowedPath(urlPath: string): boolean {
    const noQuery = urlPath.split("?", 1)[0].split("#", 1)[0];
    let p = posixNormpath(unquote(noQuery));
    if (!p.startsWith("/")) p = `/${p}`;
    if (p === VIEWER_DIR || p.startsWith(`${VIEWER_DIR}/`) || this.manifestUrls.has(p)) {
      return true;
    }
    for (const [prefix, extensions] of this.allowedPrefixes) {
      if (p.startsWith(prefix)) {
        const rest = p.slice(prefix.length);
        if (this.flatPrefixes.has(prefix) && rest.includes("/")) {
          return false; // keep this dir flat: no nested home/, xdg-cache/, ...
        }
        return extensions.has(splitext(p));
      }
    }
    return false;
  }

  // Rewrite a mount-relative URL path to the underlying repo path: manifest.json
  // is the project's config, paths that exist under the viewer directory are
  // viewer assets, and everything else is a project file. Returns the pathname
  // unchanged when it is not under any mount.
  applyMount(pathname: string): string {
    const meta = this.byMount.find((m) => pathname.startsWith(`${m.mount}/`));
    if (!meta) return pathname;
    const rest = pathname.slice(meta.mount.length + 1);
    if (rest === "manifest.json") return `/${meta.dir}/manifest.json`;
    if (rest === "") return `${VIEWER_DIR}/`;
    const rel = posixNormpath(unquote(rest));
    if (rel === ".." || rel.startsWith("/") || rel.startsWith("../")) return pathname;
    if (isFile(path.join(this.root, VIEWER_DIR.replace(/^\//, ""), rel))) {
      return `${VIEWER_DIR}/${rest}`;
    }
    return `/${meta.dir}/${rest}`;
  }

  // Relative paths (mount-root relative, posix) of every PDF that currently
  // exists in this project's served subdirectories whose allowlist includes
  // `pdf`. Only files that really exist are offered; `flat` subdirectories are
  // kept top-level only, matching the static serving rules.
  projectPdfList(meta: Manifest): string[] {
    const projectRoot = path.join(this.root, meta.dir);
    const flat = new Set(meta.flat ?? []);
    const found = new Set<string>();
    for (const [sub, exts] of Object.entries(meta.served ?? {})) {
      if (!exts.includes("pdf")) continue;
      const srcDir = path.join(projectRoot, sub);
      if (!isDir(srcDir)) continue;
      for (const full of walkFiles(srcDir)) {
        if (!full.toLowerCase().endsWith(".pdf")) continue;
        if (flat.has(sub) && path.dirname(full) !== srcDir) continue;
        if (!fs.existsSync(full)) continue; // skip a broken symlink
        found.add(path.relative(projectRoot, full).split(path.sep).join("/"));
      }
    }
    return [...found].sort();
  }
}
