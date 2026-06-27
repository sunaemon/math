// Runtime fields for the formalization viewer's About panel.
//
// Injected into the served manifest by static-dist.ts (at dist build time) and
// serve.ts (per request): the commit the viewer was built from, and each
// license file's text (so the panel can show the license inline without serving
// the files).

import { execFileSync } from "node:child_process";
import { readFileSync, realpathSync } from "node:fs";
import path from "node:path";

// Resolve `rel` against `root`, returning the absolute path only when it stays
// within `root` both lexically and after symlink resolution — the same
// containment guard serve.ts applies to every static file. License item paths
// come from on-disk config (a project manifest.json, vendor/manifest.json), so
// this keeps a stray "../../etc/passwd" entry from inlining an out-of-repo file
// into the served manifest. Returns null on escape or a non-existent path.
function resolveWithinRoot(root: string, rel: string): string | null {
  const abs = path.join(root, rel);
  const within = path.relative(root, abs);
  if (within.startsWith("..") || path.isAbsolute(within)) return null;
  let real: string;
  try {
    real = realpathSync(abs);
  } catch {
    return null;
  }
  const realWithin = path.relative(root, real);
  if (realWithin.startsWith("..") || path.isAbsolute(realWithin)) return null;
  return real;
}

export interface RepoVersion {
  describe: string;
  rev: string;
  date: string;
}

export function repoVersion(root = "."): RepoVersion {
  const git = (...args: string[]): string => {
    try {
      return execFileSync("git", ["-C", root, ...args], {
        encoding: "utf-8",
      }).trim();
    } catch {
      return "";
    }
  };

  return {
    // `describe` is the friendly version: a tag when one exists, else the short
    // hash; `-dirty` marks an uncommitted working tree.
    describe: git("describe", "--tags", "--always", "--dirty"),
    rev: git("rev-parse", "--short", "HEAD"),
    date: git("show", "-s", "--format=%cs", "HEAD"),
  };
}

interface LicenseItem {
  file?: string;
  text?: string;
  [key: string]: unknown;
}
interface LicenseObject {
  items?: LicenseItem[];
  [key: string]: unknown;
}

// Inline each license item's file text into the manifest license object so the
// About panel can display it without serving the files. Mutates and returns
// licenseObj; a missing/unreadable file just gets empty text.
export function attachLicenseText<T>(root: string, licenseObj: T): T {
  if (licenseObj === null || typeof licenseObj !== "object") return licenseObj;
  const obj = licenseObj as LicenseObject;
  for (const item of obj.items ?? []) {
    const rel = item.file;
    if (!rel) continue;
    const abs = resolveWithinRoot(root, rel);
    if (abs !== null) {
      try {
        item.text = readFileSync(abs, "utf-8");
        continue;
      } catch {
        // Fall through to the empty-text default below.
      }
    }
    if (item.text === undefined) item.text = "";
  }
  return licenseObj;
}

interface VendorComponent {
  name: string;
  version: string;
  spdx: string;
  homepage?: string;
  licenseFile?: string;
}

const VENDOR_REL = "tools/formalization-viewer/vendor";

// Expand the vendored components (vendor/manifest.json) into license items so the
// About panel lists each one — name, version, SPDX, source, and its license text
// — instead of a single opaque notices blob. Appends to licenseObj.items; the
// caller then runs attachLicenseText to inline each item's license file. Both the
// on-page notices and THIRD-PARTY-NOTICES.md are thus generated from one manifest.
export function appendVendorComponents<T>(root: string, licenseObj: T): T {
  if (licenseObj === null || typeof licenseObj !== "object") return licenseObj;
  const obj = licenseObj as LicenseObject;
  let components: VendorComponent[];
  try {
    const manifest = JSON.parse(readFileSync(path.join(root, VENDOR_REL, "manifest.json"), "utf-8"));
    components = Array.isArray(manifest.components) ? manifest.components : [];
  } catch {
    return licenseObj;
  }
  const items = (obj.items ??= []);
  for (const component of components) {
    items.push({
      scope: component.name,
      version: component.version,
      spdx: component.spdx,
      source: component.homepage,
      file: component.licenseFile ? `${VENDOR_REL}/${component.licenseFile}` : undefined,
    });
  }
  return licenseObj;
}

// text[i] is '{'; return [inner, index after matching '}'].
function readBraced(text: string, i: number): [string, number] {
  let depth = 0;
  let j = i;
  while (j < text.length) {
    if (text[j] === "{") {
      depth += 1;
    } else if (text[j] === "}") {
      depth -= 1;
      if (depth === 0) return [text.slice(i + 1, j), j + 1];
    }
    j += 1;
  }
  return [text.slice(i + 1), text.length];
}

// KaTeX lacks a few lualatex/unicode-math commands the book uses; map to close
// equivalents so the extracted macros still render.
const KATEX_SHIMS: Record<string, string> = {
  "\\symbf": "\\boldsymbol{#1}",
  "\\symbfup": "\\mathbf{#1}",
  "\\symup": "\\mathrm{#1}",
  "\\symsf": "\\mathsf{#1}",
};

// Parse \newcommand/\renewcommand definitions from a macros.tex into a KaTeX
// `macros` map ({"\\Name": "body"}). Only the macros actually used in a rendered
// fragment are expanded by KaTeX, so structural (non-math) ones are harmless to
// include; unreadable file -> just the compat shims.
export function katexMacros(macrosTexPath: string): Record<string, string> {
  const macros: Record<string, string> = { ...KATEX_SHIMS };
  let text: string;
  try {
    text = readFileSync(macrosTexPath, "utf-8");
  } catch {
    return macros;
  }
  const re = /\\(?:re)?newcommand\s*\{\s*(\\[A-Za-z]+)\s*\}/g;
  let match: RegExpExecArray | null;
  while ((match = re.exec(text)) !== null) {
    const name = match[1];
    let i = match.index + match[0].length;
    while (i < text.length && (text[i] === " " || text[i] === "\t")) i += 1;
    while (i < text.length && text[i] === "[") {
      // [nargs] and/or [default]
      const close = text.indexOf("]", i);
      if (close < 0) break;
      i = close + 1;
      while (i < text.length && (text[i] === " " || text[i] === "\t")) i += 1;
    }
    if (i < text.length && text[i] === "{") {
      const [body] = readBraced(text, i);
      macros[name] = body.trim();
    }
  }
  return macros;
}

// The book's macros.tex for a project (its tex/ may symlink another book).
export function macrosTexPath(root: string, projectDir: string): string {
  return path.join(root, projectDir, "tex", "macros.tex");
}
