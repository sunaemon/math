// Small shared helpers used across the viewer modules: project-relative path
// normalization and URL mapping, HTML escaping, and debug logging. Split out of
// app.ts so the rendering modules can import them without depending on app.ts
// (which would create import cycles). These read shared state/project but never
// call back into app.ts, so the dependency runs one way: util -> state.

import { state, project } from "./state.js";

export function reportError(error: unknown): void {
  console.error(error);
}

// Verbose scroll/sync tracing runs on the hot scroll path, so it is off unless
// the page is opened with ?debug — no per-event allocation in normal use.
const DEBUG_LOG = new URLSearchParams(window.location.search).has("debug");

export function logEvent(type: string, detail: Record<string, any> = {}): void {
  if (!DEBUG_LOG) return;
  const entry = {
    n: ++state.logSeq,
    t: Math.round(performance.now()),
    type,
    active: state.activeIndex,
    suppress: state.suppressScroll,
    ...detail,
  };
  console.debug("[booklink]", entry);
}

// Paths are tracked relative to the project root (e.g. src/..., lean/...).
// repoPath normalizes any path to that project-relative form; repoUrl maps it
// back to a fetchable URL under the project directory.
export function repoPath(path: string | null | undefined): string {
  if (!path) return "";
  const dir = project.dir || "";
  const root = state.map?.root || "";
  let rel = root && path.startsWith(root + "/") ? path.slice(root.length + 1) : path.replace(/^\/+/, "");
  if (dir && rel === dir) return "";
  if (dir && rel.startsWith(dir + "/")) rel = rel.slice(dir.length + 1);
  return rel;
}

// Prefix of the site that the mount is served under: empty for the live
// bridge (mount at the host root), the leading path segments when a static
// dist is hosted from a subdirectory.
let sitePrefix: string | null = null;

export function mountPrefix(): string {
  if (sitePrefix !== null) return sitePrefix;
  const mount = project.mount || "";
  const path = window.location.pathname;
  const index = mount ? path.lastIndexOf(mount + "/") : -1;
  sitePrefix = index > 0 ? path.slice(0, index) : "";
  return sitePrefix;
}

export function repoUrl(path: string): string {
  const rel = repoPath(path);
  // Bundled viewer fixtures live at the repo root; everything else is project
  // data served under the mount, which unifies the viewer assets and the
  // project files in one URL tree.
  return rel.startsWith("tools/") ? `${mountPrefix()}/${rel}` : `${mountPrefix()}${project.mount}/${rel}`;
}

export function displayPath(path: string | null | undefined): string {
  return repoPath(path);
}

// Vet a URL before it becomes a link target. The manifest-derived URLs we put in
// hrefs (project.repository, a vendored component's homepage) are author-controlled
// repo config, but a stray `javascript:`/`data:` scheme there would still be a
// script sink once written to an href, so allow only http/https/mailto and
// scheme-relative/relative URLs; anything else collapses to "". Spaces and control
// characters are dropped first because browsers strip tabs/newlines before
// resolving a scheme, so "java\tscript:" would otherwise slip past the check.
export function safeHref(url: string): string {
  let cleaned = "";
  for (const ch of url || "") {
    const code = ch.codePointAt(0) ?? 0;
    if (code > 0x20 && code !== 0x7f) cleaned += ch;
  }
  if (!cleaned) return "";
  const scheme = /^([a-z][a-z0-9+.-]*):/i.exec(cleaned);
  if (scheme) {
    const name = scheme[1].toLowerCase();
    if (name !== "http" && name !== "https" && name !== "mailto") return "";
  }
  return cleaned;
}

export function escapeHtml(text: string): string {
  return text
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#39;");
}
