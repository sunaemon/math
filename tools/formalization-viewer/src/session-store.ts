// Per-project reading session: where the reader was and which documents they
// had open, persisted in localStorage so a reload — including the automatic one
// the reload guard triggers whenever the viewer is rebuilt — resumes instead of
// starting over at the first marker.
//
// Split from global local preferences (line numbers, marker highlights, scroll
// sync) and URL-owned pane layout/PDF mode, which apply to every book:
// the reading position is per book, so it is keyed by the project mount and
// held in one object, written as a whole on every change.
//
// The storage handle is a parameter so this module has no DOM dependency and
// unit tests directly with `node --test` (session-store.test.ts).

export interface ViewerSession {
  // The permalink id of the active marker, or the key of the formalization skip
  // the reader was in. At most one is set: they are the two kinds of position.
  marker?: string | null;
  skip?: string | null;
  skipProgress?: number | null;
  // Markdown and Lean documents are reading-session state. PDF display mode
  // and pane layout are URL-owned and must not be restored from local storage.
  md?: string | null;
  lean?: string | null;
}

export interface StorageLike {
  getItem(key: string): string | null;
  setItem(key: string, value: string): void;
  removeItem?(key: string): void;
  key?(index: number): string | null;
  readonly length?: number;
}

export const SHARED_URL_VERSION = "1";
const LAYOUT_KEY = "formalization-viewer-layout-v2";
export const PDF_MODE_KEY = "formalization-viewer-pdf-mode";
export const PDF_PAPER_KEY = "formalization-viewer-pdf-paper";
export const PDF_FONT_SIZE_KEY = "formalization-viewer-pdf-font-size";
export const CODE_FONTS: Record<string, string> = {
  system: 'ui-monospace, SFMono-Regular, Menlo, Consolas, "Liberation Mono", monospace',
  menlo: 'Menlo, Consolas, "Liberation Mono", monospace',
  monaco: "Monaco, Menlo, Consolas, monospace",
  consolas: 'Consolas, Menlo, "Liberation Mono", monospace',
  "jetbrains-mono": '"JetBrains Mono", Menlo, Consolas, monospace',
  "fira-code": '"Fira Code", Menlo, Consolas, monospace',
};

export const SHARED_PREFERENCES: Record<string, { param: string; values?: string[]; fallback: string }> = {
  "formalization-viewer-layout-v2": { param: "layout", fallback: "{}" },
  [PDF_MODE_KEY]: { param: "pdfMode", values: ["chapter", "full"], fallback: "chapter" },
  [PDF_PAPER_KEY]: { param: "paper", values: ["default", "a4", "a5", "b5", "b6"], fallback: "default" },
  [PDF_FONT_SIZE_KEY]: { param: "fontSize", values: ["default", "10", "11", "12"], fallback: "default" },
};

function validPreference(key: string, value: string | null): string | null {
  const rule = SHARED_PREFERENCES[key];
  if (!rule || value === null || value.length > 8192) return null;
  if (rule.values) return rule.values.includes(value) ? value : null;
  try {
    const layout = JSON.parse(value);
    return layout && typeof layout === "object" && !Array.isArray(layout) ? value : null;
  } catch {
    return null;
  }
}

interface UrlLayoutNode {
  pane?: string;
  dir?: "row" | "col";
  children?: UrlLayoutNode[];
  ratios?: number[];
}

const PANE_ID = /^(?:pdf(?:-peer)?|md|lean|tex|infoview)$/;

// The URL grammar is deliberately independent of DOM/layout code so the early
// bootstrap and Node tests can use the same version migration and validation.
function decodeLayout(value: string | null, focus: string | null): string | null {
  if ((value?.length ?? 0) > 8192 || (focus && !PANE_ID.test(focus))) return null;
  let at = 0;
  const text = value ?? "";
  const seen = new Set<string>();
  function node(depth = 0): UrlLayoutNode {
    if (depth > 16) throw new Error("Layout too deep");
    const id = /^[a-z][a-z0-9-]*/.exec(text.slice(at))?.[0];
    if (!id) throw new Error("Expected pane or split");
    at += id.length;
    if (text[at] !== "(") {
      if (!PANE_ID.test(id) || seen.has(id)) throw new Error("Invalid or duplicate pane");
      seen.add(id);
      return { pane: id };
    }
    if (id !== "row" && id !== "col") throw new Error("Unknown split direction");
    at++;
    const children: UrlLayoutNode[] = [];
    const ratios: number[] = [];
    for (;;) {
      children.push(node(depth + 1));
      let ratio = 1;
      if (text[at] === ":") {
        at++;
        const number = /^(?:[0-9]+(?:\.[0-9]+)?|\.[0-9]+)/.exec(text.slice(at))?.[0];
        if (!number || !Number.isFinite(Number(number)) || Number(number) <= 0) throw new Error("Invalid ratio");
        at += number.length;
        ratio = Number(number);
      }
      ratios.push(ratio);
      if (text[at] !== ",") break;
      at++;
    }
    if (text[at++] !== ")") throw new Error("Unclosed split");
    return { dir: id, children, ratios };
  }
  try {
    const layout: { tree?: UrlLayoutNode; maximized?: string } = {};
    if (text) layout.tree = node();
    if (at !== text.length) return null;
    if (focus) layout.maximized = focus;
    return JSON.stringify(layout);
  } catch {
    return null;
  }
}

function encodeLayout(value: string): { layout: string; focus: string | null } | null {
  try {
    const saved = JSON.parse(value);
    const seen = new Set<string>();
    const encode = (node: UrlLayoutNode, depth = 0): string => {
      if (depth > 16 || !node || typeof node !== "object") throw new Error("Invalid layout");
      if (node.pane) {
        if (!PANE_ID.test(node.pane) || seen.has(node.pane)) throw new Error("Invalid pane");
        seen.add(node.pane);
        return node.pane;
      }
      if ((node.dir !== "row" && node.dir !== "col") || !Array.isArray(node.children) || !node.children.length)
        throw new Error("Invalid split");
      const children = node.children.map((child) => encode(child, depth + 1));
      if (children.length === 1) return children[0];
      const raw = children.map((_, i) => Number(node.ratios?.[i] ?? 1));
      if (raw.some((r) => !Number.isFinite(r) || r <= 0)) throw new Error("Invalid ratio");
      // Integer proportions are easier to edit than drag-generated decimals.
      // Quantize only large/fractional weights, to at most 1/10000 of the split.
      const largest = Math.max(...raw);
      const scaledTotal = raw.reduce((sum, ratio) => sum + ratio / largest, 0);
      const weights = raw.every((r) => Number.isInteger(r) && r <= 10000)
        ? raw
        : raw.map((r) => Math.max(1, Math.round((r / largest / scaledTotal) * 10000)));
      const gcd = (a: number, b: number): number => (b ? gcd(b, a % b) : a);
      const divisor = weights.reduce(gcd);
      const equal = weights.every((r) => r === weights[0]);
      return `${node.dir}(${children.map((child, i) => `${child}${equal ? "" : `:${weights[i] / divisor}`}`).join(",")})`;
    };
    const layout = saved.tree ? encode(saved.tree) : "";
    const focus = typeof saved.maximized === "string" && PANE_ID.test(saved.maximized) ? saved.maximized : null;
    return { layout, focus };
  } catch {
    return null;
  }
}

function knownVersion(params: URLSearchParams): boolean {
  return params.get("v") === SHARED_URL_VERSION;
}

export function sharedPreference(search: string, key: string): string | null {
  const params = new URLSearchParams(search);
  const rule = SHARED_PREFERENCES[key];
  if (!rule || !knownVersion(params)) return null;
  if (key === LAYOUT_KEY) {
    const layout = params.get("layout");
    // Accept links copied before the compact notation was introduced.
    if (layout?.startsWith("{")) return validPreference(key, layout);
    return decodeLayout(layout, params.get("focus"));
  }
  return validPreference(key, params.get(rule.param));
}

// Rewrite previous JSON links when writing; future versions stay untouched.
export function withSharedPreferences(
  search: string,
  preferences: Record<string, string>,
  defaults: Record<string, string> = {},
): string {
  const params = new URLSearchParams(search);
  if (params.has("v") && !knownVersion(params)) return search;
  const migrated = { ...preferences };
  if (params.get("layout")?.startsWith("{") && !(LAYOUT_KEY in migrated)) {
    const legacy = validPreference(LAYOUT_KEY, params.get("layout"));
    if (legacy) migrated[LAYOUT_KEY] = legacy;
    else params.delete("layout");
    params.delete("focus");
  }
  params.set("v", SHARED_URL_VERSION);
  for (const [key, value] of Object.entries(migrated)) {
    if (validPreference(key, value) === null) continue;
    const rule = SHARED_PREFERENCES[key];
    if (key === LAYOUT_KEY) {
      const encoded = encodeLayout(value);
      const defaultLayout = encodeLayout(defaults[key] ?? rule.fallback)?.layout;
      if (!encoded) continue;
      if (!encoded.layout || encoded.layout === defaultLayout) params.delete("layout");
      else params.set("layout", encoded.layout);
      if (encoded.focus) params.set("focus", encoded.focus);
      else params.delete("focus");
    } else if (value === (defaults[key] ?? rule.fallback)) params.delete(rule.param);
    else params.set(rule.param, value);
  }
  // Decode grammar punctuation only inside a generated layout value. Other
  // query values retain URLSearchParams escaping, including ampersands/hashes.
  return `?${params
    .toString()
    .replace(/%7E/g, "~")
    .replace(
      /(^|&)layout=([^&]*)/,
      (_match, prefix: string, layout: string) =>
        `${prefix}layout=${layout.replace(/%28/g, "(").replace(/%29/g, ")").replace(/%2C/g, ",").replace(/%3A/g, ":")}`,
    )}`;
}

export function replaceSharedUrl(search: string): void {
  if (typeof window === "undefined" || search === window.location.search) return;
  try {
    window.history.replaceState(null, "", `${window.location.pathname}${search}${window.location.hash}`);
  } catch {
    // File URLs or restricted history can still use local preferences.
  }
}

const SESSION_KEY_PREFIX = "formalization-viewer-session-v1";

export function sessionKey(mount: string): string {
  const scope = String(mount || "").trim();
  return scope ? `${SESSION_KEY_PREFIX}:${scope}` : SESSION_KEY_PREFIX;
}

function cleanString(value: unknown): string | null {
  return typeof value === "string" && value ? value : null;
}

// Keep only the known fields with the expected types: the stored JSON is from an
// older viewer as often as not, and a stale or hand-edited value must degrade to
// "no stored session" rather than propagate into navigation.
function sanitize(value: unknown): ViewerSession {
  const raw = (value && typeof value === "object" ? value : {}) as Record<string, unknown>;
  const progress = typeof raw.skipProgress === "number" && Number.isFinite(raw.skipProgress) ? raw.skipProgress : null;
  return {
    marker: cleanString(raw.marker),
    skip: cleanString(raw.skip),
    skipProgress: progress,
    md: cleanString(raw.md),
    lean: cleanString(raw.lean),
  };
}

// localStorage throws rather than returning null when it is disabled (private
// windows, blocked third-party storage), so every access is guarded: a viewer
// that cannot persist still has to run.
export function readSession(storage: StorageLike | null, key: string): ViewerSession {
  let stored: string | null = null;
  try {
    stored = storage?.getItem(key) ?? null;
  } catch (_error) {
    return sanitize(null);
  }
  if (!stored) return sanitize(null);
  try {
    return sanitize(JSON.parse(stored));
  } catch (_error) {
    return sanitize(null);
  }
}

// Merge `patch` into the stored session and persist it. Returns the merged
// session so a caller can keep using it without re-reading. An explicit null in
// the patch clears that field (how a marker position clears a skip position);
// an absent field is left as stored.
export function writeSession(storage: StorageLike | null, key: string, patch: ViewerSession): ViewerSession {
  const merged = sanitize({ ...readSession(storage, key), ...patch });
  try {
    storage?.setItem(key, JSON.stringify(merged));
  } catch (_error) {
    // Storage unavailable or full: the session simply does not persist.
  }
  return merged;
}

// Obtaining the browser storage handle can itself throw before getItem runs.
export function browserStorage(): StorageLike | null {
  try {
    return globalThis.localStorage;
  } catch {
    return null;
  }
}
export function readPreference(key: string): string | null {
  if (SHARED_PREFERENCES[key]) {
    return (
      (typeof window !== "undefined" ? sharedPreference(window.location.search, key) : null) ??
      SHARED_PREFERENCES[key].fallback
    );
  }
  try {
    return browserStorage()?.getItem(key) ?? null;
  } catch {
    return null;
  }
}
export function writePreference(key: string, value: string, defaultValue?: string): void {
  if (SHARED_PREFERENCES[key]) {
    if (typeof window !== "undefined")
      replaceSharedUrl(
        withSharedPreferences(window.location.search, { [key]: value }, defaultValue ? { [key]: defaultValue } : {}),
      );
    try {
      browserStorage()?.removeItem?.(key);
    } catch {
      /* Storage can be disabled. */
    }
    return;
  }
  try {
    browserStorage()?.setItem(key, value);
  } catch {
    /* Reading remains available without persistence. */
  }
}

// Remove the old copies instead of allowing absent URL fields to resurrect
// previous choices. Keep reading positions, source files, and local appearance.
export function removeUrlManagedStorage(storage: StorageLike | null): void {
  try {
    for (const key of Object.keys(SHARED_PREFERENCES)) storage?.removeItem?.(key);
    const keys = Array.from({ length: storage?.length ?? 0 }, (_, index) => storage?.key?.(index)).filter(
      (key): key is string => !!key && (key === SESSION_KEY_PREFIX || key.startsWith(`${SESSION_KEY_PREFIX}:`)),
    );
    for (const key of keys) {
      try {
        const session = JSON.parse(storage?.getItem(key) || "null");
        if (session && typeof session === "object" && Object.hasOwn(session, "pdf")) {
          delete session.pdf;
          storage?.setItem(key, JSON.stringify(session));
        }
      } catch {
        /* Ignore damaged sessions; normal reading handles them. */
      }
    }
  } catch {
    /* Storage can be disabled. */
  }
}
