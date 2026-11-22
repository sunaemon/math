// Shareable identity for a reading position: the marker (or formalization skip)
// the viewer is showing, encoded into the address bar so a copied URL reopens
// the same place. Pure string/array logic with no DOM access, so it unit tests
// directly with `node --test` (permalink.test.ts).
//
// The entry index that the panes use internally is deliberately NOT what the URL
// carries: it shifts whenever a booklink is added anywhere earlier in the book,
// so an index link rots at the next build. The Lean declaration name is stable
// across rebuilds, but it is not unique — a theorem's statement marker and its
// proof marker share one declaration — so a name that occurs more than once is
// qualified with its 1-based ordinal among its namesakes, `declName~2`.

// The fields of a sourcemap entry this module reads. Kept structural so the
// module stays independent of the viewer's state/sync types (which touch the
// DOM at import time and so cannot be loaded by a node test).
export interface MarkerEntry {
  lean?: { declName?: string };
}

export interface SkipSyncLocation {
  key: string;
  progress: number;
}

export type NavigationLocation = { kind: "entry"; index: number } | ({ kind: "skip" } & SkipSyncLocation);

export const MARKER_PARAM = "marker";
export const SKIP_PARAM = "skip";

// Entries whose sourcemap records no declaration name fall back to a positional
// id. It rots like a raw index would, but only for that one entry, and the `@`
// keeps it visibly distinct from a real name.
const POSITIONAL_PREFIX = "@";

function baseId(entry: MarkerEntry | undefined): string {
  return String(entry?.lean?.declName || "").trim();
}

// The URL id of the entry at `index`: its declaration name, qualified with a
// 1-based ordinal when several entries share that name.
export function markerId(entries: MarkerEntry[], index: number): string {
  const entry = entries[index];
  if (!entry) return "";
  const base = baseId(entry);
  if (!base) return `${POSITIONAL_PREFIX}${index}`;
  let ordinal = 0;
  let total = 0;
  for (let i = 0; i < entries.length; i += 1) {
    if (baseId(entries[i]) !== base) continue;
    total += 1;
    if (i === index) ordinal = total;
  }
  return total > 1 ? `${base}~${ordinal}` : base;
}

// Batch IDs for machine-readable marker inventories without quadratic scans.
export function markerIds(entries: MarkerEntry[]): string[] {
  const counts = new Map<string, number>(),
    ordinals = new Map<string, number>();
  for (const entry of entries) {
    const id = baseId(entry);
    counts.set(id, (counts.get(id) ?? 0) + 1);
  }
  return entries.map((entry, index) => {
    const id = baseId(entry);
    if (!id) return `${POSITIONAL_PREFIX}${index}`;
    const ordinal = (ordinals.get(id) ?? 0) + 1;
    ordinals.set(id, ordinal);
    return counts.get(id)! > 1 ? `${id}~${ordinal}` : id;
  });
}

// Resolve a URL id back to an entry index, or null when the book no longer has
// it. An ordinal past the end of a still-present name (markers removed from a
// declaration since the link was made) resolves to that name's first entry
// rather than failing: the declaration is what the reader asked for.
export function markerIndex(entries: MarkerEntry[], id: string): number | null {
  const wanted = String(id || "").trim();
  if (!wanted) return null;
  if (wanted.startsWith(POSITIONAL_PREFIX)) {
    const index = Number(wanted.slice(POSITIONAL_PREFIX.length));
    return Number.isInteger(index) && entries[index] ? index : null;
  }
  const qualified = wanted.match(/^(.*)~(\d+)$/);
  const base = qualified ? qualified[1] : wanted;
  const ordinal = qualified ? Number(qualified[2]) : 1;
  const matches: number[] = [];
  for (let i = 0; i < entries.length; i += 1) {
    if (baseId(entries[i]) === base) matches.push(i);
  }
  if (!matches.length) return null;
  return matches[ordinal - 1] ?? matches[0];
}

export interface LocationParams {
  marker: string | null;
  skip: string | null;
}

export interface PdfScrollAnchor {
  pageNumber: number;
  fraction: number;
  marker?: string;
  markerOffset?: number;
}

export function readLocationParams(search: string): LocationParams {
  const params = new URLSearchParams(search);
  return { marker: params.get(MARKER_PARAM), skip: params.get(SKIP_PARAM) };
}

// The query string with the position rewritten: at most one of the two params
// is present, every other param (?pdf=, ?map=, ?debug) is preserved untouched.
// Returns a string comparable with window.location.search, so the caller can
// skip a history write when nothing moved.
export function withLocationParams(search: string, location: LocationParams): string {
  const params = new URLSearchParams(search);
  params.delete(MARKER_PARAM);
  params.delete(SKIP_PARAM);
  if (location.marker) params.set(MARKER_PARAM, location.marker);
  else if (location.skip) params.set(SKIP_PARAM, location.skip);
  // form-urlencoding escapes `~`, which is unreserved in a query and is the
  // ordinal separator readers see most; put it back so links stay legible.
  const query = params.toString().replace(/%7E/g, "~");
  return query ? `?${query}` : "";
}
