import { paneScrollTop, paneViewportHeight, scrollPane } from "./pane-scroll.js";
import { state } from "./state.js";
import { markerIndex, readLocationParams, type PdfScrollAnchor } from "./permalink.js";
import { suppressPaneSync, type SkipSyncLocation } from "./sync.js";
import { markerStyle } from "./source-render.js";
import {
  skipSyncLocation,
  type AnchorPoint,
  type FlowSegment,
  type LineBox,
  type PageLineCache,
} from "./skip-bands.js";

// The machinery the two PDF panes share. The primary book PDF (pdf.ts) and
// the translated peer PDF (parallel-pdf.ts) render different documents into
// different viewers, but converting a named destination to a page point,
// caching a page's text lines, drawing the entry/skip band overlays, and the
// scroll geometry that follows entries and skips are identical. Each pane
// keeps its own document, state and resolution policy and passes them in;
// only the identical kernels live here, so a fix lands in both panes at once.

export interface PanePageState {
  pageNumber: number;
  el: HTMLElement;
}

export interface PaneEntryBand {
  index: number;
  title: string;
  target: string | null;
  segments: FlowSegment[];
}

export interface PaneSkipBand {
  key: string;
  reason: string;
  segments: FlowSegment[];
}

export interface PaneTarget {
  pageNumber: number;
  fraction: number;
}

// Convert a pdf.js named destination to its page, a vertical *fraction* of
// the page (0 = top, 1 = bottom), and the anchor's horizontal x as a fraction
// of the cropped text column (0 = crop left edge, 1 = crop right edge),
// matching how the overlay divs are positioned (the canvas fills the crop
// width). Fractions are scale-independent, so a band resolved from them
// renders correctly at any pane width — unlike a CSS-pixel y, which goes
// stale the moment the page is re-sized after resolution. The destination's
// `left` is a PDF-point x in the same space as the crop bounds, so it
// converts directly; it bounds highlights that start or end mid-line. For an
// uncropped document, `fallbackWidth` gives the width an x is measured
// against (the page's own width for the primary pane, the peer document's
// base page width for the parallel pane).
export async function destinationToPoint(
  doc: any,
  destination: any,
  crop: { x0: number; x1: number } | null,
  fallbackWidth: (pageWidth: number) => number,
  current: () => boolean,
): Promise<AnchorPoint | null> {
  if (!destination) return null;
  const [pageRef, _mode, left, top] = destination as any[];
  const pageIndex = await doc.getPageIndex(pageRef);
  if (!current()) return null;
  const page = await doc.getPage(pageIndex + 1);
  if (!current()) return null;
  const vp = page.getViewport({ scale: 1 });
  const frac = typeof top === "number" ? vp.convertToViewportPoint(0, top)[1] / vp.height : 0;
  const cropX0 = crop ? crop.x0 : 0;
  const cropWidth = crop ? crop.x1 - crop.x0 : fallbackWidth(vp.width);
  const rawX = typeof left === "number" ? (left - cropX0) / cropWidth : 0;
  const xFrac = Math.min(1, Math.max(0, rawX));
  return { pageNumber: pageIndex + 1, frac, xFrac };
}

// A per-page text-line cache: many skip/entry bands share a page, so its
// text content is fetched and line-grouped once. The caller binds the cache
// to its render token (through `compute`), so a stale resolution can't
// poison a fresh one.
export function makePageLineCache(compute: (pageNumber: number) => Promise<LineBox[]>): PageLineCache {
  const lineCache = new Map<number, Promise<LineBox[]>>();
  return (pageNumber: number): Promise<LineBox[]> => {
    let lines = lineCache.get(pageNumber);
    if (!lines) {
      lines = compute(pageNumber);
      lineCache.set(pageNumber, lines);
    }
    return lines;
  };
}

// Rasterize visible pages plus roughly one page on either side. Small panes
// can show many pages per viewport; prepainting several viewports is costly. Page rendering itself stays with the owning pane (its
// failure-counting and width policies differ).
export function renderVisiblePages(
  viewer: HTMLElement,
  pageStates: ReadonlyMap<number, PanePageState>,
  renderPage: (pageNumber: number) => void,
): void {
  const scrollTop = paneScrollTop(viewer);
  const height = paneViewportHeight(viewer);
  const first = pageStates.values().next().value;
  const overscan = Math.min(height, first?.el.offsetHeight || height);
  const top = scrollTop - overscan;
  const bottom = scrollTop + height + overscan;
  const visible: number[] = [];
  for (const pageState of pageStates.values()) {
    const pageTop = pageState.el.offsetTop;
    const pageBottom = pageTop + pageState.el.offsetHeight;
    if (pageBottom >= top && pageTop <= bottom) visible.push(pageState.pageNumber);
  }
  // Finish measuring before starting any render that may modify the DOM.
  for (const pageNumber of visible) renderPage(pageNumber);
}

// (Re)draw the per-entry booklink overlays as absolutely-positioned children
// of their page elements, colored by the entry's hue (the same --mark-rgb
// the source-pane marks use). Unlike the skip bands these take the pointer,
// so the app can wire click (navigate) and hover (cross-pane highlight) on
// them; data-entry carries the entries index so setHoveredEntry /
// applyActiveState reach them.
export function renderEntryBandOverlays(
  viewer: HTMLElement,
  pageStates: ReadonlyMap<number, PanePageState>,
  bands: readonly PaneEntryBand[],
): void {
  for (const stale of Array.from(viewer.querySelectorAll(".pdf-mark"))) stale.remove();
  const active = state.activeIndex;
  const hovered = state.hoveredEntry != null ? Number(state.hoveredEntry) : null;
  for (const band of bands) {
    for (const segment of band.segments) {
      const pageState = pageStates.get(segment.pageNumber);
      if (!pageState) continue;
      const bottomFrac = segment.bottom ?? 1;
      if (bottomFrac <= segment.top) continue;
      const el = document.createElement("div");
      el.className = "pdf-mark";
      if (band.index === active) el.classList.add("active");
      if (band.index === hovered) el.classList.add("is-hover");
      el.dataset.entry = String(band.index);
      const leftPct = (segment.left * 100).toFixed(3);
      const rightPct = ((1 - segment.right) * 100).toFixed(3);
      const topPct = (segment.top * 100).toFixed(3);
      const heightPct = ((bottomFrac - segment.top) * 100).toFixed(3);
      el.setAttribute(
        "style",
        `left:${leftPct}%;right:${rightPct}%;top:${topPct}%;height:${heightPct}%;${markerStyle(band.target)}`,
      );
      if (band.title) el.title = band.title;
      pageState.el.append(el);
    }
  }
}

// (Re)draw the skip-band overlays as absolutely-positioned children of their
// page elements. Segment top/bottom are page-height fractions, applied as
// percentages of the page element, so the bands track the page's height
// through later changes (a placeholder replaced by the rendered canvas, a
// lazy re-render adopting a new width, a resize) without any re-placement
// pass. Pointer-events are off so the bands never block PDF scrolling; the
// reason is mirrored in the Markdown pane's tooltip.
export function renderSkipBandOverlays(
  viewer: HTMLElement,
  pageStates: ReadonlyMap<number, PanePageState>,
  bands: readonly PaneSkipBand[],
): void {
  for (const stale of Array.from(viewer.querySelectorAll(".pdf-skip-band"))) stale.remove();
  const hovered = state.hoveredSkip;
  for (const band of bands) {
    for (const segment of band.segments) {
      const pageState = pageStates.get(segment.pageNumber);
      if (!pageState) continue;
      const bottomFrac = segment.bottom ?? 1;
      if (bottomFrac <= segment.top) continue;
      const el = document.createElement("div");
      el.className = "pdf-skip-band";
      // The skip's stable key, shared with the Markdown pane's .skip-mark
      // spans, so hovering one band lights every fragment of that skip
      // across panes.
      if (band.key) el.dataset.skipKey = band.key;
      if (band.key && band.key === hovered) el.classList.add("is-hover");
      el.style.left = `${(segment.left * 100).toFixed(3)}%`;
      el.style.right = `${((1 - segment.right) * 100).toFixed(3)}%`;
      el.style.top = `${(segment.top * 100).toFixed(3)}%`;
      el.style.height = `${((bottomFrac - segment.top) * 100).toFixed(3)}%`;
      if (band.reason) el.title = band.reason;
      pageState.el.append(el);
    }
  }
}

// Record the reader's current position as the topmost visible page plus a
// fractional offset into it, rather than a raw scrollTop. A rebuilt PDF may
// have a slightly different page count or crop, so a page-anchored fraction
// restores the same content even when absolute pixel offsets shift. When
// the URL names a marker, the offset from that marker's target is kept too,
// so a restore can re-anchor on the (possibly moved) target.
export function captureScrollAnchor(
  viewer: HTMLElement,
  pageStates: ReadonlyMap<number, PanePageState>,
  targets: ReadonlyMap<number, PaneTarget>,
): PdfScrollAnchor | null {
  const viewerTop = paneScrollTop(viewer);
  for (const pageState of pageStates.values()) {
    const top = pageState.el.offsetTop;
    const height = pageState.el.offsetHeight;
    if (height > 0 && viewerTop < top + height) {
      const anchor: PdfScrollAnchor = { pageNumber: pageState.pageNumber, fraction: (viewerTop - top) / height };
      const marker = readLocationParams(window.location.search).marker;
      const index = marker ? markerIndex(state.entries, marker) : null;
      const target = index !== null ? targets.get(index) : null;
      if (marker && target) {
        const offset = anchor.pageNumber + anchor.fraction - target.pageNumber - target.fraction;
        if (Math.abs(offset) <= 3) {
          anchor.marker = marker;
          anchor.markerOffset = offset;
        }
      }
      return anchor;
    }
  }
  return null;
}

// Restore a captured anchor (see captureScrollAnchor), re-anchoring on the
// URL marker's target when one was recorded. `pageCount` is the owning
// pane's current page count, used to clamp the restored page; `after` runs
// only when a page was actually scrolled to.
export function restoreScrollAnchor(
  anchor: PdfScrollAnchor,
  viewer: HTMLElement,
  pageStates: ReadonlyMap<number, PanePageState>,
  targets: ReadonlyMap<number, PaneTarget>,
  pageCount: number,
  pane: string,
  renderVisible: () => void,
  after?: () => void,
): void {
  let position = anchor.pageNumber + anchor.fraction;
  const index = anchor.marker ? markerIndex(state.entries, anchor.marker) : null;
  const target = index !== null ? targets.get(index) : null;
  if (target && Number.isFinite(anchor.markerOffset))
    position = target.pageNumber + target.fraction + anchor.markerOffset!;
  const firstPage = pageStates.keys().next().value ?? 1;
  position = Math.max(firstPage, position);
  const pageNumber = Math.min(Math.max(firstPage, Math.floor(position)), pageCount);
  const pageState = pageStates.get(pageNumber);
  if (!pageState) return;
  const top = pageState.el.offsetTop + (position - pageNumber) * pageState.el.offsetHeight;
  suppressPaneSync(pane);
  scrollPane(viewer, { top: Math.max(0, top), left: viewer.scrollLeft, behavior: "auto" });
  renderVisible();
  after?.();
}

// Scroll so an entry target sits on the reading line (35% down the
// viewport). `onScroll` observes the computed scroll top just before the
// scroll happens (the parallel pane logs it in debug mode). Returns false
// when the target's page is not laid out.
export function scrollToEntryTarget(
  viewer: HTMLElement,
  pageStates: ReadonlyMap<number, PanePageState>,
  target: PaneTarget,
  renderVisible: () => void,
  onScroll?: (top: number) => void,
): boolean {
  const pageState = pageStates.get(target.pageNumber);
  if (!pageState) return false;
  const top = Math.max(
    0,
    pageState.el.offsetTop + target.fraction * pageState.el.offsetHeight - paneViewportHeight(viewer) * 0.35,
  );
  onScroll?.(top);
  scrollPane(viewer, { top, left: viewer.scrollLeft, behavior: "auto" });
  renderVisible();
  return true;
}

// The entry whose target lies closest to the reading line, or null when no
// target sits on a laid-out page.
export function nearestEntryIndex(
  viewer: HTMLElement,
  pageStates: ReadonlyMap<number, PanePageState>,
  targets: ReadonlyMap<number, PaneTarget>,
): number | null {
  const targetTop = paneScrollTop(viewer) + paneViewportHeight(viewer) * 0.35;
  let best: number | null = null;
  let bestDistance = Infinity;
  for (const [index, target] of targets) {
    const pageState = pageStates.get(target.pageNumber);
    if (!pageState) continue;
    const absoluteTop = pageState.el.offsetTop + target.fraction * pageState.el.offsetHeight;
    const distance = Math.abs(absoluteTop - targetTop);
    if (distance < bestDistance) {
      bestDistance = distance;
      best = index;
    }
  }
  return best;
}

// The absolute scroll offset of a page point, or null when its page is not
// laid out.
export function pagePointTop(pageStates: ReadonlyMap<number, PanePageState>, point: PaneTarget): number | null {
  const pageState = pageStates.get(point.pageNumber);
  return pageState ? pageState.el.offsetTop + point.fraction * pageState.el.offsetHeight : null;
}

// The skip-sync location nearest the reading line. Each pane resolves a
// skip's pixel range its own way (the primary pane from its band segments,
// the peer pane from its stored skip targets) and passes it as `rangeFor`.
export function nearestSkipLocation(
  viewer: HTMLElement,
  pageStates: ReadonlyMap<number, PanePageState>,
  targets: ReadonlyMap<number, PaneTarget>,
  keys: Iterable<string>,
  rangeFor: (key: string) => { start: number; end: number } | null,
): SkipSyncLocation | null {
  const targetTop = paneScrollTop(viewer) + paneViewportHeight(viewer) * 0.35;
  const ranges: Array<{ key: string; start: number; end: number }> = [];
  for (const key of keys) {
    const range = rangeFor(key);
    if (range) ranges.push({ key, ...range });
  }
  let firstEntryTop = Infinity;
  for (const target of targets.values()) {
    const top = pagePointTop(pageStates, target);
    if (top !== null) firstEntryTop = Math.min(firstEntryTop, top);
  }
  return skipSyncLocation(targetTop, firstEntryTop, ranges);
}

// Scroll to a progress point inside a skip's pixel range, placing it on the
// reading line like an entry jump.
export function scrollToSkipRange(
  viewer: HTMLElement,
  range: { start: number; end: number },
  progress: number,
  renderVisible: () => void,
): void {
  const clamped = Math.min(1, Math.max(0, progress));
  const target = range.start + clamped * (range.end - range.start);
  const top = Math.max(0, target - paneViewportHeight(viewer) * 0.35);
  scrollPane(viewer, { top, left: viewer.scrollLeft, behavior: "auto" });
  renderVisible();
}
