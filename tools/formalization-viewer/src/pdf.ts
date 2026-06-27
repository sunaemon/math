// The PDF pane: loads the book PDF with pdf.js, lazily rasterizes visible
// pages (cropped to the text column and zoomed to the pane), resolves each
// booklink's page/offset target, and scrolls to entries. Depends one-way on
// state/util and on sync for the visible-pane set; it never imports app. The
// one thing app must react to — targets resolved, so the PDF overview rail can
// be redrawn — is delivered through an injected callback.

import { state, els, project } from "./state.js";
import { escapeHtml, repoUrl, reportError } from "./util.js";
import { visiblePaneNames } from "./sync.js";
import { markerStyle } from "./source-render.js";
import {
  type LineBox,
  type TextRun,
  type FlowSegment,
  groupTextLines,
  SNAP_TOL,
  snapBandTop,
  snapBandBottom,
  skipBandSegments,
  lineIndexAt,
  lineIndexBelow,
  mainLineBelow,
  endLineResolve,
  endLineBottom,
  flowBandSegments,
} from "./skip-bands.js";

const PDFJS_MODULE_URL = new URL("../vendor/pdfjs/pdf.mjs", import.meta.url).toString();
const PDFJS_WORKER_URL = new URL("../vendor/pdfjs/pdf.worker.mjs", import.meta.url).toString();

// Invoked after resolvePdfTargets places the entry targets; app wires this to
// refresh the PDF overview rail (which reads those targets).
let onPdfTargetsResolved: () => void = () => {};
export function setOnPdfTargetsResolved(fn: () => void): void {
  onPdfTargetsResolved = fn;
}

// Invoked with the selected PDF's URL whenever it changes; app wires this to
// report the selection to the server so the auto-build tracks the viewed PDF.
let onPdfSelected: (path: string) => void = () => {};
export function setOnPdfSelected(fn: (path: string) => void): void {
  onPdfSelected = fn;
}

// Invoked when a PDF fails to load (e.g. a freshly selected chapter preview that
// the server has not rendered yet — a 404). Returning a string replaces the raw
// error in the pane with that message (the app shows build progress instead);
// returning null keeps the default error.
let onPdfLoadFailed: (path: string, error: unknown) => string | null = () => null;
export function setOnPdfLoadFailed(fn: (path: string, error: unknown) => string | null): void {
  onPdfLoadFailed = fn;
}

export function refreshPdfLayoutGeometry(): void {
  if (!state.pdf.document) return;
  window.requestAnimationFrame(() => {
    renderVisiblePdfPages();
    resolvePdfTargets(state.pdf.renderToken);
  });
  schedulePdfRepaint();
}

// Keep the absolutely-positioned band overlays aligned with the page canvases
// whenever the PDF pane's rendered size changes for *any* reason — not just the
// window-resize and splitter-drag paths that call refreshPdfLayoutGeometry, but
// also the layout settling after a (re)load, a scrollbar appearing, or fonts
// loading. The band fractions are resolution-independent, so this is a cheap
// reposition against the pages' current heights (no re-resolve, no rasterize). It
// makes a band first drawn against not-yet-final geometry self-correct, instead
// of staying shifted until a manual reload. Installed once; the observer lives
// for the page's lifetime.
let bandGeometryObserver: ResizeObserver | null = null;
let bandRedrawQueued = false;
export function observePdfBandGeometry(): void {
  if (bandGeometryObserver || typeof ResizeObserver === "undefined") return;
  bandGeometryObserver = new ResizeObserver(() => {
    if (bandRedrawQueued || !state.pdf.document) return;
    bandRedrawQueued = true;
    window.requestAnimationFrame(() => {
      bandRedrawQueued = false;
      if (!state.pdf.document) return;
      renderSkipBands();
      renderEntryBands();
    });
  });
  bandGeometryObserver.observe(els.pdfViewer);
}

// After the pane width settles, re-rasterize visible pages at the new width so
// the CSS-scaled canvases become crisp again (the canvas always fills 100%).
export function schedulePdfRepaint(): void {
  if (!state.pdf.document) return;
  if (state.pdf.repaintTimer) window.clearTimeout(state.pdf.repaintTimer);
  state.pdf.repaintTimer = window.setTimeout(() => {
    state.pdf.repaintTimer = null;
    if (!state.pdf.document) return;
    for (const pageState of state.pdf.pageStates.values()) {
      if (!pageState.rendering) pageState.rendered = false;
    }
    renderVisiblePdfPages();
    // Page heights changed with the pane width; re-place the skip and entry bands
    // against the new heights (their stored fractions don't need re-resolving).
    renderSkipBands();
    renderEntryBands();
  }, 160);
}

export function pdfRank(path: string): number {
  return path.toLowerCase().includes("debug") ? 0 : 1;
}

export function pdfLabel(path: string): string {
  return path.split("/").pop() || path;
}

export function pdfChoices(
  params: URLSearchParams,
  defaults: { pdf: string; map?: string },
): { choices: any[]; initialPath: string } {
  // ?pdf= deep links select a specific render.
  const override = params.get("pdf") || "";
  // The server (live and static dist) injects "pdfs": every PDF that actually
  // exists under the mount, so the dropdown never offers a 404. Per-chapter
  // preview artifacts are dropped here; the app adds one dynamic "Chapter
  // preview" entry that follows the viewed chapter. Fall back to the debug PDF
  // for an older manifest without the list. Labels stay raw file names, matching
  // the Markdown/Lean source-pane selectors.
  const served = (Array.isArray(project.pdfs) ? project.pdfs : []).filter((rel) => !rel.includes("-preview"));
  if (served.length) {
    const choices = served
      .map((rel) => ({ key: rel, label: pdfLabel(rel), path: repoUrl(rel) }))
      .sort((a, b) => pdfRank(a.path) - pdfRank(b.path) || a.label.localeCompare(b.label));
    // A deep link may point outside the served set; keep it selectable.
    if (override && !choices.some((choice) => choice.path === override)) {
      choices.unshift({ key: "custom", label: pdfLabel(override), path: override });
    }
    const preferred =
      defaults.pdf && choices.some((choice) => choice.path === defaults.pdf) ? defaults.pdf : choices[0].path;
    return { choices, initialPath: override || preferred };
  }

  const primaryPath = override || defaults.pdf;
  const choices = [{ key: "debug", label: pdfLabel(defaults.pdf), path: defaults.pdf }];
  if (!choices.some((choice) => choice.path === primaryPath)) {
    choices.unshift({ key: "custom", label: pdfLabel(primaryPath), path: primaryPath });
  }
  return { choices, initialPath: primaryPath };
}

export function cacheBustedUrl(path: string): string {
  const url = new URL(path, window.location.href);
  const refresh = new URLSearchParams(window.location.search).get("refresh") || String(Date.now());
  url.searchParams.set("viewer-cache", refresh);
  return url.pathname + url.search + url.hash;
}

export async function loadPdfJs(): Promise<any> {
  if (state.pdfjs) return state.pdfjs;
  const pdfjs = await import(PDFJS_MODULE_URL);
  pdfjs.GlobalWorkerOptions.workerSrc = PDFJS_WORKER_URL;
  state.pdfjs = pdfjs;
  return pdfjs;
}

export function clearPdfViewer(message: string = "Loading PDF..."): void {
  if (state.pdf.loadingTask) {
    state.pdf.loadingTask.destroy();
    state.pdf.loadingTask = null;
  }
  state.pdf.document = null;
  state.pdf.currentPage = null;
  state.pdf.pageCount = null;
  state.pdf.pageStates = new Map();
  state.pdf.targets = new Map();
  state.pdf.skipBands = [];
  state.pdf.entryBands = [];
  state.pdf.targetPromise = null;
  state.pdf.crop = null;
  els.pdfViewer.innerHTML = `<div class="pdf-message">${escapeHtml(message)}</div>`;
}

export function updatePdfStatus(): void {
  if (!els.status) return;
  const entry = state.entries[state.activeIndex];
  const mdLine = entry?.match?.startLine || "?";
  const texLine = entry?.texMatch?.startLine || "?";
  const declName = entry?.lean?.declName || "entry";
  const pdfPart =
    state.pdf.currentPage && state.pdf.pageCount ? ` · PDF ${state.pdf.currentPage}/${state.pdf.pageCount}` : "";
  els.status.textContent = `${declName} · MD ${mdLine} · TeX ${texLine}${pdfPart}`;
}

// The book PDF is A5 with wide print margins; in this side-by-side view the
// left/right whitespace is wasted. We crop to the text column and zoom it to the
// pane width, keeping the full page height (only the side margins are redundant).
//
// The crop is a single document-wide horizontal band approximating the LaTeX
// text block (\textwidth + its margins), not a per-page text bbox: a per-page
// box over-zooms sparse pages (e.g. a short final index column would balloon).
// We estimate the band by sampling body pages and taking the union of their text
// extents, which lands on the geometry the preamble sets.
export async function computeDocCrop(
  doc: any,
  pageWidth: number,
  token: number,
): Promise<{ x0: number; x1: number } | null> {
  const total = doc.numPages;
  const step = Math.max(1, Math.floor(total / Math.min(total, 24)));
  let minX = Infinity;
  let maxX = -Infinity;
  for (let pageNumber = 1; pageNumber <= total; pageNumber += step) {
    if (token !== state.pdf.renderToken) return null;
    try {
      const page = await doc.getPage(pageNumber);
      const content = await page.getTextContent();
      let count = 0;
      let pMin = Infinity;
      let pMax = -Infinity;
      for (const item of content.items as any[]) {
        if (!item.str || !item.str.trim()) continue;
        count += 1;
        const x = item.transform[4];
        const width = typeof item.width === "number" ? item.width : 0;
        if (x < pMin) pMin = x;
        if (x + width > pMax) pMax = x + width;
      }
      // Only full body pages define the text block; skip near-empty pages so a
      // sparse index/title page can't shrink the band.
      if (count >= 30 && pMax > pMin) {
        if (pMin < minX) minX = pMin;
        if (pMax > maxX) maxX = pMax;
      }
    } catch {
      // Ignore a page that fails to yield text; others still inform the band.
    }
  }
  if (minX === Infinity || maxX <= minX) return null;
  const pad = 6;
  const x0 = Math.max(0, minX - pad);
  const x1 = Math.min(pageWidth, maxX + pad);
  const width = x1 - x0;
  // Crop only if it meaningfully narrows the page but isn't suspiciously tight.
  return width < pageWidth - 8 && width > pageWidth * 0.4 ? { x0, x1 } : null;
}

export async function renderPdfPage(pageNumber: number, token: number): Promise<void> {
  const pageState = state.pdf.pageStates.get(pageNumber);
  if (!pageState || pageState.rendered || pageState.rendering || token !== state.pdf.renderToken) return;
  pageState.rendering = true;
  try {
    const page = await state.pdf.document.getPage(pageNumber);
    if (token !== state.pdf.renderToken) return;
    const crop = state.pdf.crop;

    const canvas = pageState.canvas;
    const dpr = window.devicePixelRatio || 1;
    const baseViewport = page.getViewport({ scale: 1 });
    // Zoom so the cropped text column fills the pane width; only the side margins
    // are removed, so the page keeps its full height.
    const cropX0 = crop ? crop.x0 : 0;
    const cropWidth = crop ? crop.x1 - crop.x0 : baseViewport.width;
    const cssWidth = Math.max(240, pageState.el.clientWidth);
    const scale = (cssWidth / cropWidth) * dpr;
    // offsetX shifts the page so the crop's left edge lands at the canvas origin;
    // the narrower canvas then clips away both side margins.
    const viewport = page.getViewport({ scale, offsetX: -cropX0 * scale });
    const fullHeight = baseViewport.height * scale;
    canvas.hidden = false;
    canvas.width = Math.floor(cropWidth * scale);
    canvas.height = Math.floor(fullHeight);
    canvas.style.width = "100%";
    canvas.style.height = "auto";
    pageState.el.style.aspectRatio = `${cropWidth * scale} / ${Math.floor(fullHeight)}`;

    const context = canvas.getContext("2d");
    if (!context) {
      throw new Error("Failed to obtain 2D context from canvas");
    }
    await page.render({ canvasContext: context, viewport }).promise;
    if (token !== state.pdf.renderToken) return;
    pageState.rendered = true;
  } catch (error) {
    console.error("[booklink] renderPdfPage failed", { pageNumber, error });
  } finally {
    pageState.rendering = false;
  }
}

export function renderVisiblePdfPages(): void {
  if (!state.pdf.document) return;
  const token = state.pdf.renderToken;
  const top = els.pdfViewer.scrollTop - els.pdfViewer.clientHeight * 2;
  const bottom = els.pdfViewer.scrollTop + els.pdfViewer.clientHeight * 3;
  for (const pageState of state.pdf.pageStates.values()) {
    const pageTop = pageState.el.offsetTop;
    const pageBottom = pageTop + pageState.el.offsetHeight;
    if (pageBottom >= top && pageTop <= bottom) {
      renderPdfPage(pageState.pageNumber, token);
    }
  }
}

export function updatePdfPageFromScroll(): void {
  const viewerRect = els.pdfViewer.getBoundingClientRect();
  const target = viewerRect.top + viewerRect.height * 0.35;
  let bestPage: number | null = null;
  let bestDistance = Infinity;
  for (const pageState of state.pdf.pageStates.values()) {
    const rect = pageState.el.getBoundingClientRect();
    const distance = Math.abs(rect.top - target);
    if (distance < bestDistance) {
      bestDistance = distance;
      bestPage = pageState.pageNumber;
    }
  }
  if (bestPage && bestPage !== state.pdf.currentPage) {
    state.pdf.currentPage = bestPage;
    updatePdfStatus();
  }
}

// Resolve a pdf.js named destination to a page number and a y in CSS pixels from
// the page's top, matching renderPdfPage's crop-scaled zoom so the y lands where
// the content actually renders. Null if the destination/page is unresolvable.
async function destinationToPageY(destination: any, token: number): Promise<{ pageNumber: number; y: number } | null> {
  if (!destination) return null;
  const [pageRef, _mode, _left, top] = destination as any[];
  const pageIndex = await state.pdf.document.getPageIndex(pageRef);
  if (token !== state.pdf.renderToken) return null;
  const pageNumber = pageIndex + 1;
  const pageState = state.pdf.pageStates.get(pageNumber);
  const page = await state.pdf.document.getPage(pageNumber);
  if (!pageState || token !== state.pdf.renderToken) return null;
  const crop = state.pdf.crop;
  const baseViewport = page.getViewport({ scale: 1 });
  const cropWidth = crop ? crop.x1 - crop.x0 : baseViewport.width;
  const cssWidth = Math.max(240, pageState.el.clientWidth);
  const viewport = page.getViewport({ scale: cssWidth / cropWidth });
  const y = typeof top === "number" ? viewport.convertToViewportPoint(0, top)[1] : 0;
  return { pageNumber, y };
}

export async function resolvePdfTargets(token: number, scrollToActive = true): Promise<void> {
  if (!state.pdf.document) return;
  const targets = new Map<number, { pageNumber: number; y: number }>();
  await Promise.all(
    state.entries.map(async (entry, index) => {
      // The PDF numbers booklinks globally (\BooklinkStart[entry=N] / the
      // booklink-entry-N named destination), which is not the per-book array
      // index. The sourcemap's texMatch.entry carries that PDF number, so map by
      // it rather than by position.
      const entryNumber = (entry as any)?.texMatch?.entry;
      if (typeof entryNumber !== "number") return;
      const destination = await state.pdf.document.getDestination(`booklink-entry-${entryNumber}`);
      if (token !== state.pdf.renderToken) return;
      const placement = await destinationToPageY(destination, token);
      if (placement) targets.set(index, placement);
    }),
  );
  if (token !== state.pdf.renderToken) return;
  state.pdf.targets = targets;
  // Skip and entry bands both snap their edges onto text lines, so share one
  // per-page text-content cache across both passes (many bands share a page).
  const pageLines = makePageLineCache(token);
  await Promise.all([resolveSkipBands(token, pageLines), resolveEntryBands(token, pageLines)]);
  if (token !== state.pdf.renderToken) return;
  // On a scroll-preserving reload the caller has already restored the reader's
  // position, so don't yank it back to the active entry.
  if (scrollToActive) scrollPdfToEntry(state.activeIndex);
  onPdfTargetsResolved();
}

// Convert a pdf.js named destination to its page and a vertical *fraction* of
// the page (0 = top, 1 = bottom). Fractions are scale-independent, so a band
// resolved from them renders correctly at any pane width — unlike a CSS-pixel y,
// which goes stale the moment the page is re-sized after resolution.
async function destinationToPageFraction(
  destination: any,
  token: number,
): Promise<{ pageNumber: number; frac: number } | null> {
  if (!destination) return null;
  const [pageRef, _mode, _left, top] = destination as any[];
  const pageIndex = await state.pdf.document.getPageIndex(pageRef);
  if (token !== state.pdf.renderToken) return null;
  const page = await state.pdf.document.getPage(pageIndex + 1);
  if (token !== state.pdf.renderToken) return null;
  const vp = page.getViewport({ scale: 1 });
  const frac = typeof top === "number" ? vp.convertToViewportPoint(0, top)[1] / vp.height : 0;
  return { pageNumber: pageIndex + 1, frac };
}

// Like destinationToPageFraction, but also carries the anchor's horizontal x as
// a fraction of the cropped text column (0 = crop left edge, 1 = crop right
// edge), matching how the overlay divs are positioned (the canvas fills the crop
// width). The destination's `left` is a PDF-point x in the same space as the crop
// bounds, so it converts directly. Used to flow a booklink highlight that starts
// or ends mid-line.
async function destinationToPagePoint(
  destination: any,
  token: number,
): Promise<{ pageNumber: number; frac: number; xFrac: number } | null> {
  if (!destination) return null;
  const [pageRef, _mode, left, top] = destination as any[];
  const pageIndex = await state.pdf.document.getPageIndex(pageRef);
  if (token !== state.pdf.renderToken) return null;
  const page = await state.pdf.document.getPage(pageIndex + 1);
  if (token !== state.pdf.renderToken) return null;
  const vp = page.getViewport({ scale: 1 });
  const frac = typeof top === "number" ? vp.convertToViewportPoint(0, top)[1] / vp.height : 0;
  const crop = state.pdf.crop;
  const cropX0 = crop ? crop.x0 : 0;
  const cropWidth = crop ? crop.x1 - crop.x0 : vp.width;
  const rawX = typeof left === "number" ? (left - cropX0) / cropWidth : 0;
  const xFrac = Math.min(1, Math.max(0, rawX));
  return { pageNumber: pageIndex + 1, frac, xFrac };
}

// The text lines of a page as boxes expressed as *fractions* of the page height,
// fetched from pdf.js and grouped by groupTextLines. Cached (as a promise) per
// page so the many skips that share a page fetch its text content once.
async function computePageLines(pageNumber: number, token: number): Promise<LineBox[]> {
  const page = await state.pdf.document.getPage(pageNumber);
  if (token !== state.pdf.renderToken) return [];
  const vp = page.getViewport({ scale: 1 });
  const content = await page.getTextContent();
  if (token !== state.pdf.renderToken) return [];
  const runs: TextRun[] = (content.items as any[])
    .filter((item) => item.str && item.str.trim())
    .map((item) => ({
      baseline: item.transform[5],
      height: typeof item.height === "number" ? item.height : 0,
      x: item.transform[4],
    }));
  const crop = state.pdf.crop;
  const cropX0 = crop ? crop.x0 : 0;
  const cropWidth = crop ? crop.x1 - crop.x0 : vp.width;
  return groupTextLines(
    runs,
    (y) => vp.convertToViewportPoint(0, y)[1] / vp.height,
    (x) => (x - cropX0) / cropWidth,
  );
}

// Resolve each `formalization: skip` region to a set of per-page vertical
// segments, using the skip-<key>-start / skip-<key>-end hypertargets the book
// filter bakes into the debug PDF. A region that crosses a page break becomes
// several segments (start page from y to its bottom, full intermediate pages,
// end page from its top to y). The raw hypertargets land on text baselines (and
// the start one a line high), so each segment edge is snapped onto the enclosing
// line box. Missing destinations (e.g. a non-debug PDF that carries no anchors)
// just yield no band. Then draw them.
// A per-page text-line cache: many skip/entry bands share a page, so its text
// content is fetched and line-grouped once. Bound to a render token so a stale
// resolution can't poison a fresh one.
type PageLineCache = (pageNumber: number) => Promise<LineBox[]>;
function makePageLineCache(token: number): PageLineCache {
  const lineCache = new Map<number, Promise<LineBox[]>>();
  return (pageNumber: number): Promise<LineBox[]> => {
    let p = lineCache.get(pageNumber);
    if (!p) {
      p = computePageLines(pageNumber, token);
      lineCache.set(pageNumber, p);
    }
    return p;
  };
}

async function resolveSkipBands(token: number, pageLines: PageLineCache): Promise<void> {
  const bands: typeof state.pdf.skipBands = [];
  await Promise.all(
    (state.skips || []).map(async (skip: any) => {
      const key = skip?.key;
      if (typeof key !== "string") return;
      const [startDest, endDest] = await Promise.all([
        state.pdf.document.getDestination(`skip-${key}-start`),
        state.pdf.document.getDestination(`skip-${key}-end`),
      ]);
      if (token !== state.pdf.renderToken) return;
      const start = await destinationToPageFraction(startDest, token);
      const end = await destinationToPageFraction(endDest, token);
      if (!start || !end || token !== state.pdf.renderToken) return;
      const [startLines, endLines] = await Promise.all([pageLines(start.pageNumber), pageLines(end.pageNumber)]);
      if (token !== state.pdf.renderToken) return;
      const snappedStart = { pageNumber: start.pageNumber, frac: snapBandTop(start.frac, startLines) };
      const snappedEnd = { pageNumber: end.pageNumber, frac: snapBandBottom(end.frac, endLines) };
      const segments = skipBandSegments(snappedStart, snappedEnd);
      if (segments.length) bands.push({ key, reason: typeof skip.reason === "string" ? skip.reason : "", segments });
    }),
  );
  if (token !== state.pdf.renderToken) return;
  state.pdf.skipBands = bands;
  renderSkipBands();
}

// (Re)draw the skip-band overlays as absolutely-positioned children of their
// page elements. Segment top/bottom are page-height fractions, converted to px
// against each page's *current* clientHeight here, so the bands stay aligned
// after a resize even without re-resolving. Pointer-events are off so the bands
// never block PDF scrolling; the reason is mirrored in the Markdown pane's
// tooltip.
export function renderSkipBands(): void {
  for (const stale of Array.from(els.pdfViewer.querySelectorAll(".pdf-skip-band"))) stale.remove();
  const hovered = state.hoveredSkip;
  for (const band of state.pdf.skipBands) {
    for (const segment of band.segments) {
      const pageState = state.pdf.pageStates.get(segment.pageNumber);
      if (!pageState) continue;
      const pageHeight = pageState.el.clientHeight;
      const topPx = segment.top * pageHeight;
      const bottomPx = (segment.bottom ?? 1) * pageHeight;
      const height = bottomPx - topPx;
      if (height <= 0) continue;
      const el = document.createElement("div");
      el.className = "pdf-skip-band";
      // The skip's stable key, shared with the Markdown pane's .skip-mark spans,
      // so hovering one band lights every fragment of that skip across panes.
      if (band.key) el.dataset.skipKey = band.key;
      if (band.key && band.key === hovered) el.classList.add("is-hover");
      el.style.top = `${topPx}px`;
      el.style.height = `${height}px`;
      if (band.reason) el.title = band.reason;
      pageState.el.append(el);
    }
  }
}

// Resolve each booklink entry's PDF extent to per-page vertical segments, the
// same way skip regions are resolved, but from the booklink-entry-N (start) /
// booklink-entry-N-end hypertargets the \BooklinkStart/\BooklinkEnd macros bake
// into the debug PDF. The result is one colored, interactive overlay per entry —
// the PDF counterpart of the source panes' .mark spans — keyed by the entry's
// state.entries index so it shares the hover/active wiring. Then draw them.
async function resolveEntryBands(token: number, pageLines: PageLineCache): Promise<void> {
  const bands: typeof state.pdf.entryBands = [];
  await Promise.all(
    state.entries.map(async (entry, index) => {
      const entryNumber = (entry as any)?.texMatch?.entry;
      if (typeof entryNumber !== "number") return;
      const [startDest, endDest] = await Promise.all([
        state.pdf.document.getDestination(`booklink-entry-${entryNumber}`),
        state.pdf.document.getDestination(`booklink-entry-${entryNumber}-end`),
      ]);
      if (token !== state.pdf.renderToken) return;
      const start = await destinationToPagePoint(startDest, token);
      const end = await destinationToPagePoint(endDest, token);
      if (!start || !end || token !== state.pdf.renderToken) return;
      const [startLines, endLines] = await Promise.all([pageLines(start.pageNumber), pageLines(end.pageNumber)]);
      if (token !== state.pdf.renderToken) return;
      // A \BooklinkStart injected right before its span's first glyph (a prose
      // proof, a mid-line start) has \leavevmode attach the booklink-entry-N
      // destination to that glyph's baseline: lineIndexAt lands on it exactly and
      // the first line begins at the anchor's own x. But a \BooklinkStart that sits
      // before a `\begin{env}` — every kind=statement span, and a proof span whose
      // excerpt opens with \begin{proof} — is separated from it by a blank line, so
      // \leavevmode strands a zero-glyph paragraph in the inter-paragraph gap and the
      // destination lands ~a baselineskip *above* the span's first rendered line (the
      // same vertical-mode raise the skip starts compensate for). lineIndexAt would
      // then resolve onto the *previous* block's last line (a skip band, the
      // preceding proof, or this span's own statement), overlapping it. Detect that
      // geometrically: a raised anchor sits in a gap, so the line lineIndexAt picked
      // has a baseline well *above* (smaller fraction than) the anchor. Then snap DOWN
      // to the first line below and begin the highlight at that line's left edge. The
      // end marker is always injected right after the last glyph, so it stays exact.
      let si = lineIndexAt(start.frac, startLines);
      const raisedStart = si >= 0 && startLines[si].baseline < start.frac - SNAP_TOL;
      // Snap down to the first line below the raised anchor, then past any
      // superscript sub-run of the real first line (a statement heading carrying a
      // superscript groups one just above its main line) so the band starts on the
      // heading itself, not the superscript — see mainLineBelow.
      if (raisedStart) si = mainLineBelow(lineIndexBelow(start.frac, startLines), startLines);
      const endRes = endLineResolve(end.frac, end.xFrac, endLines);
      const ei = endRes.index;
      let segments: FlowSegment[];
      if (si < 0 || ei < 0) {
        // No text line to snap onto (e.g. a figure-only page); fall back to a
        // full-width band between the raw snapped y positions.
        segments = skipBandSegments(
          { pageNumber: start.pageNumber, frac: snapBandTop(start.frac, startLines) },
          { pageNumber: end.pageNumber, frac: snapBandBottom(end.frac, endLines) },
        ).map((s) => ({ ...s, left: 0, right: 1 }));
      } else {
        const sLine = startLines[si];
        const eLine = endLines[ei];
        // The indented first line ([startX, 1]) runs down to where the full-width
        // middle begins: normally the next line's top, which fills the inter-line
        // gap seamlessly. But a sub-line whose box overlaps the start line (a
        // subscript like the ₁ in Δ⁰₁ sits a couple pt below the baseline) would put
        // that boundary *above* the start line's bottom, so the full-width middle
        // bleeds up and covers the left of the start line (text before the mid-line
        // start). Clamp the boundary to at least the start line's bottom.
        const nextStart = si + 1 < startLines.length ? Math.max(startLines[si + 1].top, sLine.bottom) : null;
        // Symmetrically, the last line's box can dip into the line below it (a
        // display equation whose descenders overlap the next paragraph with no blank
        // line between). Cap the band's bottom at that next line's top so it never
        // shades a line outside the span — but skip the end line's own subscript
        // sub-runs, which group into shorter LineBoxes just below it and would
        // otherwise chop the wash in half (see endLineBottom).
        const endBottom = endLineBottom(endLines, ei);
        segments = flowBandSegments(
          {
            startPage: start.pageNumber,
            startTop: sLine.top,
            startBottom: sLine.bottom,
            nextTop: nextStart,
            endPage: end.pageNumber,
            endTop: eLine.top,
            endBottom,
            // A raised start was snapped down to the env's first line, whose anchor x
            // is the stray paragraph's indent, not the content; cover from its left
            // edge. An exact (inline) start keeps the anchor's own x.
            startX: raisedStart ? sLine.left : start.xFrac,
            endX: endRes.right,
          },
          start.pageNumber === end.pageNumber && si === ei,
        );
      }
      if (segments.length)
        bands.push({
          index,
          title: entryBandTitle(entry),
          target: (entry as any)?.booklink?.target ?? null,
          segments,
        });
    }),
  );
  if (token !== state.pdf.renderToken) return;
  state.pdf.entryBands = bands;
  renderEntryBands();
}

// A native-tooltip label for a PDF entry overlay: the linked declaration plus
// which half it marks, matching the kind shown by the rail tick. Kept here (a
// plain string off the entry record) so pdf.ts stays independent of app.ts.
function entryBandTitle(entry: any): string {
  const name = entry?.lean?.declName || "entry";
  const target = entry?.booklink?.target;
  return target ? `${name} · ${target}` : name;
}

// (Re)draw the per-entry booklink overlays as absolutely-positioned children of
// their page elements, colored by the entry's hue (the same --mark-rgb the
// source-pane marks use). Unlike the skip bands these take the pointer, so app.ts
// can wire click (navigate) and hover (cross-pane highlight) on them; data-entry
// carries the state.entries index so setHoveredEntry/applyActiveState reach them.
export function renderEntryBands(): void {
  for (const stale of Array.from(els.pdfViewer.querySelectorAll(".pdf-mark"))) stale.remove();
  const active = state.activeIndex;
  const hovered = state.hoveredEntry != null ? Number(state.hoveredEntry) : null;
  for (const band of state.pdf.entryBands) {
    for (const segment of band.segments) {
      const pageState = state.pdf.pageStates.get(segment.pageNumber);
      if (!pageState) continue;
      const pageHeight = pageState.el.clientHeight;
      const topPx = segment.top * pageHeight;
      const bottomPx = (segment.bottom ?? 1) * pageHeight;
      const height = bottomPx - topPx;
      if (height <= 0) continue;
      const el = document.createElement("div");
      el.className = "pdf-mark";
      if (band.index === active) el.classList.add("active");
      if (band.index === hovered) el.classList.add("is-hover");
      el.dataset.entry = String(band.index);
      const leftPct = (segment.left * 100).toFixed(3);
      const rightPct = ((1 - segment.right) * 100).toFixed(3);
      el.setAttribute(
        "style",
        `left:${leftPct}%;right:${rightPct}%;top:${topPx}px;height:${height}px;${markerStyle(band.target)}`,
      );
      if (band.title) el.title = band.title;
      pageState.el.append(el);
    }
  }
}

// Record the reader's current position as the topmost visible page plus a
// fractional offset into it, rather than a raw scrollTop. A rebuilt PDF may have
// a slightly different page count or crop, so a page-anchored fraction restores
// the same content even when absolute pixel offsets shift.
export function capturePdfScrollAnchor(): { pageNumber: number; fraction: number } | null {
  if (!state.pdf.document || !state.pdf.pageStates.size) return null;
  const viewerTop = els.pdfViewer.scrollTop;
  for (const pageState of state.pdf.pageStates.values()) {
    const top = pageState.el.offsetTop;
    const height = pageState.el.offsetHeight;
    if (height > 0 && viewerTop < top + height) {
      return { pageNumber: pageState.pageNumber, fraction: (viewerTop - top) / height };
    }
  }
  return null;
}

export function restorePdfScrollAnchor(anchor: { pageNumber: number; fraction: number }): void {
  const pageCount = state.pdf.pageCount ?? anchor.pageNumber;
  const pageNumber = Math.min(Math.max(1, anchor.pageNumber), pageCount);
  const pageState = state.pdf.pageStates.get(pageNumber);
  if (!pageState) return;
  const top = pageState.el.offsetTop + anchor.fraction * pageState.el.offsetHeight;
  els.pdfViewer.scrollTo({ top: Math.max(0, top), left: els.pdfViewer.scrollLeft, behavior: "auto" });
  renderVisiblePdfPages();
  updatePdfPageFromScroll();
}

export function scrollPdfToEntry(index: number): void {
  if (!visiblePaneNames().includes("pdf")) return;
  const target = state.pdf.targets.get(index);
  if (!target) return;
  const pageState = state.pdf.pageStates.get(target.pageNumber);
  if (!pageState) return;
  const nextTop = Math.max(0, pageState.el.offsetTop + target.y - els.pdfViewer.clientHeight * 0.35);
  els.pdfViewer.scrollTo({ top: nextTop, left: els.pdfViewer.scrollLeft, behavior: "auto" });
  renderVisiblePdfPages();
  updatePdfPageFromScroll();
}

export function nearestEntryFromPdfScroll(): number | null {
  if (!state.pdf.targets.size) return null;
  const targetTop = els.pdfViewer.scrollTop + els.pdfViewer.clientHeight * 0.35;
  let best: number | null = null;
  let bestDistance = Infinity;
  for (const [index, target] of state.pdf.targets.entries()) {
    const pageState = state.pdf.pageStates.get(target.pageNumber);
    if (!pageState) continue;
    const absoluteTop = pageState.el.offsetTop + target.y;
    const distance = Math.abs(absoluteTop - targetTop);
    if (distance < bestDistance) {
      bestDistance = distance;
      best = index;
    }
  }
  return Number.isInteger(best) ? best : null;
}

export async function setPdf(path: string, options: { preserveScroll?: boolean } = {}): Promise<void> {
  // Capture the reader's position before clearPdfViewer wipes the page states,
  // so a rebuild of the same PDF can restore it instead of jumping to the top.
  const anchor = options.preserveScroll ? capturePdfScrollAnchor() : null;
  state.pdf.path = path;
  onPdfSelected(path);
  els.pdfLink.href = path;
  if (els.pdfSelect.value !== path) els.pdfSelect.value = path;
  clearPdfViewer("Loading PDF...");
  const token = ++state.pdf.renderToken;

  try {
    const pdfjs = await loadPdfJs();
    if (token !== state.pdf.renderToken) return;
    const loadingTask = pdfjs.getDocument({ url: cacheBustedUrl(path) });
    state.pdf.loadingTask = loadingTask;
    const pdfDocument = await loadingTask.promise;
    if (token !== state.pdf.renderToken) {
      // A newer setPdf already superseded this one; tear down our task so the
      // stale pdf.js worker document is not leaked.
      loadingTask.destroy();
      return;
    }
    state.pdf.document = pdfDocument;
    state.pdf.pageCount = pdfDocument.numPages;
    state.pdf.currentPage = 1;
    state.pdf.pageStates = new Map();
    els.pdfViewer.innerHTML = "";

    const firstPage = await pdfDocument.getPage(1);
    const firstViewport = firstPage.getViewport({ scale: 1 });
    // One document-wide crop (the text block), shared by every page, so the side
    // margins go but no page is over-zoomed.
    state.pdf.crop = await computeDocCrop(pdfDocument, firstViewport.width, token);
    if (token !== state.pdf.renderToken) {
      loadingTask.destroy();
      return;
    }
    const cropWidth = state.pdf.crop ? state.pdf.crop.x1 - state.pdf.crop.x0 : firstViewport.width;
    const ratio = `${cropWidth} / ${firstViewport.height}`;
    for (let pageNumber = 1; pageNumber <= pdfDocument.numPages; pageNumber += 1) {
      const pageEl = document.createElement("div");
      pageEl.className = "pdf-page";
      pageEl.dataset.page = String(pageNumber);
      pageEl.style.aspectRatio = ratio;
      const canvas = document.createElement("canvas");
      canvas.hidden = true;
      pageEl.append(canvas);
      els.pdfViewer.append(pageEl);
      state.pdf.pageStates.set(pageNumber, { pageNumber, el: pageEl, canvas, rendered: false, rendering: false });
    }

    // Restore the captured position now that the new page elements exist (their
    // aspect-ratio gives a definite height before rasterizing). If we restored,
    // tell resolvePdfTargets not to override it by scrolling to the active entry.
    if (anchor) restorePdfScrollAnchor(anchor);
    window.requestAnimationFrame(() => renderVisiblePdfPages());
    state.pdf.targetPromise = resolvePdfTargets(token, !anchor).catch((error) => {
      console.error("[booklink] Failed to resolve PDF targets:", error);
    });
    updatePdfStatus();
  } catch (error) {
    if (token !== state.pdf.renderToken) return;
    const friendly = onPdfLoadFailed(path, error);
    clearPdfViewer(friendly ?? `Failed to load PDF: ${error instanceof Error ? error.message : String(error)}`);
    if (!friendly) console.error(error);
  }
}

export async function renderPdfChoices(choices: any[], initialPath: string): Promise<void> {
  els.pdfSelect.innerHTML = choices
    .map((choice) => `<option value="${escapeHtml(choice.path)}">${escapeHtml(choice.label)}</option>`)
    .join("");
  await setPdf(initialPath);
}

export function reloadPdf(): void {
  // An auto-rebuild reloads the same PDF in place; keep the reader where they
  // were rather than resetting to the top. When nothing is loaded yet (e.g. a
  // first chapter-preview build), there is no anchor and the default applies.
  if (state.pdf.path) setPdf(state.pdf.path, { preserveScroll: true }).catch(reportError);
}
