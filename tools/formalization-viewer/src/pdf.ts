import { documentWorkerApi } from "./pdf-worker.js";
import { t } from "./i18n.js";
import { trustedScriptURL } from "./safe-script-url.js";
import { setHTML } from "./safe-html.js";
import { pdfIncludesSource } from "./pdf-preview.js";
import { pdfDestination } from "./pdf-destinations.js";
import { resolveDefinition, type DefinitionRegistry } from "./definition-registry.js";
import { paneViewportTop, paneViewportHeight, scrollPane } from "./pane-scroll.js";
import { pdfLoadStatus, pdfByteProgress } from "./loading-progress.js";
import { destinationChapter, preferredDestination, termTarget } from "./pdf-chapter.js";
import { computeDocumentCrop, documentPageLines, appendPageLinks, preparePdf, paintPdfPage } from "./pdf-document.js";
import {
  captureScrollAnchor,
  destinationToPoint,
  makePageLineCache,
  nearestEntryIndex,
  nearestSkipLocation,
  renderEntryBandOverlays,
  renderSkipBandOverlays,
  renderVisiblePages,
  restoreScrollAnchor,
  scrollToEntryTarget,
  scrollToSkipRange,
} from "./pdf-pane.js";
import { dismissTermPopup } from "./term-preview.js";
import { flashPdfDestination } from "./pdf-destination-highlight.js";
import { renderedPdfPath } from "./appearance.js";
import { lightPdfPath } from "./pdf-theme.js";
import { type PdfScrollAnchor } from "./permalink.js";
// The PDF pane: loads the book PDF with pdf.js, lazily rasterizes visible
// pages (cropped to the text column and zoomed to the pane), resolves each
// booklink's page/offset target, and scrolls to entries. Depends one-way on
// state/util and on sync for the visible-pane set; it never imports app. The
// one thing app must react to — targets resolved, so the PDF overview rail can
// be redrawn — is delivered through an injected callback.

import { state, els, project } from "./state.js";
import { escapeHtml, repoUrl, reportError } from "./util.js";
import { suppressPaneSync, visiblePaneNames, type SkipSyncLocation } from "./sync.js";
import { type PageLineCache, resolveEntryFlowSegments, resolveSkipFlowSegments } from "./skip-bands.js";

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

let pdfGeometryFrame = 0;
export function refreshPdfLayoutGeometry(): void {
  if (!state.pdf.document) return;
  if (!pdfGeometryFrame)
    pdfGeometryFrame = window.requestAnimationFrame(() => {
      pdfGeometryFrame = 0;
      if (!state.pdf.document) return;
      // Page destinations and band fractions are independent of CSS width.
      renderVisiblePdfPages();
      renderSkipBands();
      renderEntryBands();
      onPdfTargetsResolved();
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
  const file = path.split(/[?#]/, 1)[0].split("/").pop() || path;
  const debug = project.pdf?.split("/").pop();
  const stem = debug?.replace(/-debug\.pdf$/, "");
  if (stem && file.startsWith(`${stem}-preview-`) && file.endsWith(".pdf")) {
    const chapter = file.slice(`${stem}-preview-`.length, -4);
    return project.previewSections?.[chapter] || project.chapterTitles?.[chapter] || chapter.replace(/-/g, " ");
  }
  if (file === debug) return t("Full book · Annotated");
  if (stem && file === `${stem}.pdf`) return t("Full book · Release");
  if (stem && file === `${stem}-diff.pdf`) return t("Full book · Changes");
  return file;
}

export function pdfChoices(
  params: URLSearchParams,
  defaults: { pdf: string; map?: string },
): { choices: any[]; initialPath: string } {
  // ?pdf= deep links select a specific render.
  const override = params.get("pdf") || "";
  // The server (live and static dist) injects "pdfs": every PDF that actually
  // exists under the mount, so the dropdown never offers a 404. Per-chapter
  // preview artifacts are dropped here; the app adds chapter and back-matter
  // choices that the live server builds on demand. Fall back to the debug PDF
  // for an older manifest without the list. Labels name chapters or distinguish
  // the whole-book renders; option values remain the original PDF paths.
  const served = (Array.isArray(project.pdfs) ? project.pdfs : []).filter(
    (rel) => !rel.includes("-preview") && !rel.includes("-layout-") && !rel.endsWith("-dark.pdf"),
  );
  // The live server can build the default on demand even when only a release
  // PDF exists. Keep it selectable so cold startup still requests the debug PDF.
  if (!project.static && project.pdf && !served.includes(project.pdf)) served.push(project.pdf);
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

// PDF requests carry a cache generation (`viewer-cache`) so repeated loads
// of the same document — switching editions, toggling the theme, changing
// the layout — reuse the HTTP cache (the live server revalidates cheaply)
// instead of re-downloading the whole book every time. The generation
// advances only when the app learns the PDF bytes changed (a rebuild, via
// notePdfContentChanged), so an in-place reload still fetches fresh bytes.
// A `?refresh=` page parameter overrides the generation: a manual hard bust
// that applies to every PDF at once.
let pdfCacheGeneration = 0;

export function notePdfContentChanged(): void {
  pdfCacheGeneration += 1;
}

export function cacheBustedUrl(path: string): string {
  const url = new URL(path, window.location.href);
  const refresh = new URLSearchParams(window.location.search).get("refresh") || String(pdfCacheGeneration);
  url.searchParams.set("viewer-cache", refresh);
  return url.pathname + url.search + url.hash;
}

let pdfJsLoad: Promise<any> | undefined;
export async function loadPdfJs(): Promise<any> {
  if (state.pdfjs) return state.pdfjs;
  return (pdfJsLoad ??= (async () => {
    const pdfjs = await import(PDFJS_MODULE_URL);
    pdfjs.GlobalWorkerOptions.workerSrc = PDFJS_WORKER_URL;
    const api = documentWorkerApi(pdfjs, () => new Worker(trustedScriptURL(PDFJS_WORKER_URL), { type: "module" }));
    state.pdfjs = api;
    return api;
  })().catch((error) => {
    pdfJsLoad = undefined;
    throw error;
  }));
}

export function clearPdfViewer(message: string = t("Loading PDF...")): void {
  if (state.pdf.loadingTask) {
    state.pdf.loadingTask.destroy();
    state.pdf.loadingTask = null;
  }
  state.pdf.document = null;
  state.pdf.loadedPath = null;
  state.pdf.currentPage = null;
  state.pdf.pageCount = null;
  state.pdf.pageStates = new Map();
  state.pdf.targets = new Map();
  state.pdf.skipBands = [];
  state.pdf.entryBands = [];
  state.pdf.targetPromise = null;
  state.pdf.crop = null;
  setHTML(els.pdfViewer, `<div class="pdf-message">${escapeHtml(message)}</div>`);
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
export function computeDocCrop(doc: any, pageWidth: number, token: number) {
  return computeDocumentCrop(doc, pageWidth, () => token === state.pdf.renderToken);
}

export async function renderPdfPage(pageNumber: number, token: number): Promise<void> {
  const pageState = state.pdf.pageStates.get(pageNumber);
  if (
    !pageState ||
    (pageState.failures ?? 0) >= 3 ||
    pageState.rendered ||
    pageState.rendering ||
    token !== state.pdf.renderToken
  )
    return;
  pageState.rendering = true;
  try {
    const page = await state.pdf.document.getPage(pageNumber);
    if (token !== state.pdf.renderToken) return;
    pageState.el.style.aspectRatio = await paintPdfPage(
      page,
      pageState.canvas,
      state.pdf.crop,
      pageState.el.clientWidth,
    );
    if (token !== state.pdf.renderToken) return;
    pageState.rendered = true;
    void resolvePageLinks(pageNumber, token);
  } catch (error) {
    pageState.failures = (pageState.failures ?? 0) + 1;
    console.error("[booklink] renderPdfPage failed", { pageNumber, error });
  } finally {
    pageState.rendering = false;
  }
}

// Pages whose link annotations have been turned into overlays, for the current
// document (cleared on every setPdf).
const linkResolvedPages = new Set<number>();

// Re-expose each PDF annotation at its original text/graphic position. Link
// overlays scale with their page and survive text-layer repaints. Internal
// destinations navigate within the viewer; external URLs open a tab.
async function resolvePageLinks(pageNumber: number, token: number): Promise<void> {
  if (linkResolvedPages.has(pageNumber)) return;
  linkResolvedPages.add(pageNumber);
  const pageState = state.pdf.pageStates.get(pageNumber);
  if (!pageState || !state.pdf.document) return;
  const page = await state.pdf.document.getPage(pageNumber);
  if (token !== state.pdf.renderToken) return;
  const annotations = await page.getAnnotations();
  if (token !== state.pdf.renderToken) return;
  const doc = state.pdf.document;
  const path = state.pdf.loadedPath;
  appendPageLinks(pageState.el, annotations, page.getViewport({ scale: 1 }), state.pdf.crop, scrollPdfToDestination, {
    document: (definition) =>
      referencePdfDocument(doc, !!path?.includes("-preview-"), repoUrl(project.pdf!), definition),
    current: () => token === state.pdf.renderToken,
  });
}

// Follow an internal link annotation: resolve a named destination if needed,
// then bring its anchor to the reading line, exactly like a marker jump. A
// term link's printed destination is its index entry; the reader almost
// always wants the definition, so prefer the term-def-<slug> companion anchor
// the book filter drops at the definition site, falling back to the index.
let pendingDestination: { dest: string; preferDefinition: boolean } | null = null;
const referenceDocuments = new Map<string, { task: any; promise: Promise<any> }>();

export async function referencePdfDocument(
  doc: any,
  preview: boolean,
  fullPath: string,
  definition?: unknown,
): Promise<any> {
  if (
    !preview ||
    Array.isArray(definition) ||
    (typeof definition === "string" && (await pdfDestination(doc, definition)))
  )
    return doc;
  return completePdfDocument(fullPath);
}

export function invalidateReferenceDocuments(): void {
  dismissTermPopup();
  for (const { task } of referenceDocuments.values()) void task.destroy().catch(() => {});
  referenceDocuments.clear();
}

export async function completePdfDocument(path: string, lightFallback = false): Promise<any> {
  if (!lightFallback && state.pdf.loadedPath === path && state.pdf.document) return state.pdf.document;
  const requested = lightFallback ? path : renderedPdfPath(path);
  const existing = referenceDocuments.get(requested);
  if (existing) return existing.promise;
  const pdfjs = await loadPdfJs();
  const concurrent = referenceDocuments.get(requested);
  if (concurrent) return concurrent.promise;
  const task = pdfjs.getDocument({ url: cacheBustedUrl(requested) });
  const promise = task.promise.catch((error: unknown) => {
    if (referenceDocuments.get(requested)?.task === task) referenceDocuments.delete(requested);
    // A dark chapter can be built before the full dark book exists. Chapter
    // ownership and off-chapter definitions remain available in the light book.
    if (requested !== path && (error as { status?: number })?.status === 404) return completePdfDocument(path, true);
    throw error;
  });
  referenceDocuments.set(requested, { task, promise });
  while (referenceDocuments.size > 2) {
    const oldest = referenceDocuments.keys().next().value!;
    void referenceDocuments
      .get(oldest)!
      .task.destroy()
      .catch(() => {});
    referenceDocuments.delete(oldest);
  }
  return promise;
}

export async function chapterPdfForDestination(
  dest: string,
  fullPath = repoUrl(project.pdf!),
  preferDefinition = true,
  definitions: DefinitionRegistry | undefined = project.definitionRegistry,
): Promise<string | null> {
  if (!preferDefinition && termTarget(dest))
    return repoUrl(project.pdf!.replace(/-debug\.pdf$/, "-preview-_index.pdf"));
  const definition = resolveDefinition(definitions, dest);
  if (definition) return repoUrl(project.pdf!.replace(/-debug\.pdf$/, `-preview-${definition.chapter}.pdf`));
  const doc = await completePdfDocument(fullPath);
  const chapter = await destinationChapter(
    doc,
    dest,
    project.chapterTitles ?? {},
    project.previewSections ?? {},
    preferDefinition,
  );
  return chapter ? repoUrl(project.pdf!.replace(/-debug\.pdf$/, `-preview-${chapter}.pdf`)) : null;
}

let destinationJump = 0;
async function scrollPdfToDestination(dest: any, preferDefinition = true): Promise<void> {
  dismissTermPopup();
  const jump = ++destinationJump;
  const token = state.pdf.renderToken;
  const doc = state.pdf.document;
  const current = () => jump === destinationJump && token === state.pdf.renderToken;
  let resolved: any = null;
  let name = typeof dest === "string" ? preferredDestination(dest, preferDefinition) : undefined;
  if (typeof dest === "string") {
    const preferred = preferredDestination(dest, preferDefinition);
    resolved = await pdfDestination(doc, preferred);
    if (state.pdf.loadedPath?.includes("-preview-") && project.pdf) {
      const path = await chapterPdfForDestination(dest, repoUrl(project.pdf), preferDefinition);
      if (!current()) return;
      if (path && path !== state.pdf.path) {
        pendingDestination = { dest, preferDefinition };
        await setPdf(path, { scrollToActive: false });
        return;
      }
    }
    if (!resolved) {
      resolved = await pdfDestination(doc, dest);
      name = dest;
    }
  } else {
    resolved = dest;
  }
  if (!current()) return;
  const point = await destinationToPagePoint(resolved, token);
  if (!point || !current()) return;
  const pageState = state.pdf.pageStates.get(point.pageNumber);
  if (!pageState) return;
  suppressPaneSync("pdf");
  const top =
    pageState.el.offsetTop + point.frac * pageState.el.offsetHeight - paneViewportHeight(els.pdfViewer) * 0.35;
  scrollPane(els.pdfViewer, { top: Math.max(0, top), left: els.pdfViewer.scrollLeft, behavior: "auto" });
  renderVisiblePdfPages();
  updatePdfPageFromScroll();
  const page = await doc.getPage(point.pageNumber);
  if (current())
    await flashPdfDestination(page, resolved, name, pageState.el, state.pdf.crop, current, () => pageState.rendered);
}

export function renderVisiblePdfPages(): void {
  if (!state.pdf.document) return;
  const token = state.pdf.renderToken;
  renderVisiblePages(els.pdfViewer, state.pdf.pageStates, (pageNumber) => {
    void renderPdfPage(pageNumber, token);
  });
}

export function updatePdfPageFromScroll(): void {
  const target = paneViewportTop(els.pdfViewer) + paneViewportHeight(els.pdfViewer) * 0.35;
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
  }
}

export async function resolvePdfTargets(token: number, scrollToActive = true): Promise<void> {
  if (!state.pdf.document) return;
  const targets = new Map<number, { pageNumber: number; fraction: number }>();
  await Promise.all(
    state.entries.map(async (entry, index) => {
      if (!pdfIncludesSource(state.pdf.loadedPath || "", entry.match?.source ?? entry.booklink?.source)) return;
      // The PDF numbers booklinks globally (\BooklinkStart[entry=N] / the
      // booklink-entry-N named destination), which is not the per-book array
      // index. The sourcemap's texMatch.entry carries that PDF number, so map by
      // it rather than by position.
      const entryNumber = (entry as any)?.texMatch?.entry;
      if (typeof entryNumber !== "number") return;
      const destination = await pdfDestination(state.pdf.document, `booklink-entry-${entryNumber}`);
      if (token !== state.pdf.renderToken) return;
      const placement = await destinationToPagePoint(destination, token);
      if (placement) targets.set(index, { pageNumber: placement.pageNumber, fraction: placement.frac });
    }),
  );
  if (token !== state.pdf.renderToken) return;
  state.pdf.targets = targets;
  // Skip and entry bands both snap their edges onto text lines, so share one
  // per-page text-content cache across both passes (many bands share a page).
  const pageLines = makePageLineCache((pageNumber) =>
    documentPageLines(state.pdf.document, pageNumber, state.pdf.crop, () => token === state.pdf.renderToken),
  );
  await Promise.all([resolveSkipBands(token, pageLines), resolveEntryBands(token, pageLines)]);
  if (token !== state.pdf.renderToken) return;
  // On a scroll-preserving reload the caller has already restored the reader's
  // position, so don't yank it back to the active entry.
  if (scrollToActive) {
    if (state.location.kind === "skip") scrollPdfToSkip(state.location);
    else scrollPdfToEntry(state.activeIndex);
  }
  onPdfTargetsResolved();
}

// Convert a pdf.js named destination to its page, a vertical *fraction* of the
// page (0 = top, 1 = bottom), and the anchor's horizontal x as a fraction of
// the cropped text column (0 = crop left edge, 1 = crop right edge), matching
// how the overlay divs are positioned (the canvas fills the crop width).
// Fractions are scale-independent, so a band resolved from them renders
// correctly at any pane width — unlike a CSS-pixel y, which goes stale the
// moment the page is re-sized after resolution. The destination's `left` is a
// PDF-point x in the same space as the crop bounds, so it converts directly;
// it bounds highlights that start or end mid-line.
async function destinationToPagePoint(
  destination: any,
  token: number,
): Promise<{ pageNumber: number; frac: number; xFrac: number } | null> {
  return destinationToPoint(
    state.pdf.document,
    destination,
    state.pdf.crop,
    (pageWidth) => pageWidth,
    () => token === state.pdf.renderToken,
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
async function resolveSkipBands(token: number, pageLines: PageLineCache): Promise<void> {
  const bands: typeof state.pdf.skipBands = [];
  await Promise.all(
    (state.skips || []).map(async (skip: any) => {
      if (!pdfIncludesSource(state.pdf.loadedPath || "", skip.source)) return;
      const key = skip?.key;
      if (typeof key !== "string") return;
      const [startDest, endDest] = await Promise.all([
        pdfDestination(state.pdf.document, `skip-${key}-start`),
        pdfDestination(state.pdf.document, `skip-${key}-end`),
      ]);
      if (token !== state.pdf.renderToken) return;
      // Points, not bare fractions: a skip that starts or ends inside a
      // paragraph is bounded mid-line by its anchor's x.
      const start = await destinationToPagePoint(startDest, token);
      const end = await destinationToPagePoint(endDest, token);
      if (!start || !end || token !== state.pdf.renderToken) return;
      const segments = await resolveSkipFlowSegments(start, end, pageLines);
      if (token !== state.pdf.renderToken) return;
      if (segments.length) bands.push({ key, reason: typeof skip.reason === "string" ? skip.reason : "", segments });
    }),
  );
  if (token !== state.pdf.renderToken) return;
  state.pdf.skipBands = bands;
  renderSkipBands();
}

export function renderSkipBands(): void {
  renderSkipBandOverlays(els.pdfViewer, state.pdf.pageStates, state.pdf.skipBands);
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
      if (!pdfIncludesSource(state.pdf.loadedPath || "", entry.match?.source ?? entry.booklink?.source)) return;
      const entryNumber = (entry as any)?.texMatch?.entry;
      if (typeof entryNumber !== "number") return;
      const [startDest, endDest] = await Promise.all([
        pdfDestination(state.pdf.document, `booklink-entry-${entryNumber}`),
        pdfDestination(state.pdf.document, `booklink-entry-${entryNumber}-end`),
      ]);
      if (token !== state.pdf.renderToken) return;
      const start = await destinationToPagePoint(startDest, token);
      const end = await destinationToPagePoint(endDest, token);
      if (!start || !end || token !== state.pdf.renderToken) return;
      const segments = await resolveEntryFlowSegments(start, end, pageLines);
      if (token !== state.pdf.renderToken) return;
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

export function renderEntryBands(): void {
  renderEntryBandOverlays(els.pdfViewer, state.pdf.pageStates, state.pdf.entryBands);
}

export function capturePdfScrollAnchor(): PdfScrollAnchor | null {
  if (!state.pdf.document || !state.pdf.pageStates.size) return null;
  return captureScrollAnchor(els.pdfViewer, state.pdf.pageStates, state.pdf.targets);
}

export function restorePdfScrollAnchor(anchor: PdfScrollAnchor): void {
  restoreScrollAnchor(
    anchor,
    els.pdfViewer,
    state.pdf.pageStates,
    state.pdf.targets,
    state.pdf.pageCount ?? anchor.pageNumber,
    "pdf",
    renderVisiblePdfPages,
    updatePdfPageFromScroll,
  );
}

export function scrollPdfToEntry(index: number): void {
  if (!visiblePaneNames().includes("pdf")) return;
  const target = state.pdf.targets.get(index);
  if (!target) return;
  if (scrollToEntryTarget(els.pdfViewer, state.pdf.pageStates, target, renderVisiblePdfPages))
    updatePdfPageFromScroll();
}

export function nearestEntryFromPdfScroll(): number | null {
  if (!state.pdf.targets.size) return null;
  return nearestEntryIndex(els.pdfViewer, state.pdf.pageStates, state.pdf.targets);
}

function primarySkipRange(key: string): { start: number; end: number } | null {
  const band = state.pdf.skipBands.find((candidate) => candidate.key === key);
  if (!band?.segments.length) return null;
  let start = Infinity;
  let end = -Infinity;
  for (const segment of band.segments) {
    const page = state.pdf.pageStates.get(segment.pageNumber);
    if (!page) continue;
    start = Math.min(start, page.el.offsetTop + segment.top * page.el.offsetHeight);
    end = Math.max(end, page.el.offsetTop + (segment.bottom ?? 1) * page.el.offsetHeight);
  }
  return Number.isFinite(start) && end >= start ? { start, end } : null;
}

export function nearestSkipFromPdfScroll(): SkipSyncLocation | null {
  return nearestSkipLocation(
    els.pdfViewer,
    state.pdf.pageStates,
    state.pdf.targets,
    state.pdf.skipBands.map((band) => band.key),
    primarySkipRange,
  );
}

export function scrollPdfToSkip(location: SkipSyncLocation): void {
  if (!visiblePaneNames().includes("pdf")) return;
  const range = primarySkipRange(location.key);
  if (!range) return;
  scrollToSkipRange(els.pdfViewer, range, location.progress, renderVisiblePdfPages);
  updatePdfPageFromScroll();
}

let retainedScroll: { path: string; anchor: PdfScrollAnchor } | null = null;
let loadedLayoutPath: string | null = null;
let pdfRequest = 0;
let pendingPdfTask: any = null;

let pdfLoadPromise: Promise<void> | null = null;

export function currentPdfLoad(): Promise<void> | null {
  return pdfLoadPromise;
}

export function setPdf(
  path: string,
  options: { preserveScroll?: boolean; scrollToActive?: boolean } = {},
): Promise<void> {
  const loading = loadSelectedPdf(path, options);
  pdfLoadPromise = loading;
  void loading
    .finally(() => {
      if (pdfLoadPromise === loading) pdfLoadPromise = null;
    })
    .catch(() => {});
  return loading;
}

async function loadSelectedPdf(
  path: string,
  options: { preserveScroll?: boolean; scrollToActive?: boolean } = {},
): Promise<void> {
  dismissTermPopup();
  const request = ++pdfRequest;
  const current = () => request === pdfRequest;
  if (pendingPdfTask) void pendingPdfTask.destroy().catch(() => {});
  pendingPdfTask = null;
  const layoutPath = lightPdfPath(renderedPdfPath(path));
  const sameLayout = state.pdf.loadedPath === path && loadedLayoutPath === layoutPath;
  const initialAnchor = options.preserveScroll && sameLayout ? capturePdfScrollAnchor() : null;
  if (path !== state.pdf.path && options.scrollToActive !== false) pendingDestination = null;
  state.pdf.path = path;
  state.pdf.pending = true;
  syncPdfControls(path);
  onPdfSelected(path);
  els.pdfLink.href = renderedPdfPath(path);
  // Selection remains global, but hidden panes do not download or prepare PDFs.
  state.pdf.deferred = !visiblePaneNames().includes("pdf");
  if (state.pdf.deferred) return;
  if (!state.pdf.document) clearPdfViewer(t("Loading PDF…"));
  const report = (text: string) => {
    if (current())
      pdfLoadStatus(
        els.pdfViewer,
        state.pdf.document && state.pdf.pending ? `${text} · ${t("Current PDF remains available")}` : text,
      );
  };
  report(t("Loading PDF renderer…"));
  let task: any = null;
  try {
    const pdfjs = await loadPdfJs();
    if (!current()) return;
    const url = renderedPdfPath(path);
    task = pdfjs.getDocument({ url: cacheBustedUrl(url) });
    pendingPdfTask = task;
    task.onProgress = (progress: { loaded: number; total?: number }) => report(pdfByteProgress(progress));
    const doc = await task.promise;
    if (!current()) return;
    let initialPage = initialAnchor?.pageNumber;
    if (!initialPage && options.scrollToActive !== false) {
      const location = state.location;
      const entry = location.kind === "entry" ? state.entries[location.index] : null;
      const skip = location.kind === "skip" ? state.skips?.find((skip: any) => skip.key === location.key) : null;
      const source = entry?.match?.source ?? entry?.booklink?.source ?? skip?.source;
      const name = skip
        ? `skip-${skip.key}-start`
        : typeof entry?.texMatch?.entry === "number"
          ? `booklink-entry-${entry.texMatch.entry}`
          : null;
      if (name && pdfIncludesSource(path, source)) {
        const destination = await pdfDestination(doc, name);
        if (Array.isArray(destination) && destination[0] != null) {
          const index = typeof destination[0] === "number" ? destination[0] : await doc.getPageIndex(destination[0]);
          if (Number.isInteger(index) && index >= 0 && index < doc.numPages) initialPage = index + 1;
        }
      }
    }
    if (!current()) return;
    const prepared = await preparePdf(
      doc,
      path,
      els.pdfViewer.clientWidth,
      /-dark\.pdf(?:[?#]|$)/.test(url),
      current,
      report,
      initialPage,
    );
    if (!prepared || !current()) return;
    // Capture at commit time: the reader may have kept scrolling the old PDF.
    const anchor =
      (options.preserveScroll && sameLayout ? capturePdfScrollAnchor() : null) ??
      (retainedScroll?.path === layoutPath ? retainedScroll.anchor : null);
    retainedScroll = anchor ? { path: layoutPath, anchor } : null;
    if (anchor) {
      const at = Math.max(prepared.start, Math.min(doc.numPages, anchor.pageNumber));
      const page = prepared.pages.get(at);
      if (page && !page.rendered) {
        page.el.style.aspectRatio = await paintPdfPage(
          await doc.getPage(at),
          page.canvas,
          prepared.crop,
          els.pdfViewer.clientWidth,
        );
        page.rendered = true;
      }
    }
    if (!current()) return;
    const oldTask = state.pdf.loadingTask;
    const token = ++state.pdf.renderToken;
    state.pdf.loadingTask = task;
    pendingPdfTask = null;
    state.pdf.document = doc;
    state.pdf.loadedPath = path;
    loadedLayoutPath = layoutPath;
    state.pdf.pending = false;
    state.pdf.pageCount = doc.numPages;
    state.pdf.currentPage = prepared.start;
    state.pdf.pageStates = prepared.pages;
    state.pdf.crop = prepared.crop;
    state.pdf.targets = new Map();
    state.pdf.entryBands = [];
    state.pdf.skipBands = [];
    linkResolvedPages.clear();
    els.pdfViewer.replaceChildren(prepared.fragment);
    if (oldTask && oldTask !== task) void oldTask.destroy().catch(() => {});
    if (anchor) restorePdfScrollAnchor(anchor);
    else if (initialPage) {
      const page = prepared.pages.get(initialPage);
      if (page) {
        suppressPaneSync("pdf");
        scrollPane(els.pdfViewer, { top: page.el.offsetTop, left: els.pdfViewer.scrollLeft, behavior: "auto" });
      }
    }
    renderVisiblePdfPages();
    for (const page of prepared.pages.values()) if (page.rendered) void resolvePageLinks(page.pageNumber, token);
    report(t("Resolving PDF links and markers…"));
    state.pdf.targetPromise = resolvePdfTargets(
      token,
      (options.scrollToActive ?? true) && !anchor && !pendingDestination,
    )
      .then(() => {
        if (anchor && token === state.pdf.renderToken) {
          restorePdfScrollAnchor(anchor);
          retainedScroll = null;
        }
      })
      .catch((error) => console.error("[booklink] Failed to resolve PDF targets:", error))
      .finally(() => {
        if (current()) pdfLoadStatus(els.pdfViewer, null);
      });
    if (pendingDestination) {
      const destination = pendingDestination;
      pendingDestination = null;
      await scrollPdfToDestination(destination.dest, destination.preferDefinition);
    }
  } catch (error) {
    if (!current()) return;
    const friendly = onPdfLoadFailed(path, error);
    if (state.pdf.document) {
      pdfLoadStatus(els.pdfViewer, `${friendly ?? t("PDF update failed")} · ${t("Current PDF remains available")}`);
    } else {
      clearPdfViewer(friendly ?? t("Failed to load PDF: {0}", error instanceof Error ? error.message : String(error)));
      pdfLoadStatus(els.pdfViewer, friendly);
    }
    if (!friendly) console.error(error);
  } finally {
    if (task && state.pdf.loadingTask !== task) {
      if (pendingPdfTask === task) pendingPdfTask = null;
      void task.destroy().catch(() => {});
    }
  }
}

let pdfControlChoices: any[] = [];
const lastPdfByMode = new Map<string, string>();
export function syncPdfControls(path: string): void {
  const preview = path.includes("-preview-");
  const mode = document.getElementById("pdf-mode-seg")!;
  state.pdfMode = preview ? "chapter" : "full";
  for (const button of mode.querySelectorAll<HTMLButtonElement>("button[data-value]"))
    button.setAttribute("aria-pressed", String(button.dataset.value === state.pdfMode));
  lastPdfByMode.set(state.pdfMode, path);
  const choices = pdfControlChoices.filter((c) => c.path.includes("-preview-") === preview);
  els.pdfSelect.setAttribute("aria-label", preview ? t("PDF chapter") : t("Full book edition"));
  setHTML(
    els.pdfSelect,
    choices.map((c) => `<option value="${escapeHtml(c.path)}">${escapeHtml(c.label)}</option>`).join(""),
  );
  els.pdfSelect.value = path;
}
export function pdfPathForMode(mode: string): string | undefined {
  const chapter = (state.selectedSources.md ?? "").split("/").pop()?.replace(/\.md$/, "");
  return (
    lastPdfByMode.get(mode) ??
    (mode === "chapter" && chapter
      ? pdfControlChoices.find((c) => c.path.endsWith(`-preview-${chapter}.pdf`))?.path
      : undefined) ??
    (mode === "chapter" ? pdfControlChoices.find((c) => /-preview-(?!_)[^/]+\.pdf$/.test(c.path))?.path : undefined) ??
    pdfControlChoices.find((c) => c.path.includes("-preview-") === (mode === "chapter"))?.path
  );
}

export async function renderPdfChoices(choices: any[], initialPath: string): Promise<void> {
  pdfControlChoices = choices;
  syncPdfControls(initialPath);
  await setPdf(initialPath);
}

export function reloadPdf(): void {
  notePdfContentChanged();
  invalidateReferenceDocuments();
  // An auto-rebuild reloads the same PDF in place; keep the reader where they
  // were rather than resetting to the top. When nothing is loaded yet (e.g. a
  // first chapter-preview build), there is no anchor and the default applies.
  if (state.pdf.path) setPdf(state.pdf.path, { preserveScroll: true }).catch(reportError);
}
