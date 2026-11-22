import { t } from "./i18n.js";
import { setHTML } from "./safe-html.js";
import { pdfIncludesSource } from "./pdf-preview.js";
import { pdfDestination } from "./pdf-destinations.js";
import { paneScrollTop, paneViewportHeight, scrollPane } from "./pane-scroll.js";
import { pdfLoadStatus, pdfByteProgress } from "./loading-progress.js";
import { preparePdf, paintPdfPage, documentPageLines, appendPageLinks } from "./pdf-document.js";
import {
  captureScrollAnchor,
  destinationToPoint,
  makePageLineCache,
  nearestEntryIndex,
  nearestSkipLocation,
  pagePointTop,
  renderEntryBandOverlays,
  renderSkipBandOverlays,
  renderVisiblePages,
  restoreScrollAnchor,
  scrollToEntryTarget,
  scrollToSkipRange,
} from "./pdf-pane.js";
// A second, marker-synchronized PDF renderer used by translated projects. It
// follows the primary PDF's displayed page width, so both documents retain the
// same visual zoom even when the pane layout is resized. Named booklink
// destinations align corresponding passages despite different page counts.

import { els, state, project, type Project } from "./state.js";
import {
  cacheBustedUrl,
  loadPdfJs,
  notePdfContentChanged,
  setPdf,
  chapterPdfForDestination,
  referencePdfDocument,
  invalidateReferenceDocuments,
} from "./pdf.js";
import { preferredDestination } from "./pdf-chapter.js";
import { dismissTermPopup } from "./term-preview.js";
import { flashPdfDestination } from "./pdf-destination-highlight.js";
import { lightPdfPath } from "./pdf-theme.js";
import { type PdfScrollAnchor } from "./permalink.js";
import { isPaneSuppressed, suppressPaneSync, syncFromScroll, visiblePaneNames, type SkipSyncLocation } from "./sync.js";
import { escapeHtml, mountPrefix } from "./util.js";
import { peerTexRelativePath } from "./copy-tex.js";
import {
  type AnchorPoint,
  type PageLineCache,
  resolveEntryFlowSegments,
  resolveSkipFlowSegments,
} from "./skip-bands.js";

const DEBUG = new URLSearchParams(window.location.search).has("debug");
function debug(type: string, detail: Record<string, unknown>): void {
  if (DEBUG) console.debug(`[booklink] parallelPdf:${type} ${JSON.stringify(detail)}`);
}

interface PageState {
  pageNumber: number;
  el: HTMLElement;
  canvas: HTMLCanvasElement;
  rendered: boolean;
  rendering: boolean;
}

interface PdfPoint {
  pageNumber: number;
  fraction: number;
}

interface EntryBand {
  index: number;
  title: string;
  target: string | null;
  segments: Array<{ pageNumber: number; top: number; bottom: number | null; left: number; right: number }>;
}

interface SkipBand {
  key: string;
  reason: string;
  segments: Array<{ pageNumber: number; top: number; bottom: number | null; left: number; right: number }>;
}

// One-shot: a link follow that switches documents positions the pane itself,
// so the next initParallelPdf must not open at the active entry.
let suppressNextActiveScroll = false;

const parallel = {
  path: null as string | null,
  document: null as any,
  loadingTask: null as any,
  token: 0,
  crop: null as { x0: number; x1: number } | null,
  baseWidth: 0,
  baseHeight: 0,
  pageStates: new Map<number, PageState>(),
  targets: new Map<number, PdfPoint>(),
  entryBands: [] as EntryBand[],
  skipBands: [] as SkipBand[],
  skipTargets: new Map<string, { start: PdfPoint; end: PdfPoint }>(),
  entries: [] as any[],
  skips: [] as any[],
  mapRoot: "",
  repaintTimer: null as ReturnType<typeof setTimeout> | null,
  scrollTimer: null as ReturnType<typeof setTimeout> | null,
  resizeObserver: null as ResizeObserver | null,
};

// The peer document's TeX match for an entry, plus the URL its tex file is
// served at under the peer mount. Entries in the peer map are index-aligned
// with state.entries: the translated project's sourcemap is a projection of
// the same booklink list. Used by the copy-TeX shortcut when the peer PDF
// pane is displayed.
export function parallelTexMatch(index: number): { match: any; url: string } | null {
  return peerMatchUrl(parallel.entries[index]?.texMatch);
}

// The peer document's TeX match for a `formalization: skip` band, by the
// skip's stable key. Used by the copy-TeX shortcut when the reader points at
// a skip band in the peer PDF pane.
export function parallelSkipTexMatch(key: string): { match: any; url: string } | null {
  return peerMatchUrl(parallel.skips.find((skip: any) => skip?.key === key)?.texMatch);
}

function peerMatchUrl(match: any): { match: any; url: string } | null {
  if (!match || match.status !== "matched" || typeof match.source !== "string") return null;
  const peer = project.parallelPdf;
  if (!peer?.mount) return null;
  // A static dist bundles the peer tex next to the peer map and records the
  // copy in texPath (there is no peer mount to fall back to); the live server
  // serves it from the peer project, derived from the sourcemap's path.
  const rel = peer.texPath
    ? peer.texPath.replace(/^\/+/, "")
    : peerTexRelativePath(match.source, parallel.mapRoot, peer.dir || "");
  return { match, url: `${mountPrefix()}${peer.mount}/${rel}` };
}

function primaryPageWidth(): number {
  const page = els.pdfViewer.querySelector(".pdf-page") as HTMLElement | null;
  return Math.max(240, page?.clientWidth || els.pdfViewer.clientWidth || els.pdfPeerViewer.clientWidth);
}

function cropWidth(): number {
  return parallel.crop ? parallel.crop.x1 - parallel.crop.x0 : parallel.baseWidth;
}

async function renderPage(pageNumber: number, token: number): Promise<void> {
  const pageState = parallel.pageStates.get(pageNumber);
  if (!pageState || pageState.rendered || pageState.rendering || token !== parallel.token) return;
  pageState.rendering = true;
  try {
    const page = await parallel.document.getPage(pageNumber);
    if (token !== parallel.token) return;
    const cssWidth = primaryPageWidth();
    pageState.el.style.width = `${cssWidth}px`;
    pageState.el.style.aspectRatio = await paintPdfPage(page, pageState.canvas, parallel.crop, cssWidth);
    if (token === parallel.token) {
      pageState.rendered = true;
      void resolvePeerPageLinks(pageNumber, token);
    }
  } catch (error) {
    console.error("[booklink] parallel PDF page render failed", { pageNumber, error });
  } finally {
    pageState.rendering = false;
  }
}

export function renderVisibleParallelPdfPages(): void {
  if (!parallel.document) return;
  renderVisiblePages(els.pdfPeerViewer, parallel.pageStates, (pageNumber) => {
    void renderPage(pageNumber, parallel.token);
  });
}

async function resolveTargets(token: number, pageLines: PageLineCache): Promise<void> {
  const targets = new Map<number, PdfPoint>();
  const bands: EntryBand[] = [];
  await Promise.all(
    parallel.entries.map(async (entry, index) => {
      if (!pdfIncludesSource(parallel.path || "", entry.match?.source ?? entry.booklink?.source)) return;
      const entryNumber = entry?.texMatch?.entry;
      if (typeof entryNumber !== "number") return;
      const [start, end] = await Promise.all([
        destinationPoint(`booklink-entry-${entryNumber}`, token),
        destinationPoint(`booklink-entry-${entryNumber}-end`, token),
      ]);
      if (!start) return;
      targets.set(index, { pageNumber: start.pageNumber, fraction: start.frac });
      if (!end) return;
      const segments = await resolveEntryFlowSegments(start, end, pageLines);
      if (!segments.length) return;
      targets.set(index, { pageNumber: segments[0].pageNumber, fraction: segments[0].top });
      const name = entry?.lean?.declName || "entry";
      const target = typeof entry?.booklink?.target === "string" ? entry.booklink.target : null;
      bands.push({ index, title: target ? `${name} · ${target}` : name, target, segments });
    }),
  );
  if (token !== parallel.token) return;
  parallel.targets = targets;
  parallel.entryBands = bands;
  renderParallelEntryBands();
  debug("ready", {
    pages: parallel.document.numPages,
    targets: targets.size,
    pageWidth: primaryPageWidth(),
  });
}

export function renderParallelEntryBands(): void {
  renderEntryBandOverlays(els.pdfPeerViewer, parallel.pageStates, parallel.entryBands);
}

// Pages whose link annotations have been turned into overlays, for the current
// peer document (cleared on every initParallelPdf).
const linkResolvedPages = new Set<number>();

// The peer counterpart of pdf.ts's resolvePageLinks: re-expose the canvas-lost
// link annotations as overlay anchors. Internal destinations scroll the peer
// pane; external URLs open a tab. The global Links setting controls outlines.
let peerDefinitionContext: { token: number; value: Promise<Project> } | null = null;
function peerDefinitions(token: number): Promise<Project> {
  if (peerDefinitionContext?.token === token) return peerDefinitionContext.value;
  const url = `${mountPrefix()}${project.parallelPdf?.mount}/manifest.json`;
  const value = fetch(url, { cache: "no-store" }).then((response) => {
    if (!response.ok) throw new Error(`Peer definitions: HTTP ${response.status}`);
    return response.json();
  });
  peerDefinitionContext = { token, value };
  return value;
}

async function resolvePeerPageLinks(pageNumber: number, token: number): Promise<void> {
  if (linkResolvedPages.has(pageNumber)) return;
  linkResolvedPages.add(pageNumber);
  const pageState = parallel.pageStates.get(pageNumber);
  if (!pageState || !parallel.document) return;
  const page = await parallel.document.getPage(pageNumber);
  if (token !== parallel.token) return;
  const annotations = (await page.getAnnotations()) as any[];
  if (token !== parallel.token) return;
  const doc = parallel.document;
  const definitions = await peerDefinitions(token);
  if (token !== parallel.token) return;
  appendPageLinks(pageState.el, annotations, page.getViewport({ scale: 1 }), parallel.crop, scrollPeerToDestination, {
    document: (definition) =>
      referencePdfDocument(
        doc,
        !!parallel.path?.includes("-preview-"),
        `${mountPrefix()}${project.parallelPdf?.mount}/${project.parallelPdf?.path}`,
        definition,
      ),
    current: () => token === parallel.token,
    definitions: () => definitions.definitionRegistry,
    references: () => definitions.references,
    macros: () => definitions.katexMacros ?? {},
    chapterTitles: () => definitions.chapterTitles ?? {},
  });
}

let pendingPeerDestination: { dest: string; preferDefinition: boolean } | null = null;
let destinationJump = 0;
async function scrollPeerToDestination(dest: any, preferDefinition = true): Promise<void> {
  dismissTermPopup();
  const jump = ++destinationJump;
  const token = parallel.token;
  const doc = parallel.document;
  const current = () => jump === destinationJump && token === parallel.token;
  // Resolve chapter ownership in the peer's complete PDF, then mirror the
  // chapter selection and follow the destination after that preview loads.
  let resolved: any = null;
  let name = typeof dest === "string" ? preferredDestination(dest, preferDefinition) : undefined;
  if (typeof dest === "string") {
    resolved = await pdfDestination(doc, preferredDestination(dest, preferDefinition));
    if (parallel.path?.includes("-preview-") && project.parallelPdf?.path) {
      const fullPath = `${mountPrefix()}${project.parallelPdf.mount}/${project.parallelPdf.path}`;
      const path = await chapterPdfForDestination(
        dest,
        fullPath,
        preferDefinition,
        (await peerDefinitions(token)).definitionRegistry,
      );
      if (!current()) return;
      if (path && path !== state.pdf.path) {
        pendingPeerDestination = { dest, preferDefinition };
        suppressNextActiveScroll = true;
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
  if (!resolved || !current()) return;
  const [pageRef, _mode, , top] = resolved as any[];
  const pageIndex = typeof pageRef === "number" ? pageRef : await doc.getPageIndex(pageRef);
  const page = await doc.getPage(pageIndex + 1);
  if (!current()) return;
  const vp = page.getViewport({ scale: 1 });
  const frac = typeof top === "number" ? vp.convertToViewportPoint(0, top)[1] / vp.height : 0;
  const pageState = parallel.pageStates.get(pageIndex + 1);
  if (!pageState) return;
  suppressPaneSync("pdf-peer");
  const target =
    pageState.el.offsetTop + frac * pageState.el.offsetHeight - paneViewportHeight(els.pdfPeerViewer) * 0.35;
  scrollPane(els.pdfPeerViewer, { top: Math.max(0, target), left: els.pdfPeerViewer.scrollLeft, behavior: "auto" });
  renderVisibleParallelPdfPages();
  await flashPdfDestination(page, resolved, name, pageState.el, parallel.crop, current, () => pageState.rendered);
}

async function destinationPoint(name: string, token: number): Promise<AnchorPoint | null> {
  const destination = await pdfDestination(parallel.document, name);
  if (!destination || token !== parallel.token) return null;
  return destinationToPoint(
    parallel.document,
    destination,
    parallel.crop,
    () => parallel.baseWidth,
    () => token === parallel.token,
  );
}

async function resolveSkipTargets(token: number, pageLines: PageLineCache): Promise<void> {
  const targets = new Map<string, { start: PdfPoint; end: PdfPoint }>();
  const bands: SkipBand[] = [];
  await Promise.all(
    parallel.skips.map(async (skip) => {
      if (!pdfIncludesSource(parallel.path || "", skip.source)) return;
      const key = skip?.key;
      if (typeof key !== "string") return;
      const [start, end] = await Promise.all([
        destinationPoint(`skip-${key}-start`, token),
        destinationPoint(`skip-${key}-end`, token),
      ]);
      if (!start || !end) return;
      const segments = await resolveSkipFlowSegments(start, end, pageLines);
      if (segments.length) {
        const first = segments[0];
        const last = segments[segments.length - 1];
        targets.set(key, {
          start: { pageNumber: first.pageNumber, fraction: first.top },
          end: { pageNumber: last.pageNumber, fraction: last.bottom ?? 1 },
        });
        bands.push({ key, reason: typeof skip.reason === "string" ? skip.reason : "", segments });
      }
    }),
  );
  if (token !== parallel.token) return;
  parallel.skipTargets = targets;
  parallel.skipBands = bands;
  renderParallelSkipBands();
}

export function renderParallelSkipBands(): void {
  renderSkipBandOverlays(els.pdfPeerViewer, parallel.pageStates, parallel.skipBands);
}

export function captureParallelScrollAnchor(): PdfScrollAnchor | null {
  if (!parallel.document || !parallel.pageStates.size) return null;
  return captureScrollAnchor(els.pdfPeerViewer, parallel.pageStates, parallel.targets);
}

export function restoreParallelScrollAnchor(anchor: PdfScrollAnchor): void {
  restoreScrollAnchor(
    anchor,
    els.pdfPeerViewer,
    parallel.pageStates,
    parallel.targets,
    parallel.document?.numPages || anchor.pageNumber,
    "pdf-peer",
    renderVisibleParallelPdfPages,
  );
}

export function scrollParallelPdfToEntry(index: number): void {
  const target = parallel.targets.get(index);
  if (!target) return;
  const page = parallel.pageStates.get(target.pageNumber);
  if (!page) return;
  scrollToEntryTarget(els.pdfPeerViewer, parallel.pageStates, target, renderVisibleParallelPdfPages, (top) => {
    debug("scrollTo", {
      index,
      pageNumber: target.pageNumber,
      currentTop: Math.round(paneScrollTop(els.pdfPeerViewer)),
      nextTop: Math.round(top),
      pageWidth: Math.round(page.el.getBoundingClientRect().width),
    });
  });
}

export function nearestEntryFromParallelPdfScroll(): number | null {
  return nearestEntryIndex(els.pdfPeerViewer, parallel.pageStates, parallel.targets);
}

function parallelSkipRange(key: string): { start: number; end: number } | null {
  const target = parallel.skipTargets.get(key);
  if (!target) return null;
  const start = pagePointTop(parallel.pageStates, target.start);
  const end = pagePointTop(parallel.pageStates, target.end);
  if (start === null || end === null) return null;
  return { start: Math.min(start, end), end: Math.max(start, end) };
}

export function nearestSkipFromParallelPdfScroll(): SkipSyncLocation | null {
  return nearestSkipLocation(
    els.pdfPeerViewer,
    parallel.pageStates,
    parallel.targets,
    parallel.skipTargets.keys(),
    parallelSkipRange,
  );
}

export function scrollParallelPdfToSkip(location: SkipSyncLocation): void {
  const range = parallelSkipRange(location.key);
  if (!range) return;
  scrollToSkipRange(els.pdfPeerViewer, range, location.progress, renderVisibleParallelPdfPages);
}

export function refreshParallelPdfZoom(): void {
  if (!parallel.document) return;
  if (parallel.repaintTimer) window.clearTimeout(parallel.repaintTimer);
  parallel.repaintTimer = window.setTimeout(() => {
    parallel.repaintTimer = null;
    // A re-zoom only re-lays-out the same document: keep the reader's place
    // instead of snapping back to the active entry.
    const anchor = captureParallelScrollAnchor();
    const width = primaryPageWidth();
    for (const page of parallel.pageStates.values()) {
      page.rendered = false;
      page.el.style.width = `${width}px`;
      page.el.style.aspectRatio = `${cropWidth()} / ${parallel.baseHeight}`;
    }
    renderParallelSkipBands();
    renderParallelEntryBands();
    renderVisibleParallelPdfPages();
    if (anchor) restoreParallelScrollAnchor(anchor);
  }, 160);
}

let retainedScroll: { path: string; anchor: PdfScrollAnchor } | null = null;
let peerRequest = 0;
let pendingPeerTask: any = null;

export function parallelDocumentPath(): string | null {
  return parallel.path;
}

export async function initParallelPdf(
  path: string,
  mapPath?: string,
  options: { preserveScroll?: boolean } = {},
): Promise<void> {
  if (!visiblePaneNames().includes("pdf-peer")) return;
  dismissTermPopup();
  if (options.preserveScroll) {
    invalidateReferenceDocuments();
    // A preserve-scroll re-load of the peer document already on screen
    // follows a rebuild, like reloadPdf for the primary pane: the next
    // fetch must not reuse the previous bytes.
    if (parallel.document) notePdfContentChanged();
  }
  const request = ++peerRequest;
  const current = () => request === peerRequest;
  if (pendingPeerTask) void pendingPeerTask.destroy().catch(() => {});
  pendingPeerTask = null;
  const identity = lightPdfPath(path);
  const same = lightPdfPath(parallel.path ?? "") === identity;
  const initialAnchor = options.preserveScroll && same ? captureParallelScrollAnchor() : null;
  const skipActiveScroll = suppressNextActiveScroll;
  suppressNextActiveScroll = false;
  if (!parallel.document) setHTML(els.pdfPeerViewer, '<div class="pdf-message">Loading PDF…</div>');
  let committed = false;
  const report = (text: string) => {
    if (current())
      pdfLoadStatus(
        els.pdfPeerViewer,
        `${project.parallelPdf?.label ? t(project.parallelPdf?.label) : t("Parallel PDF")}: ${text}${parallel.document && !committed ? ` · ${t("Current PDF remains available")}` : ""}`,
      );
  };
  report(t("Loading PDF renderer…"));
  let task: any = null;
  try {
    const pdfjs = await loadPdfJs();
    const map = mapPath
      ? await fetch(mapPath, { cache: "no-store" }).then((response) => {
          if (!response.ok) throw new Error(`${mapPath}: HTTP ${response.status}`);
          return response.json();
        })
      : { entries: state.entries, skips: state.skips };
    if (!current()) return;
    task = pdfjs.getDocument({ url: cacheBustedUrl(path) });
    pendingPeerTask = task;
    task.onProgress = (progress: { loaded: number; total?: number }) => report(pdfByteProgress(progress));
    const doc = await task.promise;
    if (!current()) return;
    const prepared = await preparePdf(
      doc,
      path,
      primaryPageWidth(),
      lightPdfPath(path) !== path,
      current,
      report,
      initialAnchor?.pageNumber,
    );
    if (!prepared || !current()) return;
    const anchor =
      (options.preserveScroll && same ? captureParallelScrollAnchor() : null) ??
      (retainedScroll?.path === identity ? retainedScroll.anchor : null);
    retainedScroll = anchor ? { path: identity, anchor } : null;
    if (anchor) {
      const at = Math.max(prepared.start, Math.min(doc.numPages, anchor.pageNumber));
      const page = prepared.pages.get(at);
      if (page && !page.rendered) {
        page.el.style.aspectRatio = await paintPdfPage(
          await doc.getPage(at),
          page.canvas,
          prepared.crop,
          primaryPageWidth(),
        );
        page.rendered = true;
      }
    }
    if (!current()) return;
    const oldTask = parallel.loadingTask;
    const token = ++parallel.token;
    parallel.loadingTask = task;
    pendingPeerTask = null;
    parallel.document = doc;
    parallel.path = path;
    parallel.crop = prepared.crop;
    parallel.baseWidth = prepared.base.width;
    parallel.baseHeight = prepared.base.height;
    parallel.pageStates = prepared.pages;
    parallel.targets = new Map();
    parallel.entryBands = [];
    parallel.skipTargets = new Map();
    parallel.skipBands = [];
    parallel.entries = map.entries || [];
    parallel.skips = map.skips || [];
    parallel.mapRoot = typeof map.root === "string" ? map.root : "";
    linkResolvedPages.clear();
    for (const page of prepared.pages.values()) page.el.style.width = `${primaryPageWidth()}px`;
    els.pdfPeerViewer.replaceChildren(prepared.fragment);
    committed = true;
    if (oldTask && oldTask !== task) void oldTask.destroy().catch(() => {});
    if (anchor) restoreParallelScrollAnchor(anchor);
    renderVisibleParallelPdfPages();
    for (const page of prepared.pages.values()) if (page.rendered) void resolvePeerPageLinks(page.pageNumber, token);
    report(t("Resolving PDF links and markers…"));
    const pageLines = makePageLineCache((pageNumber) =>
      documentPageLines(parallel.document, pageNumber, parallel.crop, () => token === parallel.token),
    );
    await Promise.all([resolveTargets(token, pageLines), resolveSkipTargets(token, pageLines)]);
    if (token !== parallel.token) return;
    if (!anchor && !skipActiveScroll && !pendingPeerDestination) {
      if (state.location.kind === "skip") scrollParallelPdfToSkip(state.location);
      else scrollParallelPdfToEntry(state.activeIndex);
    }
    if (anchor) {
      restoreParallelScrollAnchor(anchor);
      retainedScroll = null;
    }
    if (pendingPeerDestination) {
      const destination = pendingPeerDestination;
      pendingPeerDestination = null;
      await scrollPeerToDestination(destination.dest, destination.preferDefinition);
    }
    if (!parallel.resizeObserver && typeof ResizeObserver !== "undefined") {
      parallel.resizeObserver = new ResizeObserver(refreshParallelPdfZoom);
      parallel.resizeObserver.observe(els.pdfViewer);
    }
    if (current()) pdfLoadStatus(els.pdfPeerViewer, null);
  } catch (error) {
    if (!current()) return;
    const friendly = onParallelPdfLoadFailed(path, error);
    if (parallel.document) {
      pdfLoadStatus(els.pdfPeerViewer, `${friendly ?? t("PDF update failed")} · ${t("Current PDF remains available")}`);
    } else {
      setHTML(
        els.pdfPeerViewer,
        `<div class="pdf-message">${escapeHtml(friendly ?? t("Failed to load PDF: {0}", error instanceof Error ? error.message : String(error)))}</div>`,
      );
      pdfLoadStatus(els.pdfPeerViewer, friendly);
    }
    if (!friendly) console.error(error);
  } finally {
    if (task && parallel.loadingTask !== task) {
      if (pendingPeerTask === task) pendingPeerTask = null;
      void task.destroy().catch(() => {});
    }
  }
}

// Like pdf.ts's onPdfLoadFailed: lets the app substitute a friendly message for
// an expected failure (a mirrored chapter preview that is still being built).
let onParallelPdfLoadFailed: (path: string, error: unknown) => string | null = () => null;

export function setOnParallelPdfLoadFailed(fn: (path: string, error: unknown) => string | null): void {
  onParallelPdfLoadFailed = fn;
}

els.pdfPeerViewer.addEventListener(
  "scroll",
  () => {
    renderVisibleParallelPdfPages();
    if (parallel.scrollTimer) window.clearTimeout(parallel.scrollTimer);
    parallel.scrollTimer = window.setTimeout(() => {
      parallel.scrollTimer = null;
      if (!isPaneSuppressed("pdf-peer")) void syncFromScroll("pdf-peer");
    }, 80);
  },
  { passive: true },
);

export function parallelPdfSearchState() {
  return { document: parallel.document, pages: parallel.pageStates, token: parallel.token, path: parallel.path };
}

export function prefetchParallelPdfPage(pageNumber: number): Promise<void> {
  return renderPage(pageNumber, parallel.token);
}
