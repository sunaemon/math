import { t, localizeStaticUI, uiLanguagePreference } from "./i18n.js";
import { initCorrespondence, refreshCorrespondence } from "./correspondence.js";
import { initFormulaOverlays, refreshFormulaOverlays } from "./formula-overlays.js";
import { setHTML } from "./safe-html.js";
import { initViewerAgent } from "./viewer-agent.js";
import { searchNavigation } from "./search-navigation.js";
import { initSearch } from "./search.js";
import { initOffline } from "./offline.js";
import { initChat } from "./chat.js";
import { pdfOverlayAtPoint } from "./pdf-text-layer.js";
import { splitMathSource } from "./math-source.js";
import { listWindow, MARKER_ROW_HEIGHT } from "./virtual-list.js";
import { openingProseClause, markerProseSource } from "./prose.js";
import { dismissTermPopup, setOpenDefinitionUse } from "./term-preview.js";
import { startupStep, startupDetail, finishStartup, pdfLoadStatus, paneLoadStatus } from "./loading-progress.js";
import {
  setDocumentPane,
  paneScrollTop,
  paneViewportTop,
  paneViewportHeight,
  paneScrollHeight,
  scrollPane,
} from "./pane-scroll.js";
import { applySplitFlex, buildLayoutNode, resizePair } from "./layout-dom.js";
import { languageForPath, parseHighlightData, type HighlightData } from "./highlight.js";
import {
  connectLeanLsp,
  openDocument as lspOpenDocument,
  changeDocument as lspChangeDocument,
  plainGoal as lspPlainGoal,
  plainTermGoal as lspPlainTermGoal,
  hover as lspHover,
  isReady as lspIsReady,
} from "./lean-lsp.js";
import { connectFileWatch } from "./file-watch.js";
import { installReloadGuard, checkForNewBuild } from "./reload-guard.js";
import { attachBuildLog } from "./build-log.js";
import { connectBuildStatus, reportSelectedPdf } from "./build-status.js";
import type { BuildStatus } from "./build-status.js";
import {
  PANE_NAMES,
  defaultTree,
  makeSplit,
  eachLeaf,
  treeLeaves,
  treeKind,
  validateTree,
  removeLeaf,
  replaceLeaf,
  flattenSameDir,
  addLeaf,
} from "./layout-tree.js";
import type { LayoutNode } from "./layout-tree.js";
import { state, els, project, setProject } from "./state.js";
import { reportError, logEvent, repoPath, mountPrefix, repoUrl, displayPath, escapeHtml, safeHref } from "./util.js";
import { renderInfoview } from "./infoview.js";
import { enhanceSelect, enterSearchFromList } from "./select-dropdown.js";
import { renderSource, markerStyle, buildLineStarts } from "./source-render.js";
import { spanText } from "./source-offsets.js";
import { copyTexSource } from "./copy-tex.js";
import { skipSyncLocation } from "./skip-bands.js";
import {
  setActive,
  setSkipActive,
  syncFromScroll,
  syncCurrentLocation,
  visiblePaneNames,
  isPaneSuppressed,
  suppressPaneSync,
  registerPaneSync,
  setActivateHook,
  setLocationHook,
} from "./sync.js";
import { markerId, markerIndex, readLocationParams, withLocationParams, type PdfScrollAnchor } from "./permalink.js";
import {
  removeUrlManagedStorage,
  readSession,
  writeSession,
  sessionKey,
  browserStorage,
  readPreference,
  writePreference,
  withSharedPreferences,
  replaceSharedUrl,
  PDF_MODE_KEY,
} from "./session-store.js";
import type { ViewerSession } from "./session-store.js";
import {
  setPdf,
  currentPdfLoad,
  clearPdfViewer,
  renderPdfChoices,
  pdfChoices,
  pdfLabel,
  renderVisiblePdfPages,
  updatePdfPageFromScroll,
  scrollPdfToEntry,
  nearestEntryFromPdfScroll,
  nearestSkipFromPdfScroll,
  scrollPdfToSkip,
  resolvePdfTargets,
  refreshPdfLayoutGeometry,
  observePdfBandGeometry,
  reloadPdf,
  capturePdfScrollAnchor,
  restorePdfScrollAnchor,
  invalidateReferenceDocuments,
  setOnPdfTargetsResolved,
  setOnPdfSelected,
  pdfPathForMode,
  setOnPdfLoadFailed,
  renderPdfPage,
} from "./pdf.js";
import {
  initParallelPdf,
  parallelPdfSearchState,
  captureParallelScrollAnchor,
  restoreParallelScrollAnchor,
  nearestEntryFromParallelPdfScroll,
  nearestSkipFromParallelPdfScroll,
  parallelSkipTexMatch,
  parallelTexMatch,
  scrollParallelPdfToEntry,
  scrollParallelPdfToSkip,
  setOnParallelPdfLoadFailed,
  parallelDocumentPath,
} from "./parallel-pdf.js";

import { initAppearance, initPdfLayout, renderedPdfPath } from "./appearance.js";
import { lightPdfPath } from "./pdf-theme.js";
import { installChapterPull, type ChapterDirection } from "./chapter-pull.js";

localizeStaticUI();
removeUrlManagedStorage(browserStorage());

const LAYOUT_STORAGE_KEY = "formalization-viewer-layout-v2";
const LINE_NUMBERS_STORAGE_KEY = "formalization-viewer-line-numbers";
const HIGHLIGHTS_STORAGE_KEY = "formalization-viewer-highlights";
const LINKS_STORAGE_KEY = "formalization-viewer-links";
const SYNC_STORAGE_KEY = "formalization-viewer-scroll-sync";
// Passive scrolling navigates continuously, so the address bar and the stored
// session are written from a trailing timer rather than per navigation.
const LOCATION_RECORD_MS = 250;
const RELOAD_POSITION_KEY = "formalization-viewer-reload-position";

interface SourcePosition {
  path: string;
  line: number;
  text: string;
  fraction: number;
  left: number;
}
interface ViewPosition {
  url: string;
  pdfPath: string | null;
  pdf: PdfScrollAnchor | null;
  peer: PdfScrollAnchor | null;
  sources: Partial<Record<"md" | "lean" | "tex", SourcePosition>>;
}

function captureViewPosition(): ViewPosition {
  const sources: ViewPosition["sources"] = {};
  for (const kind of ["md", "lean", "tex"] as const) {
    const pane = state.panes[kind];
    const path = state.selectedSources[kind];
    if (!pane || !path || !paneViewportHeight(pane)) continue;
    const lines = pane.querySelectorAll<HTMLElement>(".line");
    if (!lines.length) continue;
    const top = paneViewportTop(pane);
    let first = 0;
    let last = lines.length - 1;
    while (first < last) {
      const middle = Math.floor((first + last) / 2);
      if (lines[middle].getBoundingClientRect().bottom <= top) first = middle + 1;
      else last = middle;
    }
    const rect = lines[first].getBoundingClientRect();
    sources[kind] = {
      path,
      line: first,
      text: lines[first].textContent ?? "",
      fraction: (top - rect.top) / Math.max(1, rect.height),
      left: pane.scrollLeft,
    };
  }
  return {
    url: window.location.href,
    pdfPath: state.pdf.path,
    pdf: paneViewportHeight(els.pdfViewer) ? capturePdfScrollAnchor() : null,
    peer: paneViewportHeight(els.pdfPeerViewer) ? captureParallelScrollAnchor() : null,
    sources,
  };
}

function restoreViewPosition(position: ViewPosition): void {
  for (const kind of ["md", "lean", "tex"] as const) {
    const saved = position.sources?.[kind];
    const pane = state.panes[kind];
    if (
      !saved ||
      saved.path !== state.selectedSources[kind] ||
      !pane?.clientHeight ||
      !Number.isFinite(saved.line) ||
      !Number.isFinite(saved.fraction)
    )
      continue;
    const lines = pane.querySelectorAll<HTMLElement>(".line");
    const at = Math.min(Math.max(0, Math.floor(saved.line)), lines.length - 1);
    let line = lines[at];
    // Insertions before the reading line should move its number, not the
    // reader. Match the same source line near its old position when possible.
    if (line?.textContent !== saved.text) {
      for (let distance = 1; distance <= 500; distance += 1) {
        const match = [lines[at - distance], lines[at + distance]].find(
          (candidate) => candidate && candidate.textContent === saved.text,
        );
        if (match) {
          line = match;
          break;
        }
      }
    }
    if (!line) continue;
    const rect = line.getBoundingClientRect();
    suppressPaneSync(kind);
    scrollPane(pane, {
      top: paneScrollTop(pane) + rect.top - paneViewportTop(pane) + saved.fraction * rect.height,
      left: Number.isFinite(saved.left) ? saved.left : 0,
      behavior: "auto",
    });
  }
  if (position.pdfPath === state.pdf.path) {
    if (position.pdf && Number.isFinite(position.pdf.pageNumber) && Number.isFinite(position.pdf.fraction))
      restorePdfScrollAnchor(position.pdf);
    if (position.peer && Number.isFinite(position.peer.pageNumber) && Number.isFinite(position.peer.fraction))
      restoreParallelScrollAnchor(position.peer);
  }
}

function saveReloadPosition(): void {
  if (document.body.dataset.viewerReady !== "1") return;
  flushLocation();
  try {
    sessionStorage.setItem(RELOAD_POSITION_KEY, JSON.stringify(captureViewPosition()));
  } catch {
    /* Storage may be disabled. */
  }
}

function reloadPosition(): ViewPosition | null {
  const navigation = performance.getEntriesByType("navigation")[0] as PerformanceNavigationTiming | undefined;
  if (navigation?.type !== "reload") return null;
  try {
    const saved = JSON.parse(sessionStorage.getItem(RELOAD_POSITION_KEY) || "null");
    return saved?.url === window.location.href ? saved : null;
  } catch {
    return null;
  }
}

// Fill the About dialog from the project manifest: name, the build version the
// server/dist stamped in, and the license summary + per-scope breakdown.
function populateAbout(): void {
  els.aboutBook.textContent = project.name || project.dir || "—";
  const version = project.version || {};
  // Label the short hash as a commit; the date is that commit's date (git %cs),
  // not a separate build timestamp. Explicit dirty flag rather than a -dirty
  // suffix glued onto the hash.
  const base = version.rev || (version.describe || "").replace(/-dirty$/, "");
  const dirty = (version.describe || "").endsWith("-dirty");
  const parts = [base ? `commit ${base}` : "", dirty ? "dirty" : "", version.date || ""].filter(Boolean);
  els.aboutVersionText.textContent = parts.length ? parts.join(" · ") : t("unknown");
  if (els.aboutCopy) els.aboutCopy.dataset.copy = version.rev || version.describe || "";

  if (els.aboutRepo) {
    const repo = safeHref(project.repository || "");
    els.aboutRepo.textContent = repo ? repo.replace(/^https?:\/\//, "") : "—";
    if (repo) els.aboutRepo.href = repo;
    else els.aboutRepo.removeAttribute("href");
  }

  const license = project.license || {};
  els.aboutLicenseSummary.textContent = t(license.summary || "");
  const items = (license.items || []).map((item, i) => {
    const scope = escapeHtml(t(item.scope || ""));
    const spdx = escapeHtml(item.spdx || "");
    const name = item.file ? escapeHtml(item.file.split("/").pop() || item.file) : "";
    // Vendored components carry a version and an upstream repository link; the
    // repo's own license scopes (MIT / CC BY 4.0) carry neither.
    const version = item.version ? ` <span class="about-license-version">${escapeHtml(item.version)}</span>` : "";
    const sourceHref = item.source ? safeHref(item.source) : "";
    const source = sourceHref
      ? ` · <a class="about-license-source" href="${escapeHtml(sourceHref)}" target="_blank" rel="noreferrer">${t("repository ↗")}</a>`
      : "";
    // Lead with the thing being licensed (component name / scope); the license
    // is secondary. Consistent across the project's own scopes and the vendored
    // components: "<name> <version> — <SPDX> · repository ↗".
    const head = `<div class="about-license-head"><span class="about-license-name">${scope}</span>${version} — <span class="about-license-spdx">${spdx}</span>${source}</div>`;
    // The license text is inlined in the manifest; the filename below is a
    // disclosure toggle (the triangle implies the action).
    const view = item.text
      ? `<button type="button" class="about-license-view" data-license="${i}" aria-expanded="false">${name}</button>`
      : name
        ? `<div class="about-license-file">${name}</div>`
        : "";
    const pre = item.text
      ? `<pre class="about-license-text" id="about-license-text-${i}" hidden>${escapeHtml(item.text)}</pre>`
      : "";
    return `<li>${head}${view}${pre}</li>`;
  });
  setHTML(els.aboutLicenseList, items.join(""));
}

// The viewer's popups are real popovers / a modal dialog where the platform
// provides them (top layer, light dismiss, focus return); these helpers keep
// the call sites working where the Popover API is unavailable, in which case
// the elements fall back to their `hidden` toggling.
function popoverSupported(el: HTMLElement): boolean {
  return typeof (el as any).showPopover === "function";
}
function showPopover(el: HTMLElement): void {
  if (popoverSupported(el) && !el.matches(":popover-open")) (el as any).showPopover();
}
function hidePopover(el: HTMLElement): void {
  if (popoverSupported(el) && el.matches(":popover-open")) (el as any).hidePopover();
}
function closeSettingsMenu(): void {
  if (popoverSupported(els.settingsMenu)) hidePopover(els.settingsMenu);
  else {
    els.settingsMenu.hidden = true;
    els.settingsToggle.setAttribute("aria-expanded", "false");
  }
}

function openAbout(): void {
  populateAbout();
  // Close the menu the About item lives in, then show the dialog. showModal
  // focuses the first control (the close button) and returns focus to the
  // invoker on close, replacing the hand-rolled trap/restore.
  closeSettingsMenu();
  els.aboutOverlay.showModal();
}

function closeAbout(): void {
  els.aboutOverlay.close();
}

function swapLeaves(a: string, b: string): void {
  let leafA: LayoutNode | null = null;
  let leafB: LayoutNode | null = null;
  eachLeaf(state.layout.tree, (leaf) => {
    if (leaf.pane === a) leafA = leaf;
    if (leaf.pane === b) leafB = leaf;
  });
  if (leafA && leafB) {
    (leafA as any).pane = b;
    (leafB as any).pane = a;
  }
}

function splitAt(dragged: string, target: string, zone: string): void {
  let tree = removeLeaf(state.layout.tree, dragged);
  const dir: "row" | "col" = zone === "left" || zone === "right" ? "row" : "col";
  const draggedFirst = zone === "left" || zone === "top";
  const newSplit: LayoutNode = {
    dir,
    children: draggedFirst ? [{ pane: dragged }, { pane: target }] : [{ pane: target }, { pane: dragged }],
    ratios: [1, 1],
  };
  tree = replaceLeaf(tree, target, newSplit);
  state.layout.tree = flattenSameDir(tree);
}

function defaultLayoutTree(): LayoutNode | null {
  let tree = defaultTree();
  if (project.parallelPdf)
    tree = replaceLeaf(tree, "pdf", {
      dir: "row",
      children: [{ pane: "pdf" }, { pane: "pdf-peer" }],
      ratios: [1, 1],
    });
  return flattenSameDir(tree);
}

function layoutDefaults(): Record<string, string> {
  return { [LAYOUT_STORAGE_KEY]: JSON.stringify({ tree: defaultLayoutTree() }) };
}

function loadLayout(): void {
  let stored: any = {};
  try {
    stored = JSON.parse(readPreference(LAYOUT_STORAGE_KEY) || "{}");
  } catch (_error) {
    stored = {};
  }
  let tree = validateTree(stored.tree) || defaultLayoutTree();
  if (!project.parallelPdf) tree = removeLeaf(tree, "pdf-peer");
  state.layout = { tree: flattenSameDir(tree) };
  if (typeof stored.maximized === "string" && treeLeaves(tree).includes(stored.maximized))
    state.layout.maximized = stored.maximized;
  else {
    const params = new URLSearchParams(window.location.search);
    if (!params.has("layout") && !params.has("focus") && window.matchMedia("(max-width: 767px)").matches)
      state.layout.maximized = "pdf";
  }
}

function saveLayout(): void {
  writePreference(LAYOUT_STORAGE_KEY, JSON.stringify(state.layout), layoutDefaults()[LAYOUT_STORAGE_KEY]);
}

function loadLineNumbers(): void {
  state.lineNumbers = readPreference(LINE_NUMBERS_STORAGE_KEY) === "on";
}

// Scroll sync defaults to on, so only an explicit "off" is stored.
function loadSync(): void {
  state.sync = readPreference(SYNC_STORAGE_KEY) !== "off";
}

// --- Reading position: address bar + stored session -------------------------
// The position lives in the URL (so a copied link reopens it) and in the
// project's stored session (so a reload — including the automatic one after a
// viewer rebuild — resumes where the reader was). The session additionally
// holds the documents the panes were showing; the pane layout and the view
// toggles stay in their own book-independent keys above.

// Set once the manifest has loaded, since the session is scoped to the mount.
let storeKey = sessionKey("");

function storedSession(): ViewerSession {
  return readSession(browserStorage(), storeKey);
}

function recordSession(patch: ViewerSession): void {
  writeSession(browserStorage(), storeKey, patch);
}

let locationTimer: ReturnType<typeof setTimeout> | null = null;

function flushLocation(): void {
  const location = state.location;
  const marker = location.kind === "entry" ? markerId(state.entries, location.index) || null : null;
  const skip = location.kind === "skip" ? location.key : null;
  const search = withSharedPreferences(withLocationParams(window.location.search, { marker, skip }), {});
  if (search !== window.location.search) {
    try {
      window.history.replaceState(null, "", `${window.location.pathname}${search}${window.location.hash}`);
    } catch (_error) {
      // A static export opened straight off disk (file://) refuses history
      // writes; the session below still records the position.
    }
  }
  // Navigation selects the sources the position lives in, so store them with it
  // and the stored session always describes one coherent view.
  recordSession({
    marker,
    skip,
    skipProgress: location.kind === "skip" ? location.progress : null,
    md: state.selectedSources.md,
    lean: state.selectedSources.lean,
  });
}

function recordLocation(): void {
  if (locationTimer) return;
  locationTimer = setTimeout(() => {
    locationTimer = null;
    flushLocation();
  }, LOCATION_RECORD_MS);
}

// Where to open: an explicit ?marker=/?skip= link wins, then the stored session,
// then the first marker. A link whose marker the book no longer has falls
// through to the stored position with a console warning rather than silently
// landing somewhere else.
async function navigateToInitialLocation(): Promise<void> {
  const linked = readLocationParams(window.location.search);
  if (linked.marker) {
    const index = markerIndex(state.entries, linked.marker);
    if (index !== null) return setActive(index, null, true);
    reportError(new Error(`?marker=${linked.marker} matches no marker in this book; using the stored position`));
  } else if (linked.skip) {
    if (state.skips?.some((skip: any) => skip.key === linked.skip)) {
      return setSkipActive({ key: linked.skip, progress: 0 }, null, true);
    }
    reportError(new Error(`?skip=${linked.skip} matches no skipped region in this book; using the stored position`));
  }
  const session = storedSession();
  if (session.marker) {
    const index = markerIndex(state.entries, session.marker);
    if (index !== null) return setActive(index, null, true);
  } else if (session.skip && state.skips?.some((skip: any) => skip.key === session.skip)) {
    return setSkipActive({ key: session.skip, progress: session.skipProgress ?? 0 }, null, true);
  }
  return setActive(0);
}

// Restore the documents the reader had open, for the panes the navigation above
// did not already point somewhere deliberate: a reader who browsed to a chapter
// that holds no marker gets that chapter back. A ?marker= link is authoritative
// about what to show, so it is left untouched.
async function restoreSessionSources(): Promise<void> {
  if (readLocationParams(window.location.search).marker) return;
  const session = storedSession();
  const pick = (kind: "md" | "lean", stored: string | null | undefined): string | null =>
    stored && stored !== state.selectedSources[kind] && state.fileChoices[kind].includes(stored) ? stored : null;
  const md = pick("md", session.md);
  const lean = pick("lean", session.lean);
  if (!md && !lean) return;
  if (md) state.selectedSources.md = md;
  if (lean) state.selectedSources.lean = lean;
  await renderSelectedSources();
}

// Mark the button whose data-value matches `activeValue` as pressed (the rest
// unpressed); pass null to leave none active. Styling keys off [aria-pressed].
function updateSegmented(group: HTMLElement | null, activeValue: string | null): void {
  if (!group) return;
  for (const btn of Array.from(group.querySelectorAll("button"))) {
    btn.setAttribute("aria-pressed", String((btn as HTMLElement).dataset.value === activeValue));
  }
}

function applyLineNumbers(): void {
  document.body.classList.toggle("show-line-numbers", state.lineNumbers);
  updateSegmented(els.linenumSeg, state.lineNumbers ? "on" : "off");
}

// Preserve an explicit choice from the old per-pane settings until the reader
// chooses a global value: any hidden marker pane means off; any outlined PDF
// pane means on. Unset or malformed preferences retain the existing defaults.
function overlayPreference(key: string, legacyKey: string, defaultOn: boolean, panes: string[]): boolean {
  const value = readPreference(key);
  if (value === "on" || value === "off") return value === "on";
  try {
    const legacy: unknown = JSON.parse(readPreference(legacyKey) || "[]");
    if (Array.isArray(legacy) && legacy.some((pane) => panes.includes(pane))) return !defaultOn;
  } catch (_error) {
    // Ignore damaged stored preferences.
  }
  return defaultOn;
}

function loadMarkHighlights(): void {
  state.markHighlights = overlayPreference(HIGHLIGHTS_STORAGE_KEY, "formalization-viewer-marks-off", true, [
    "pdf",
    "pdf-peer",
    "md",
    "lean",
    "tex",
  ]);
}

function loadLinkHighlights(): void {
  state.linkHighlights = overlayPreference(LINKS_STORAGE_KEY, "formalization-viewer-links-on", false, [
    "pdf",
    "pdf-peer",
  ]);
}

function applyLinkHighlights(): void {
  document.body.classList.toggle("links-on", state.linkHighlights);
  updateSegmented(els.linksSeg, state.linkHighlights ? "on" : "off");
  updateOverlayButtons("links", state.linkHighlights, t("link outlines"));
}

// Hide every pane's booklink visuals together; keep their spans for scroll sync
// and navigation through the marker palette.
function updateMarkKeyboardAccess(): void {
  for (const mark of document.querySelectorAll<HTMLElement>("[data-mark-control]")) {
    mark.tabIndex = state.markHighlights ? 0 : -1;
    if (state.markHighlights) mark.setAttribute("role", "button");
    else mark.removeAttribute("role");
  }
}

function applyMarkHighlights(): void {
  updateMarkKeyboardAccess();
  document.body.classList.toggle("marks-off", !state.markHighlights);
  updateSegmented(els.highlightsSeg, state.markHighlights ? "on" : "off");
  updateOverlayButtons("highlights", state.markHighlights, "highlights");
}

function updateOverlayButtons(kind: string, enabled: boolean, label: string): void {
  for (const button of document.querySelectorAll<HTMLButtonElement>(`.overlay-toggle[data-overlay="${kind}"]`)) {
    button.setAttribute("aria-pressed", String(enabled));
    button.title = enabled ? t("Hide {0}", t(label)) : t("Show {0}", t(label));
    button.setAttribute("aria-label", button.title);
  }
}

function setMarkHighlights(enabled: boolean): void {
  state.markHighlights = enabled;
  writePreference(HIGHLIGHTS_STORAGE_KEY, enabled ? "on" : "off");
  applyMarkHighlights();
}

function setLinkHighlights(enabled: boolean): void {
  state.linkHighlights = enabled;
  writePreference(LINKS_STORAGE_KEY, enabled ? "on" : "off");
  applyLinkHighlights();
}

function addOverlayButtons(container: Element, before: Element): void {
  const icons = {
    highlights: "M4 10l6-6 3 3-6 6H4ZM9 3l2-2 4 4-2 2M2 15h8",
    links: "M7 5l1.5-1.5a3 3 0 0 1 4.25 4.25L11 9M9 11l-1.5 1.5a3 3 0 0 1-4.25-4.25L5 7M6 10l4-4",
  };
  for (const kind of ["highlights", "links"] as const) {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "icon-button overlay-toggle";
    button.dataset.overlay = kind;
    setHTML(
      button,
      `<svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true" focusable="false"><path d="${icons[kind]}" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/></svg>`,
    );
    button.addEventListener("click", (event) => {
      event.stopPropagation();
      if (kind === "highlights") setMarkHighlights(!state.markHighlights);
      else setLinkHighlights(!state.linkHighlights);
    });
    button.addEventListener("dragstart", (event) => {
      event.preventDefault();
      event.stopPropagation();
    });
    container.insertBefore(button, before);
  }
}

function checkedPaneNames(): string[] {
  return els.paneChecks.filter((input) => input.checked).map((input) => input.value);
}

function syncPaneChecksFromLayout(): void {
  const visible = new Set(treeLeaves(state.layout.tree));
  for (const input of els.paneChecks) {
    input.checked = visible.has(input.value);
    input.disabled = false;
  }
}

function syncLayoutSelect(): void {
  if (!els.layoutSeg) return;
  const kind = treeKind(state.layout.tree);
  // A custom (dragged) arrangement is "others" — leave both presets unpressed.
  updateSegmented(els.layoutSeg, kind === "columns" || kind === "rows" ? kind : null);
  const disabled = treeLeaves(state.layout.tree).length < 2;
  for (const btn of Array.from(els.layoutSeg.querySelectorAll("button"))) {
    (btn as HTMLButtonElement).disabled = disabled;
  }
}

function applyPaneCheckboxes(): void {
  const checked = new Set(checkedPaneNames());
  const current = treeLeaves(state.layout.tree);
  delete state.layout.maximized;
  maximizedPosition = null;
  let tree = state.layout.tree;
  for (const pane of current) {
    if (!checked.has(pane)) tree = removeLeaf(tree, pane);
  }
  for (const pane of checked) {
    if (!current.includes(pane)) tree = addLeaf(tree, pane);
  }
  state.layout.tree = tree;
  saveLayout();
  applyPaneLayout();
  syncCurrentLocation().catch(reportError);
}

function setLayoutKind(kind: string): void {
  const panes = treeLeaves(state.layout.tree);
  if (kind === "columns") state.layout.tree = makeSplit("row", panes);
  else if (kind === "rows") state.layout.tree = makeSplit("col", panes);
  else return;
  delete state.layout.maximized;
  maximizedPosition = null;
  saveLayout();
  applyPaneLayout();
  syncCurrentLocation().catch(reportError);
}

function paneParking(): HTMLElement {
  let parking = document.getElementById("pane-parking");
  if (!parking) {
    parking = document.createElement("div");
    parking.id = "pane-parking";
    parking.hidden = true;
    parking.style.display = "none";
  }
  return parking;
}

// Live flex sizing for the (interleaved with splitters) children of a split.
function applyPaneLayout(): void {
  document.body.classList.toggle("is-pane-maximized", !!state.layout.maximized);
  document.documentElement.classList.toggle("is-pane-maximized", !!state.layout.maximized);
  const name = state.layout.maximized;
  const focusedSearch = document.getElementById("pane-search-focused");
  if (focusedSearch) focusedSearch.hidden = !["md", "lean", "tex", "pdf", "pdf-peer"].includes(name ?? "");
  setDocumentPane(
    name === "pdf"
      ? els.pdfViewer
      : name === "pdf-peer"
        ? els.pdfPeerViewer
        : name === "infoview"
          ? els.infoviewBody
          : name
            ? state.panes[name]
            : null,
  );
  const visible = new Set(visiblePaneNames());
  const workspace = els.workspace;
  const parking = paneParking();
  for (const name of PANE_NAMES) {
    const section = state.paneSections?.[name];
    if (section && section.parentNode) section.parentNode.removeChild(section);
  }
  setHTML(workspace, "");
  workspace.append(parking);
  for (const name of PANE_NAMES) {
    if (!visible.has(name)) {
      const section = state.paneSections?.[name];
      if (section) {
        section.hidden = true;
        section.style.display = "none";
        parking.append(section);
      }
    }
  }
  const displayTree = state.layout.maximized ? { pane: state.layout.maximized } : state.layout.tree;
  const root = buildLayoutNode(displayTree, { save: saveLayout, refresh: refreshPdfLayoutGeometry });
  if (root) {
    // A surviving leaf may still carry its former sibling share (e.g. 0.5).
    // The root always owns the whole workspace, irrespective of old splits.
    root.style.flex = "1 1 0";
    workspace.append(root);
  }
  workspace.append(dropOverlayElement());
  edgeZoneElements().forEach((zone) => workspace.append(zone));
  syncLayoutSelect();
  syncPaneChecksFromLayout();
  updateMaximizeButtons();
  refreshPdfLayoutGeometry();
  // Source panes rewrap at their new size, so their rail ticks must be
  // recomputed; defer a frame so flex layout has settled.
  window.requestAnimationFrame(() => updateAllMarkRails());
  if (paneContentEnabled) void ensureVisiblePaneContent().catch(reportError);
  document.dispatchEvent(new Event("pane-layout-changed"));
}

let maximizedPosition: ViewPosition | null = null;
let maximizeRevision = 0;
const MAXIMIZE_ICON =
  '<svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true" focusable="false"><path d="M6 2H2v4m8-4h4v4M2 10v4h4m8-4v4h-4" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/></svg>';
const CLOSE_ICON =
  '<svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true" focusable="false"><path d="M4 4l8 8M12 4l-8 8" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round"/></svg>';
const RESTORE_ICON =
  '<svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true" focusable="false"><path d="M3 6h3V3m4 0v3h3M3 10h3v3m4 0v-3h3" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/></svg>';

function updateMaximizeButtons(): void {
  els.paneRestore.hidden = !state.layout.maximized;
  els.paneTools.hidden = !state.layout.maximized;
  // Keep at least one pane open; the menu's pane checkboxes can reopen others.
  const lastPane = treeLeaves(state.layout.tree).length < 2;
  for (const button of document.querySelectorAll<HTMLButtonElement>(".pane-close")) {
    button.disabled = lastPane;
    button.title = lastPane ? t("The last pane cannot be closed") : t("Close pane");
  }
  for (const name of PANE_NAMES) {
    const button = state.paneSections?.[name]?.querySelector<HTMLButtonElement>(".pane-maximize");
    if (!button) continue;
    const maximized = state.layout.maximized === name;
    const label = maximized ? t("Restore pane layout") : t("Maximize pane");
    button.setAttribute("aria-label", label);
    button.setAttribute("aria-pressed", String(maximized));
    button.title = label;
    setHTML(button, maximized ? RESTORE_ICON : MAXIMIZE_ICON);
  }
}

function togglePaneMaximize(name: string): void {
  const revision = ++maximizeRevision;
  let position = captureViewPosition();
  if (state.layout.maximized === name) {
    const previous = maximizedPosition;
    const samePdf = previous?.pdfPath === position.pdfPath;
    position = {
      ...position,
      sources: { ...previous?.sources, ...position.sources },
      pdf: position.pdf ?? (samePdf ? (previous?.pdf ?? null) : null),
      peer: position.peer ?? (samePdf ? (previous?.peer ?? null) : null),
    };
    delete state.layout.maximized;
    maximizedPosition = null;
  } else {
    maximizedPosition ??= position;
    state.layout.maximized = name;
  }
  saveLayout();
  applyPaneLayout();
  const settle = () =>
    window.requestAnimationFrame(() => {
      if (revision !== maximizeRevision) return;
      restoreViewPosition(position);
      const button = state.layout.maximized
        ? els.paneRestore
        : state.paneSections?.[name]?.querySelector<HTMLButtonElement>(".pane-maximize");
      button?.focus({ preventScroll: true });
    });
  settle();
}

function closePane(name: string): void {
  if (treeLeaves(state.layout.tree).length < 2) return;
  const input = els.paneChecks.find((check) => check.value === name);
  if (!input) return;
  input.checked = false;
  applyPaneCheckboxes();
}

function paneCloseButton(name: string): HTMLButtonElement {
  const button = document.createElement("button");
  button.type = "button";
  button.className = "icon-button pane-close";
  button.setAttribute("aria-label", t("Close pane"));
  button.title = t("Close pane");
  setHTML(button, CLOSE_ICON);
  button.addEventListener("click", (event) => {
    event.stopPropagation();
    closePane(name);
  });
  button.addEventListener("dragstart", (event) => {
    event.preventDefault();
    event.stopPropagation();
  });
  return button;
}

function wirePaneMaximize(): void {
  setHTML(els.paneRestore, RESTORE_ICON);
  addOverlayButtons(els.paneTools, els.paneRestore);
  els.paneRestore.addEventListener("click", () => {
    if (state.layout.maximized) togglePaneMaximize(state.layout.maximized);
  });
  for (const name of PANE_NAMES) {
    const header = state.paneSections?.[name]?.querySelector(".pane-header");
    if (!header) continue;
    let actions = header.querySelector(".pane-actions");
    if (!actions) {
      actions = document.createElement("div");
      actions.className = "pane-actions";
      header.append(actions);
    }
    const button = document.createElement("button");
    button.type = "button";
    button.className = "icon-button pane-maximize";
    button.addEventListener("click", (event) => {
      event.stopPropagation();
      togglePaneMaximize(name);
    });
    button.addEventListener("dragstart", (event) => {
      event.preventDefault();
      event.stopPropagation();
    });
    actions.append(button);
    if (name === "pdf" || name === "pdf-peer") addOverlayButtons(actions, button);
    actions.append(paneCloseButton(name));
  }
  applyMarkHighlights();
  applyLinkHighlights();
  updateMaximizeButtons();
}

function applyResizeFromPointer(event: MouseEvent): void {
  if (!state.resizing) return;
  const { node, leftIndex, container } = state.resizing;
  if (!container) return;
  const rect = container.getBoundingClientRect();
  const pointer =
    node.dir === "row"
      ? Math.min(0.99, Math.max(0.01, (event.clientX - rect.left) / Math.max(1, rect.width)))
      : Math.min(0.99, Math.max(0.01, (event.clientY - rect.top) / Math.max(1, rect.height)));
  node.ratios = resizePair(node.ratios ?? [], leftIndex, pointer);
  applySplitFlex(container, node);
  refreshPdfLayoutGeometry();
}

// ===== Drag and drop: header = swap, edge = split where the pane lands =====

function dropOverlayElement(): HTMLElement {
  if (!state.dropOverlay) {
    const overlay = document.createElement("div");
    overlay.className = "drop-overlay";
    overlay.hidden = true;
    state.dropOverlay = overlay;
  }
  return state.dropOverlay;
}

function dropZone(pane: HTMLElement, event: MouseEvent): string {
  const header = pane.querySelector(".pane-header");
  if (header && event.clientY <= header.getBoundingClientRect().bottom) return "swap";
  const rect = pane.getBoundingClientRect();
  const x = (event.clientX - rect.left) / Math.max(1, rect.width);
  const y = (event.clientY - rect.top) / Math.max(1, rect.height);
  const edges: [string, number][] = [
    ["left", x],
    ["right", 1 - x],
    ["top", y],
    ["bottom", 1 - y],
  ];
  edges.sort((a, b) => a[1] - b[1]);
  return edges[0][0];
}

function showDropOverlay(pane: HTMLElement, zone: string): void {
  const overlay = dropOverlayElement();
  const rect = pane.getBoundingClientRect();
  const ws = els.workspace.getBoundingClientRect();
  let left = rect.left - ws.left;
  let top = rect.top - ws.top;
  let width = rect.width;
  let height = rect.height;
  if (zone === "left") width /= 2;
  else if (zone === "right") {
    left += width / 2;
    width /= 2;
  } else if (zone === "top") height /= 2;
  else if (zone === "bottom") {
    top += height / 2;
    height /= 2;
  }
  overlay.dataset.zone = zone;
  Object.assign(overlay.style, { left: `${left}px`, top: `${top}px`, width: `${width}px`, height: `${height}px` });
  overlay.hidden = false;
}

function hideDropOverlay(): void {
  if (state.dropOverlay) state.dropOverlay.hidden = true;
}

function applyDrop(dragged: string | null, target: string, zone: string): void {
  if (!dragged || dragged === target) return;
  if (zone === "swap") swapLeaves(dragged, target);
  else splitAt(dragged, target, zone);
  saveLayout();
  applyPaneLayout();
  syncCurrentLocation().catch(reportError);
}

// ===== Dock-to-edge: drop on a window border to split the whole layout =====

const WORKSPACE_EDGES = ["top", "bottom", "left", "right"];

function edgeZoneElements(): HTMLElement[] {
  if (state.edgeZones) return state.edgeZones;
  state.edgeZones = WORKSPACE_EDGES.map((edge) => {
    const zone = document.createElement("div");
    zone.className = `edge-zone edge-zone-${edge}`;
    zone.addEventListener("dragover", (event) => {
      if (!state.dragPane) return;
      event.preventDefault();
      if (event.dataTransfer) event.dataTransfer.dropEffect = "move";
      showRootOverlay(edge);
    });
    zone.addEventListener("dragleave", () => hideDropOverlay());
    zone.addEventListener("drop", (event) => {
      event.preventDefault();
      const dragged = event.dataTransfer?.getData("text/plain") || state.dragPane;
      hideDropOverlay();
      if (dragged) dockToRoot(dragged, edge);
    });
    return zone;
  });
  return state.edgeZones;
}

function showRootOverlay(edge: string): void {
  const overlay = dropOverlayElement();
  const pad = 8;
  const innerWidth = els.workspace.clientWidth - pad * 2;
  const innerHeight = els.workspace.clientHeight - pad * 2;
  const slots = visiblePaneNames().length + 1;
  let left = pad;
  let top = pad;
  let width = innerWidth;
  let height = innerHeight;
  if (edge === "left" || edge === "right") width = Math.max(80, innerWidth / slots);
  else height = Math.max(80, innerHeight / slots);
  if (edge === "right") left = pad + innerWidth - width;
  if (edge === "bottom") top = pad + innerHeight - height;
  overlay.dataset.zone = `root-${edge}`;
  Object.assign(overlay.style, { left: `${left}px`, top: `${top}px`, width: `${width}px`, height: `${height}px` });
  overlay.hidden = false;
}

function dockToRoot(dragged: string, edge: string): void {
  const rest = removeLeaf(state.layout.tree, dragged);
  const leaf: LayoutNode = { pane: dragged };
  if (!rest) {
    state.layout.tree = leaf;
  } else {
    const dir: "row" | "col" = edge === "left" || edge === "right" ? "row" : "col";
    const draggedFirst = edge === "left" || edge === "top";
    const restWeight = treeLeaves(rest).length || 1;
    state.layout.tree = flattenSameDir({
      dir,
      children: draggedFirst ? [leaf, rest] : [rest, leaf],
      ratios: draggedFirst ? [1, restWeight] : [restWeight, 1],
    });
  }
  saveLayout();
  applyPaneLayout();
  syncCurrentLocation().catch(reportError);
}

// Order the PDF dropdown so the debug render comes first, then everything else.

async function loadText(path: string | null): Promise<string> {
  const response = await fetch(repoUrl(path ?? ""), { cache: "no-store" });
  if (!response.ok) throw new Error(`${path}: HTTP ${response.status}`);
  return response.text();
}

async function loadCachedText(path: string | null): Promise<string> {
  const normalized = repoPath(path);
  // An empty path is "no source selected"; never fetch the mount root for it.
  if (!normalized) return "";
  if (!state.sourceCache.has(normalized)) {
    state.sourceCache.set(normalized, await loadText(path));
  }
  return state.sourceCache.get(normalized) ?? "";
}

const highlightDataPromises = new Map<string, Promise<HighlightData | null>>();

// Precomputed tree-sitter highlight data for one source file, generated on
// the Node side: the live server computes it on demand and a static
// distribution ships it as a file, both under `highlight-cache/<path>.json`.
// Null when unavailable; the pane then renders as plain text.
function loadHighlightData(path: string | null): Promise<HighlightData | null> {
  const normalized = repoPath(path);
  if (!normalized || !languageForPath(normalized)) return Promise.resolve(null);
  if (!highlightDataPromises.has(normalized)) {
    highlightDataPromises.set(
      normalized,
      (async () => {
        try {
          const response = await fetch(repoUrl(`highlight-cache/${normalized}.json`), { cache: "no-store" });
          if (!response.ok) return null;
          return parseHighlightData(await response.json());
        } catch {
          return null;
        }
      })(),
    );
  }
  return highlightDataPromises.get(normalized)!;
}

async function loadCachedHighlights(path: string | null): Promise<any[]> {
  const normalized = repoPath(path);
  if (!languageForPath(normalized)) return [];
  if (!state.highlightCache.has(normalized)) {
    const data = await loadHighlightData(path);
    state.highlightCache.set(normalized, data?.spans ?? []);
  }
  return state.highlightCache.get(normalized) ?? [];
}

// Ranges of `/-@ … -/` machine-metadata comments to fold (Lean panes only).
async function loadCachedLeanFolds(path: string | null): Promise<any[]> {
  const normalized = repoPath(path);
  if (languageForPath(normalized) !== "lean") return [];
  if (!state.foldCache.has(normalized)) {
    const data = await loadHighlightData(path);
    state.foldCache.set(normalized, data?.folds ?? []);
  }
  return state.foldCache.get(normalized) ?? [];
}

function uniquePaths(paths: (string | null | undefined)[]): string[] {
  const seen: Set<string> = new Set();
  const result: string[] = [];
  for (const path of paths) {
    const normalized = repoPath(path);
    if (!normalized || seen.has(normalized)) continue;
    seen.add(normalized);
    result.push(normalized);
  }
  return result;
}

async function mdChoices(map: any): Promise<string[]> {
  const mappedSources = (map.entries || []).map((entry: any) => entry.match?.source);
  try {
    const response = await fetch(repoUrl(project.bookManifest ?? ""), { cache: "no-store" });
    if (response.ok) {
      const manifest = await response.json();
      return uniquePaths([manifest.source, ...(manifest.chapters || []), ...mappedSources]);
    }
  } catch (_error) {
    // Fall back to source-map paths below.
  }
  return uniquePaths([project.book, ...mappedSources]);
}

function pascalCaseStem(stem: string): string {
  const acronyms = new Map([
    ["dst", "DST"],
    ["tte", "TTE"],
    ["souslin", "Suslin"],
  ]);
  return stem
    .split("-")
    .filter(Boolean)
    .map((part) => acronyms.get(part) || part.slice(0, 1).toUpperCase() + part.slice(1))
    .join("");
}

function derivedLeanPath(mdPath: string): string | null {
  const normalized = repoPath(mdPath);
  if (normalized === project.book) return project.leanRootModule ?? null;
  const prefix = project.bookSourcePrefix ?? "";
  if (!normalized.startsWith(prefix) || !normalized.endsWith(".md")) return null;
  const stem = normalized.slice(prefix.length, -".md".length);
  return `${project.leanSourcePrefix}${pascalCaseStem(stem)}.lean`;
}

function leanChoices(map: any, mdPaths: string[]): string[] {
  const mappedSources = [map.leanFile, ...(map.entries || []).map((entry: any) => entry.lean?.source)];
  const derivedSources = mdPaths.map(derivedLeanPath);
  return uniquePaths([...mappedSources, ...derivedSources]);
}

function populateFileSelect(select: HTMLSelectElement, paths: string[]): void {
  setHTML(
    select,
    paths
      .map((path) => `<option value="${escapeHtml(path)}">${escapeHtml(path.split("/").pop() || path)}</option>`)
      .join(""),
  );
}

function correspondingLeanForMd(mdPath: string): string | null {
  const selectedMd = repoPath(mdPath);
  const mapped = state.entries.find((entry) => repoPath(entry.match?.source) === selectedMd)?.lean?.source;
  if (mapped) return repoPath(mapped);
  const derived = derivedLeanPath(selectedMd);
  if (derived && state.fileChoices.lean.includes(repoPath(derived))) return repoPath(derived);
  return state.selectedSources.lean;
}

function sourceMatchesSelected(span: any, kind: "md" | "lean" | "tex"): boolean {
  const selected = state.selectedSources[kind];
  if (!selected) return true;
  return repoPath(span?.source) === selected;
}

let renderGeneration = 0;
let paneContentEnabled = false;
let infoviewStarted = false;
const renderedSources: Partial<Record<"md" | "lean" | "tex", string | null>> = {};

function startVisibleInfoview(): void {
  const visible = new Set(visiblePaneNames());
  if ((visible.has("lean") || visible.has("infoview")) && !infoviewStarted) {
    infoviewStarted = true;
    void connectInfoview().catch(reportError);
  }
}

async function ensureVisiblePaneContent(): Promise<void> {
  const visible = new Set(visiblePaneNames());
  startVisibleInfoview();
  const work: Promise<unknown>[] = [];
  if (visible.has("pdf") && state.pdf.path && state.pdf.deferred)
    work.push(setPdf(state.pdf.path, { preserveScroll: true }));
  if (visible.has("pdf-peer") && (peerDirty || peerPdfDoc()?.url !== peerLoadedUrl)) loadPeerPdf();
  if (
    ["md", "lean", "tex"].some(
      (kind) =>
        visible.has(kind) &&
        renderedSources[kind as "md" | "lean" | "tex"] !== state.selectedSources[kind as "md" | "lean" | "tex"],
    )
  )
    work.push(renderSelectedSources().then(() => syncCurrentLocation()));
  await Promise.all(work);
}

async function renderSelectedSources(): Promise<void> {
  const generation = ++renderGeneration;
  const selected = { ...state.selectedSources };
  const visible = new Set(visiblePaneNames());
  const kinds = (["md", "lean", "tex"] as const).filter((kind) => visible.has(kind));
  const needed = visible.has("infoview") && !kinds.includes("lean") ? [...kinds, "lean" as const] : kinds;
  if (!needed.length) return;
  startupDetail("sources", t("Loading visible source documents…"));
  state.sources ??= { md: "", lean: "", tex: "" };
  els.mdSelect.value = selected.md ?? "";
  els.leanSelect.value = selected.lean ?? "";
  if (els.texMeta) els.texMeta.textContent = displayPath(selected.tex);
  await Promise.all(
    needed.map(async (kind) => {
      if (visible.has(kind))
        paneLoadStatus(
          state.panes[kind],
          t("Loading {0}…", kind === "md" ? "Markdown" : kind === "lean" ? "Lean" : "TeX"),
        );
      const text = await loadCachedText(selected[kind]).catch(() => "");
      if (generation !== renderGeneration) return;
      state.sources![kind] = text;
      if (kind === "lean") syncLeanDocument();
      if (!visible.has(kind)) return;
      const highlights = kind === "tex" ? [] : await loadCachedHighlights(selected[kind]);
      const folds = kind === "lean" ? await loadCachedLeanFolds(selected.lean) : [];
      if (generation !== renderGeneration || !visiblePaneNames().includes(kind)) return;
      renderSource(
        state.panes[kind],
        text,
        collectSpans(kind),
        kind,
        highlights,
        folds,
        kind === "lean" ? "utf16" : "codepoint",
        kind === "md" ? collectSkipSpans() : [],
      );
      renderedSources[kind] = selected[kind];
      paneLoadStatus(state.panes[kind], null);
      applyActiveState();
      updateMarkRail(kind);
    }),
  );
  if (generation !== renderGeneration) return;
  refreshCorrespondence();
  refreshFormulaOverlays();
  if (visible.has("infoview")) renderInfoview();
}

async function syncSelectedSourcesForEntry(entry: any): Promise<boolean> {
  const next = {
    md: repoPath(entry.match?.source) || state.selectedSources.md,
    lean: repoPath(entry.lean?.source) || state.selectedSources.lean,
    tex: repoPath(entry.texMatch?.source) || state.selectedSources.tex,
  };
  const changed =
    next.md !== state.selectedSources.md ||
    next.lean !== state.selectedSources.lean ||
    next.tex !== state.selectedSources.tex;
  if (!changed) return false;

  state.selectedSources = next;
  await renderSelectedSources();
  return true;
}

interface MarkerInfo {
  title: string; // plain-text primary label (for search / fallback)
  titleHtml?: string;
  titleSource: string; // the title's TeX source, rendered via KaTeX for display
  id: string; // Lean declaration name (muted secondary)
  kind: string; // "prose" | "statement" — shown as a chip
  snippet: string; // one-line prose excerpt, only when there's no real title
}

// \termdefine{term} / \termdefineas{term}{display}: capture group 1 is the
// canonical term, group 2 the optional display form. Non-global so it works
// with String.match for capture groups; stripTermDefine builds a global copy.
const TERM_DEFINE_RE = /\\termdefine(?:as)?\{([^}]*)\}(?:\{([^}]*)\})?/;

// Flatten term macros to their printed words (display form if present, else the
// term). Shared by every prose/title cleaner so the pattern lives in one place.
function stripTermDefine(s: string): string {
  return s.replace(new RegExp(TERM_DEFINE_RE, "g"), (_m, a, b) => b || a);
}

// Strip the common TeX so an excerpt reads as prose: \termdefine{t}/{display}
// becomes its term, \cmd{arg} -> arg, $math$ -> math, bare \cmd dropped.
function cleanProse(s: string): string {
  return stripTermDefine(markerProseSource(s))
    .replace(/§\{[^}]*\}/g, "") // §{sec:...} section references
    .replace(/\\[a-zA-Z]+\*?\{([^}]*)\}/g, "$1") // \cmd{arg} -> arg
    .replace(/\$([^$]*)\$/g, "$1") // $math$ -> math
    .replace(/\\[a-zA-Z]+\*?/g, " ") // bare \commands
    .replace(/[{}$^_~\\]/g, " ") // leftover TeX punctuation
    .replace(/\s+([,.;:])/g, "$1")
    .replace(/\s+/g, " ")
    .trim();
}

function sentenceCase(s: string): string {
  return s ? s.charAt(0).toUpperCase() + s.slice(1) : s;
}

// Clean a TEXT segment (outside $...$): term macros -> their term, section refs
// and other bare \commands dropped. Math is handled separately by KaTeX.
function cleanTextSegment(s: string): string {
  return stripTermDefine(markerProseSource(s))
    .replace(/§\{[^}]*\}/g, "")
    .replace(/\\[a-zA-Z]+\*?\{([^}]*)\}/g, "$1")
    .replace(/\\[a-zA-Z]+\*?/g, "")
    .replace(/[{}~]/g, "")
    .replace(/\s+/g, " ");
}

// Render a title/excerpt's TeX source to HTML: text via cleanTextSegment
// (escaped), $...$ via KaTeX with the book's macros. Falls back to plain text
// before KaTeX has loaded or on a render error.
function renderMath(source: string): string {
  return splitMathSource(source)
    .map((part) => {
      if (part.kind === "text") return escapeHtml(cleanTextSegment(part.source));
      return project.fixedMath?.[part.source] ?? escapeHtml(part.source);
    })
    .join("")
    .trim();
}

// markerInfo is pure in (entry, index) and runs several regexes; the marker
// palette and rail recompute it for every entry on each keystroke/redraw, so
// cache by index. Cleared whenever the entry list is rebuilt (reloadMap).
const markerInfoCache = new Map<number, MarkerInfo>();

function markerInfo(entry: any, index: number): MarkerInfo {
  const cached = markerInfoCache.get(index);
  if (cached) return cached;
  const info = computeMarkerInfo(entry, index);
  markerInfoCache.set(index, info);
  return info;
}

function computeMarkerInfo(entry: any, index: number): MarkerInfo {
  const lean = entry.lean || {};
  const link = entry.booklink || {};
  const id = String(lean.declName || "");
  const rawExcerpt = link.excerpt ? markerProseSource(String(link.excerpt)) : "";
  // The TeX source we render (math kept): the human title, else the defined
  // term's display form, else the excerpt's opening clause.
  let titleSource = String(link.title || "").trim();
  if (!titleSource && rawExcerpt) {
    const term = rawExcerpt.match(TERM_DEFINE_RE);
    titleSource = term ? (term[2] || term[1]).trim() : openingProseClause(rawExcerpt);
  }
  // Plain text for search/fallback: prefer the canonical term, sort key dropped.
  let title = link.title ? cleanProse(String(link.title)) : "";
  if (!title && rawExcerpt) {
    const term = rawExcerpt.match(TERM_DEFINE_RE);
    title = term
      ? sentenceCase(cleanProse(term[1].split("@")[0]))
      : sentenceCase(cleanProse(openingProseClause(rawExcerpt)).split(" ").slice(0, 8).join(" "));
  }
  if (!title) title = id || `Marker ${index + 1}`;
  if (!titleSource) titleSource = title;
  const prose = cleanProse(rawExcerpt);
  const snippet = !link.title && prose ? prose : "";
  return { title, titleSource, id, kind: String(link.target || ""), snippet };
}

// --- Marker combobox ("Jump to marker" palette) -----------------------------
let markerFilter = "";
let markerHighlight = -1; // position within the currently filtered list

let markerFilterCache: { entries: any[]; query: string; indices: number[] } | null = null;
function filteredMarkerIndices(): number[] {
  const q = markerFilter.trim().toLowerCase();
  if (markerFilterCache?.entries === state.entries && markerFilterCache.query === q) return markerFilterCache.indices;
  const all = state.entries.map((_entry, i) => i);
  const indices = !q
    ? all
    : all.filter((i) => {
        const m = markerInfo(state.entries[i], i);
        return `${m.title} ${m.id} ${m.kind} ${m.snippet}`.toLowerCase().includes(q);
      });
  markerFilterCache = { entries: state.entries, query: q, indices };
  return indices;
}

let markerWindow: { indices: number[]; start: number; end: number } | null = null;
let markerScrollFrame = 0;
function renderMarkerList(focusPosition?: number): void {
  const filtered = filteredMarkerIndices();
  if (markerHighlight < 0 || markerHighlight >= filtered.length) markerHighlight = 0;
  const height = els.markerList.clientHeight || Math.max(52, Math.min(320, window.innerHeight * 0.45 - 80));
  const requested =
    focusPosition === undefined
      ? els.markerList.scrollTop
      : Math.max(0, focusPosition * MARKER_ROW_HEIGHT - height / 2);
  const rowWindow = listWindow(filtered.length, requested, height);
  const changed =
    focusPosition !== undefined ||
    markerWindow?.indices !== filtered ||
    markerWindow.start !== rowWindow.start ||
    markerWindow.end !== rowWindow.end;
  if (changed) {
    markerWindow = { indices: filtered, start: rowWindow.start, end: rowWindow.end };
    els.markerList.style.setProperty("--marker-row-height", `${MARKER_ROW_HEIGHT}px`);
    const spacer = (height: number) => `<li role="presentation" aria-hidden="true" style="height:${height}px"></li>`;
    setHTML(
      els.markerList,
      filtered.length
        ? spacer(rowWindow.before) +
            filtered
              .slice(rowWindow.start, rowWindow.end)
              .map((i, offset) => {
                const pos = rowWindow.start + offset;
                const m = markerInfo(state.entries[i], i);
                const selected = i === state.activeIndex;
                const chip = m.kind
                  ? ` <span class="marker-chip" data-kind="${escapeHtml(m.kind)}">${escapeHtml(m.kind)}</span>`
                  : "";
                const id = m.id && m.id !== m.title ? `<span class="marker-id">${escapeHtml(m.id)}</span>` : "";
                const snip = m.snippet ? `<span class="marker-snip">${escapeHtml(m.snippet)}</span>` : "";
                const meta = id || snip ? `<div class="marker-row-meta">${id}${snip}</div>` : "";
                return `<li class="marker-row${selected ? " is-selected" : ""}${pos === markerHighlight ? " is-highlight" : ""}" id="marker-option-${i}" role="option" aria-selected="${selected}" aria-posinset="${pos + 1}" aria-setsize="${filtered.length}" data-position="${pos}" data-index="${i}"><div class="marker-row-head"><span class="marker-title" title="${escapeHtml(m.title)}">${(m.titleHtml ??= renderMath(m.titleSource))}</span>${chip}</div>${meta}</li>`;
              })
              .join("") +
            spacer(rowWindow.after)
        : `<li class="marker-empty">No markers match “${escapeHtml(markerFilter.trim())}”.</li>`,
    );
    els.markerList.scrollTop = rowWindow.top;
  }
  for (const row of els.markerList.querySelectorAll<HTMLElement>(".marker-row")) {
    row.classList.toggle("is-highlight", Number(row.dataset.position) === markerHighlight);
    const selected = Number(row.dataset.index) === state.activeIndex;
    row.classList.toggle("is-selected", selected);
    row.setAttribute("aria-selected", String(selected));
  }
  for (const control of [els.markerSearch, els.markerList]) {
    if (
      filtered[markerHighlight] !== undefined &&
      markerHighlight >= rowWindow.start &&
      markerHighlight < rowWindow.end
    )
      control.setAttribute("aria-activedescendant", `marker-option-${filtered[markerHighlight]}`);
    else control.removeAttribute("aria-activedescendant");
  }
}

function updateMarkerField(): void {
  const i = state.activeIndex;
  const m = state.entries[i] ? markerInfo(state.entries[i], i) : null;
  setHTML(
    els.markerFieldLabel,
    m ? (m.titleHtml ??= renderMath(m.titleSource)) : state.location.kind === "skip" ? t("Skipped passage") : "—",
  );
  els.markerFieldLabel.title = m ? m.title : "";
}

function scrollHighlightedMarkerIntoView(): void {
  const top = markerHighlight * MARKER_ROW_HEIGHT;
  if (top < els.markerList.scrollTop) els.markerList.scrollTop = top;
  else if (top + MARKER_ROW_HEIGHT > els.markerList.scrollTop + els.markerList.clientHeight)
    els.markerList.scrollTop = top + MARKER_ROW_HEIGHT - els.markerList.clientHeight;
  renderMarkerList();
  const row = els.markerList.querySelector(".marker-row.is-highlight") as HTMLElement | null;
  row?.scrollIntoView({ block: "nearest" });
}

function openMarkerPopover(keyboard = false): void {
  markerFilter = "";
  els.markerSearch.value = "";
  markerHighlight = Math.max(0, filteredMarkerIndices().indexOf(state.activeIndex));
  els.markerPopover.hidden = false;
  showPopover(els.markerPopover);
  markerWindow = null;
  renderMarkerList(markerHighlight);
  els.markerField.setAttribute("aria-expanded", "true");
  (keyboard ? els.markerSearch : els.markerList).focus({ preventScroll: true });
  scrollHighlightedMarkerIntoView();
}

function closeMarkerPopover(): void {
  if (els.markerPopover.hidden) return;
  hidePopover(els.markerPopover);
  els.markerPopover.hidden = true;
  els.markerField.setAttribute("aria-expanded", "false");
}

function chooseMarker(index: number): void {
  closeMarkerPopover();
  els.markerField.focus();
  setActive(index, null, true).catch(reportError);
}

// Ctrl/Cmd+C with no text selection copies the active marker's TeX source (the
// booklink span between its BOOKLINK-START/END markers, marker lines excluded).
// Pointing at a `formalization: skip` band instead copies that skipped
// passage's TeX — the band under the cursor is what the reader means.
// Feedback flashes the marker field: accent on success, error hue when the
// marker has no resolved TeX span.
let copyFlashTimer: number | null = null;

function flashMarkerField(ok: boolean, title: string): void {
  const cls = ok ? "is-copied" : "is-copy-failed";
  if (copyFlashTimer != null) window.clearTimeout(copyFlashTimer);
  els.markerField.classList.remove("is-copied", "is-copy-failed");
  els.markerField.classList.add(cls);
  els.markerField.setAttribute("title", title);
  copyFlashTimer = window.setTimeout(() => {
    copyFlashTimer = null;
    els.markerField.classList.remove("is-copied", "is-copy-failed");
    els.markerField.setAttribute("title", t("Jump to linked passage"));
  }, 1200);
}

// Fetch cache for the peer document's tex — it lives under the peer mount, so
// loadCachedText (which resolves against the project's own mount) does not
// apply.
const peerTextCache = new Map<string, string>();

async function loadPeerText(url: string): Promise<string> {
  if (!peerTextCache.has(url)) {
    const response = await fetch(url, { cache: "no-store" });
    if (!response.ok) throw new Error(`${url}: HTTP ${response.status}`);
    peerTextCache.set(url, await response.text());
  }
  return peerTextCache.get(url) ?? "";
}

async function copyTexSpan(text: string, match: any, what: string): Promise<void> {
  // texMatch offsets are codepoint offsets into the debug tex (produced by the
  // Python sourcemap), the same space collectSpans passes to renderSource.
  const tex = spanText(text, match, "codepoint");
  if (!tex) {
    flashMarkerField(false, t("No {0} for this marker", what));
    return;
  }
  try {
    await navigator.clipboard.writeText(tex);
    flashMarkerField(true, t("Copied {0}", what));
  } catch (_error) {
    // Clipboard unavailable (e.g. non-secure context).
    flashMarkerField(false, t("Clipboard unavailable"));
  }
}

async function copyHoveredSkipTex(key: string): Promise<void> {
  // The project's own skip with this key wins; skip keys are offset-derived
  // slugs, so the peer document's keys don't collide with the project's, and a
  // key found only in the peer map identifies a band hovered in the peer pane.
  const skip = (state.skips || []).find((candidate: any) => candidate?.key === key);
  if (skip) {
    const match = skip.texMatch;
    if (!match || match.status !== "matched") {
      flashMarkerField(false, t("No TeX source for this skip"));
      return;
    }
    await copyTexSpan(await loadCachedText(match.source), match, "skip TeX");
    return;
  }
  const what = `${project.parallelPdf?.label || "peer PDF"} skip TeX`;
  const peer = parallelSkipTexMatch(key);
  if (!peer) {
    flashMarkerField(false, t("No {0} for this band", what));
    return;
  }
  let text: string;
  try {
    text = await loadPeerText(peer.url);
  } catch (_error) {
    flashMarkerField(false, `${what} unavailable`);
    return;
  }
  await copyTexSpan(text, peer.match, what);
}

async function copyActiveMarkerTex(): Promise<void> {
  // A skip band under the cursor takes precedence over the active marker.
  if (state.hoveredSkip != null) {
    await copyHoveredSkipTex(state.hoveredSkip);
    return;
  }
  // Copy from the document whose pane the reader last selected a marker in: a
  // marker picked in the peer PDF pane (e.g. the English PDF beside a
  // translated book) copies the peer document's TeX, a marker picked anywhere
  // else copies the project's own — the contract copyTexSource pins in
  // copy-tex.test.ts.
  if (copyTexSource(Boolean(project.parallelPdf?.mapPath), state.copyTexOrigin, visiblePaneNames()) === "peer") {
    const what = `${project.parallelPdf?.label || "peer PDF"} TeX`;
    const peer = parallelTexMatch(state.activeIndex);
    if (!peer) {
      flashMarkerField(false, t("No {0} for this marker", what));
      return;
    }
    let text: string;
    try {
      text = await loadPeerText(peer.url);
    } catch (_error) {
      flashMarkerField(false, `${what} unavailable`);
      return;
    }
    await copyTexSpan(text, peer.match, what);
    return;
  }
  const entry = state.entries[state.activeIndex];
  const match = entry?.texMatch;
  if (!match || match.status !== "matched") {
    flashMarkerField(false, t("No TeX source for this marker"));
    return;
  }
  const text = await loadCachedText(match.source);
  await copyTexSpan(text, match, t("TeX source"));
}

// Overlay a custom dropdown (matching the marker palette) on a native <select>:
// the native element stays as the value source so existing populate/change code
// is untouched; we mirror its options/value and forward selections back.

function collectSpans(kind: "md" | "lean" | "tex"): any[] {
  // Line-starts for the Lean source are the same for every entry, so build them
  // once here rather than per entry inside leanSpan.
  const leanStarts = kind === "lean" ? buildLineStarts(state.sources?.lean || "") : [];
  return state.entries
    .map((entry, index) => ({
      entryIndex: index,
      ...(kind === "lean" ? leanSpan(entry, leanStarts) : kind === "md" ? entry.match : entry.texMatch),
      // Carry the booklink kind so the mark is colored by role (after the spread,
      // so it always wins over any like-named field on the match object).
      target: entry.booklink?.target ?? null,
    }))
    .filter((span) => sourceMatchesSelected(span, kind));
}

// The `formalization: skip` overlays for the selected Markdown source. These
// are book-prose spans, not booklink entries, so they live outside state.entries
// and only ever apply to the md pane.
function collectSkipSpans(): any[] {
  if (state.selectedSources.md == null) return [];
  return (state.skips || []).filter((span) => repoPath(span?.source) === state.selectedSources.md);
}

function applyActiveState(): void {
  updateMarkKeyboardAccess();
  const index = state.activeIndex;
  updateMarkerField();
  if (!els.markerPopover.hidden) renderMarkerList();
  document.querySelectorAll(".mark.active, .pdf-mark.active").forEach((node) => node.classList.remove("active"));
  document
    .querySelectorAll(`.mark[data-entry="${index}"], .pdf-mark[data-entry="${index}"]`)
    .forEach((node) => node.classList.add("active"));
  document.querySelectorAll(".mark-rail-tick.is-active").forEach((node) => node.classList.remove("is-active"));
  document
    .querySelectorAll(`.mark-rail-tick[data-entry="${index}"]`)
    .forEach((node) => node.classList.add("is-active"));
}

// The pane the reader last interacted with renders the active marker at full
// strength (and its markers a touch brighter); the linked pane stays softer, so
// the active selection reads as one place rather than two equal highlights.
function setFocusPane(pane: string | null): void {
  const sections = state.paneSections || {};
  const visible = new Set(visiblePaneNames());
  // The PDF panes are valid pick origins but never the focus pane: focus
  // strength is a source-pane affair.
  let next = pane && pane !== "pdf" && pane !== "pdf-peer" && visible.has(pane) ? pane : state.focusedPane;
  if (!next || !visible.has(next)) {
    next = ["md", "lean", "tex"].find((name) => visible.has(name)) || "md";
  }
  state.focusedPane = next;
  for (const [name, section] of Object.entries(sections)) {
    section?.classList.toggle("is-focus-pane", name === next);
  }
}

// Hover highlights the whole booklink: a multiline marker is rendered as one
// .mark span per line (a span can't cross the per-line wrappers), all sharing
// data-entry, so we toggle .is-hover on every fragment of the entry — CSS :hover
// would only reach the fragment under the pointer.
function setHoveredEntry(entry: string | null): void {
  if (state.hoveredEntry === entry) return;
  if (state.hoveredEntry != null) {
    document
      .querySelectorAll(".mark.is-hover, .mark-rail-tick.is-hover, .pdf-mark.is-hover")
      .forEach((node) => node.classList.remove("is-hover"));
  }
  state.hoveredEntry = entry;
  if (entry != null) {
    document
      .querySelectorAll(
        `.mark[data-entry="${entry}"], .mark-rail-tick[data-entry="${entry}"], .pdf-mark[data-entry="${entry}"]`,
      )
      .forEach((node) => node.classList.add("is-hover"));
  }
}

// The skip counterpart of setHoveredEntry: a `formalization: skip` region wraps
// into one .skip-mark per line in the Markdown pane and one .pdf-skip-band per
// page in the PDF, all sharing the skip's stable key, so we toggle .is-hover on
// every fragment of that key — lighting the whole skipped region across panes.
function setHoveredSkip(key: string | null): void {
  if (state.hoveredSkip === key) return;
  if (state.hoveredSkip != null) {
    document
      .querySelectorAll(".skip-mark.is-hover, .pdf-skip-band.is-hover")
      .forEach((node) => node.classList.remove("is-hover"));
  }
  state.hoveredSkip = key;
  if (key != null) {
    // The key is a sanitized slug (letters, digits, hyphens) from the filter, so
    // it is safe to splice into a selector without escaping.
    document
      .querySelectorAll(`.skip-mark[data-skip-key="${key}"], .pdf-skip-band[data-skip-key="${key}"]`)
      .forEach((node) => node.classList.add("is-hover"));
  }
}

function skipLocationFromClick(pane: HTMLElement, key: string, clientY: number): { key: string; progress: number } {
  // Source panes render a skip as .skip-mark line fragments, the PDF panes as
  // .pdf-skip-band page overlays; both carry data-skip-key and both reduce to
  // the same on-screen extent for the progress computation.
  const fragments = Array.from(
    pane.querySelectorAll(`.skip-mark[data-skip-key="${key}"], .pdf-skip-band[data-skip-key="${key}"]`),
  );
  let start = Infinity;
  let end = -Infinity;
  for (const fragment of fragments) {
    const rect = fragment.getBoundingClientRect();
    if (rect.height <= 0) continue;
    start = Math.min(start, rect.top);
    end = Math.max(end, rect.bottom);
  }
  const progress = Number.isFinite(start) && end > start ? (clientY - start) / (end - start) : 0;
  return { key, progress: Math.min(1, Math.max(0, progress)) };
}

// The Lean-pane highlight for a booklink. A theorem's statement and proof are
// linked by two markers (target: statement / proof) that both resolve to the
// same declaration, so we split the declaration at its `:=` proof separator and
// highlight the matching half: `statement` (and any other target) gets the
// signature (decl start … `:=`), `proof` gets the body (`:=` … end of decl).
function leanSpan(entry: any, starts: number[]): any {
  const lean = entry.lean || {};
  const source = state.sources?.lean || "";
  const target = entry.booklink?.target;
  const declStartLine = Math.max(1, lean.declLine || lean.markerLine || 1);
  const declEndLine = Math.max(declStartLine, lean.declEndLine || lean.declLine || lean.markerEndLine || declStartLine);
  const declStartOffset = starts[declStartLine - 1] ?? 0;
  const declEndLineStart = starts[declEndLine - 1] ?? source.length;
  const declEndOffset =
    (starts[declEndLine] ?? source.length) > declEndLineStart ? (starts[declEndLine] ?? source.length) : source.length;

  // Locate the `:=` proof separator at bracket depth 0: a `:=` inside (…), […],
  // {…}, or ⟨…⟩ is a default-value binder or a structure-instance field, not the
  // statement/proof boundary, so matching the first `:=` blindly would split early.
  let sepStart: number | null = null; // offset of the `:` in `:=`
  let sigEnd: number | null = null; // offset just past the signature text
  let depth = 0;
  for (let lineNo = declStartLine; lineNo <= declEndLine && sepStart === null; lineNo += 1) {
    const lineStart = starts[lineNo - 1] ?? source.length;
    const lineEnd = starts[lineNo] ?? source.length;
    const lineText = source.slice(lineStart, lineEnd);
    const bodyStart = lineNo === declStartLine ? Math.max(0, declStartOffset - lineStart) : 0;
    for (let i = bodyStart; i < lineText.length; i += 1) {
      const ch = lineText[i];
      if (ch === "(" || ch === "[" || ch === "{" || ch === "⟨") {
        depth += 1;
      } else if (ch === ")" || ch === "]" || ch === "}" || ch === "⟩") {
        if (depth > 0) depth -= 1;
      } else if (depth === 0 && ch === ":" && lineText[i + 1] === "=") {
        sepStart = lineStart + i;
        sigEnd = lineStart + Math.max(bodyStart, lineText.slice(0, i).replace(/\s+$/, "").length);
        break;
      }
    }
  }

  let startOffset: number;
  let endOffset: number;
  if (target === "proof" && sepStart !== null) {
    // The proof body: from the `:=` to the end of the declaration.
    startOffset = sepStart;
    endOffset = declEndOffset;
  } else {
    // The statement/signature: from the declaration start to the `:=`.
    startOffset = declStartOffset;
    endOffset = sigEnd !== null && sigEnd > declStartOffset ? sigEnd : declEndOffset;
  }
  return {
    source: lean.source,
    startLine: offsetToLeanLine(starts, startOffset),
    endLine: offsetToLeanLine(starts, Math.max(startOffset, endOffset - 1)),
    startOffset,
    endOffset,
  };
}

// 1-based line containing a code-point offset, via the precomputed line starts.
function offsetToLeanLine(starts: number[], offset: number): number {
  let lo = 0;
  let hi = starts.length;
  while (lo + 1 < hi) {
    const mid = (lo + hi) >> 1;
    if (starts[mid] <= offset) lo = mid;
    else hi = mid;
  }
  return lo + 1;
}

function scrollPaneToEntry(paneName: string, index: number): void {
  const pane = state.panes[paneName];
  if (!pane) return;
  const mark = pane.querySelector(`.mark[data-entry="${index}"]`);
  if (!mark) return;
  const paneTop = paneViewportTop(pane);
  const markRect = mark.getBoundingClientRect();
  const markTop = markRect.top - paneTop + paneScrollTop(pane);
  const top = markTop - Math.max(0, paneViewportHeight(pane) * 0.35);
  logEvent("scrollTo", {
    paneName,
    index,
    currentTop: Math.round(paneScrollTop(pane)),
    nextTop: Math.round(Math.max(0, top)),
    markTop: Math.round(markTop),
    paneHeight: paneViewportHeight(pane),
  });
  scrollPane(pane, { top: Math.max(0, top), left: pane.scrollLeft, behavior: "auto" });
}

function sourceSkipRanges(pane: HTMLElement): Array<{ key: string; start: number; end: number }> {
  const paneTop = paneViewportTop(pane);
  const byKey = new Map<string, { key: string; start: number; end: number }>();
  for (const fragment of Array.from(pane.querySelectorAll(".skip-mark")) as HTMLElement[]) {
    const key = fragment.dataset.skipKey;
    if (!key) continue;
    const rect = fragment.getBoundingClientRect();
    if (rect.height <= 0) continue;
    const start = rect.top - paneTop + paneScrollTop(pane);
    const end = rect.bottom - paneTop + paneScrollTop(pane);
    const range = byKey.get(key);
    if (range) {
      range.start = Math.min(range.start, start);
      range.end = Math.max(range.end, end);
    } else {
      byKey.set(key, { key, start, end });
    }
  }
  return [...byKey.values()];
}

async function scrollMarkdownToSkip(location: { key: string; progress: number }): Promise<void> {
  const skip = (state.skips || []).find((candidate) => candidate?.key === location.key);
  const source = repoPath(skip?.source);
  if (source && source !== state.selectedSources.md) {
    state.selectedSources.md = source;
    state.selectedSources.lean = correspondingLeanForMd(source);
    await renderSelectedSources();
  }
  const pane = state.panes.md;
  if (!pane) return;
  const range = sourceSkipRanges(pane).find((candidate) => candidate.key === location.key);
  if (!range) return;
  const progress = Math.min(1, Math.max(0, location.progress));
  const target = range.start + progress * (range.end - range.start);
  const top = Math.max(0, target - paneViewportHeight(pane) * 0.35);
  scrollPane(pane, { top, left: pane.scrollLeft, behavior: "auto" });
}

function nearestSkipFromMarkdownScroll(): { key: string; progress: number } | null {
  const pane = state.panes.md;
  if (!pane) return null;
  const target = paneScrollTop(pane) + paneViewportHeight(pane) * 0.35;
  const paneTop = paneViewportTop(pane);
  let firstEntry = Infinity;
  for (const mark of Array.from(pane.querySelectorAll(".mark")) as HTMLElement[]) {
    firstEntry = Math.min(firstEntry, mark.getBoundingClientRect().top - paneTop + paneScrollTop(pane));
  }
  return skipSyncLocation(target, firstEntry, sourceSkipRanges(pane));
}

// Overview ruler: a thin lane on the right of each pane (its own grid column, so
// it never sits under the scrollbar thumb) with one tick per booklink at the
// marker's fractional position in the scrollable content — a "map" of where the
// linked passages are. Ticks are neutral and quiet by default; the active and
// hovered markers light up in their booklink hue. Clicking jumps to the marker;
// hovering mirrors the in-text highlight and shows the title/type.
const RAIL_PANES = ["md", "lean", "tex", "pdf"] as const;

// Fractional vertical positions (0..1) of each booklink in a pane's scroll
// content. Source panes read the rendered .mark fragments; the PDF reads the
// resolved page/offset targets.
function railTickFractions(paneName: string): { index: number; frac: number }[] {
  const clamp = (v: number) => Math.min(1, Math.max(0, v));
  if (paneName === "pdf") {
    const viewer = els.pdfViewer;
    const height = viewer ? paneScrollHeight(viewer) : 0;
    if (!height) return [];
    const out: { index: number; frac: number }[] = [];
    for (const [index, target] of state.pdf.targets.entries()) {
      const pageState = state.pdf.pageStates.get(target.pageNumber);
      if (!pageState) continue;
      out.push({ index, frac: clamp((pageState.el.offsetTop + target.fraction * pageState.el.offsetHeight) / height) });
    }
    return out.sort((a, b) => a.frac - b.frac);
  }
  const pre = state.panes[paneName];
  const height = pre ? paneScrollHeight(pre) : 0;
  if (!pre || !height) return [];
  const preTop = paneViewportTop(pre);
  const scrollTop = paneScrollTop(pre);
  const seen = new Set<string>();
  const out: { index: number; frac: number }[] = [];
  // One tick per booklink: take the first rendered fragment of each data-entry.
  for (const node of Array.from(pre.querySelectorAll(".mark")) as HTMLElement[]) {
    const entry = node.dataset.entry;
    if (!entry || seen.has(entry)) continue;
    seen.add(entry);
    const top = node.getBoundingClientRect().top - preTop + scrollTop;
    out.push({ index: Number(entry), frac: clamp(top / height) });
  }
  return out;
}

const pendingMarkRails = new Set<string>();
let markRailFrame = 0;
function updateMarkRail(paneName: string): void {
  // Reserve the gutter before restoring reading positions; only its ticks
  // are deferred. Changing the gutter later would change line wrapping.
  const section = state.paneSections?.[paneName];
  const hasMarks = paneName === "pdf" ? state.pdf.targets.size > 0 : !!state.panes[paneName]?.querySelector(".mark");
  section?.classList.toggle("has-mark-rail", hasMarks);
  pendingMarkRails.add(paneName);
  if (markRailFrame) return;
  markRailFrame = window.requestAnimationFrame(() => {
    markRailFrame = 0;
    const names = [...pendingMarkRails];
    pendingMarkRails.clear();
    // Measure every pane before modifying any rail or gutter.
    const measured = names.map((name) => ({ name, fractions: railTickFractions(name) }));
    for (const { name, fractions } of measured) paintMarkRail(name, fractions);
  });
}

function paintMarkRail(paneName: string, fractions: { index: number; frac: number }[]): void {
  const section = state.paneSections?.[paneName];
  if (!section) return;
  let rail = section.querySelector(":scope > .mark-rail") as HTMLElement | null;
  if (!rail) {
    rail = document.createElement("div");
    rail.className = "mark-rail";
    rail.setAttribute("aria-hidden", "true");
    section.appendChild(rail);
    rail.addEventListener("click", (event) => {
      const tick = (event.target as Element | null)?.closest(".mark-rail-tick") as HTMLElement | null;
      // Rails belong to source panes, so a tick click selects the project side.
      if (tick) {
        state.copyTexOrigin = "project";
        setActive(Number(tick.dataset.entry), null, true).catch(reportError);
      }
    });
    rail.addEventListener("mouseover", (event) => {
      const tick = (event.target as Element | null)?.closest(".mark-rail-tick") as HTMLElement | null;
      setHoveredEntry(tick?.dataset.entry ?? null);
    });
    rail.addEventListener("mouseleave", () => setHoveredEntry(null));
  }

  const ticks = fractions.map(({ index, frac }) => {
    const info = state.entries[index] ? markerInfo(state.entries[index], index) : null;
    const kind = info?.kind ? ` · ${info.kind}` : "";
    const tip = info ? `${info.title}${kind}` : "";
    const target = state.entries[index]?.booklink?.target ?? null;
    return (
      // tabindex -1: the rail is aria-hidden overview chrome and its jump
      // targets are reachable via the marker palette and in-text marks, so the
      // ticks must not sit in the tab order (focusable + aria-hidden conflict).
      `<button type="button" tabindex="-1" class="mark-rail-tick${index === state.activeIndex ? " is-active" : ""}"` +
      ` data-entry="${index}" style="top:${(frac * 100).toFixed(3)}%;${markerStyle(target)}"` +
      ` title="${escapeHtml(tip)}"></button>`
    );
  });
  setHTML(rail, ticks.join(""));
}

function updateAllMarkRails(): void {
  for (const paneName of RAIL_PANES) updateMarkRail(paneName);
}

function nearestEntryFromScroll(paneName: string): number | null {
  const pane = state.panes[paneName];
  if (!pane) return null;
  const paneTop = paneViewportTop(pane);
  const target = paneTop + paneViewportHeight(pane) * 0.35;
  let best: number | null = null;
  let bestDistance = Infinity;
  for (const mark of pane.querySelectorAll(".mark")) {
    const rect = mark.getBoundingClientRect();
    const distance = Math.abs(rect.top - target);
    if (distance < bestDistance) {
      bestDistance = distance;
      best = Number((mark as HTMLElement).dataset.entry);
    }
  }
  return Number.isInteger(best) ? best : null;
}

function wirePaneDrag(): void {
  for (const name of PANE_NAMES) {
    const pane = state.paneSections?.[name];
    if (!pane) continue;
    const header = pane.querySelector(".pane-header") as HTMLElement | null;
    if (!header) continue;
    header.draggable = true;
    header.addEventListener("dragstart", (event) => {
      if (state.layout.maximized) {
        event.preventDefault();
        return;
      }
      state.dragPane = name;
      pane.classList.add("dragging");
      els.workspace.classList.add("dragging-active");
      if (event.dataTransfer) {
        event.dataTransfer.effectAllowed = "move";
        event.dataTransfer.setData("text/plain", name);
      }
    });
    header.addEventListener("dragend", () => {
      state.dragPane = null;
      pane.classList.remove("dragging");
      els.workspace.classList.remove("dragging-active");
      hideDropOverlay();
    });
    pane.addEventListener("dragover", (event) => {
      if (!state.dragPane || state.dragPane === name) return;
      event.preventDefault();
      if (event.dataTransfer) event.dataTransfer.dropEffect = "move";
      showDropOverlay(pane, dropZone(pane, event));
    });
    pane.addEventListener("dragleave", (event) => {
      if (!pane.contains(event.relatedTarget as Node | null)) hideDropOverlay();
    });
    pane.addEventListener("drop", (event) => {
      event.preventDefault();
      const dragged = event.dataTransfer?.getData("text/plain") || state.dragPane;
      const zone = dropZone(pane, event);
      hideDropOverlay();
      if (dragged && dragged !== name) applyDrop(dragged, name, zone);
    });
  }
  window.addEventListener("mousemove", (event) => {
    applyResizeFromPointer(event);
  });
  window.addEventListener("mouseup", () => {
    if (state.resizing) {
      state.resizing = null;
      document.querySelectorAll(".splitter.dragging").forEach((node) => node.classList.remove("dragging"));
      document.body.classList.remove("is-resizing");
      saveLayout();
      // Panes settled at their final size; realign the marker rail ticks.
      window.requestAnimationFrame(() => updateAllMarkRails());
    }
  });
}

function wireEvents(): void {
  window.addEventListener("beforeunload", saveReloadPosition);
  window.addEventListener("pagehide", saveReloadPosition);
  const segButton = (group: HTMLElement | null, event: Event): HTMLElement | null => {
    const btn = (event.target as Element | null)?.closest("button") as HTMLElement | null;
    return btn && group && group.contains(btn) && !(btn as HTMLButtonElement).disabled ? btn : null;
  };
  els.syncSeg?.addEventListener("click", (event) => {
    const btn = segButton(els.syncSeg, event);
    if (!btn) return;
    state.sync = btn.dataset.value === "on";
    writePreference(SYNC_STORAGE_KEY, state.sync ? "on" : "off");
    updateSegmented(els.syncSeg, state.sync ? "on" : "off");
  });
  els.linenumSeg?.addEventListener("click", (event) => {
    const btn = segButton(els.linenumSeg, event);
    if (!btn) return;
    state.lineNumbers = btn.dataset.value === "on";
    writePreference(LINE_NUMBERS_STORAGE_KEY, state.lineNumbers ? "on" : "off");
    applyLineNumbers();
  });
  els.highlightsSeg?.addEventListener("click", (event) => {
    const btn = segButton(els.highlightsSeg, event);
    if (!btn) return;
    setMarkHighlights(btn.dataset.value === "on");
  });
  els.linksSeg?.addEventListener("click", (event) => {
    const btn = segButton(els.linksSeg, event);
    if (!btn) return;
    setLinkHighlights(btn.dataset.value === "on");
  });
  els.layoutSeg?.addEventListener("click", (event) => {
    const btn = segButton(els.layoutSeg, event);
    if (!btn) return;
    setLayoutKind(btn.dataset.value as string);
  });
  els.markerField.addEventListener("click", (event) => {
    if (els.markerPopover.hidden) openMarkerPopover(event.isTrusted && event.detail === 0);
    else closeMarkerPopover();
  });
  els.markerField.addEventListener("keydown", (event) => {
    if (els.markerPopover.hidden && ["ArrowDown", "ArrowUp", "Enter", " "].includes(event.key)) {
      event.preventDefault();
      openMarkerPopover(true);
    }
  });
  els.markerSearch.addEventListener("input", () => {
    markerFilter = els.markerSearch.value;
    markerHighlight = 0;
    renderMarkerList(0);
  });
  const navigateMarkers = (event: KeyboardEvent) => {
    if (enterSearchFromList(event, els.markerList, els.markerSearch)) return;
    const filtered = filteredMarkerIndices();
    if (event.key === "ArrowDown") {
      event.preventDefault();
      markerHighlight = Math.min(filtered.length - 1, markerHighlight + 1);
      renderMarkerList();
      scrollHighlightedMarkerIntoView();
    } else if (event.key === "ArrowUp") {
      event.preventDefault();
      markerHighlight = Math.max(0, markerHighlight - 1);
      renderMarkerList();
      scrollHighlightedMarkerIntoView();
    } else if (event.key === "Enter" || (event.currentTarget === els.markerList && event.key === " ")) {
      event.preventDefault();
      if (filtered[markerHighlight] !== undefined) chooseMarker(filtered[markerHighlight]);
    } else if (event.key === "Escape") {
      event.preventDefault();
      closeMarkerPopover();
      els.markerField.focus();
    }
  };
  els.markerSearch.addEventListener("keydown", navigateMarkers);
  els.markerList.addEventListener("keydown", navigateMarkers);
  els.markerList.addEventListener("click", (event) => {
    const row = (event.target as Element | null)?.closest(".marker-row") as HTMLElement | null;
    if (row?.dataset.index) chooseMarker(Number(row.dataset.index));
  });
  els.markerList.addEventListener(
    "scroll",
    () => {
      if (markerScrollFrame) return;
      markerScrollFrame = requestAnimationFrame(() => {
        markerScrollFrame = 0;
        if (!els.markerPopover.hidden) renderMarkerList();
      });
    },
    { passive: true },
  );
  new ResizeObserver(() => {
    if (!els.markerPopover.hidden) renderMarkerList();
  }).observe(els.markerList);
  els.markerList.addEventListener("mousemove", (event) => {
    const row = (event.target as Element | null)?.closest(".marker-row") as HTMLElement | null;
    if (!row?.dataset.index) return;
    const pos = Number(row.dataset.position);
    if (pos >= 0 && pos !== markerHighlight) {
      markerHighlight = pos;
      renderMarkerList();
    }
  });
  document.addEventListener("click", (event) => {
    if (!(event.target as Element | null)?.closest("#marker-combo")) closeMarkerPopover();
  });
  const adjacentMarker = (step: number) => {
    const index =
      state.activeIndex >= 0 ? state.activeIndex : (nearestEntryFromScroll("md") ?? nearestEntryFromPdfScroll() ?? 0);
    return setActive(Math.max(0, Math.min(state.entries.length - 1, index + step)), null, true);
  };
  els.prev.addEventListener("click", () => adjacentMarker(-1).catch(reportError));
  els.next.addEventListener("click", () => adjacentMarker(1).catch(reportError));
  // Let the reader browse to any chapter file. renderSelectedSources already
  // re-applies the active entry's highlight (applyActiveState) for whichever
  // file is shown; do NOT call setActive here — it re-navigates to the active
  // entry's own source and snaps the just-picked file back, which would make the
  // dropdowns useless for any chapter that does not contain the active marker.
  els.mdSelect.addEventListener("change", async () => {
    state.selectedSources.md = repoPath(els.mdSelect.value);
    state.selectedSources.lean = correspondingLeanForMd(state.selectedSources.md);
    recordSession({ md: state.selectedSources.md, lean: state.selectedSources.lean });
    await renderSelectedSources();
  });
  els.leanSelect.addEventListener("change", async () => {
    state.selectedSources.lean = repoPath(els.leanSelect.value);
    recordSession({ lean: state.selectedSources.lean });
    await renderSelectedSources();
  });
  if (!popoverSupported(els.settingsMenu)) {
    els.settingsMenu.hidden = true;
    els.settingsToggle.removeAttribute("popovertarget");
    els.settingsToggle.addEventListener("click", () => {
      const nextOpen = els.settingsMenu.hidden;
      els.settingsMenu.hidden = !nextOpen;
      els.settingsToggle.setAttribute("aria-expanded", String(nextOpen));
    });
    document.addEventListener("click", (event) => {
      if ((event.target as Element | null)?.closest(".settings")) return;
      closeSettingsMenu();
    });
    document.addEventListener("keydown", (event) => {
      if (event.key === "Escape") closeSettingsMenu();
    });
  }
  els.settingsMenu.addEventListener("toggle", (event) => {
    const open = (event as { newState?: string }).newState === "open";
    els.settingsToggle.setAttribute("aria-expanded", String(open));
  });
  els.aboutOpen?.addEventListener("click", openAbout);
  els.aboutClose?.addEventListener("click", closeAbout);
  els.aboutCopy?.addEventListener("click", async () => {
    const text = els.aboutCopy?.dataset.copy || "";
    if (!text) return;
    try {
      await navigator.clipboard.writeText(text);
      els.aboutCopy!.classList.add("is-copied");
      els.aboutCopy!.setAttribute("title", t("Copied"));
      window.setTimeout(() => {
        els.aboutCopy?.classList.remove("is-copied");
        els.aboutCopy?.setAttribute("title", t("Copy version"));
      }, 1200);
    } catch (_error) {
      // Clipboard unavailable (e.g. non-secure context); ignore.
    }
  });
  els.aboutLicenseList?.addEventListener("click", (event) => {
    const btn = (event.target as Element | null)?.closest(".about-license-view") as HTMLElement | null;
    if (!btn) return;
    const pre = document.getElementById(`about-license-text-${btn.dataset.license}`);
    if (!pre) return;
    const show = pre.hidden;
    pre.hidden = !show;
    btn.setAttribute("aria-expanded", String(show));
  });
  els.aboutOverlay?.addEventListener("click", (event) => {
    // Click on the backdrop (outside the dialog) closes; clicks inside don't.
    if (event.target === els.aboutOverlay) closeAbout();
  });
  document.addEventListener("keydown", (event) => {
    // Ctrl/Cmd+C copies the active marker's TeX source — but only when it
    // cannot be a real copy: no text selection, and not inside an editable
    // element (the marker search box keeps its native behavior).
    if (event.key.toLowerCase() === "c" && (event.ctrlKey || event.metaKey) && !event.altKey && !event.shiftKey) {
      const target = event.target as Element | null;
      if (target?.closest("input, textarea, select, [contenteditable]")) return;
      const selection = window.getSelection();
      if (selection && !selection.isCollapsed) return;
      event.preventDefault();
      copyActiveMarkerTex().catch(reportError);
    }
  });
  for (const input of els.paneChecks) {
    input.addEventListener("change", () => applyPaneCheckboxes());
  }
  wirePaneDrag();
  window.addEventListener("resize", () => {
    if (state.pdf.resizeTimer) window.clearTimeout(state.pdf.resizeTimer);
    state.pdf.resizeTimer = window.setTimeout(() => {
      state.pdf.resizeTimer = null;
      refreshPdfLayoutGeometry();
      updateAllMarkRails();
    }, 120);
  });
  els.pdfViewer.addEventListener(
    "scroll",
    () => {
      renderVisiblePdfPages();
      if (state.pdf.scrollTimer) window.clearTimeout(state.pdf.scrollTimer);
      state.pdf.scrollTimer = window.setTimeout(() => {
        state.pdf.scrollTimer = null;
        updatePdfPageFromScroll();
        syncFromScroll("pdf").catch(reportError);
      }, 80);
    },
    { passive: true },
  );

  for (const paneName of ["md", "lean", "tex"]) {
    const pane = state.panes[paneName];
    pane.addEventListener("keydown", (event) => {
      const mark = (event.target as Element)?.closest<HTMLElement>("[data-mark-control]");
      if (!mark || !state.markHighlights || event.repeat || !["Enter", " "].includes(event.key)) return;
      event.preventDefault();
      event.stopPropagation();
      state.copyTexOrigin = "project";
      setActive(Number(mark.dataset.entry), paneName, true).catch(reportError);
    });
    pane.addEventListener("click", (event) => {
      if (window.getSelection()?.isCollapsed === false) return;
      const target = event.target as Element | null;
      const mark = target?.closest(".mark") as HTMLElement | null;
      const skip = target?.closest(".skip-mark") as HTMLElement | null;
      // A direct click is explicit "go here" navigation: scroll every linked
      // pane to the entry even when scroll-sync is off. With the
      // highlights hidden the marks are invisible, so a click must not navigate.
      if (mark && state.markHighlights) {
        state.copyTexOrigin = "project";
        setActive(Number(mark.dataset.entry), paneName, true).catch(reportError);
      } else if (skip?.dataset.skipKey && state.markHighlights) {
        const clientY = event instanceof MouseEvent ? event.clientY : skip.getBoundingClientRect().top;
        setSkipActive(skipLocationFromClick(pane, skip.dataset.skipKey, clientY), paneName, true).catch(reportError);
      }
      if (paneName === "lean") inspectLeanClick(event);
    });
    // Hover a marker -> highlight every fragment of that booklink. mouseover
    // bubbles (unlike mouseenter), so one delegated listener per pane covers
    // all marks; leaving the pane clears it. Hidden highlights don't hover:
    // an invisible mark must not light up the other panes.
    pane.addEventListener("mouseover", (event) => {
      const target = event.target as Element | null;
      const mark = state.markHighlights ? (target?.closest(".mark") as HTMLElement | null) : null;
      setHoveredEntry(mark?.dataset.entry ?? null);
      // Skip overlays only render in the md pane, but the lookup is harmless on
      // the others (no .skip-mark to find), so one handler covers every pane.
      // Gated like the marks: an invisible skip must not light the PDF band.
      const skip = state.markHighlights ? (target?.closest(".skip-mark") as HTMLElement | null) : null;
      setHoveredSkip(skip?.dataset.skipKey ?? null);
    });
    pane.addEventListener("mouseleave", () => {
      setHoveredEntry(null);
      setHoveredSkip(null);
    });
    if (paneName === "lean") {
      pane.addEventListener("mousemove", onLeanHover);
      pane.addEventListener("mouseleave", hideHover);
      // Folds shift content below them; recompute tick positions. `toggle` does
      // not bubble, so listen in the capture phase.
      pane.addEventListener("toggle", () => updateMarkRail("lean"), true);
    }
    pane.addEventListener(
      "scroll",
      () => {
        if (paneName === "lean") hideHover();
        logEvent("scroll:event", {
          paneName,
          scrollTop: Math.round(paneScrollTop(pane)),
          sync: state.sync,
          suppressed: isPaneSuppressed(paneName),
        });
        if (!state.sync || isPaneSuppressed(paneName)) return;
        if (state.syncScrollTimer) window.clearTimeout(state.syncScrollTimer);
        state.syncScrollTimer = window.setTimeout(() => {
          state.syncScrollTimer = null;
          syncFromScroll(paneName).catch(reportError);
        }, 80);
      },
      { passive: true },
    );
  }

  // The PDF pane's booklink overlays (.pdf-mark) are the canvas counterpart of
  // the source-pane .mark spans: clicking one navigates every linked pane to that
  // entry, hovering mirrors the in-text highlight across panes. Delegated on the
  // viewer so it covers overlays added lazily as pages rasterize. The PDF is the
  // origin pane of the pick, so it keeps its own reading position while every
  // other pane (sources and the peer PDF alike) scrolls to the entry.
  els.pdfViewer.addEventListener("click", (event) => {
    if (window.getSelection()?.isCollapsed === false) return;
    const target = event.target as Element | null;
    const mark = state.markHighlights ? pdfOverlayAtPoint(target, ".pdf-mark", event.clientX, event.clientY) : null;
    const skip = state.markHighlights
      ? pdfOverlayAtPoint(target, ".pdf-skip-band", event.clientX, event.clientY)
      : null;
    if (mark && state.markHighlights) {
      state.copyTexOrigin = "project";
      setActive(Number(mark.dataset.entry), "pdf", true).catch(reportError);
    } else if (skip?.dataset.skipKey && state.markHighlights) {
      const clientY = event instanceof MouseEvent ? event.clientY : skip.getBoundingClientRect().top;
      setSkipActive(skipLocationFromClick(els.pdfViewer, skip.dataset.skipKey, clientY), "pdf", true).catch(
        reportError,
      );
    }
  });
  els.pdfViewer.addEventListener("mouseover", (event) => {
    const target = event.target as Element | null;
    const mark = state.markHighlights ? pdfOverlayAtPoint(target, ".pdf-mark", event.clientX, event.clientY) : null;
    setHoveredEntry(mark?.dataset.entry ?? null);
    const skip = state.markHighlights
      ? pdfOverlayAtPoint(target, ".pdf-skip-band", event.clientX, event.clientY)
      : null;
    setHoveredSkip(skip?.dataset.skipKey ?? null);
  });
  els.pdfViewer.addEventListener("mouseleave", () => {
    setHoveredEntry(null);
    setHoveredSkip(null);
  });
  // Like the primary PDF pane: the peer keeps its own position as the origin of
  // the pick while the other panes scroll to it.
  els.pdfPeerViewer.addEventListener("click", (event) => {
    if (window.getSelection()?.isCollapsed === false) return;
    const target = event.target as Element | null;
    const mark = state.markHighlights ? pdfOverlayAtPoint(target, ".pdf-mark", event.clientX, event.clientY) : null;
    const skip = state.markHighlights
      ? pdfOverlayAtPoint(target, ".pdf-skip-band", event.clientX, event.clientY)
      : null;
    // Selecting a marker in the peer PDF makes it the copy-TeX source until a
    // marker is selected in another pane.
    if (mark && state.markHighlights) {
      state.copyTexOrigin = "peer";
      setActive(Number(mark.dataset.entry), "pdf-peer", true).catch(reportError);
    } else if (skip?.dataset.skipKey && state.markHighlights) {
      const clientY = event instanceof MouseEvent ? event.clientY : skip.getBoundingClientRect().top;
      setSkipActive(skipLocationFromClick(els.pdfPeerViewer, skip.dataset.skipKey, clientY), "pdf-peer", true).catch(
        reportError,
      );
    }
  });
  els.pdfPeerViewer.addEventListener("mouseover", (event) => {
    const target = event.target as Element | null;
    const mark = state.markHighlights ? pdfOverlayAtPoint(target, ".pdf-mark", event.clientX, event.clientY) : null;
    setHoveredEntry(mark?.dataset.entry ?? null);
    const skip = state.markHighlights
      ? pdfOverlayAtPoint(target, ".pdf-skip-band", event.clientX, event.clientY)
      : null;
    setHoveredSkip(skip?.dataset.skipKey ?? null);
  });
  els.pdfPeerViewer.addEventListener("mouseleave", () => {
    setHoveredEntry(null);
    setHoveredSkip(null);
  });
}

async function connectInfoview(): Promise<void> {
  state.lsp.status = "connecting";
  renderInfoview();
  const info = await connectLeanLsp({
    // In a static dist there is no bridge: answers come from the per-file
    // caches generated by tools/formalization-viewer/server/lsp-cache.ts.
    staticCacheUrlFor: project.static ? (repoRelPath) => repoUrl(`lsp-cache/${repoRelPath}.json`) : undefined,
    projectDir: project.dir,
    onDiagnostics: (uri) => {
      if (uri === state.lsp.uri) renderInfoview();
    },
    onStatus: (status) => {
      state.lsp.status = status;
      if (status === "ready" || status === "static") {
        syncLeanDocument();
        if (state.entries[state.activeIndex]) {
          const pos = leanEntryPosition(state.entries[state.activeIndex]);
          queryGoalAt(pos.line, pos.character).catch(reportError);
        }
      }
      renderInfoview();
    },
  });
  state.lsp.info = info;
}

// Open (or re-sync) the selected Lean document with the LSP server. Resets the
// shown goal when the file changes so stale state never lingers across files.
function syncLeanDocument(): void {
  if (!lspIsReady()) return;
  const path = state.selectedSources.lean;
  const text = state.sources?.lean;
  if (!path || text == null) return;
  const uri = lspOpenDocument(path, text);
  if (uri !== state.lsp.uri) {
    state.lsp.uri = uri;
    state.lsp.goal = null;
    state.lsp.termGoal = null;
    state.lsp.position = null;
    hideHover();
  }
}

function leanEntryPosition(entry: any): { line: number; character: number } {
  const lean = entry?.lean || {};
  const line = Math.max(1, lean.declLine || lean.markerLine || 1) - 1;
  return { line, character: 0 };
}

async function queryGoalAt(line: number, character: number): Promise<void> {
  if (!lspIsReady() || !state.lsp.uri) {
    renderInfoview();
    return;
  }
  const uri = state.lsp.uri;
  const token = ++state.lsp.goalToken;
  state.lsp.position = { line, character };
  renderInfoview();
  const [goal, termGoal] = await Promise.all([
    lspPlainGoal(uri, line, character),
    lspPlainTermGoal(uri, line, character),
  ]);
  // Drop a stale response: the file changed, or a newer query (a later line
  // click, or a reload-triggered re-query) was issued while this one was in
  // flight. Without the token, the slower-to-settle response — possibly for an
  // older position — would overwrite the goal for the current one.
  if (uri !== state.lsp.uri || token !== state.lsp.goalToken) return;
  state.lsp.goal = goal;
  state.lsp.termGoal = termGoal;
  renderInfoview();
}

function inspectLeanClick(event: MouseEvent): void {
  if ((event.target as Element | null)?.closest("summary")) return; // Fold toggle, not a goal query.
  const pos = leanPositionFromPoint(event.clientX, event.clientY);
  if (pos) queryGoalAt(pos.line, pos.character).catch(reportError);
}

// LSP position (UTF-16, 0-based) of a viewport point inside the Lean pane, or
// null if it is not over a source line. UTF-16 columns match the offsets the
// Lean server uses and Range.toString().length.
function leanPositionFromPoint(x: number, y: number): { line: number; character: number } | null {
  const element = document.elementFromPoint(x, y);
  const lineEl = (element && element.closest ? element.closest(".line") : null) as HTMLElement | null;
  const pane = state.panes.lean;
  if (!lineEl || !pane || !pane.contains(lineEl)) return null;
  const dataLine = Number(lineEl.dataset.line);
  if (!Number.isInteger(dataLine)) return null;
  return { line: dataLine - 1, character: caretColumnAt(lineEl, x, y) };
}

function caretColumnAt(lineEl: Element, x: number, y: number): number {
  let node: Node | null = null;
  let offset = 0;
  if (document.caretRangeFromPoint) {
    const range = document.caretRangeFromPoint(x, y);
    if (range) {
      node = range.startContainer;
      offset = range.startOffset;
    }
  } else if (document.caretPositionFromPoint) {
    const position = document.caretPositionFromPoint(x, y);
    if (position) {
      node = position.offsetNode;
      offset = position.offset;
    }
  }
  if (!node || !lineEl.contains(node)) return 0;
  const range = document.createRange();
  range.selectNodeContents(lineEl);
  try {
    range.setEnd(node, offset);
  } catch (_error) {
    return 0;
  }
  return range.toString().length;
}

// Hover tooltip: debounced textDocument/hover over the Lean pane.
interface HoverState {
  timer: ReturnType<typeof setTimeout> | null;
  token: number;
  key: string | null;
  x: number;
  y: number;
  el: HTMLElement | null;
}

const HOVER: HoverState = { timer: null, token: 0, key: null, x: 0, y: 0, el: null };

function hoverElement(): HTMLElement {
  let el = HOVER.el;
  if (!el) {
    el = document.createElement("div");
    el.className = "lean-hover";
    el.hidden = true;
    document.body.append(el);
    HOVER.el = el;
  }
  return el;
}

function hideHover(): void {
  if (HOVER.timer) {
    window.clearTimeout(HOVER.timer);
    HOVER.timer = null;
  }
  HOVER.token += 1; // invalidate any in-flight request
  HOVER.key = null;
  if (HOVER.el) HOVER.el.hidden = true;
}

function onLeanHover(event: MouseEvent): void {
  if (!lspIsReady() || !state.lsp.uri || (event.target as Element | null)?.closest("summary")) {
    hideHover();
    return;
  }
  HOVER.x = event.clientX;
  HOVER.y = event.clientY;
  if (HOVER.timer) window.clearTimeout(HOVER.timer);
  HOVER.timer = window.setTimeout(() => requestHover().catch(reportError), 180);
}

async function requestHover(): Promise<void> {
  HOVER.timer = null;
  const pos = leanPositionFromPoint(HOVER.x, HOVER.y);
  if (!pos) {
    hideHover();
    return;
  }
  const key = `${pos.line}:${pos.character}`;
  if (key === HOVER.key && HOVER.el && !HOVER.el.hidden) return;
  const token = ++HOVER.token;
  const result = await lspHover(state.lsp.uri, pos.line, pos.character);
  if (token !== HOVER.token) return;
  const text = hoverText(result);
  if (!text) {
    if (HOVER.el) HOVER.el.hidden = true;
    HOVER.key = null;
    return;
  }
  HOVER.key = key;
  showHover(text);
}

// Lean hover contents are markdown (a ```lean signature, then docstring). Flatten
// to plain text: drop code fences, turn markdown rules into a separator.
function hoverText(result: any): string {
  const contents = result?.contents;
  if (!contents) return "";
  const raw =
    typeof contents === "string"
      ? contents
      : Array.isArray(contents)
        ? contents.map((item: any) => (typeof item === "string" ? item : item.value || "")).join("\n\n")
        : contents.value || "";
  return raw
    .replace(/```[a-zA-Z]*\n?/g, "")
    .replace(/```/g, "")
    .replace(/^\s*(?:\*\*\*|---)\s*$/gm, "—")
    .replace(/\n{3,}/g, "\n\n")
    .trim();
}

function showHover(text: string): void {
  const el = hoverElement();
  el.textContent = text;
  el.hidden = false;
  const margin = 14;
  const rect = el.getBoundingClientRect();
  let left = HOVER.x + margin;
  let top = HOVER.y + margin;
  if (left + rect.width > window.innerWidth - 8) left = window.innerWidth - rect.width - 8;
  if (top + rect.height > window.innerHeight - 8) top = HOVER.y - rect.height - margin;
  el.style.left = `${Math.max(8, left)}px`;
  el.style.top = `${Math.max(8, top)}px`;
}

const SOURCE_ELEMENT: Record<string, string> = { md: "mdSource", lean: "leanSource", tex: "texSource" };
const watchTimers: Map<string, ReturnType<typeof setTimeout>> = new Map();

// A watched file changed on disk; debounce per path so a burst of native FS
// events (or a multi-write build) collapses into a single reload.
function onWatchedFileChanged(path: string): void {
  if (path.endsWith(".md")) document.dispatchEvent(new Event("book-search-invalidated"));
  if (watchTimers.has(path)) window.clearTimeout(watchTimers.get(path));
  watchTimers.set(
    path,
    window.setTimeout(() => {
      watchTimers.delete(path);
      applyWatchedChange(path);
    }, 200),
  );
}

// Report the currently viewed PDF to the server's auto-builder. The path must
// be repo-relative (e.g. "polish-space/build/…debug.pdf") to match the builder's
// per-project target prefixes; repoPath() strips the project dir, so prepend it.
function reportPdfSelection(path: string | null | undefined): void {
  const rel = repoPath(path ? renderedPdfPath(path) : path);
  reportSelectedPdf(rel ? `${project.dir}/${rel}` : "");
}

// Chapter preview PDFs: a fast \includeonly render of one chapter each
// (build/<stem>-preview-<chapter>.pdf). One dropdown option per chapter source,
// independent of the Markdown pane like the other selectors; the server builds
// the selected one on selection/edit via the same selection-aware auto-build.
// "build/<stem>-debug.pdf" -> book stem. Lazy: project is populated by
// setProject() after this module loads.
function bookStem(): string {
  return (project.pdf ?? "").replace(/^.*\//, "").replace(/-debug\.pdf$/, "");
}
function chapterStemOf(md: string | null | undefined): string {
  return (md ?? "").replace(/^.*\//, "").replace(/\.md$/, "");
}
function previewUrlForChapter(chapter: string): string {
  const stem = bookStem();
  // The whole-book master source is not a chapter and has no preview.
  return stem && chapter && chapter !== stem ? repoUrl(`build/${stem}-preview-${chapter}.pdf`) : "";
}
// One preview option per chapter source, labelled with its book heading.
function chapterPreviewChoices(): { key: string; label: string; path: string }[] {
  const seen = new Set<string>();
  const choices: { key: string; label: string; path: string }[] = [];
  for (const md of state.fileChoices.md) {
    const chapter = chapterStemOf(md);
    const path = previewUrlForChapter(chapter);
    if (!path || seen.has(chapter)) continue;
    seen.add(chapter);
    choices.push({ key: `preview:${chapter}`, label: pdfLabel(path), path });
  }
  for (const [unit, label] of Object.entries(project.previewSections ?? {})) {
    if (!/^[A-Za-z0-9_-]+$/.test(unit) || seen.has(unit)) continue;
    const path = previewUrlForChapter(unit);
    if (path) {
      const choice = { key: `preview:${unit}`, label, path };
      if (unit === "_contents") choices.unshift(choice);
      else choices.push(choice);
    }
  }
  return choices;
}
function isPreviewPath(path: string): boolean {
  const stem = bookStem();
  return !!stem && path.includes(`${stem}-preview-`);
}

let chapterLanding: {
  path: string;
  direction: ChapterDirection;
  primaryDone: boolean;
  peerDone: boolean;
  finishing: boolean;
} | null = null;

function adjacentChapter(direction: ChapterDirection): { path: string; label: string } | null {
  if (state.pdfMode !== "chapter") return null;
  const choices = Array.from(els.pdfSelect.options);
  const index = choices.findIndex((choice) => choice.value === state.pdf.path);
  const next = index >= 0 ? choices[index + direction] : null;
  return next && !next.disabled ? { path: next.value, label: next.textContent || next.value } : null;
}

function landAtChapterEdge(viewer: HTMLElement, direction: ChapterDirection): void {
  suppressPaneSync(viewer === els.pdfViewer ? "pdf" : "pdf-peer");
  scrollPane(viewer, { top: direction > 0 ? 0 : paneScrollHeight(viewer), behavior: "auto" });
}

// Keep the landing request until each PDF actually arrives. A newly requested
// chapter can initially 404 while its build runs, including the translated peer.
async function finishChapterLanding(): Promise<void> {
  const landing = chapterLanding;
  if (
    !landing ||
    landing.finishing ||
    landing.primaryDone ||
    state.pdf.loadedPath !== landing.path ||
    !state.pdf.document
  )
    return;
  landing.finishing = true;
  try {
    landAtChapterEdge(els.pdfViewer, landing.direction);
    updatePdfPageFromScroll();
    const skip = nearestSkipFromPdfScroll();
    const index = nearestEntryFromPdfScroll();
    // Chapter navigation updates the same canonical location as marker picks.
    if (skip) await setSkipActive(skip, "pdf");
    else if (index !== null) await setActive(index, "pdf");
    if (state.pdf.path !== landing.path || chapterLanding !== landing) return;
    landAtChapterEdge(els.pdfViewer, landing.direction);
    updatePdfPageFromScroll();
    if (landing.peerDone && project.parallelPdf) landAtChapterEdge(els.pdfPeerViewer, landing.direction);
    landing.primaryDone = true;
    if (landing.peerDone) chapterLanding = null;
  } finally {
    landing.finishing = false;
  }
}

function wireChapterPull(): void {
  for (const viewer of [els.pdfViewer, els.pdfPeerViewer]) {
    installChapterPull(viewer, {
      target: adjacentChapter,
      enabled: () => state.pdfMode === "chapter" && (!chapterLanding || chapterLanding.primaryDone),
      navigate: async (direction) => {
        const next = adjacentChapter(direction);
        if (!next) return;
        chapterLanding = {
          path: next.path,
          direction,
          primaryDone: false,
          peerDone: !project.parallelPdf,
          finishing: false,
        };
        await setPdf(next.path, { scrollToActive: false });
        await state.pdf.targetPromise;
        await finishChapterLanding();
      },
      onError: reportError,
    });
  }
}

// URL mode owns the initial render. Reader positions may choose the chapter,
// but a stale local full-book selection must never override the chapter default.
function initialPdfPath(choices: { path: string }[], params: URLSearchParams, fallback: string): string {
  if (params.get("pdf")) return fallback;
  if (state.pdfMode === "full")
    return choices.find((choice) => choice.path === repoUrl(project.pdf ?? ""))?.path ?? fallback;
  const session = storedSession();
  const linkedSkip = params.get("skip");
  const marker = params.get("marker") || (!linkedSkip ? session.marker : null);
  const index = marker ? markerIndex(state.entries, marker) : null;
  const skipKey = linkedSkip || (!marker ? session.skip : null);
  const skip = skipKey ? state.skips?.find((item) => item.key === skipKey) : null;
  const source =
    index !== null
      ? state.entries[index]?.match?.source
      : skip?.match?.source || skip?.source || session.md || state.selectedSources.md;
  const wanted = previewUrlForChapter(chapterStemOf(source));
  return (
    choices.find((choice) => choice.path === wanted)?.path ??
    choices.find((choice) => /-preview-(?!_)[^/]+\.pdf$/.test(choice.path))?.path ??
    choices.find((choice) => isPreviewPath(choice.path))?.path ??
    fallback
  );
}

// Build-log icons in the PDF pane headers: the primary pane tracks this
// project's builds, the peer pane its peer project's. Each shows while its
// project has an in-flight build; a failed build flashes briefly. The server's
// build channel carries every project's events; onBuildStatus dispatches them.
function makeBuildIndicator(el: () => HTMLElement | null): (status: BuildStatus) => void {
  const building = new Set<string>();
  let logAttached = false;
  let logDir = "";
  return (status) => {
    if (status.state === "building") building.add(status.dir);
    else building.delete(status.dir);
    const node = el();
    if (!node) return;
    logDir = status.dir;
    if (!logAttached) {
      attachBuildLog(node, () => logDir);
      logAttached = true;
    }
    const indicatorState = building.size > 0 ? "building" : status.state === "failed" ? "failed" : "done";
    const label =
      indicatorState === "building" ? t("Building…") : indicatorState === "failed" ? t("Build failed") : t("Build log");
    node.hidden = false;
    node.dataset.state = indicatorState;
    node.title = indicatorState === "done" ? t("Show build log") : `${label} — ${t("Show build log")}`;
    node.setAttribute("aria-label", node.title);
    const text = node.querySelector(".build-status-text");
    if (text) text.textContent = label;
  };
}
const primaryBuildIndicator = makeBuildIndicator(() => els.pdfBuildStatus);
const peerBuildIndicator = makeBuildIndicator(() => els.pdfPeerBuildStatus);
const buildingProjects = new Set<string>();
const pendingBuildArtifacts = new Map<string, Set<string>>();

function onBuildStatus(status: BuildStatus): void {
  const wasBuilding = buildingProjects.has(status.dir);
  if (status.state === "building") buildingProjects.add(status.dir);
  else buildingProjects.delete(status.dir);
  const artifacts = pendingBuildArtifacts.get(status.dir);
  if (status.state !== "building") pendingBuildArtifacts.delete(status.dir);
  if (project.parallelPdf?.dir === status.dir) {
    peerBuildIndicator(status);
    if (status.state === "building")
      pdfLoadStatus(els.pdfPeerViewer, t("Building PDF… Current PDF remains available."));
    else if (status.state === "done" && (wasBuilding || artifacts?.size)) schedulePeerPdfReload();
    else if (status.state === "failed")
      pdfLoadStatus(els.pdfPeerViewer, t("PDF build failed. Current PDF remains available — see build log."));
  }
  if (status.dir !== project.dir) return;
  // When the viewed PDF has not been built yet, show the build state in the
  // pane body and load it once the build lands, instead of a stale 404 error.
  const selected = state.pdf.path ?? "";
  if (isPreviewPath(selected) || repoPath(selected) === project.pdf) {
    if (status.state === "building") {
      if (!state.pdf.document) clearPdfViewer(t("Building PDF…"));
      pdfLoadStatus(
        els.pdfViewer,
        state.pdf.document ? t("Building PDF… Current PDF remains available.") : t("Building PDF…"),
      );
    } else if (status.state === "failed") {
      if (!state.pdf.document) clearPdfViewer(t("PDF build failed — see build log."));
      pdfLoadStatus(els.pdfViewer, t("PDF build failed — see build log."));
    } else if (status.state === "done" && (wasBuilding || artifacts?.size || !state.pdf.document)) {
      const mapChanged = [...(artifacts ?? [])].some((path) => repoPath(path) === repoPath(state.mapPath));
      if (mapChanged)
        void reloadMap({ refreshPdf: false })
          .then(() => {
            if (!buildingProjects.has(status.dir)) reloadPdf();
          })
          .catch(reportError);
      else reloadPdf();
    }
  }
  primaryBuildIndicator(status);
}

const VIEWER_ASSET = /^tools\/formalization-viewer\/[^?]*\.(?:js|css|html)$/;
let reloadTimer: ReturnType<typeof setTimeout> | null = null;

// Re-check the served build version, debounced so esbuild's burst of output
// writes collapses into one check, then reload only if the server reports a
// different build (the version reflects the final, fully-written outputs — never
// a half-written bundle). The same check runs on reconnect/focus as the safety
// net. Called on *every* watched change (see applyWatchedChange), so a reliably
// delivered content event backstops a coalesced/missed build/*.js event.
function scheduleReload(): void {
  if (reloadTimer) window.clearTimeout(reloadTimer);
  reloadTimer = window.setTimeout(() => {
    reloadTimer = null;
    void checkForNewBuild();
  }, 250);
}

// "…/<stem>-preview-<chapter>.pdf" -> "<chapter>"; null for any other path.
// The chapter feeds a peer-book file name, so it passes the same
// plain-identifier guard as the server's preview targets.
function previewChapterOf(path: string | null | undefined): string | null {
  const stem = bookStem();
  const name = (path ?? "").replace(/^.*\//, "");
  const prefix = `${stem}-preview-`;
  if (!stem || !name.startsWith(prefix) || !name.endsWith(".pdf")) return null;
  const chapter = name.slice(prefix.length, -".pdf".length);
  return /^[A-Za-z0-9_-]+$/.test(chapter) ? chapter : null;
}

// The peer pane's document, derived from the manifest's parallelPdf block and
// the primary selection: with a chapter preview shown in the Rendered PDF pane
// the peer mirrors it with the peer book's preview of the same chapter,
// otherwise it shows the peer debug PDF. Returns repo-relative paths alongside
// the fetch URLs so watch events can be matched against whichever document is
// currently mirrored. Null when the project has no peer or the block is
// incomplete.
function peerPdfDoc(): { url: string; mapUrl: string | null; repoPdf: string; repoMap: string | null } | null {
  const peer = project.parallelPdf;
  if (!peer) return null;
  const mount = peer.mount?.replace(/\/$/, "") || "";
  const debugPath = peer.path?.replace(/^\/+/, "") || "";
  if (!mount || !debugPath) return null;
  const mapPath = peer.mapPath?.replace(/^\/+/, "") || "";
  const chapter = previewChapterOf(state.pdf.path);
  const pdfPath =
    chapter && debugPath.endsWith("-debug.pdf")
      ? `${debugPath.slice(0, -"-debug.pdf".length)}-preview-${chapter}.pdf`
      : debugPath;
  return {
    url: renderedPdfPath(`${mountPrefix()}${mount}/${pdfPath}`),
    mapUrl: mapPath ? `${mountPrefix()}${mount}/${mapPath}` : null,
    repoPdf: renderedPdfPath(`${peer.dir}/${pdfPath}`),
    repoMap: mapPath ? `${peer.dir}/${mapPath}` : null,
  };
}

// (Re)load the peer pane onto the document peerPdfDoc() currently names. A
// same-document reload may preserve the reading position; switching documents
// starts fresh at the active entry.
let peerLoadedUrl: string | null = null;
let peerDirty = false;
let peerLoadPromise: Promise<void> | null = null;

function loadPeerPdf(options: { preserveScroll?: boolean } = {}): void {
  if (!visiblePaneNames().includes("pdf-peer")) {
    peerDirty = true;
    return;
  }
  peerDirty = false;
  const doc = peerPdfDoc();
  if (!doc) return;
  const sameDoc = lightPdfPath(doc.url) === lightPdfPath(peerLoadedUrl ?? "");
  const themeChange = sameDoc && doc.url !== peerLoadedUrl;
  peerLoadedUrl = doc.url;
  els.pdfPeerLink.href = doc.url;
  peerLoadPromise = initParallelPdf(
    doc.url,
    doc.mapUrl ?? undefined,
    sameDoc
      ? {
          ...options,
          preserveScroll: options.preserveScroll || themeChange,
        }
      : {},
  )
    .then(() => {
      const landing = chapterLanding;
      if (
        !landing ||
        state.pdf.path !== landing.path ||
        peerLoadedUrl !== doc.url ||
        parallelDocumentPath() !== doc.url ||
        !els.pdfPeerViewer.querySelector(".pdf-page")
      )
        return;
      landAtChapterEdge(els.pdfPeerViewer, landing.direction);
      landing.peerDone = true;
      if (landing.primaryDone) chapterLanding = null;
    })
    .catch(reportError);
}

// The peer PDF and its map land in one build burst; debounce so the pair of
// watch events re-initializes the peer pane once, with both files fresh.
let peerReloadTimer: ReturnType<typeof setTimeout> | null = null;

function schedulePeerPdfReload(): void {
  if (peerReloadTimer != null) window.clearTimeout(peerReloadTimer);
  peerReloadTimer = window.setTimeout(() => {
    peerReloadTimer = null;
    // The peer tex backing the copy shortcut was rebuilt with the PDF.
    peerTextCache.clear();
    loadPeerPdf({ preserveScroll: true });
  }, 400);
}

let definitionRefreshTimer: ReturnType<typeof setTimeout> | undefined;
let definitionRefreshToken = 0;
function refreshDefinitions(): void {
  if (project.static) return;
  const token = ++definitionRefreshToken;
  clearTimeout(definitionRefreshTimer);
  definitionRefreshTimer = setTimeout(() => {
    void fetch("manifest.json", { cache: "no-cache" })
      .then((response) => {
        if (!response.ok) throw new Error(`manifest.json: ${response.status}`);
        return response.json();
      })
      .then((next) => {
        if (token !== definitionRefreshToken) return;
        project.definitionRegistry = next.definitionRegistry;
        project.chapterTitles = next.chapterTitles;
        state.katexMacros = next.katexMacros ?? {};
        project.fixedMath = next.fixedMath ?? {};
        for (const info of markerInfoCache.values()) delete info.titleHtml;
        markerWindow = null;
        updateMarkerField();
        if (!els.markerPopover.hidden) renderMarkerList();
        dismissTermPopup();
      })
      .catch(reportError);
  }, 250);
}

function applyWatchedChange(path: string): void {
  const changed = repoPath(path);
  if (
    /\.(?:md|aux)$/.test(changed) ||
    /(?:^|\/)tex\/macros\.tex$/.test(changed) ||
    changed === project.bookManifest ||
    changed === repoPath(state.mapPath)
  )
    refreshDefinitions();
  const fullPeer = project.parallelPdf;
  if (lightPdfPath(changed) === project.pdf || (fullPeer && lightPdfPath(path) === `${fullPeer.dir}/${fullPeer.path}`))
    invalidateReferenceDocuments();
  // Any rebuild may have rewritten the viewer's own bundle (editing pdf.ts/app.ts
  // → build/*.js; the book filter change in this same session rebuilt the PDF in
  // one burst). A single build/*.js watch event can be coalesced or missed,
  // stranding the page on stale client code until the next tab focus. So re-check
  // the build version on every change — checkForNewBuild is a no-op unless the
  // viewer build actually changed, in which case it forces a full reload — and the
  // reliably-delivered PDF/map events thus act as a backstop for the asset event.
  scheduleReload();
  if (VIEWER_ASSET.test(changed)) return;
  // TeX writes PDFs and maps repeatedly during a build. Do not expose those
  // intermediate files; a done event loads the completed pair in the background.
  const owner = [...buildingProjects].find(
    (dir) =>
      path.replace(/^\/+/, "").startsWith(`${dir}/build/`) || (dir === project.dir && changed.startsWith("build/")),
  );
  if (owner && /\.(?:pdf|json)$/.test(changed)) {
    const artifacts = pendingBuildArtifacts.get(owner) ?? new Set<string>();
    artifacts.add(path);
    pendingBuildArtifacts.set(owner, artifacts);
    return;
  }
  if (changed === repoPath(state.mapPath) || changed === project.bookManifest) {
    reloadMap().catch(reportError);
    return;
  }
  if (changed === repoPath(state.selectedSources.md) || changed.endsWith(".lean")) refreshCorrespondence(true);
  if (changed === repoPath(state.selectedSources.md) || changed.endsWith(".lean")) refreshFormulaOverlays(true);
  if (changed === repoPath(state.selectedSources.md)) refreshSource("md").catch(reportError);
  if (changed === repoPath(state.selectedSources.lean)) refreshSource("lean").catch(reportError);
  if (changed === repoPath(state.selectedSources.tex)) refreshSource("tex").catch(reportError);
  if (state.pdf.path && changed === repoPath(renderedPdfPath(state.pdf.path))) reloadPdf();
  // The peer pane's current document (debug or mirrored chapter preview) or
  // its sourcemap was rebuilt (the peer repo lives outside this mount, so
  // compare against dir-prefixed repo paths).
  const peerDoc = peerPdfDoc();
  if (peerDoc && (changed === peerDoc.repoPdf || changed === peerDoc.repoMap)) schedulePeerPdfReload();
}

// The booklink source map (or chapter manifest) was regenerated: reload it,
// rebuild the entry list and file choices, re-render the source panes, and
// re-resolve PDF targets so markers track the new entries.
async function reloadMap(options: { refreshPdf?: boolean } = {}): Promise<void> {
  let map: any;
  try {
    map = await fetch(state.mapPath ?? "", { cache: "no-cache" }).then((response) => {
      if (!response.ok) throw new Error(`${state.mapPath}: HTTP ${response.status}`);
      return response.json();
    });
  } catch (error) {
    reportError(error);
    return;
  }
  // An edit anywhere earlier in the book shifts every later entry index, so
  // follow the active marker by its permalink id instead of its position.
  flushLocation();
  const position = captureViewPosition();
  const location = state.location;
  const activeMarker = readLocationParams(window.location.search).marker || markerId(state.entries, state.activeIndex);
  state.map = map;
  state.entries = map.entries || [];
  state.skips = map.skips || [];
  markerInfoCache.clear();
  state.fileChoices.md = await mdChoices(map);
  state.fileChoices.lean = leanChoices(map, state.fileChoices.md);
  state.fileChoices.tex = uniquePaths([map.texFile]);
  // A selected file may have been renamed or dropped from the regenerated map;
  // fall back to a still-present choice so the pane doesn't point at a 404 and
  // the dropdown value still matches an option.
  const clampSource = (kind: "md" | "lean" | "tex", fallback?: string | null): string | null => {
    const current = state.selectedSources[kind];
    if (current && state.fileChoices[kind].includes(current)) return current;
    return (fallback && state.fileChoices[kind].includes(fallback) ? fallback : state.fileChoices[kind][0]) ?? null;
  };
  state.selectedSources.md = clampSource("md");
  state.selectedSources.lean = clampSource("lean", correspondingLeanForMd(state.selectedSources.md ?? ""));
  state.selectedSources.tex = clampSource("tex");
  populateFileSelect(els.mdSelect, state.fileChoices.md);
  populateFileSelect(els.leanSelect, state.fileChoices.lean);
  updateMarkerField();
  state.location =
    location.kind === "skip" && state.skips?.some((skip: any) => skip.key === location.key)
      ? location
      : {
          kind: "entry",
          index:
            markerIndex(state.entries, activeMarker) ??
            Math.min(location.kind === "entry" ? location.index : 0, Math.max(0, state.entries.length - 1)),
        };
  await renderSelectedSources();
  if (state.pdf.document && options.refreshPdf !== false) {
    state.pdf.targetPromise = resolvePdfTargets(state.pdf.renderToken, false).catch((error) => {
      console.error("[booklink] Failed to resolve PDF targets:", error);
    });
    await state.pdf.targetPromise;
  }
  applyActiveState();
  restoreViewPosition(position);
}

// Re-fetch and re-render one source pane in place, preserving its scroll
// position. For the Lean pane, also push the new text to the LSP server and
// re-query the current goal so the infoview tracks the edit.
async function refreshSource(kind: "md" | "lean" | "tex"): Promise<void> {
  const path = state.selectedSources[kind];
  if (!path || !state.sources) return;
  const normalized = repoPath(path);
  state.sourceCache.delete(normalized);
  state.highlightCache.delete(normalized);
  state.foldCache.delete(normalized);
  highlightDataPromises.delete(normalized);
  if (!visiblePaneNames().includes(kind) && !(kind === "lean" && visiblePaneNames().includes("infoview"))) {
    delete renderedSources[kind];
    return;
  }
  let text: string;
  try {
    text = await loadText(path);
  } catch (error) {
    reportError(error);
    return;
  }
  state.sourceCache.set(normalized, text);
  state.sources[kind] = text;
  const highlights = await loadCachedHighlights(path);
  const folds = kind === "lean" ? await loadCachedLeanFolds(path) : [];
  const pane = state.panes[kind];
  const prevScroll = pane ? paneScrollTop(pane) : 0;
  const position = captureViewPosition();
  renderSource(
    els[SOURCE_ELEMENT[kind] as "mdSource" | "leanSource" | "texSource"],
    text,
    collectSpans(kind),
    kind,
    highlights,
    folds,
    kind === "lean" ? "utf16" : "codepoint",
    kind === "md" ? collectSkipSpans() : [],
  );
  applyActiveState();
  if (pane) scrollPane(pane, { top: prevScroll, behavior: "auto" });
  if (position.sources[kind])
    restoreViewPosition({ ...position, pdf: null, peer: null, sources: { [kind]: position.sources[kind] } });
  renderedSources[kind] = path;
  if (kind === "lean" && lspIsReady()) {
    lspChangeDocument(normalized, text);
    if (state.lsp.position) {
      queryGoalAt(state.lsp.position.line, state.lsp.position.character).catch(reportError);
    }
  }
}

// The live server serves every project at its own mount and lists them at
// /projects.json; the book selector navigates between those mounts. A static
// dist holds a single project, so the selector stays hidden there.
async function initBookSelect(): Promise<void> {
  if (!els.bookSelect || project.static) return;
  const bookSelect = els.bookSelect;
  let projects: any = null;
  try {
    const response = await fetch("/projects.json", { cache: "no-store" });
    if (response.ok) projects = await response.json();
  } catch (_error) {
    projects = null;
  }
  if (!Array.isArray(projects) || projects.length < 2) return;
  setHTML(
    bookSelect,
    projects
      .map(
        (entry: any) =>
          `<option value="${escapeHtml(entry.mount)}"${entry.dir === project.dir ? " selected" : ""}>${escapeHtml(entry.selectorLabel || entry.name || entry.dir)}</option>`,
      )
      .join(""),
  );
  bookSelect.addEventListener("change", () => {
    const layout = JSON.stringify(state.layout);
    const search = withSharedPreferences(
      "",
      { [LAYOUT_STORAGE_KEY]: layout, [PDF_MODE_KEY]: state.pdfMode },
      layoutDefaults(),
    );
    window.location.href = `${mountPrefix()}${bookSelect.value}/${search}`;
  });
  const label = document.getElementById("book-select-label");
  if (label) label.hidden = false;
  enhanceSelect(bookSelect);
}

// Register the per-entry activation orchestration and each pane's scroll
// handlers with the sync hub, so sync.setActive / sync.syncFromScroll can drive
// the panes without app and the pane modules importing each other.
function wireActiveSync(): void {
  // Every navigation, explicit or by scroll, updates the address bar and the
  // stored position.
  setLocationHook(() => {
    applyActiveState();
    recordLocation();
  });
  setActivateHook(async (index, originPane, mode, current) => {
    if (mode === "navigate" && originPane) setFocusPane(originPane);
    await syncSelectedSourcesForEntry(state.entries[index]);
    if (!current()) return;
    refreshFormulaOverlays();
    applyActiveState();
    // When a chapter preview is shown, follow an activated marker to its
    // chapter's preview, so the PDF jumps to it even when the marker lives in a
    // different chapter than the one displayed. (Debug/release show the whole
    // book, so no switch is needed.)
    if (mode === "navigate" && isPreviewPath(state.pdf.path ?? "")) {
      const url = previewUrlForChapter(chapterStemOf(state.selectedSources.md));
      if (url && url !== state.pdf.path) await setPdf(url);
      if (!current()) return;
    }
    if (mode === "navigate" && lspIsReady() && state.lsp.uri) {
      const pos = leanEntryPosition(state.entries[index]);
      queryGoalAt(pos.line, pos.character).catch(reportError);
    }
  });
  for (const paneName of ["md", "lean", "tex"]) {
    registerPaneSync(paneName, {
      supports: (location) => location.kind === "entry" || paneName === "md",
      scrollTo: (location) =>
        location.kind === "entry" ? scrollPaneToEntry(paneName, location.index) : scrollMarkdownToSkip(location),
      nearest: () => {
        if (paneName === "md") {
          const skip = nearestSkipFromMarkdownScroll();
          if (skip) return { kind: "skip", ...skip };
        }
        const index = nearestEntryFromScroll(paneName);
        return index === null ? null : { kind: "entry", index };
      },
    });
  }
  registerPaneSync("pdf", {
    supports: () => true,
    scrollTo: (location) => (location.kind === "entry" ? scrollPdfToEntry(location.index) : scrollPdfToSkip(location)),
    nearest: () => {
      const skip = nearestSkipFromPdfScroll();
      if (skip) return { kind: "skip", ...skip };
      const index = nearestEntryFromPdfScroll();
      return index === null ? null : { kind: "entry", index };
    },
  });
  if (project.parallelPdf) {
    registerPaneSync("pdf-peer", {
      supports: () => true,
      scrollTo: (location) =>
        location.kind === "entry" ? scrollParallelPdfToEntry(location.index) : scrollParallelPdfToSkip(location),
      nearest: () => {
        const skip = nearestSkipFromParallelPdfScroll();
        if (skip) return { kind: "skip", ...skip };
        const index = nearestEntryFromParallelPdfScroll();
        return index === null ? null : { kind: "entry", index };
      },
    });
  }
  // pdf.ts resolved its entry targets; redraw the PDF overview rail, which reads
  // them. (pdf.ts cannot call the rail code in app.ts directly.)
  setOnPdfTargetsResolved(() => {
    updateMarkRail("pdf");
    // Wait for pdf.ts's final anchor restoration before positioning the edge.
    if (chapterLanding) void Promise.resolve(state.pdf.targetPromise).then(finishChapterLanding).catch(reportError);
  });
}

async function init(): Promise<void> {
  startupStep("manifest", t("Loading book settings…"));
  // Offline support is auxiliary: registration failure cannot break startup.
  await initOffline().catch(reportError);
  const language = document.querySelector<HTMLSelectElement>("#ui-language")!;
  language.value = uiLanguagePreference();
  language.addEventListener("change", () => {
    writePreference("formalization-viewer-ui-language", language.value);
    if (uiLanguagePreference() !== language.value) {
      language.value = uiLanguagePreference();
      return;
    }
    saveReloadPosition();
    location.reload();
  });
  initAppearance((modeChanged) => {
    window.requestAnimationFrame(updateAllMarkRails);
    if (!modeChanged) return;
    invalidateReferenceDocuments();
    if (state.pdf.path) void setPdf(state.pdf.path, { preserveScroll: true, scrollToActive: false }).catch(reportError);
  });
  state.pdfMode = readPreference(PDF_MODE_KEY) === "full" ? "full" : "chapter";
  window.history.scrollRestoration = "manual";
  const savedPosition = reloadPosition();
  const params = new URLSearchParams(window.location.search);
  setProject(
    await fetch("manifest.json", { cache: "no-cache" }).then((response) => {
      if (!response.ok) throw new Error(`manifest.json: HTTP ${response.status}`);
      return response.json();
    }),
  );
  document.getElementById("md-source")?.setAttribute("lang", String(project.dir).includes("ja") ? "ja" : "en");
  // The reading session is per book, so it can only be keyed once the manifest
  // names the mount this page is serving.
  storeKey = sessionKey(project.mount || project.dir || "");
  // Fixed formulas arrive as precomputed MathML; chat alone loads a converter.
  state.katexMacros = project.katexMacros || {};
  initBookSelect().catch(reportError);
  // Keep the PDF band overlays aligned whenever the pane geometry settles, so a
  // band drawn against not-yet-final geometry self-corrects without a reload.
  observePdfBandGeometry();
  // A static dist has no watcher endpoint; skip the EventSource retry loop.
  if (!project.static) {
    connectFileWatch(onWatchedFileChanged);
    if (project.dir) primaryBuildIndicator({ dir: project.dir, state: "done" });
    if (project.parallelPdf?.dir) peerBuildIndicator({ dir: project.parallelPdf.dir, state: "done" });
    connectBuildStatus(onBuildStatus, () => reportPdfSelection(state.pdf.path));
    // Safety net: reload if a rebuild landed while a watch event was missed.
    installReloadGuard();
  }
  loadLayout();
  loadLineNumbers();
  applyLineNumbers();
  loadMarkHighlights();
  applyMarkHighlights();
  loadLinkHighlights();
  applyLinkHighlights();
  loadSync();
  updateSegmented(els.syncSeg, state.sync ? "on" : "off");
  const defaults = {
    map: repoUrl(project.sourceMap ?? ""),
    pdf: repoUrl(project.pdf ?? ""),
  };
  const mapPath = params.get("map") || defaults.map;
  state.mapPath = mapPath;
  const { choices: pdfChoiceList, initialPath: pdfPath } = pdfChoices(params, defaults);
  // Degrade to an empty map if the sourcemap is missing: it does not exist on a
  // fresh checkout before the first build, and 404s after a rename until the
  // rebuild lands. The UI wiring below must still run (mirroring reloadMap's
  // guarded fetch) so a yet-to-be-built map never leaves the whole viewer — pane
  // drag, menus, selects, keyboard — dead. The watcher re-renders once the build
  // produces the map.
  startupStep("map", t("Loading source map…"));
  let map: any;
  try {
    map = await fetch(mapPath, { cache: "no-cache" }).then((response) => {
      if (!response.ok) throw new Error(`${mapPath}: HTTP ${response.status}`);
      return response.json();
    });
  } catch (error) {
    reportError(error);
    map = {};
  }

  state.map = map;
  state.entries = map.entries || [];
  state.skips = map.skips || [];
  startupStep("files", t("Finding Markdown and Lean documents…"));
  state.fileChoices.md = await mdChoices(map);
  state.fileChoices.lean = leanChoices(map, state.fileChoices.md);
  state.fileChoices.tex = uniquePaths([map.texFile]);
  state.selectedSources.md = repoPath(state.entries[0]?.match?.source || state.fileChoices.md[0]);
  state.selectedSources.lean = repoPath(
    map.leanFile || correspondingLeanForMd(state.selectedSources.md) || state.fileChoices.lean[0],
  );
  state.selectedSources.tex = repoPath(map.texFile || state.fileChoices.tex[0]);
  // Select linked/stored documents before any pane starts downloading them.
  const initialLocation = readLocationParams(window.location.search);
  const session = storedSession();
  const initialIndex = markerIndex(state.entries, initialLocation.marker || session.marker || "");
  const initialEntry = initialIndex !== null ? state.entries[initialIndex] : null;
  if (initialEntry) {
    state.location = { kind: "entry", index: initialIndex! };
    state.selectedSources.md = repoPath(initialEntry.match?.source) || state.selectedSources.md;
    state.selectedSources.lean = repoPath(initialEntry.lean?.source) || state.selectedSources.lean;
    state.selectedSources.tex = repoPath(initialEntry.texMatch?.source) || state.selectedSources.tex;
  }

  state.panes = {
    md: els.mdSource,
    lean: els.leanSource,
    tex: els.texSource,
  };
  state.paneSections = {};
  for (const name of PANE_NAMES) {
    state.paneSections[name] = document.querySelector(`.pane[data-pane="${name}"]`);
  }
  setFocusPane(state.focusedPane || "md");

  if (project.parallelPdf && peerPdfDoc()) {
    const peerLabel = project.parallelPdf.label ? t(project.parallelPdf.label) : t("Parallel PDF");
    state.paneSections["pdf-peer"]?.setAttribute("aria-label", peerLabel);
    els.pdfPeerViewer.setAttribute("aria-label", t("{0} preview", peerLabel));
    const optionLabel = els.pdfPeerPaneOption.querySelector("span");
    if (optionLabel) optionLabel.textContent = peerLabel;
    els.pdfPeerLink.href = peerPdfDoc()!.url;
    els.pdfPeerPaneOption.hidden = false;
    const checkbox = els.pdfPeerPaneOption.querySelector("input") as HTMLInputElement | null;
    if (checkbox) checkbox.checked = treeLeaves(state.layout.tree).includes("pdf-peer");
  }

  startupStep("panes", t("Preparing pane layout and controls…"));
  wirePaneMaximize();
  applyPaneLayout();

  // Populate the native selects and wire every UI event handler (pane drag,
  // menus, keyboard, select popovers) BEFORE loading any content. The content
  // fetches/renders below are guarded, so a corrupt source or sourcemap blanks
  // one pane instead of throwing out of init() and leaving the whole UI — pane
  // drag included — unwired.
  // Remember which render the reader was viewing, and report it to the server so
  // the auto-build tracks it. Set before the first setPdf below so the initial
  // selection is both stored and reported.
  setOnPdfSelected((path) => {
    if (chapterLanding?.path !== path) chapterLanding = null;
    writePreference(PDF_MODE_KEY, state.pdfMode);
    if (!project.static && visiblePaneNames().some((name) => name === "pdf" || name === "pdf-peer"))
      reportPdfSelection(path);
    // The peer pane mirrors the selection's document kind (debug PDF vs the
    // same chapter's preview); follow a kind switch with the peer document.
    if (peerPdfDoc()?.url !== peerLoadedUrl) loadPeerPdf();
  });
  if (!project.static) {
    // A missing debug PDF or preview 404s until the server renders it; show build
    // progress in the pane rather than the raw error.
    setOnPdfLoadFailed((path, error) =>
      (error as { status?: number })?.status === 404 && (isPreviewPath(path) || repoPath(path) === project.pdf)
        ? t("Building PDF…")
        : null,
    );
    // Same for the peer pane: mirroring a fresh preview selection loads the
    // peer book's preview before its build lands; the watch event for the
    // built file reloads the pane.
    setOnParallelPdfLoadFailed((path, error) =>
      (error as { status?: number })?.status === 404 &&
      /-(?:debug|preview-[A-Za-z0-9_-]+)\.pdf$/.test(path.replace(/\?.*$/, ""))
        ? t("Building PDF…")
        : null,
    );
  }
  const chapters = chapterPreviewChoices().filter(
    (choice) => !project.static || project.pdfs?.includes(repoPath(choice.path)),
  );
  pdfChoiceList.unshift(...chapters);
  const modeGroup = document.getElementById("pdf-mode-seg")!;
  initPdfLayout(() => {
    invalidateReferenceDocuments();
    // Reflow changes page numbers; return to the active source anchor instead
    // of carrying an old physical page offset into the new layout.
    if (state.pdf.path) {
      const path = isPreviewPath(state.pdf.path) ? state.pdf.path : repoUrl(project.pdf ?? "");
      if (path) setPdf(path).catch(reportError);
    }
  });
  modeGroup.querySelector<HTMLButtonElement>('button[data-value="chapter"]')!.disabled = chapters.length === 0;
  const savedPdf = savedPosition?.pdfPath;
  startupStep("pdf", t("Loading PDF and preparing pages…"));
  const initialPdfLoad = renderPdfChoices(
    pdfChoiceList,
    savedPdf &&
      isPreviewPath(savedPdf) === (state.pdfMode === "chapter") &&
      pdfChoiceList.some((choice) => choice.path === savedPdf)
      ? savedPdf
      : initialPdfPath(pdfChoiceList, params, pdfPath),
  ).catch(reportError);
  // The onPdfSelected hook above already loaded the peer document mirroring the
  // restored selection; this only covers the case where no PDF got selected.
  if (peerLoadedUrl === null) loadPeerPdf();
  populateFileSelect(els.mdSelect, state.fileChoices.md);
  populateFileSelect(els.leanSelect, state.fileChoices.lean);

  wireActiveSync();
  wireEvents();
  wireChapterPull();
  for (const button of modeGroup.querySelectorAll<HTMLButtonElement>("button[data-value]")) {
    button.addEventListener("click", () => {
      const path = pdfPathForMode(button.dataset.value!);
      if (path) setPdf(path).catch(reportError);
    });
  }
  els.pdfSelect.addEventListener("change", () => setPdf(els.pdfSelect.value).catch(reportError));
  // Every dropdown owns its label and caret through the same component.
  document.querySelectorAll<HTMLSelectElement>("select").forEach((select) => enhanceSelect(select));

  // Chat is auxiliary: isolate its startup like the content load below, so
  // a failure to build its UI is reported instead of reaching init's catch
  // and replacing the whole viewer.
  try {
    initChat();
  } catch (error) {
    reportError(error);
  }
  paneContentEnabled = true;
  startVisibleInfoview();
  // The layout and controls are usable now. Each visible pane owns its loading
  // status; an unrelated pane cannot cover the reader with a startup screen.
  const navigateToSearchResult = searchNavigation({
    togglePaneMaximize,
    applyPaneLayout,
    setActive,
    correspondingLeanForMd,
    renderSelectedSources,
    setFocusPane,
    recordSession,
  });
  initCorrespondence(navigateToSearchResult);
  initFormulaOverlays(
    (index) => setActive(index, "md", true),
    async (source) => {
      if (!state.fileChoices.lean.includes(source) || state.selectedSources.lean === source) return;
      state.selectedSources.lean = source;
      await renderSelectedSources();
    },
    renderPdfPage,
  );
  // Definition previews list where a term or section is used; a use opens the
  // source pane at that file and line, exactly like a search result.
  setOpenDefinitionUse((use) => void navigateToSearchResult(use.file, use.line));
  const searchApi = initSearch(navigateToSearchResult, async (name) => {
    if (!visiblePaneNames().includes(name)) {
      if (!treeLeaves(state.layout.tree).includes(name)) state.layout.tree = addLeaf(state.layout.tree, name);
      if (state.layout.maximized && state.layout.maximized !== name) togglePaneMaximize(state.layout.maximized);
      applyPaneLayout();
    }
    await ensureVisiblePaneContent();
    if (name === "pdf") {
      await currentPdfLoad();
      if (!state.pdf.document && state.pdf.path) await setPdf(state.pdf.path, { scrollToActive: false });
    } else {
      await peerLoadPromise;
      if (!parallelPdfSearchState().document) {
        loadPeerPdf();
        await peerLoadPromise;
      }
    }
  });
  const searchSource = params.get("searchSource");
  const searchLine = Number(params.get("searchLine"));
  finishStartup();

  // Content load: guarded so one bad source/highlight/sourcemap cannot abort
  // init() and leave the panes unwired.
  try {
    startupStep("sources", t("Loading source documents…"));
    await renderSelectedSources();
    updateMarkerField();
    startupStep("position", t("Restoring reading position and synchronized panes…"));
    await navigateToInitialLocation();
    await restoreSessionSources();
    await Promise.allSettled([initialPdfLoad, visiblePaneNames().includes("pdf-peer") ? peerLoadPromise : null]);
    if (savedPosition) {
      for (const kind of ["md", "lean", "tex"] as const) {
        const path = savedPosition.sources?.[kind]?.path;
        if (path && state.fileChoices[kind].includes(path)) state.selectedSources[kind] = path;
      }
      await renderSelectedSources();
      await Promise.allSettled([state.pdf.targetPromise, peerLoadPromise]);
      restoreViewPosition(savedPosition);
    }
  } catch (error) {
    reportError(error);
  }
  if (searchSource && searchLine > 0) await navigateToSearchResult(searchSource, searchLine);
  // Startup is done, position restored: the panes now show what they will keep
  // showing until the reader moves. Browser automation waits on this rather than
  // on the first rendered mark, which is still the pre-restore first entry.
  replaceSharedUrl(
    withSharedPreferences(
      window.location.search,
      { [LAYOUT_STORAGE_KEY]: JSON.stringify(state.layout), [PDF_MODE_KEY]: state.pdfMode },
      layoutDefaults(),
    ),
  );
  await initViewerAgent(visiblePaneNames, loadText, setActive, searchApi.searchBook);
  document.body.dataset.viewerReady = "1";
  finishStartup();
}

init().catch((error) => {
  finishStartup();
  els.workspace.textContent = t("Unable to initialize viewer: {0}", error.message);
  console.error(error);
});
