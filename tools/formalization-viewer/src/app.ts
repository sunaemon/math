import { initHighlighter, computeHighlights, languageForPath, leanFolds } from "./highlight.js";
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
import { enhanceSelect } from "./select-dropdown.js";
import { renderSource, markerStyle, buildLineStarts } from "./source-render.js";
import {
  setActive,
  syncFromScroll,
  visiblePaneNames,
  isPaneSuppressed,
  registerPaneSync,
  setActivateHook,
} from "./sync.js";
import {
  setPdf,
  clearPdfViewer,
  renderPdfChoices,
  pdfChoices,
  pdfLabel,
  renderVisiblePdfPages,
  updatePdfPageFromScroll,
  scrollPdfToEntry,
  nearestEntryFromPdfScroll,
  resolvePdfTargets,
  updatePdfStatus,
  refreshPdfLayoutGeometry,
  observePdfBandGeometry,
  reloadPdf,
  setOnPdfTargetsResolved,
  setOnPdfSelected,
  setOnPdfLoadFailed,
} from "./pdf.js";

const KATEX_MODULE_URL = new URL("../vendor/katex/katex.mjs", import.meta.url).toString();
const LAYOUT_STORAGE_KEY = "formalization-viewer-layout-v2";
const LINE_NUMBERS_STORAGE_KEY = "formalization-viewer-line-numbers";

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
  els.aboutVersionText.textContent = parts.length ? parts.join(" · ") : "unknown";
  if (els.aboutCopy) els.aboutCopy.dataset.copy = version.rev || version.describe || "";

  if (els.aboutRepo) {
    const repo = safeHref(project.repository || "");
    els.aboutRepo.textContent = repo ? repo.replace(/^https?:\/\//, "") : "—";
    if (repo) els.aboutRepo.href = repo;
    else els.aboutRepo.removeAttribute("href");
  }

  const license = project.license || {};
  els.aboutLicenseSummary.textContent = license.summary || "";
  els.aboutLicenseList.innerHTML = (license.items || [])
    .map((item, i) => {
      const scope = escapeHtml(item.scope || "");
      const spdx = escapeHtml(item.spdx || "");
      const name = item.file ? escapeHtml(item.file.split("/").pop() || item.file) : "";
      // Vendored components carry a version and an upstream repository link; the
      // repo's own license scopes (MIT / CC BY 4.0) carry neither.
      const version = item.version ? ` <span class="about-license-version">${escapeHtml(item.version)}</span>` : "";
      const sourceHref = item.source ? safeHref(item.source) : "";
      const source = sourceHref
        ? ` · <a class="about-license-source" href="${escapeHtml(sourceHref)}" target="_blank" rel="noreferrer">repository ↗</a>`
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
    })
    .join("");
}

function openAbout(): void {
  populateAbout();
  // Close the menu the About item lives in, then show the dialog.
  els.settingsMenu.hidden = true;
  els.settingsToggle.setAttribute("aria-expanded", "false");
  els.aboutOverlay.hidden = false;
  els.aboutClose?.focus();
}

function closeAbout(): void {
  els.aboutOverlay.hidden = true;
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

function loadLayout(): void {
  let stored: any = {};
  try {
    stored = JSON.parse(localStorage.getItem(LAYOUT_STORAGE_KEY) || "{}");
  } catch (_error) {
    stored = {};
  }
  state.layout = { tree: validateTree(stored.tree) || defaultTree() };
}

function saveLayout(): void {
  localStorage.setItem(LAYOUT_STORAGE_KEY, JSON.stringify(state.layout));
}

function loadLineNumbers(): void {
  state.lineNumbers = localStorage.getItem(LINE_NUMBERS_STORAGE_KEY) === "on";
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

function checkedPaneNames(): string[] {
  return els.paneChecks.filter((input) => input.checked).map((input) => input.value);
}

function syncPaneChecksFromLayout(): void {
  const visible = new Set(visiblePaneNames());
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
  const disabled = visiblePaneNames().length < 2;
  for (const btn of Array.from(els.layoutSeg.querySelectorAll("button"))) {
    (btn as HTMLButtonElement).disabled = disabled;
  }
}

function applyPaneCheckboxes(): void {
  const checked = new Set(checkedPaneNames());
  const current = visiblePaneNames();
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
  setActive(state.activeIndex).catch(reportError);
}

function setLayoutKind(kind: string): void {
  const panes = visiblePaneNames();
  if (kind === "columns") state.layout.tree = makeSplit("row", panes);
  else if (kind === "rows") state.layout.tree = makeSplit("col", panes);
  else return;
  saveLayout();
  applyPaneLayout();
  setActive(state.activeIndex).catch(reportError);
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
function applySplitFlex(container: HTMLElement, node: LayoutNode): void {
  const ratios = node.ratios ?? [];
  const total = ratios.reduce((sum, ratio) => sum + ratio, 0) || (node.children ?? []).length;
  const slots = [...container.children].filter((child) => !child.classList.contains("splitter")) as HTMLElement[];
  slots.forEach((slot, i) => {
    slot.style.flex = `${ratios[i] / total} 1 0`;
  });
}

function buildSplitter(node: LayoutNode, leftIndex: number): HTMLElement {
  const splitter = document.createElement("div");
  splitter.className = `splitter splitter-${node.dir === "row" ? "vertical" : "horizontal"}`;
  splitter.addEventListener("mousedown", (event) => {
    event.preventDefault();
    state.resizing = { node, leftIndex, container: splitter.parentElement };
    splitter.classList.add("dragging");
    document.body.classList.add("is-resizing");
  });
  return splitter;
}

function buildLayoutNode(node: LayoutNode | null): HTMLElement | null {
  if (!node) return null;
  if (node.pane) {
    const section = state.paneSections?.[node.pane];
    if (!section) return null;
    section.hidden = false;
    section.classList.remove("pane-hidden");
    section.style.display = "";
    return section;
  }
  const container = document.createElement("div");
  container.className = "split";
  container.dataset.dir = node.dir;
  (node.children ?? []).forEach((child, i) => {
    if (i > 0) container.append(buildSplitter(node, i - 1));
    const childEl = buildLayoutNode(child);
    if (childEl) container.append(childEl);
  });
  applySplitFlex(container, node);
  return container;
}

function applyPaneLayout(): void {
  const visible = new Set(visiblePaneNames());
  const workspace = els.workspace;
  const parking = paneParking();
  for (const name of PANE_NAMES) {
    const section = state.paneSections?.[name];
    if (section && section.parentNode) section.parentNode.removeChild(section);
  }
  workspace.innerHTML = "";
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
  const root = buildLayoutNode(state.layout.tree);
  if (root) workspace.append(root);
  workspace.append(dropOverlayElement());
  edgeZoneElements().forEach((zone) => workspace.append(zone));
  syncLayoutSelect();
  syncPaneChecksFromLayout();
  refreshPdfLayoutGeometry();
  // Source panes rewrap at their new size, so their rail ticks must be
  // recomputed; defer a frame so flex layout has settled.
  window.requestAnimationFrame(() => updateAllMarkRails());
}

function resizePair(ratios: number[], index: number, pointerRatio: number): number[] {
  const total = ratios.reduce((sum, ratio) => sum + ratio, 0);
  const before = ratios.slice(0, index).reduce((sum, ratio) => sum + ratio, 0);
  const pairTotal = ratios[index] + ratios[index + 1];
  const boundary = pointerRatio * total;
  const first = Math.min(pairTotal - 0.25, Math.max(0.25, boundary - before));
  const next = [...ratios];
  next[index] = first;
  next[index + 1] = pairTotal - first;
  return next;
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
  setActive(state.activeIndex).catch(reportError);
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
  setActive(state.activeIndex).catch(reportError);
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

async function loadCachedHighlights(path: string | null, text: string): Promise<any[]> {
  const lang = languageForPath(repoPath(path));
  if (!lang) return [];
  const highlighter = await initHighlighter();
  if (!highlighter) return [];
  const normalized = repoPath(path);
  if (!state.highlightCache.has(normalized)) {
    state.highlightCache.set(normalized, computeHighlights(highlighter, text, lang));
  }
  return state.highlightCache.get(normalized) ?? [];
}

// Ranges of `/-@ … -/` machine-metadata comments to fold (Lean panes only).
async function loadCachedLeanFolds(path: string | null, text: string): Promise<any[]> {
  if (languageForPath(repoPath(path)) !== "lean") return [];
  const highlighter = await initHighlighter();
  if (!highlighter) return [];
  const normalized = repoPath(path);
  if (!state.foldCache.has(normalized)) {
    state.foldCache.set(normalized, leanFolds(highlighter, text));
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
  select.innerHTML = paths
    .map((path) => `<option value="${escapeHtml(path)}">${escapeHtml(displayPath(path))}</option>`)
    .join("");
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

async function renderSelectedSources(): Promise<void> {
  // Each call renders the source set selected at its start; concurrent calls can
  // overlap (a select-change render racing a watcher-driven reloadMap, or a fast
  // A->B->A switch). Bump a generation at entry and bail after each await once a
  // newer render has superseded this one, so the last writer cannot paint one
  // file's body under another file's overlays. Snapshot the selection so this
  // call is internally consistent even as state.selectedSources moves on.
  const generation = ++renderGeneration;
  const selected = { ...state.selectedSources };
  // Guard each load: loadText throws on a non-2xx (e.g. a stale/renamed 404),
  // and one failure must not blank every pane.
  const sources = {
    md: await loadCachedText(selected.md).catch(() => ""),
    lean: await loadCachedText(selected.lean).catch(() => ""),
    tex: await loadCachedText(selected.tex).catch(() => ""),
  };
  if (generation !== renderGeneration) return;

  const [mdHighlights, leanHighlights, leanFoldRanges] = await Promise.all([
    loadCachedHighlights(selected.md, sources.md),
    loadCachedHighlights(selected.lean, sources.lean),
    loadCachedLeanFolds(selected.lean, sources.lean),
  ]);
  if (generation !== renderGeneration) return;

  state.sources = sources;
  els.mdSelect.value = state.selectedSources.md ?? "";
  els.leanSelect.value = state.selectedSources.lean ?? "";
  if (els.mdMeta) els.mdMeta.textContent = displayPath(state.selectedSources.md);
  if (els.leanMeta) els.leanMeta.textContent = displayPath(state.selectedSources.lean);
  if (els.texMeta) els.texMeta.textContent = displayPath(state.selectedSources.tex);

  renderSource(
    els.mdSource,
    state.sources.md,
    collectSpans("md"),
    "md",
    mdHighlights,
    [],
    "codepoint",
    collectSkipSpans(),
  );
  renderSource(els.leanSource, state.sources.lean, collectSpans("lean"), "lean", leanHighlights, leanFoldRanges);
  renderSource(els.texSource, state.sources.tex, collectSpans("tex"), "tex", [], [], "codepoint");
  syncLeanDocument();
  renderInfoview();
  applyActiveState(state.activeIndex);
  updateAllMarkRails();
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
  return stripTermDefine(s)
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
  return stripTermDefine(s)
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
  let out = "";
  let last = 0;
  const re = /\$([^$]+)\$/g;
  let m: RegExpExecArray | null;
  while ((m = re.exec(source)) !== null) {
    out += escapeHtml(cleanTextSegment(source.slice(last, m.index)));
    if (state.katex) {
      try {
        out += state.katex.renderToString(m[1], {
          macros: state.katexMacros || {},
          throwOnError: false,
          displayMode: false,
        });
      } catch (_error) {
        out += escapeHtml(m[1]);
      }
    } else {
      out += escapeHtml(m[1]);
    }
    last = re.lastIndex;
  }
  out += escapeHtml(cleanTextSegment(source.slice(last)));
  return out.trim();
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
  const rawExcerpt = link.excerpt ? String(link.excerpt) : "";
  // The TeX source we render (math kept): the human title, else the defined
  // term's display form, else the excerpt's opening clause.
  let titleSource = String(link.title || "").trim();
  if (!titleSource && rawExcerpt) {
    const term = rawExcerpt.match(TERM_DEFINE_RE);
    titleSource = term ? (term[2] || term[1]).trim() : rawExcerpt.split(/[.;:]/)[0].trim();
  }
  // Plain text for search/fallback: prefer the canonical term, sort key dropped.
  let title = link.title ? cleanProse(String(link.title)) : "";
  if (!title && rawExcerpt) {
    const term = rawExcerpt.match(TERM_DEFINE_RE);
    title = term
      ? sentenceCase(cleanProse(term[1].split("@")[0]))
      : sentenceCase(cleanProse(rawExcerpt).split(/[.;:]/)[0].split(" ").slice(0, 8).join(" "));
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

function filteredMarkerIndices(): number[] {
  const q = markerFilter.trim().toLowerCase();
  const all = state.entries.map((_entry, i) => i);
  if (!q) return all;
  return all.filter((i) => {
    const m = markerInfo(state.entries[i], i);
    return `${m.title} ${m.id} ${m.kind} ${m.snippet}`.toLowerCase().includes(q);
  });
}

function renderMarkerList(): void {
  const filtered = filteredMarkerIndices();
  if (markerHighlight < 0 || markerHighlight >= filtered.length) markerHighlight = 0;
  els.markerList.innerHTML = filtered.length
    ? filtered
        .map((i, pos) => {
          const m = markerInfo(state.entries[i], i);
          const selected = i === state.activeIndex;
          const chip = m.kind
            ? ` <span class="marker-chip" data-kind="${escapeHtml(m.kind)}">${escapeHtml(m.kind)}</span>`
            : "";
          const id = m.id && m.id !== m.title ? `<span class="marker-id">${escapeHtml(m.id)}</span>` : "";
          const snip = m.snippet ? `<span class="marker-snip">${escapeHtml(m.snippet)}</span>` : "";
          const meta = id || snip ? `<div class="marker-row-meta">${id}${snip}</div>` : "";
          return `<li class="marker-row${selected ? " is-selected" : ""}${pos === markerHighlight ? " is-highlight" : ""}" role="option" aria-selected="${selected}" data-index="${i}"><div class="marker-row-head"><span class="marker-title" title="${escapeHtml(m.title)}">${renderMath(m.titleSource)}</span>${chip}</div>${meta}</li>`;
        })
        .join("")
    : `<li class="marker-empty">No markers match “${escapeHtml(markerFilter.trim())}”.</li>`;
}

function updateMarkerField(): void {
  const i = state.activeIndex;
  const m = state.entries[i] ? markerInfo(state.entries[i], i) : null;
  els.markerFieldLabel.innerHTML = m ? renderMath(m.titleSource) : "—";
  els.markerFieldLabel.title = m ? m.title : "";
}

function scrollHighlightedMarkerIntoView(): void {
  const row = els.markerList.querySelector(".marker-row.is-highlight") as HTMLElement | null;
  row?.scrollIntoView({ block: "nearest" });
}

function openMarkerPopover(): void {
  markerFilter = "";
  els.markerSearch.value = "";
  markerHighlight = Math.max(0, filteredMarkerIndices().indexOf(state.activeIndex));
  renderMarkerList();
  els.markerPopover.hidden = false;
  els.markerField.setAttribute("aria-expanded", "true");
  els.markerSearch.focus();
  scrollHighlightedMarkerIntoView();
}

function closeMarkerPopover(): void {
  if (els.markerPopover.hidden) return;
  els.markerPopover.hidden = true;
  els.markerField.setAttribute("aria-expanded", "false");
}

function chooseMarker(index: number): void {
  closeMarkerPopover();
  els.markerField.focus();
  setActive(index, null, true).catch(reportError);
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

function applyActiveState(index: number): void {
  state.activeIndex = index;
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
  updatePdfStatus();
}

// The pane the reader last interacted with renders the active marker at full
// strength (and its markers a touch brighter); the linked pane stays softer, so
// the active selection reads as one place rather than two equal highlights.
function setFocusPane(pane: string | null): void {
  const sections = state.paneSections || {};
  const visible = new Set(visiblePaneNames());
  let next = pane && pane !== "pdf" && visible.has(pane) ? pane : state.focusedPane;
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
  const paneRect = pane.getBoundingClientRect();
  const markRect = mark.getBoundingClientRect();
  const markTop = markRect.top - paneRect.top + pane.scrollTop;
  const top = markTop - Math.max(0, pane.clientHeight * 0.35);
  logEvent("scrollTo", {
    paneName,
    index,
    currentTop: Math.round(pane.scrollTop),
    nextTop: Math.round(Math.max(0, top)),
    markTop: Math.round(markTop),
    paneHeight: pane.clientHeight,
  });
  pane.scrollTo({ top: Math.max(0, top), left: pane.scrollLeft, behavior: "auto" });
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
    const height = viewer?.scrollHeight || 0;
    if (!height) return [];
    const out: { index: number; frac: number }[] = [];
    for (const [index, target] of state.pdf.targets.entries()) {
      const pageState = state.pdf.pageStates.get(target.pageNumber);
      if (!pageState) continue;
      out.push({ index, frac: clamp((pageState.el.offsetTop + target.y) / height) });
    }
    return out.sort((a, b) => a.frac - b.frac);
  }
  const pre = state.panes[paneName];
  const height = pre?.scrollHeight || 0;
  if (!pre || !height) return [];
  const preTop = pre.getBoundingClientRect().top;
  const seen = new Set<string>();
  const out: { index: number; frac: number }[] = [];
  // One tick per booklink: take the first rendered fragment of each data-entry.
  for (const node of Array.from(pre.querySelectorAll(".mark")) as HTMLElement[]) {
    const entry = node.dataset.entry;
    if (!entry || seen.has(entry)) continue;
    seen.add(entry);
    const top = node.getBoundingClientRect().top - preTop + pre.scrollTop;
    out.push({ index: Number(entry), frac: clamp(top / height) });
  }
  return out;
}

function updateMarkRail(paneName: string): void {
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
      if (tick) setActive(Number(tick.dataset.entry), null, true).catch(reportError);
    });
    rail.addEventListener("mouseover", (event) => {
      const tick = (event.target as Element | null)?.closest(".mark-rail-tick") as HTMLElement | null;
      setHoveredEntry(tick?.dataset.entry ?? null);
    });
    rail.addEventListener("mouseleave", () => setHoveredEntry(null));
  }

  const ticks = railTickFractions(paneName).map(({ index, frac }) => {
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
  rail.innerHTML = ticks.join("");
  section.classList.toggle("has-mark-rail", ticks.length > 0);
}

function updateAllMarkRails(): void {
  for (const paneName of RAIL_PANES) updateMarkRail(paneName);
}

function nearestEntryFromScroll(paneName: string): number | null {
  const pane = state.panes[paneName];
  if (!pane) return null;
  const paneTop = pane.getBoundingClientRect().top;
  const target = paneTop + pane.clientHeight * 0.35;
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
  const segButton = (group: HTMLElement | null, event: Event): HTMLElement | null => {
    const btn = (event.target as Element | null)?.closest("button") as HTMLElement | null;
    return btn && group && group.contains(btn) && !(btn as HTMLButtonElement).disabled ? btn : null;
  };
  els.syncSeg?.addEventListener("click", (event) => {
    const btn = segButton(els.syncSeg, event);
    if (!btn) return;
    state.sync = btn.dataset.value === "on";
    updateSegmented(els.syncSeg, state.sync ? "on" : "off");
  });
  els.linenumSeg?.addEventListener("click", (event) => {
    const btn = segButton(els.linenumSeg, event);
    if (!btn) return;
    state.lineNumbers = btn.dataset.value === "on";
    localStorage.setItem(LINE_NUMBERS_STORAGE_KEY, state.lineNumbers ? "on" : "off");
    applyLineNumbers();
  });
  els.layoutSeg?.addEventListener("click", (event) => {
    const btn = segButton(els.layoutSeg, event);
    if (!btn) return;
    setLayoutKind(btn.dataset.value as string);
  });
  els.markerField.addEventListener("click", () => {
    if (els.markerPopover.hidden) openMarkerPopover();
    else closeMarkerPopover();
  });
  els.markerSearch.addEventListener("input", () => {
    markerFilter = els.markerSearch.value;
    markerHighlight = 0;
    renderMarkerList();
  });
  els.markerSearch.addEventListener("keydown", (event) => {
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
    } else if (event.key === "Enter") {
      event.preventDefault();
      if (filtered[markerHighlight] !== undefined) chooseMarker(filtered[markerHighlight]);
    } else if (event.key === "Escape") {
      event.preventDefault();
      closeMarkerPopover();
      els.markerField.focus();
    }
  });
  els.markerList.addEventListener("click", (event) => {
    const row = (event.target as Element | null)?.closest(".marker-row") as HTMLElement | null;
    if (row?.dataset.index) chooseMarker(Number(row.dataset.index));
  });
  els.markerList.addEventListener("mousemove", (event) => {
    const row = (event.target as Element | null)?.closest(".marker-row") as HTMLElement | null;
    if (!row?.dataset.index) return;
    const pos = filteredMarkerIndices().indexOf(Number(row.dataset.index));
    if (pos >= 0 && pos !== markerHighlight) {
      markerHighlight = pos;
      renderMarkerList();
    }
  });
  document.addEventListener("click", (event) => {
    if (!(event.target as Element | null)?.closest("#marker-combo")) closeMarkerPopover();
  });
  els.prev.addEventListener("click", () =>
    setActive(Math.max(0, state.activeIndex - 1), null, true).catch(reportError),
  );
  els.next.addEventListener("click", () =>
    setActive(Math.min(state.entries.length - 1, state.activeIndex + 1), null, true).catch(reportError),
  );
  // Let the reader browse to any chapter file. renderSelectedSources already
  // re-applies the active entry's highlight (applyActiveState) for whichever
  // file is shown; do NOT call setActive here — it re-navigates to the active
  // entry's own source and snaps the just-picked file back, which would make the
  // dropdowns useless for any chapter that does not contain the active marker.
  els.mdSelect.addEventListener("change", async () => {
    state.selectedSources.md = repoPath(els.mdSelect.value);
    state.selectedSources.lean = correspondingLeanForMd(state.selectedSources.md);
    await renderSelectedSources();
  });
  els.leanSelect.addEventListener("change", async () => {
    state.selectedSources.lean = repoPath(els.leanSelect.value);
    await renderSelectedSources();
  });
  els.settingsToggle.addEventListener("click", () => {
    const nextOpen = els.settingsMenu.hidden;
    els.settingsMenu.hidden = !nextOpen;
    els.settingsToggle.setAttribute("aria-expanded", String(nextOpen));
  });
  document.addEventListener("click", (event) => {
    if ((event.target as Element | null)?.closest(".settings")) return;
    els.settingsMenu.hidden = true;
    els.settingsToggle.setAttribute("aria-expanded", "false");
  });
  els.aboutOpen?.addEventListener("click", openAbout);
  els.aboutClose?.addEventListener("click", closeAbout);
  els.aboutCopy?.addEventListener("click", async () => {
    const text = els.aboutCopy?.dataset.copy || "";
    if (!text) return;
    try {
      await navigator.clipboard.writeText(text);
      els.aboutCopy!.classList.add("is-copied");
      els.aboutCopy!.setAttribute("title", "Copied");
      window.setTimeout(() => {
        els.aboutCopy?.classList.remove("is-copied");
        els.aboutCopy?.setAttribute("title", "Copy version");
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
    if (event.key === "Escape" && els.aboutOverlay && !els.aboutOverlay.hidden) closeAbout();
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
    pane.addEventListener("click", (event) => {
      const mark = (event.target as Element | null)?.closest(".mark") as HTMLElement | null;
      // A direct click is explicit "go here" navigation: scroll every linked
      // pane to the entry even when scroll-sync is off.
      if (mark) setActive(Number(mark.dataset.entry), paneName, true).catch(reportError);
      if (paneName === "lean") inspectLeanClick(event);
    });
    // Hover a marker -> highlight every fragment of that booklink. mouseover
    // bubbles (unlike mouseenter), so one delegated listener per pane covers
    // all marks; leaving the pane clears it.
    pane.addEventListener("mouseover", (event) => {
      const target = event.target as Element | null;
      const mark = target?.closest(".mark") as HTMLElement | null;
      setHoveredEntry(mark?.dataset.entry ?? null);
      // Skip overlays only render in the md pane, but the lookup is harmless on
      // the others (no .skip-mark to find), so one handler covers every pane.
      const skip = target?.closest(".skip-mark") as HTMLElement | null;
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
          scrollTop: Math.round(pane.scrollTop),
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
  // viewer so it covers overlays added lazily as pages rasterize.
  els.pdfViewer.addEventListener("click", (event) => {
    const mark = (event.target as Element | null)?.closest(".pdf-mark") as HTMLElement | null;
    // Like a rail-tick click, drive the sync hub with no origin pane (the PDF is
    // never the focus pane), so every source pane scrolls to the entry.
    if (mark) setActive(Number(mark.dataset.entry), null, true).catch(reportError);
  });
  els.pdfViewer.addEventListener("mouseover", (event) => {
    const target = event.target as Element | null;
    const mark = target?.closest(".pdf-mark") as HTMLElement | null;
    setHoveredEntry(mark?.dataset.entry ?? null);
    const skip = target?.closest(".pdf-skip-band") as HTMLElement | null;
    setHoveredSkip(skip?.dataset.skipKey ?? null);
  });
  els.pdfViewer.addEventListener("mouseleave", () => {
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
  const rel = repoPath(path);
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
// One preview option per chapter source. Labels are the raw preview file names,
// matching the other PDF options.
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
  return choices;
}
function isPreviewPath(path: string): boolean {
  const stem = bookStem();
  return !!stem && path.includes(`${stem}-preview-`);
}

// Books currently auto-building on the server. The "Building…" indicator in the
// PDF pane header shows while the set is non-empty; a failed build flashes
// briefly. The server's build channel carries every project's events, so ignore
// any whose dir is not the project this tab is viewing.
const buildingBooks = new Set<string>();
let buildFailedTimer: ReturnType<typeof setTimeout> | null = null;

function onBuildStatus(status: BuildStatus): void {
  if (status.dir !== project.dir) return;
  if (status.state === "building") buildingBooks.add(status.dir);
  else buildingBooks.delete(status.dir);
  // When the viewed PDF is a chapter preview the server is still rendering (its
  // file 404'd on selection, so nothing is loaded), show the build state in the
  // pane body and load it once the build lands, instead of a stale 404 error.
  if (!state.pdf.document && isPreviewPath(state.pdf.path ?? "")) {
    if (status.state === "building") clearPdfViewer("Building chapter preview…");
    else if (status.state === "failed") clearPdfViewer("Chapter preview build failed — see the terminal.");
    else if (status.state === "done") reloadPdf();
  }
  const el = els.pdfBuildStatus;
  if (!el) return;
  if (buildFailedTimer) {
    window.clearTimeout(buildFailedTimer);
    buildFailedTimer = null;
  }
  if (buildingBooks.size > 0) {
    el.hidden = false;
    el.dataset.state = "building";
    el.textContent = "Building…";
  } else if (status.state === "failed") {
    el.hidden = false;
    el.dataset.state = "failed";
    el.textContent = "Build failed";
    buildFailedTimer = window.setTimeout(() => {
      if (buildingBooks.size === 0 && els.pdfBuildStatus) els.pdfBuildStatus.hidden = true;
    }, 6000);
  } else {
    el.hidden = true;
    el.dataset.state = "done";
  }
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

function applyWatchedChange(path: string): void {
  const changed = repoPath(path);
  // Any rebuild may have rewritten the viewer's own bundle (editing pdf.ts/app.ts
  // → build/*.js; the book filter change in this same session rebuilt the PDF in
  // one burst). A single build/*.js watch event can be coalesced or missed,
  // stranding the page on stale client code until the next tab focus. So re-check
  // the build version on every change — checkForNewBuild is a no-op unless the
  // viewer build actually changed, in which case it forces a full reload — and the
  // reliably-delivered PDF/map events thus act as a backstop for the asset event.
  scheduleReload();
  if (VIEWER_ASSET.test(changed)) return;
  if (changed === repoPath(state.mapPath) || changed === project.bookManifest) {
    reloadMap().catch(reportError);
    return;
  }
  if (changed === repoPath(state.selectedSources.md)) refreshSource("md").catch(reportError);
  if (changed === repoPath(state.selectedSources.lean)) refreshSource("lean").catch(reportError);
  if (changed === repoPath(state.selectedSources.tex)) refreshSource("tex").catch(reportError);
  if (state.pdf.path && changed === repoPath(state.pdf.path)) reloadPdf();
}

// The booklink source map (or chapter manifest) was regenerated: reload it,
// rebuild the entry list and file choices, re-render the source panes, and
// re-resolve PDF targets so markers track the new entries.
async function reloadMap(): Promise<void> {
  let map: any;
  try {
    map = await fetch(state.mapPath ?? "", { cache: "no-store" }).then((response) => {
      if (!response.ok) throw new Error(`${state.mapPath}: HTTP ${response.status}`);
      return response.json();
    });
  } catch (error) {
    reportError(error);
    return;
  }
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
  state.activeIndex = Math.min(state.activeIndex, Math.max(0, state.entries.length - 1));
  await renderSelectedSources();
  if (state.pdf.document) {
    state.pdf.targetPromise = resolvePdfTargets(state.pdf.renderToken).catch((error) => {
      console.error("[booklink] Failed to resolve PDF targets:", error);
    });
  }
  applyActiveState(state.activeIndex);
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
  let text: string;
  try {
    text = await loadText(path);
  } catch (error) {
    reportError(error);
    return;
  }
  state.sourceCache.set(normalized, text);
  state.sources[kind] = text;
  const highlights = await loadCachedHighlights(path, text);
  const folds = kind === "lean" ? await loadCachedLeanFolds(path, text) : [];
  const pane = state.panes[kind];
  const prevScroll = pane ? pane.scrollTop : 0;
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
  applyActiveState(state.activeIndex);
  if (pane) pane.scrollTop = prevScroll;
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
  bookSelect.innerHTML = projects
    .map(
      (entry: any) =>
        `<option value="${escapeHtml(entry.mount)}"${entry.dir === project.dir ? " selected" : ""}>${escapeHtml(entry.name || entry.dir)}</option>`,
    )
    .join("");
  bookSelect.addEventListener("change", () => {
    window.location.href = `${mountPrefix()}${bookSelect.value}/`;
  });
  const label = document.getElementById("book-select-label");
  if (label) label.hidden = false;
  enhanceSelect(bookSelect);
}

// Register the per-entry activation orchestration and each pane's scroll
// handlers with the sync hub, so sync.setActive / sync.syncFromScroll can drive
// the panes without app and the pane modules importing each other.
function wireActiveSync(): void {
  setActivateHook(async (index, originPane, mode) => {
    if (mode === "navigate" && originPane) setFocusPane(originPane);
    await syncSelectedSourcesForEntry(state.entries[index]);
    applyActiveState(index);
    // When a chapter preview is shown, follow an activated marker to its
    // chapter's preview, so the PDF jumps to it even when the marker lives in a
    // different chapter than the one displayed. (Debug/release show the whole
    // book, so no switch is needed.)
    if (mode === "navigate" && isPreviewPath(state.pdf.path ?? "")) {
      const url = previewUrlForChapter(chapterStemOf(state.selectedSources.md));
      if (url && url !== state.pdf.path) setPdf(url).catch(reportError);
    }
    if (mode === "navigate" && lspIsReady() && state.lsp.uri) {
      const pos = leanEntryPosition(state.entries[index]);
      queryGoalAt(pos.line, pos.character).catch(reportError);
    }
  });
  for (const paneName of ["md", "lean", "tex"]) {
    registerPaneSync(paneName, {
      scrollToEntry: (index) => scrollPaneToEntry(paneName, index),
      nearestEntry: () => nearestEntryFromScroll(paneName),
    });
  }
  registerPaneSync("pdf", { scrollToEntry: scrollPdfToEntry, nearestEntry: nearestEntryFromPdfScroll });
  // pdf.ts resolved its entry targets; redraw the PDF overview rail, which reads
  // them. (pdf.ts cannot call the rail code in app.ts directly.)
  setOnPdfTargetsResolved(() => updateMarkRail("pdf"));
}

async function init(): Promise<void> {
  const params = new URLSearchParams(window.location.search);
  setProject(
    await fetch("manifest.json", { cache: "no-store" }).then((response) => {
      if (!response.ok) throw new Error(`manifest.json: HTTP ${response.status}`);
      return response.json();
    }),
  );
  // Load KaTeX lazily with the book's macros; marker titles re-render with real
  // math once it's ready (they show plain text until then).
  state.katexMacros = project.katexMacros || {};
  import(KATEX_MODULE_URL)
    .then((mod) => {
      state.katex = (mod as any).default || mod;
      updateMarkerField();
      if (!els.markerPopover.hidden) renderMarkerList();
    })
    .catch(() => {});
  initBookSelect().catch(reportError);
  initHighlighter().catch(reportError);
  connectInfoview().catch(reportError);
  // Keep the PDF band overlays aligned whenever the pane geometry settles, so a
  // band drawn against not-yet-final geometry self-corrects without a reload.
  observePdfBandGeometry();
  // A static dist has no watcher endpoint; skip the EventSource retry loop.
  if (!project.static) {
    connectFileWatch(onWatchedFileChanged);
    connectBuildStatus(onBuildStatus, () => reportPdfSelection(state.pdf.path));
    // Safety net: reload if a rebuild landed while a watch event was missed.
    installReloadGuard();
  }
  loadLayout();
  loadLineNumbers();
  applyLineNumbers();
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
  let map: any;
  try {
    map = await fetch(mapPath, { cache: "no-store" }).then((response) => {
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
  state.fileChoices.md = await mdChoices(map);
  state.fileChoices.lean = leanChoices(map, state.fileChoices.md);
  state.fileChoices.tex = uniquePaths([map.texFile]);
  state.selectedSources.md = repoPath(state.entries[0]?.match?.source || state.fileChoices.md[0]);
  state.selectedSources.lean = repoPath(
    map.leanFile || correspondingLeanForMd(state.selectedSources.md) || state.fileChoices.lean[0],
  );
  state.selectedSources.tex = repoPath(map.texFile || state.fileChoices.tex[0]);

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

  applyPaneLayout();

  // Populate the native selects and wire every UI event handler (pane drag,
  // menus, keyboard, select popovers) BEFORE loading any content. The content
  // fetches/renders below are guarded, so a corrupt source or sourcemap blanks
  // one pane instead of throwing out of init() and leaving the whole UI — pane
  // drag included — unwired.
  // Report the viewed PDF to the server so the auto-build tracks it; set before
  // the first setPdf below so the initial selection is reported too.
  if (!project.static) {
    setOnPdfSelected(reportPdfSelection);
    // A freshly selected preview 404s until the server renders it; show build
    // progress in the pane rather than the raw error.
    setOnPdfLoadFailed((path) => (isPreviewPath(path) ? "Building chapter preview…" : null));
  }
  // List every chapter's preview (the live bridge builds the selected one on
  // demand); debug stays the default initial view.
  if (!project.static) pdfChoiceList.unshift(...chapterPreviewChoices());
  await renderPdfChoices(pdfChoiceList, pdfPath).catch(reportError);
  populateFileSelect(els.mdSelect, state.fileChoices.md);
  populateFileSelect(els.leanSelect, state.fileChoices.lean);

  wireActiveSync();
  wireEvents();
  els.pdfSelect.addEventListener("change", () => setPdf(els.pdfSelect.value).catch(reportError));
  // Give the native pane/PDF selects the same custom popover as the marker palette.
  enhanceSelect(els.pdfSelect);
  enhanceSelect(els.mdSelect);
  enhanceSelect(els.leanSelect);

  // Content load: guarded so one bad source/highlight/sourcemap cannot abort
  // init() and leave the panes unwired.
  try {
    await renderSelectedSources();
    updateMarkerField();
    await setActive(0);
  } catch (error) {
    reportError(error);
  }
}

init().catch((error) => {
  if (els.status) els.status.textContent = error.message;
  console.error(error);
});
