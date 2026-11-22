import type { ReferenceRegistry } from "./link-preview.js";
import type { DefinitionRegistry } from "./definition-registry.js";
// Shared viewer state: the loaded project manifest, the live application state
// object, and the cached DOM element references. Split out of app.ts so the
// rendering modules (source view, PDF, infoview, ...) can read and mutate one
// shared state without app.ts having to thread it through every call.
//
// `state` and `els` are const and mutated in place. `project` is reassigned once
// (when manifest.json loads), so it is exposed as a live binding plus setProject;
// importers see the updated value because the reassignment happens in this module.

import type { LayoutNode } from "./layout-tree.js";
import type { NavigationLocation } from "./permalink.js";

export interface Project {
  references?: ReferenceRegistry;
  fixedMath?: Record<string, string>;
  definitionRegistry?: DefinitionRegistry;
  dir?: string;
  mount?: string;
  repository?: string;
  book?: string;
  bookManifest?: string;
  bookSourcePrefix?: string;
  leanSourcePrefix?: string;
  leanRootModule?: string;
  sourceMap?: string;
  parallelPdf?: { label?: string; dir?: string; mount?: string; path?: string; mapPath?: string; texPath?: string };
  pdf?: string;
  pdfs?: string[];
  chapterTitles?: Record<string, string>;
  previewSections?: Record<string, string>;
  static?: boolean;
  version?: { describe?: string; rev?: string; date?: string };
  license?: {
    vendorManifests?: string[];
    summary?: string;
    items?: Array<{
      scope?: string;
      spdx?: string;
      version?: string;
      source?: string;
      file?: string;
      text?: string;
    }>;
  };
  [key: string]: any;
}

// The project that the viewer renders describes itself in manifest.json (fetched
// at startup, relative to the mount), so the viewer holds no project-specific
// paths. `project.dir` is the directory the project lives in under the repo root.
export let project: Project = {};

export function setProject(next: Project): void {
  project = next;
}

export interface PdfPageState {
  failures?: number;
  pageNumber: number;
  el: HTMLElement;
  canvas: HTMLCanvasElement;
  rendered: boolean;
  rendering: boolean;
}

export interface State {
  pdfMode: "chapter" | "full";
  sync: boolean;
  lineNumbers: boolean;
  // Workspace-wide marker highlights and PDF link outlines.
  markHighlights: boolean;
  linkHighlights: boolean;
  entries: any[];
  location: NavigationLocation;
  readonly activeIndex: number;
  panes: Record<string, HTMLElement>;
  fileChoices: { md: string[]; lean: string[]; tex: string[] };
  selectedSources: { md: string | null; lean: string | null; tex: string | null };
  sourceCache: Map<string, string>;
  highlightCache: Map<string, any[]>;
  foldCache: Map<string, any[]>;
  highlighter: any;
  lsp: {
    info: any;
    status: string;
    uri: string | null;
    position: { line: number; character: number } | null;
    goal: any;
    termGoal: any;
    // Monotonic id bumped on every goal query so a slow earlier response cannot
    // overwrite a newer position's goal (the same discipline as the hover token).
    goalToken: number;
  };
  layout: { tree: LayoutNode | null; maximized?: string };
  suppressScroll: boolean;
  suppressedPanes: Set<string>;
  syncScrollTimer: ReturnType<typeof setTimeout> | null;
  pdf: {
    path: string | null;
    loadedPath?: string | null;
    pending?: boolean;
    deferred?: boolean;
    document: any;
    loadingTask: any;
    renderToken: number;
    currentPage: number | null;
    pageCount: number | null;
    pageStates: Map<number, PdfPageState>;
    targets: Map<number, { pageNumber: number; fraction: number }>;
    skipBands: Array<{
      key: string;
      reason: string;
      // top/bottom are fractions of the page height (0 = page top, 1 = page
      // bottom); bottom null means "down to the page bottom". left/right are
      // page-width fractions: skips flow like the entry bands (first line from
      // its first glyph, last line to its last glyph, full width between).
      // Stored scale-independently so a pane resize never leaves the band stale.
      segments: Array<{ pageNumber: number; top: number; bottom: number | null; left: number; right: number }>;
    }>;
    // One colored, interactive overlay per booklink entry, mirroring the source
    // panes' .mark spans. `index` is the entry's position in state.entries (the
    // same id the .mark/.mark-rail-tick data-entry carries); segments are stored
    // as page-height fractions like skipBands, so a resize never leaves them stale.
    entryBands: Array<{
      index: number;
      title: string;
      // The booklink kind (statement/proof/prose), so the overlay is colored by
      // role like the source-pane marks.
      target: string | null;
      // Text-flow segments: a booklink that starts/ends mid-line is highlighted
      // like a text selection — left/right are page-width fractions (0..1) so the
      // first line begins at the start x and the last line ends at the end x,
      // with the lines between running full width.
      segments: Array<{ pageNumber: number; top: number; bottom: number | null; left: number; right: number }>;
    }>;
    targetPromise: Promise<any> | null;
    crop: { x0: number; x1: number } | null;
    repaintTimer?: ReturnType<typeof setTimeout> | null;
    resizeTimer?: ReturnType<typeof setTimeout> | null;
    scrollTimer?: ReturnType<typeof setTimeout> | null;
  };
  logSeq: number;
  map?: any;
  mapPath?: string;
  skips?: any[];
  sources?: Record<string, string>;
  resizing?: { node: LayoutNode; leftIndex: number; container: HTMLElement | null } | null;
  dropOverlay?: HTMLElement;
  edgeZones?: HTMLElement[];
  dragPane?: string | null;
  paneSections?: Record<string, HTMLElement | null>;
  focusedPane?: string;
  // Which document Ctrl/Cmd+C copies TeX from: the pane the reader last
  // selected a marker in ("peer" only via the peer PDF pane's marks).
  copyTexOrigin: "project" | "peer";
  hoveredEntry?: string | null;
  hoveredSkip?: string | null;
  pdfjs?: any;
  katex?: any;
  katexMacros?: Record<string, string>;
}

export const state: State = {
  pdfMode: "chapter",
  sync: true,
  lineNumbers: false,
  markHighlights: true,
  linkHighlights: false,
  entries: [],
  location: { kind: "entry", index: 0 },
  get activeIndex() {
    return this.location.kind === "entry" ? this.location.index : -1;
  },
  focusedPane: "md",
  copyTexOrigin: "project",
  panes: {},
  fileChoices: {
    md: [],
    lean: [],
    tex: [],
  },
  selectedSources: {
    md: null,
    lean: null,
    tex: null,
  },
  sourceCache: new Map(),
  highlightCache: new Map(),
  foldCache: new Map(),
  highlighter: null,
  lsp: {
    info: null,
    status: "connecting",
    uri: null,
    position: null,
    goal: null,
    termGoal: null,
    goalToken: 0,
  },
  layout: { tree: null },
  suppressScroll: false,
  suppressedPanes: new Set(),
  syncScrollTimer: null,
  pdf: {
    path: null,
    document: null,
    loadingTask: null,
    renderToken: 0,
    currentPage: null,
    pageCount: null,
    pageStates: new Map(),
    targets: new Map(),
    skipBands: [],
    entryBands: [],
    targetPromise: null,
    crop: null,
  },
  logSeq: 0,
};

export const els = {
  bookSelect: document.getElementById("book-select") as HTMLSelectElement | null,
  markerCombo: document.getElementById("marker-combo") as HTMLElement,
  markerField: document.getElementById("marker-field") as HTMLButtonElement,
  markerFieldLabel: document.getElementById("marker-field-label") as HTMLElement,
  markerPopover: document.getElementById("marker-popover") as HTMLElement,
  markerSearch: document.getElementById("marker-search") as HTMLInputElement,
  markerList: document.getElementById("marker-list") as HTMLElement,
  syncSeg: document.getElementById("sync-seg") as HTMLElement | null,
  linenumSeg: document.getElementById("linenum-seg") as HTMLElement | null,
  highlightsSeg: document.getElementById("highlights-seg") as HTMLElement | null,
  linksSeg: document.getElementById("links-seg") as HTMLElement | null,
  prev: document.getElementById("prev-entry") as HTMLElement,
  next: document.getElementById("next-entry") as HTMLElement,
  workspace: document.querySelector(".workspace") as HTMLElement,
  paneRestore: document.getElementById("pane-restore") as HTMLButtonElement,
  paneTools: document.getElementById("pane-tools") as HTMLElement,
  settingsToggle: document.getElementById("settings-toggle") as HTMLElement,
  settingsMenu: document.getElementById("settings-menu") as HTMLElement,
  aboutOpen: document.getElementById("about-open") as HTMLElement,
  aboutOverlay: document.getElementById("about-overlay") as HTMLDialogElement,
  aboutClose: document.getElementById("about-close") as HTMLElement,
  aboutBook: document.getElementById("about-book") as HTMLElement,
  aboutVersionText: document.getElementById("about-version-text") as HTMLElement,
  aboutCopy: document.getElementById("about-copy") as HTMLButtonElement | null,
  aboutRepo: document.getElementById("about-repo") as HTMLAnchorElement | null,
  aboutLicenseSummary: document.getElementById("about-license-summary") as HTMLElement,
  aboutLicenseList: document.getElementById("about-license-list") as HTMLElement,
  paneChecks: [...document.querySelectorAll(".pane-check")] as HTMLInputElement[],
  layoutSeg: document.getElementById("layout-seg") as HTMLElement | null,
  pdfViewer: document.getElementById("pdf-viewer") as HTMLElement,
  pdfLink: document.getElementById("pdf-link") as HTMLAnchorElement,
  pdfSelect: document.getElementById("pdf-select") as HTMLSelectElement,
  pdfBuildStatus: document.getElementById("pdf-build-status") as HTMLElement | null,
  mdSource: document.getElementById("md-source") as HTMLElement,
  pdfPeerViewer: document.getElementById("pdf-peer-viewer") as HTMLElement,
  pdfPeerBuildStatus: document.getElementById("pdf-peer-build-status") as HTMLElement | null,
  pdfPeerLink: document.getElementById("pdf-peer-link") as HTMLAnchorElement,
  pdfPeerPaneOption: document.getElementById("pdf-peer-pane-option") as HTMLElement,
  leanSource: document.getElementById("lean-source") as HTMLElement,
  texSource: document.getElementById("tex-source") as HTMLElement,
  mdSelect: document.getElementById("md-select") as HTMLSelectElement,
  leanSelect: document.getElementById("lean-select") as HTMLSelectElement,
  texMeta: document.getElementById("tex-meta"),
  infoviewBody: document.getElementById("infoview-body"),
  infoviewStatus: document.getElementById("infoview-status"),
};
