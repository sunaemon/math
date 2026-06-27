// Shared viewer state: the loaded project manifest, the live application state
// object, and the cached DOM element references. Split out of app.ts so the
// rendering modules (source view, PDF, infoview, ...) can read and mutate one
// shared state without app.ts having to thread it through every call.
//
// `state` and `els` are const and mutated in place. `project` is reassigned once
// (when manifest.json loads), so it is exposed as a live binding plus setProject;
// importers see the updated value because the reassignment happens in this module.

import type { LayoutNode } from "./layout-tree.js";

export interface Project {
  dir?: string;
  mount?: string;
  repository?: string;
  book?: string;
  bookManifest?: string;
  bookSourcePrefix?: string;
  leanSourcePrefix?: string;
  leanRootModule?: string;
  sourceMap?: string;
  pdf?: string;
  pdfs?: string[];
  static?: boolean;
  version?: { describe?: string; rev?: string; date?: string };
  license?: {
    summary?: string;
    items?: Array<{ scope?: string; spdx?: string; version?: string; source?: string; file?: string; text?: string }>;
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
  pageNumber: number;
  el: HTMLElement;
  canvas: HTMLCanvasElement;
  rendered: boolean;
  rendering: boolean;
}

export interface State {
  sync: boolean;
  lineNumbers: boolean;
  entries: any[];
  activeIndex: number;
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
  layout: { tree: LayoutNode | null };
  suppressScroll: boolean;
  suppressedPanes: Set<string>;
  scrollReleaseTimer: ReturnType<typeof setTimeout> | null;
  syncScrollTimer: ReturnType<typeof setTimeout> | null;
  pdf: {
    path: string | null;
    document: any;
    loadingTask: any;
    renderToken: number;
    currentPage: number | null;
    pageCount: number | null;
    pageStates: Map<number, PdfPageState>;
    targets: Map<number, { pageNumber: number; y: number }>;
    skipBands: Array<{
      key: string;
      reason: string;
      // top/bottom are fractions of the page height (0 = page top, 1 = page
      // bottom); bottom null means "down to the page bottom". Stored
      // scale-independently so a pane resize never leaves the band stale.
      segments: Array<{ pageNumber: number; top: number; bottom: number | null }>;
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
  hoveredEntry?: string | null;
  hoveredSkip?: string | null;
  pdfjs?: any;
  katex?: any;
  katexMacros?: Record<string, string>;
}

export const state: State = {
  sync: true,
  lineNumbers: false,
  entries: [],
  activeIndex: 0,
  focusedPane: "md",
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
  scrollReleaseTimer: null,
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
  status: document.getElementById("status"),
  bookSelect: document.getElementById("book-select") as HTMLSelectElement | null,
  markerCombo: document.getElementById("marker-combo") as HTMLElement,
  markerField: document.getElementById("marker-field") as HTMLButtonElement,
  markerFieldLabel: document.getElementById("marker-field-label") as HTMLElement,
  markerPopover: document.getElementById("marker-popover") as HTMLElement,
  markerSearch: document.getElementById("marker-search") as HTMLInputElement,
  markerList: document.getElementById("marker-list") as HTMLElement,
  syncSeg: document.getElementById("sync-seg") as HTMLElement | null,
  linenumSeg: document.getElementById("linenum-seg") as HTMLElement | null,
  prev: document.getElementById("prev-entry") as HTMLElement,
  next: document.getElementById("next-entry") as HTMLElement,
  workspace: document.querySelector(".workspace") as HTMLElement,
  settingsToggle: document.getElementById("settings-toggle") as HTMLElement,
  settingsMenu: document.getElementById("settings-menu") as HTMLElement,
  aboutOpen: document.getElementById("about-open") as HTMLElement,
  aboutOverlay: document.getElementById("about-overlay") as HTMLElement,
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
  leanSource: document.getElementById("lean-source") as HTMLElement,
  texSource: document.getElementById("tex-source") as HTMLElement,
  mdSelect: document.getElementById("md-select") as HTMLSelectElement,
  leanSelect: document.getElementById("lean-select") as HTMLSelectElement,
  mdMeta: document.getElementById("md-meta"),
  leanMeta: document.getElementById("lean-meta"),
  texMeta: document.getElementById("tex-meta"),
  infoviewBody: document.getElementById("infoview-body"),
  infoviewStatus: document.getElementById("infoview-status"),
};
