// The cross-pane "active entry" sync hub. It owns which booklink entry is active
// and keeps the panes' scroll positions in step — without any pane knowing about
// the others. Each pane registers how to scroll itself to an entry and how to
// report the entry nearest its current scroll; app registers what it means to
// "activate" an entry (select sources, mark it, query the LSP). This is the seam
// that lets the PDF pane and the source panes live in their own modules with a
// one-way dependency on sync, instead of calling each other directly.

import { state } from "./state.js";
import { logEvent } from "./util.js";
import { treeLeaves } from "./layout-tree.js";

export interface PaneSync {
  scrollToEntry: (index: number) => void;
  nearestEntry: () => number | null;
}

const panes = new Map<string, PaneSync>();

export function registerPaneSync(name: string, handlers: PaneSync): void {
  panes.set(name, handlers);
}

// "navigate" = an explicit pick (entry selector, prev/next, marker click): also
// focuses the origin pane and refreshes the LSP goal. "follow" = a passive
// scroll: just selects sources and marks the entry active.
export type ActivateMode = "navigate" | "follow";
type ActivateHook = (index: number, originPane: string | null, mode: ActivateMode) => Promise<void> | void;
let onActivate: ActivateHook = () => {};

export function setActivateHook(fn: ActivateHook): void {
  onActivate = fn;
}

export function visiblePaneNames(): string[] {
  return treeLeaves(state.layout.tree);
}

export function isPaneSuppressed(paneName: string): boolean {
  return state.suppressedPanes.has(paneName);
}

function beginProgrammaticScroll(paneNames: string[]): void {
  state.suppressedPanes = new Set(paneNames);
  state.suppressScroll = state.suppressedPanes.size > 0;
  logEvent("programmatic:start", { panes: paneNames });
  if (state.scrollReleaseTimer) {
    window.clearTimeout(state.scrollReleaseTimer);
    state.scrollReleaseTimer = null;
  }
}

function scheduleScrollRelease(): void {
  if (state.scrollReleaseTimer) window.clearTimeout(state.scrollReleaseTimer);
  logEvent("programmatic:releaseScheduled");
  state.scrollReleaseTimer = window.setTimeout(() => {
    state.suppressedPanes.clear();
    state.suppressScroll = false;
    state.scrollReleaseTimer = null;
    logEvent("programmatic:released");
  }, 300);
}

// Scroll every visible pane except `originPane` to the entry, suppressing the
// scroll-follow on those panes for the duration so the programmatic scroll does
// not bounce back as a user scroll.
function scrollOthersToEntry(index: number, originPane: string | null): void {
  const targets = visiblePaneNames().filter((paneName) => paneName !== originPane);
  beginProgrammaticScroll(targets);
  for (const paneName of targets) panes.get(paneName)?.scrollToEntry(index);
  scheduleScrollRelease();
}

// Explicit navigation to an entry (entry selector, prev/next, marker click):
// activate it, and — when scroll-sync is on or the pick is explicit — scroll
// every other pane to it.
export async function setActive(
  index: number,
  originPane: string | null = null,
  explicit: boolean = false,
): Promise<void> {
  if (!state.entries[index]) return;
  logEvent("setActive:start", { index, originPane, explicit });
  await onActivate(index, originPane, "navigate");
  if (!state.sync && !explicit) return;
  scrollOthersToEntry(index, originPane);
  logEvent("setActive:end", { index, originPane });
}

// A pane was scrolled by the user; follow with the others (when scroll-sync is
// on and this pane is not currently being scrolled programmatically).
export async function syncFromScroll(paneName: string): Promise<void> {
  if (!state.sync || isPaneSuppressed(paneName)) return;
  const index = panes.get(paneName)?.nearestEntry() ?? null;
  logEvent("scroll:nearest", { paneName, index });
  if (index === null || !state.entries[index]) return;
  await onActivate(index, paneName, "follow");
  scrollOthersToEntry(index, paneName);
}
