import { ScrollSuppression } from "./scroll-suppression.js";
// The cross-pane navigation hub. Markers and formalization skips are the two
// kinds of first-class navigation location: every pane reports the location
// nearest its reading line, declares which kinds it supports, and scrolls to a
// supported location. The hub owns cross-pane suppression and entry activation
// side effects, so panes remain independent of one another.

import { state } from "./state.js";
import { logEvent } from "./util.js";
import { treeLeaves } from "./layout-tree.js";
import type { NavigationLocation, SkipSyncLocation } from "./permalink.js";
export type { NavigationLocation, SkipSyncLocation } from "./permalink.js";

export interface PaneSync {
  supports: (location: NavigationLocation) => boolean;
  scrollTo: (location: NavigationLocation) => void | Promise<void>;
  nearest: () => NavigationLocation | null;
}

const panes = new Map<string, PaneSync>();

export function registerPaneSync(name: string, handlers: PaneSync): void {
  panes.set(name, handlers);
}

// "navigate" = an explicit pick (entry selector, prev/next, marker click): also
// focuses the origin pane and refreshes the LSP goal. "follow" = a passive
// scroll: just selects sources and marks the entry active. Skips have no entry
// activation side effects, but share the same current-location state.
export type ActivateMode = "navigate" | "follow";
type ActivateHook = (
  index: number,
  originPane: string | null,
  mode: ActivateMode,
  current: () => boolean,
) => Promise<void> | void;
let onActivate: ActivateHook = () => {};

export function setActivateHook(fn: ActivateHook): void {
  onActivate = fn;
}

// Every navigation the reader makes — an explicit pick or a passive scroll, a
// marker or a skip — passes through navigateTo, so this is the one place the
// current reading position can be observed. app.ts records it into the address
// bar and the stored session from here.
type LocationHook = (location: NavigationLocation, mode: ActivateMode) => void;
let onLocation: LocationHook = () => {};
let navigationRevision = 0;

export function setLocationHook(fn: LocationHook): void {
  onLocation = fn;
}

export function visiblePaneNames(): string[] {
  return state.layout.maximized ? [state.layout.maximized] : treeLeaves(state.layout.tree);
}

const suppression = new ScrollSuppression(
  (run, ms) => {
    const timer = window.setTimeout(run, ms);
    return () => window.clearTimeout(timer);
  },
  () => {
    state.suppressedPanes = suppression.panes;
    state.suppressScroll = suppression.panes.size > 0;
  },
);

export function isPaneSuppressed(paneName: string): boolean {
  return suppression.panes.has(paneName);
}

function beginProgrammaticScroll(paneNames: string[]): void {
  suppression.begin(paneNames);
  logEvent("programmatic:start", { panes: paneNames });
}

// PDF links may land among lazily rendered pages, so hold their suppression
// longer than ordinary navigation to avoid a late layout event feeding back.
export function suppressPaneSync(paneName: string): void {
  suppression.hold(paneName);
  logEvent("programmatic:linkJump", { paneName });
}

function scheduleScrollRelease(): void {
  suppression.releaseAfter();
  logEvent("programmatic:releaseScheduled");
}

function validLocation(location: NavigationLocation): boolean {
  if (location.kind === "entry") return Boolean(state.entries[location.index]);
  return typeof location.key === "string" && Number.isFinite(location.progress);
}

// Scroll every visible pane that supports the location — except the origin
// pane: the pane the pick was made in keeps its reading position (this is what
// lets the reader work through one pane, e.g. the rendered PDF, clicking
// markers without being yanked around in it), while all linked panes follow.
async function scrollOthersTo(location: NavigationLocation, originPane: string | null): Promise<void> {
  const targets = visiblePaneNames().filter((paneName) => {
    const pane = panes.get(paneName);
    return paneName !== originPane && pane?.supports(location);
  });
  if (!targets.length) return;
  beginProgrammaticScroll(targets);
  try {
    await Promise.all(targets.map((paneName) => panes.get(paneName)?.scrollTo(location)));
  } finally {
    scheduleScrollRelease();
  }
}

async function navigateTo(
  location: NavigationLocation,
  originPane: string | null,
  explicit: boolean,
  mode: ActivateMode,
): Promise<void> {
  if (!validLocation(location)) return;
  const revision = ++navigationRevision;
  const current = () => revision === navigationRevision && state.location === location;
  // Selection, synchronization and persistence all read this one location.
  // Publish it before async source loading; an older navigation must never
  // publish its own location after a newer user action has already won.
  state.location = location;
  onLocation(state.location, mode);
  logEvent("navigate:start", { location, originPane, explicit, mode });
  if (location.kind === "entry") await onActivate(location.index, originPane, mode, current);
  if (!current()) return;
  if (state.sync || explicit) await scrollOthersTo(state.location, originPane);
  logEvent("navigate:end", { location, originPane, mode });
}

export function setActive(index: number, originPane: string | null = null, explicit = false): Promise<void> {
  return navigateTo({ kind: "entry", index }, originPane, explicit, "navigate");
}

export function syncCurrentLocation(): Promise<void> {
  return navigateTo(state.location, null, false, "follow");
}

export function setSkipActive(
  location: SkipSyncLocation,
  originPane: string | null = null,
  explicit = false,
): Promise<void> {
  return navigateTo({ kind: "skip", ...location }, originPane, explicit, "navigate");
}

// A pane was scrolled by the user; follow its nearest navigation object in all
// other panes that support that object. Entry locations additionally update the
// source/LSP state; skip locations select the skipped passage instead.
export async function syncFromScroll(paneName: string): Promise<void> {
  if (!state.sync || isPaneSuppressed(paneName)) return;
  const location = panes.get(paneName)?.nearest() ?? null;
  logEvent("scroll:nearest", { paneName, location });
  if (!location || !validLocation(location)) return;
  await navigateTo(location, paneName, false, "follow");
}
