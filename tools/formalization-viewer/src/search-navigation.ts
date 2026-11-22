import { addLeaf, treeLeaves } from "./layout-tree.js";
import type { ViewerSession } from "./session-store.js";
import { state } from "./state.js";
import { repoPath } from "./util.js";

export function searchNavigation({
  togglePaneMaximize,
  applyPaneLayout,
  setActive,
  correspondingLeanForMd,
  renderSelectedSources,
  setFocusPane,
  recordSession,
}: {
  togglePaneMaximize(pane: string): void;
  applyPaneLayout(): void;
  setActive(index: number, pane: "md"): Promise<void>;
  correspondingLeanForMd(source: string): string | null;
  renderSelectedSources(): Promise<void>;
  setFocusPane(pane: "md"): void;
  recordSession(patch: ViewerSession): void;
}): (source: string, line: number) => Promise<void> {
  return async (source, line) => {
    source = repoPath(source);
    if (!state.fileChoices.md.includes(source) || !Number.isInteger(line) || line < 1) return;
    if (!treeLeaves(state.layout.tree).includes("md")) {
      state.layout.tree = addLeaf(state.layout.tree, "md");
    }
    if (state.layout.maximized && state.layout.maximized !== "md") togglePaneMaximize(state.layout.maximized);
    applyPaneLayout();
    const covered = state.entries.findIndex(
      (entry) =>
        repoPath(entry.match?.source) === source && entry.match?.startLine <= line && entry.match?.endLine >= line,
    );
    if (covered >= 0) await setActive(covered, "md");
    state.selectedSources.md = source;
    state.selectedSources.lean = correspondingLeanForMd(source);
    await renderSelectedSources();
    setFocusPane("md");
    const node = state.panes.md?.querySelector<HTMLElement>(`.line[data-line="${line}"]`);
    document.querySelectorAll(".search-hit").forEach((hit) => hit.classList.remove("search-hit"));
    if (node) {
      node.classList.add("search-hit");
      node.scrollIntoView({ block: "center" });
      node.tabIndex = -1;
      node.focus({ preventScroll: true });
    }
    recordSession({ md: source, lean: state.selectedSources.lean });
    const url = new URL(location.href);
    url.searchParams.set("searchSource", source);
    url.searchParams.set("searchLine", String(line));
    history.replaceState(null, "", url);
  };
}
