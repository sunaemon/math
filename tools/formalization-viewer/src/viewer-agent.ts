import type { ViewerAgentAdapter } from "./agent-tools.js";
import { markerId, markerIds, markerIndex } from "./permalink.js";
import { project, state } from "./state.js";
import { repoPath, repoUrl } from "./util.js";

export async function initViewerAgent(
  visiblePaneNames: () => string[],
  loadText: (path: string) => Promise<string>,
  setActive: (index: number, pane: null, force: boolean) => Promise<void>,
  search: ViewerAgentAdapter["search"],
): Promise<void> {
  if (window.isSecureContext && "modelContext" in document) {
    try {
      const { registerViewerAgentTools } = await import("./agent-tools.js");
      let markerEntries = state.entries,
        ids = markerIds(markerEntries);
      await registerViewerAgentTools({
        state: () => ({
          book: { name: project.name ?? project.dir, mount: project.mount },
          panes: visiblePaneNames(),
          focusedPane: state.layout.maximized ?? null,
          sources: { ...state.selectedSources },
          pdf: state.pdf.path ? repoPath(state.pdf.path) : null,
          location:
            state.location.kind === "entry"
              ? { marker: markerId(state.entries, state.activeIndex) }
              : { ...state.location },
        }),
        entries: () => state.entries,
        markerId: (index) => {
          if (markerEntries !== state.entries) {
            markerEntries = state.entries;
            ids = markerIds(markerEntries);
          }
          return ids[index];
        },
        markerIndex: (id) => markerIndex(state.entries, id),
        path: (source) => repoPath(source),
        sources: () =>
          Object.values(state.fileChoices)
            .flat()
            .map((source) => repoPath(source)),
        readSource: (source) => loadText(repoUrl(source)),
        pdfLocation: (index) => {
          const entry = state.entries[index]?.texMatch?.entry;
          const target = state.pdf.targets.get(index);
          return {
            path: project.pdf ? repoPath(project.pdf) : null,
            destination: typeof entry === "number" ? `booklink-entry-${entry}` : null,
            loadedDocument: state.pdf.loadedPath
              ? { path: repoPath(state.pdf.loadedPath), page: target?.pageNumber ?? null }
              : null,
          };
        },
        navigate: (index) => setActive(index, null, true),
        search: (query, limit, signal) => search(query, limit, signal),
      });
    } catch (error) {
      console.error("[viewer] WebMCP registration", error);
    }
  }
}
