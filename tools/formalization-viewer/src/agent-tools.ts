// WebMCP callbacks operate on the same viewer state as the human-facing UI.
// Source excerpts remain data; no credentials, chat history, or server commands
// are exposed through this interface.
export interface ViewerAgentAdapter {
  state(): unknown;
  entries(): readonly any[];
  markerId(index: number): string;
  markerIndex(id: string): number | null;
  path(source: string | undefined): string;
  sources(): string[];
  readSource(source: string): Promise<string>;
  pdfLocation(index: number): unknown;
  navigate(index: number): Promise<void>;
  search(query: string, limit: number, signal?: AbortSignal): Promise<unknown>;
}
interface ToolDescriptor {
  name: string;
  description: string;
  inputSchema: object;
  annotations?: object;
}
export function viewerAgentTools(descriptors: ToolDescriptor[], adapter: ViewerAgentAdapter) {
  const text = (value: unknown, name: string, maximum = 2000): string => {
    if (typeof value !== "string" || !value.trim() || value.length > maximum) throw new Error(`Invalid ${name}.`);
    return value.trim();
  };
  const integer = (
    value: unknown,
    name: string,
    fallback: number,
    minimum = 1,
    maximum = Number.MAX_SAFE_INTEGER,
  ): number => {
    if (value === undefined) return fallback;
    if (!Number.isSafeInteger(value) || Number(value) < minimum || Number(value) > maximum)
      throw new Error(`Invalid ${name}.`);
    return Number(value);
  };
  const span = (value: any) =>
    value
      ? {
          status: value.status ?? null,
          source: adapter.path(value.source),
          startLine: value.startLine ?? null,
          endLine: value.endLine ?? null,
        }
      : null;
  const record = (entry: any, index: number, excerptLimit = 6000) => ({
    marker: adapter.markerId(index),
    book: {
      ...span(entry.match),
      target: entry.booklink?.target ?? null,
      excerpt: String(entry.booklink?.excerpt ?? "").slice(0, excerptLimit),
    },
    lean: entry.lean
      ? {
          source: adapter.path(entry.lean.source),
          declaration: entry.lean.declName ?? null,
          kind: entry.lean.declKind ?? null,
          declarationStartLine: entry.lean.declLine ?? null,
          declarationEndLine: entry.lean.declEndLine ?? null,
          markerStartLine: entry.lean.markerLine ?? null,
          markerEndLine: entry.lean.markerEndLine ?? null,
        }
      : null,
    tex: span(entry.texMatch),
    pdf: adapter.pdfLocation(index),
  });
  const marker = (value: unknown) => {
    const id = text(value, "marker", 500),
      index = adapter.markerIndex(id);
    if (index === null) throw new Error(`Unknown marker: ${id}`);
    return index;
  };
  const handlers: Record<string, (args: Record<string, unknown>, signal?: AbortSignal) => unknown | Promise<unknown>> =
    {
      get_viewer_state: () => adapter.state(),
      list_markers: (args) => {
        const query = args.query === undefined ? "" : text(args.query, "query", 300).toLowerCase();
        const source = args.source === undefined ? "" : text(args.source, "source");
        const offset = integer(args.offset, "offset", 0, 0),
          limit = integer(args.limit, "limit", 20, 1, 50);
        const matches = adapter
          .entries()
          .map((entry, index) => ({ entry, index }))
          .filter(
            ({ entry, index }) =>
              (!source ||
                [entry.match?.source, entry.lean?.source, entry.texMatch?.source].some(
                  (path) => adapter.path(path) === source,
                )) &&
              (!query ||
                [
                  adapter.markerId(index),
                  entry.booklink?.excerpt,
                  entry.lean?.declName,
                  adapter.path(entry.match?.source),
                  adapter.path(entry.lean?.source),
                ].some((value) =>
                  String(value ?? "")
                    .toLowerCase()
                    .includes(query),
                )),
          );
        return {
          total: matches.length,
          offset,
          markers: matches.slice(offset, offset + limit).map(({ entry, index }) => record(entry, index, 400)),
        };
      },
      get_marker: (args) => {
        const index = marker(args.marker);
        return record(adapter.entries()[index], index);
      },
      find_markers_for_location: (args) => {
        const source = text(args.source, "source"),
          line = integer(args.line, "line", 0),
          limit = integer(args.limit, "limit", 20, 1, 50);
        if (!line) throw new Error("line is required.");
        const within = (path: unknown, start: unknown, end: unknown) =>
          path === source && typeof start === "number" && typeof end === "number" && line >= start && line <= end;
        const matches = adapter
          .entries()
          .map((entry, index) => ({ entry, index }))
          .filter(
            ({ entry }) =>
              within(adapter.path(entry.match?.source), entry.match?.startLine, entry.match?.endLine) ||
              within(adapter.path(entry.lean?.source), entry.lean?.declLine, entry.lean?.declEndLine) ||
              within(adapter.path(entry.lean?.source), entry.lean?.markerLine, entry.lean?.markerEndLine) ||
              within(adapter.path(entry.texMatch?.source), entry.texMatch?.startLine, entry.texMatch?.endLine),
          );
        return {
          total: matches.length,
          markers: matches.slice(0, limit).map(({ entry, index }) => record(entry, index)),
        };
      },
      read_source: async (args, signal) => {
        const source = text(args.source, "source");
        if (!adapter.sources().includes(source)) throw new Error("Source is not exposed by this book.");
        const start = integer(args.startLine, "startLine", 1),
          end = integer(args.endLine, "endLine", start + 79);
        if (end < start || end - start >= 200) throw new Error("Read at most 200 consecutive lines.");
        const lines = (await adapter.readSource(source)).split("\n");
        signal?.throwIfAborted();
        return {
          source,
          totalLines: lines.length,
          lines: lines.slice(start - 1, end).map((text, offset) => ({ line: start + offset, text })),
        };
      },
      search_book: (args, signal) =>
        adapter.search(text(args.query, "query", 300), integer(args.limit, "limit", 20, 1, 50), signal),
      navigate_marker: async (args) => {
        const index = marker(args.marker);
        await adapter.navigate(index);
        return record(adapter.entries()[index], index);
      },
    };
  return descriptors.map((descriptor) => {
    const handler = handlers[descriptor.name];
    if (!handler) throw new Error(`Unsupported viewer tool: ${descriptor.name}`);
    const allowed = Object.keys((descriptor.inputSchema as { properties?: object }).properties ?? {});
    return {
      ...descriptor,
      execute: async (input: unknown, options?: { signal?: AbortSignal }) => {
        options?.signal?.throwIfAborted();
        if (
          !input ||
          typeof input !== "object" ||
          Array.isArray(input) ||
          Object.keys(input).some((key) => !allowed.includes(key))
        )
          throw new Error("Invalid tool arguments.");
        const result = await handler(input as Record<string, unknown>, options?.signal);
        options?.signal?.throwIfAborted();
        return result;
      },
    };
  });
}

interface ModelContext {
  registerTool(tool: object, options: { signal: AbortSignal }): Promise<void> | void;
}
export async function registerViewerAgentTools(adapter: ViewerAgentAdapter): Promise<void> {
  const context = (document as Document & { modelContext?: ModelContext }).modelContext;
  if (!window.isSecureContext || !context?.registerTool) return;
  const response = await fetch(new URL("./ai-catalog.json", location.href));
  if (!response.ok) throw new Error(`AI Catalog: HTTP ${response.status}`);
  const catalog = await response.json();
  const tools = viewerAgentTools(catalog.entries[0].data.tools, adapter);
  let controller: AbortController | undefined;
  const register = async () => {
    controller?.abort();
    const current = new AbortController();
    controller = current;
    try {
      await Promise.all(tools.map((tool) => context.registerTool(tool, { signal: current.signal })));
    } catch (error) {
      current.abort();
      throw error;
    }
  };
  await register();
  window.addEventListener("pagehide", () => controller?.abort());
  window.addEventListener("pageshow", (event) => {
    if (event.persisted) void register().catch((error) => console.error("[viewer] WebMCP", error));
  });
}
