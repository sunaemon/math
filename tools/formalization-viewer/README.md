# Formalization Viewer

Source-map-driven viewer for the Polish-space book (PDF · Markdown · Lean · TeX),
with a Lean infoview, comment folding, and live reload.

Start the server (serves static files plus the Lean LSP bridge and file watcher):

```sh
make formalization-viewer
```

Then open:

```text
http://127.0.0.1:8765/polish-space/
```

The mount `/polish-space/` is one URL tree holding both the viewer and the
project: paths that exist in the generic viewer directory
`tools/formalization-viewer/` are served as viewer assets, and everything else is a
project file checked against the manifest allowlist. `/` redirects to the
mount. The viewer loads these defaults:

- `/polish-space/build/polish-space-book-sourcemap.json`
- `/polish-space/build/polish-space-book-debug.pdf`

Override them with query parameters:

```text
http://127.0.0.1:8765/polish-space/?map=/polish-space/build/polish-space-book-sourcemap.json&pdf=/polish-space/build/polish-space-book-debug.pdf
```

Minimal fixture test:

```text
http://127.0.0.1:8765/polish-space/?map=/tools/formalization-viewer/fixtures/simple-sourcemap.json&pdf=about:blank
```

The fixture has exactly three entries: a named theorem, a prose sentence, and a proof sentence. Each entry should render with the same color in the Markdown, Lean, and TeX panes. It also carries one `formalization: skip` overlay (see below) over a block of filler prose.

## Formalization-skip overlays

Book prose that is deliberately not a formalization obligation is bracketed in the `.md` sources with `<!-- formalization: skip ... -->` comments: `skip-begin`/`skip-end` mark a region, and a bare `skip` governs the single block that follows it. `tools/booklink_sourcemap.py` parses these into a top-level `skips` array on the source map, and the Markdown pane renders each as a neutral grey wash with a dashed left rail — distinct from the coloured booklink marks — so skipped regions read as "intentionally out of scope". The skip reason shows as a tooltip on hover. Skip overlays carry no entry/rail/click wiring, so they never interfere with booklink navigation.

Each skip also gets a stable `key` (`<chapter-stem>-<offset>`), and the book filter wraps the region in the rendered TeX with `\SkipStart{key}`/`\SkipEnd{key}` — zero-width hypertargets (`skip-key-start` / `skip-key-end`) gated on the same `\booklinkhighlighttrue` debug flag as the Booklink coloring. So the **debug** PDF (the one the viewer loads) carries the anchors while the released book stays byte-for-byte unchanged. The PDF pane resolves those destinations and draws a translucent grey band over the skipped region — crossing page breaks into per-page segments — mirroring the Markdown grey wash. A non-debug PDF simply has no anchors, so no bands appear.

Scroll sync currently applies to the Markdown, Lean, and TeX panes. The PDF pane is displayed alongside them, but page-level PDF sync is a later step because the current source map tracks TeX spans rather than PDF coordinates.

## Syntax highlighting

The Lean pane is highlighted with the Lean tree-sitter grammar and the Markdown pane is parsed with the Markdown grammar; the TeX pane stays plain. Highlighting runs in the browser through `web-tree-sitter`, with the runtime, grammars (Lean, Markdown, Markdown-inline), and `highlights.scm` queries committed under `vendor/treesitter/`. Token colors compose over the source-map mark backgrounds, so scroll sync and click-to-activate are unaffected.

Refresh the vendored assets with:

```sh
make treesitter-assets
```

That runs `tools/fetch_treesitter_assets.sh`, which downloads the pinned `web-tree-sitter` runtime and Markdown grammar Wasm modules, and builds the Lean grammar to Wasm with the tree-sitter CLI from mise. Pinned versions live at the top of the script and in `vendor/treesitter/VERSIONS`.

The `.md` sources are Pandoc Markdown with heavy embedded LaTeX, which the Markdown grammar treats as plain prose. A LaTeX-aware overlay therefore colors `\commands`, `\begin{}`/`\end{}` environments, `$`/`$$` math delimiters, and `{}` grouping on top of the Markdown structure.

If the vendored assets are missing or fail to load, the viewer logs a single warning and renders all panes as plain text.

A Node smoke check loads the vendored runtime, grammars, and queries the same way the browser does and prints capture tallies for the fixtures:

```sh
node tools/formalization-viewer/check_highlights.mjs
```

## Lean infoview

The Infoview pane shows live Lean goal state and diagnostics, like the VS Code infoview but rendered as text. It needs a backend, so the viewer is served by `tools/formalization-viewer/server/serve.ts` (started by `make formalization-viewer`) rather than `python -m http.server`. That server serves the repository statically _and_ bridges a shared `lake env lean --server` subprocess:

- `GET /lsp/info` — bridge health and the repository `file://` root.
- `GET /events` — Server-Sent Events stream; its `lsp` channel carries JSON-RPC messages from the Lean server, its `watch` channel file-watch notifications.
- `POST /lsp/send` — forwards one JSON-RPC message to the Lean server.

The two channels share one stream (`event-stream.js`) so each tab pins a single connection: browsers cap concurrent HTTP/1.x connections per origin across all tabs, and with one stream per channel a few viewer tabs exhausted the cap and stalled every further request, including the LSP handshake itself.

The browser client (`lean-lsp.js`) runs the LSP handshake, opens the selected Lean file, and queries `$/lean/plainGoal` / `$/lean/plainTermGoal`. Goals refresh automatically at the active booklink entry and when you click a line in the Lean pane; `textDocument/publishDiagnostics` populates the Messages section. Hovering a symbol in the Lean pane issues a debounced `textDocument/hover` and shows the type signature and docstring in a floating tooltip. `lake` must be on PATH (via mise/elan) and the project should be built so imports resolve from cached oleans. If the bridge is absent — for example when the viewer is served by plain `python -m http.server` — the pane shows an "unavailable" notice and the rest of the viewer works unchanged.

## Static distribution

```sh
make formalization-viewer STATIC=1
```

builds a self-contained copy of the viewer under `dist/` and serves it at
`http://127.0.0.1:8765/` by default. Override the port with
`BOOKLINK_VIEWER_PORT=...`. The distribution remains hostable by any static
file server: no live bridge, no Lean toolchain.

`tools/formalization-viewer/server/static-dist.ts` mirrors the live server's URL space: the viewer
assets, the project files the live server allowlists, and the LSP cache all
land in one tree at the mount path, and `dist/index.html` redirects to the
mount. The dist `manifest.json` gains `"static": true`, which tells the browser
client to skip the LSP bridge and the file watcher. URLs are resolved relative
to the mount, so the dist also works when hosted from a subdirectory.

Instead of live LSP queries, the infoview reads a pregenerated cache
(`lsp-cache/…/<file>.lean.json` under the mount, built by
`tools/formalization-viewer/server/lsp-cache.ts`). For every Lean file the generator runs
`lake env lean --server` once, waits for elaboration, and records
`$/lean/plainGoal`, `$/lean/plainTermGoal`, and `textDocument/hover` **once per
symbol** (each token start, plus column 0 of every line), along with the file's
diagnostics; a click or hover at any position resolves to the enclosing
symbol's cached answer. Responses are deduplicated into shared tables, so the
cache stays compact.

Each cache file is keyed by a hash of the Lean source, its transitive
in-project imports, and the toolchain pins, and the generator keeps its working
copy in `polish-space/build/lsp-cache/`. Regeneration therefore only
re-elaborates files whose import cone actually changed; everything else is
reused. The status pill shows `LSP: cached` in this mode.

## Live reload

`tools/formalization-viewer/server/serve.ts` also runs `watchexec` (native inotify on Linux, FSEvents on macOS) over everything the viewer depends on and relays changed paths on the `watch` channel of the shared `GET /events` stream (`file-watch.js`):

- **`src/**.md`, `polish-space/lean/PolishSpaceBook/**.lean`, `build/…-debug.tex`** — re-render the affected source pane in place (scroll preserved); a changed Lean file is also pushed to the LSP server so goals/diagnostics update.
- **`build/…*.pdf`** — reload the PDF.
- **booklink source map and `polish-space/src/polish-space-book.json` manifest** — reload the map, rebuild the entry list and file choices, and re-render.
- **the viewer's own `tools/formalization-viewer/*.{js,css,html}`** — full page reload.

`watchexec` runs through mise; if it is not on PATH the `watch` channel stays idle and the viewer works without live reload.

### Auto-build on Markdown edits

A change under a project's served Markdown source tree (`src/**.md`) also triggers `serve.ts` (`server/book-builder.ts`) to run that project's `make` build, so editing prose refreshes the rendered panes without a manual `make`. The regenerated `build/` files flow back through the same watcher as the reload events above; only Markdown changes start a build, so the build's own TeX/PDF/JSON output never loops. Builds are debounced per project and coalesced: a save during an in-flight build queues exactly one rebuild.

The build **target is resolved from the PDF the tab is showing**. Each tab reports its selected PDF (`POST /build/select`, repo-relative path), and the builder rebuilds the matching `make` target — the debug PDF (manifest `pdf`) plus its source map (`sourceMap`), or a per-chapter preview PDF (`<stem>-preview-<chapter>.pdf`) — whichever is selected. The **release PDF is never auto-built**. The source map is always rebuilt so the Markdown/Lean/TeX marker overlays track the edit even when a preview PDF is the one selected. With no tab connected the debug PDF is the default. The **Chapter preview** dropdown entry tracks the chapter in the Markdown pane: it renders just that chapter via `\includeonly` (a few pages, ~1s) instead of the whole 400-page debug PDF, and follows the source you switch to. Switching the PDF dropdown to a different render rebuilds that target so it is current when you view it; the initial selection on page load only records the preference.

The debug PDF build runs LuaLaTeX, so it is not instant; disable the feature with `BOOKLINK_AUTOBUILD=0`, point it at a different build program with `BOOKLINK_MAKE=<executable>` (a single program name run without a shell, so it cannot carry arguments), or tune the per-project debounce with `BOOKLINK_AUTOBUILD_DEBOUNCE_MS` (default 400).

While a build runs, the server relays its `{ dir, state }` status (`state: "building" | "done" | "failed"`) on a `build` channel of the `GET /events` stream, and the viewer (`build-status.js`) shows a **Building…** pill in the PDF pane header — flashing red on failure. A tab only reacts to its own project's events. The in-flight set is replayed to each new stream, so a tab opened mid-build still shows it.

## Type checking

The browser modules are authored in TypeScript under `src/` and transpiled by esbuild (type-strip only, no bundling) to the `.js` files index.html loads under `build/`; `make viewer-build` runs the transpile and `build/` is gitignored. `src/` and `build/` sit at the same depth, so the modules' `import.meta.url`-relative `../vendor/...` paths resolve identically whether `tsc` reads `src/` or the browser loads `build/`.

`make lint` type-checks the `src/` modules with `tsc` (pinned in `mise.toml`, configured by `tools/formalization-viewer/tsconfig.json`). `strict` is on for every viewer module. The vendored tree-sitter runtime under `vendor/` is shimmed out by `vendor/treesitter/web-tree-sitter.d.ts` and never checked. `make doctor` verifies `tsc` is available.

All viewer modules carry JSDoc types and the check is green; keep it that way by running `make lint` after editing them. A module can be temporarily opted out with a `// @ts-nocheck` header if needed.

## Server

The server (`server/`) is TypeScript run directly by node's type-stripping — no build step: `serve.ts` (live HTTP + Lean LSP bridge + file watcher), `static-dist.ts` (the `dist/` builder), `lsp-cache.ts` (the static LSP cache generator), plus `free-port.ts` and small helpers. It uses only Node built-ins; `watchexec` (via mise) is the file-watch engine. `make lint` type-checks it with `tsc` against `server/tsconfig.json`, and `make test-node` runs the `node --test` unit tests (`request-trust`, the bridge race contract). tsc resolves the `node:` imports through `@types/node` (pinned in `mise.toml`); the Makefile symlinks it into `server/node_modules` (gitignored), which node itself does not need.

## End-to-end tests

`make test-e2e` drives the real SPA in a headless browser — the coverage the unit tests deliberately cannot reach: the DOM/async glue and the live server connection. It launches the live `serve.ts` (the HTTP + SSE bridge, **not** the static dist, which has no `/events` stream or LSP) and a headless Chrome, then exercises the rendered page: the source panes rendering with booklink marks, the live `/events` + `/lsp` connections, the custom dropdown filtering and switching files, and cross-pane marker activation.

The harness lives under `e2e/` and uses **no npm dependency**: `cdp.ts` speaks the Chrome DevTools Protocol over Node's global `WebSocket` (it spawns Chrome with `--remote-debugging-port` and attaches to a page target), and `viewer-server.ts` spawns `serve.ts` on an ephemeral port. It needs a Chrome/Chromium binary (auto-detected at the usual macOS/Linux paths; override with `CHROME=/path/to/chrome`) and the polish-space sourcemap + debug PDF, which the target builds as prerequisites. It is **not** part of `make test` because it needs a browser and is slower; run it explicitly. `make lint` type-checks the harness with `tsc` against `e2e/tsconfig.json`.
