# Formalization Viewer

Source-map-driven viewer for the Polish-space book (PDF · Markdown · Lean · TeX),
with a Lean infoview, comment folding, and live reload.

The Markdown header's **Correspondence / AST** button opens the selected
chapter's formula inspector. Choose a formula to see its source spans, resolved
variables, syntax AST, actual Haskell semantic AST and Lean interpretation.
Each operator lists the mapping rule, resolved Lean function, ordered arguments,
implicit arguments and premise checks. Click an operator or AST span to highlight
its original formula; **Open source** returns to the corresponding Markdown line.
Offsets count Unicode characters from zero; line numbers start at one.

**Formula overlays** adds a separate dotted layer in Markdown and the annotated
PDF alongside the existing lemma/proof bands. Hover or keyboard-focus an
expression in PDF, Markdown or the indexed original Lean source to highlight
its counterparts in all visible panes. Counterparts outside the viewport are
revealed without changing the active marker or URL. Lean occurrences shared by
several book formulas retain every correspondence. Whole-expression matches use the filled highlight. A match confined to a
subexpression uses an amber dotted underline, with explicit whole/partial counts
in the popup. Only a verified single-call operator that covers the entire source
formula qualifies for whole-expression styling; disconnected partial matches
never fill their unverified gaps. Moving away clears the hover;
click or press Enter to pin the popup, and Escape or an outside click dismisses
it. Hovering another formula temporarily previews it and restores the pinned
selection on leave. The popup shows its Lean interpretation and operator rules;
the popup's **Correspondence / AST** button opens that exact formula's details.
The layer has its own toggle and does not remove lemma correspondence.
PDF locations come from source-identified marked content on TeX math nodes,
including wrapped formulas, scripts, fractions and multiline displays. Tags
carry a source revision fingerprint, so a PDF from another source revision
cannot acquire an overlay through text similarity. Glyph/rule tagging adds no
boxes or spacing and is emitted only for configured chapters in debug PDFs.
The browser draws every colored overlay; the PDF carries invisible identity
metadata, following the existing lemma anchor approach at expression granularity.

Selecting a formula also locates operator occurrences in the original Lean
source. A separate read-only InfoTree index is matched in Haskell against the
validated full kernel application and its local variable types/values. This is
conservative: a matching function name alone is insufficient. Missing exact
locations are reported explicitly; the viewer never substitutes an entire lemma
as an expression highlight. When the Lean pane is visible, its exact ranges
load in the background so reverse hover works before the first click. The source
index is cached by source, exporter, query and Lean dependency content. It does
not block Markdown/PDF correspondence loading; subsequent hover and selection
reuse the same in-flight request or loaded index.

The live server shares concurrent inspections and caches results until their
source, rules, review, validation snapshot or exact Lean dependency files change.
Unrelated PDF/build updates do not discard the cache. Reopening the inspector
shows the previous result immediately while checking for updates; HTTP ETags
avoid transferring an unchanged chapter again.

The AST inspector uses the latest chapter validation snapshot without running
Lean checks or granting interpretation approval. The separate original-source
index elaborates the unchanged Lean module and does not replace correspondence
validation. If the source, rules, review,
configuration or Lean dependencies changed, it labels the evidence historical
and withholds the current semantic AST. Refresh after running
`make validate-correspondence CHAPTER=polish-spaces` to load new evidence.
The semantic tree is an opt-in, read-only projection of the Haskell value,
separate from the ordinary Python/Haskell transaction interface.

This inspector currently requires the live viewer and a registered chapter
report. Other chapters and Japanese translations without their own projected
expression evidence show an unavailable message; English offsets are never
applied to translated Markdown. Ordinary source, PDF and Lean browsing continue
to work for those books and for static exports.

Start the server (serves static files plus the Lean LSP bridge and file watcher):

```sh
make formalization-viewer
```

To listen on this machine's Tailscale IPv4 address instead of loopback:

```sh
make formalization-viewer BOOKLINK_VIEWER_HOST="$(tailscale ip -4)"
```

Open the printed URL from another device on the same Tailscale network.
To use its MagicDNS domain, pass the machine's full Tailscale DNS name instead:

```sh
make formalization-viewer BOOKLINK_VIEWER_HOST=your-machine.your-tailnet.ts.net
```

The server binds to the address resolved from that name. The HTTP bridge and
Build log WebSocket accept only the configured IP or DNS name and matching
origins. `BOOKLINK_VIEWER_PORT` selects the preferred port, defaulting to 8765.

The live server starts after compiling the viewer's JavaScript, without waiting
for book PDFs or source maps. Opening a book reports the restored PDF selection
and schedules an incremental build of that render and its source map in the
background. Existing artifacts remain readable while the build runs; missing
artifacts appear through live reload. The Japanese book also builds the English
PDF shown alongside it. Other books are not built just because the server starts.
`STATIC=1` and `make dist` still build their artifacts before packaging them.

The PDF selector names chapter previews using their Markdown chapter headings,
including Japanese titles in the translated book. Whole-book PDFs are labelled
**Full book · Annotated**, **Full book · Release**, or **Full book · Changes**.
The selection still identifies the same PDF path for builds and saved sessions.

The hamburger menu's **全文検索** action searches every book chapter through a
local Pagefind index. Cmd/Ctrl+K opens that search. Cmd/Ctrl+F and each pane's **検索**
button search the selected Markdown, Lean, TeX, or PDF document. Each scope
remembers its own query. Pane search appears as a floating bar on the right,
with a fixed-width match counter and previous/next controls. Its initial counter
is `- / -`. Results are scanned in resumable batches of 200. Advancing to within
100 matches of the current end scans another 200 without changing the selected
match; `+` disappears once the document is exhausted. In a maximized pane it replaces the normal floating controls until
closed with × or Escape. PDF search waits for loading automatically and prepares
the next two distinct result pages and the previous result page in advance;
changing the query or closing the bar cancels queued prefetch work. Whole-book results open their source
line, and their links preserve that location when shared or reloaded.

Static exports generate the index during packaging. The live server builds and
caches it on first use, then invalidates it when book inputs change. Pagefind's
Japanese segmentation supports queries without spaces; queries stay in the
browser. Visited index assets join the offline cache. PDF search extracts text
from the selected PDF rather than using the Markdown index.

The viewer enforces Trusted Types in supporting browsers. HTML insertion passes
through the `viewer-html` DOMPurify policy, while `viewer-script-url` accepts only
the bundled PDF, search, and offline worker URLs. Other browsers still sanitize
HTML. The CSP also permits DOMPurify's internal `dompurify` policy for parsing.
Each PDF loading task owns a separate Trusted Types-approved worker. Replacing
one document releases only its own worker, including failed loading tasks;
primary, parallel, and reference PDFs do not share a destructible worker proxy.

Pagefind is pinned: index generation checks and adapts its worker constructor
for Trusted Types, failing if a future version changes that integration point.

The hamburger menu's **PDF** section also offers **Page size** (A4, A5, JIS B5,
JIS B6) and **Text size** (10, 11, 12 pt). **Book default** retains the source's
setting. Choices travel in the URL as `paper` and `fontSize`, and apply to both
PDF panes, chapter previews, and the annotated full book. Changing a setting
while viewing a release PDF switches to the annotated full book. The first
selection builds a separate PDF; the existing PDF stays visible during that
build. Each layout keeps separate auxiliary files, so concurrent readers can
use different settings. Static exports disable these controls because they
cannot build new layouts.
Chapter previews begin at the chapter bookmark, omitting preceding part-title
and odd/even padding pages from both PDF panes. Original PDF page numbers and
destinations are retained for source synchronization and links.

In Chapter mode, scroll to the bottom and pull again to open the next chapter at
its beginning. Pull upwards at the top to return to the previous chapter's end.
This works in either PDF pane with a wheel, trackpad, or a touch-and-release
gesture. Reaching an edge through normal scrolling does not turn the chapter;
momentum cannot skip additional chapters. A pull indicator names the destination.

Viewer controls follow the browser's ordered language preferences, supporting
Japanese and English with English as the fallback. This is independent of the
book selection: English books can use Japanese controls and vice versa. Reload
after changing browser language settings. Book text, code, quoted passages,
license originals, and chat responses retain their own language.

The Panels section also contains the Layout controls.

Tab focus opens link previews immediately. The preview follows the focused PDF
link through the browser's automatic scroll; ordinary pointer hover keeps its
delay, and scrolling the focused link out of view dismisses the preview.

Pane header actions follow the same order in the DOM and on screen: search,
marker highlights, link highlights, build log, open in a new tab, maximize, close.
Unavailable actions are omitted; status text stays before the action icons.
Search uses the same magnifying-glass icon in the menu and every pane, with
accessible labels and hover titles identifying its scope.

Each pane has a maximize icon at the right of its header. Maximizing hides the
viewer toolbar, pane headers, and marker rail, filling the viewport with the
document. A small floating restore icon brings back the original layout and
reading positions. The maximized document uses normal page scrolling, allowing
iPhone Safari to shrink its browser bars naturally while reading. Split panes
retain independent scrolling. Maximization is part of the URL's pane layout, so reloads
keep the focused pane and preserve the layout to restore.

Then open:

```text
http://127.0.0.1:8765/polish-space/
```

## Ask about a passage

Open chat with the round speech-bubble button at the bottom right. Close the
chat panel to return to the document; the button reappears.

In either the live or static viewer, select text in a PDF, Markdown, Lean, or TeX pane and choose
**これを説明**. A side panel shows the selected passage and the exact context that
will be sent: nearby source lines, corresponding Lean, referenced definitions,
and the mathematical macros used there. Review it, edit the question, and press
**送信**. Selection alone never sends book content to OpenAI. Answers stream with
Markdown/KaTeX rendering; follow-up questions retain the initial context. Use
**停止** to cancel or **新しい会話** to clear the conversation. Chats live in the tab
and are cleared on reload. Chat uses only browser-to-OpenAI requests and needs
no Node server, proxy, viewer API, or server-side credentials.

Open **ChatGPT に接続** and choose **Continue with ChatGPT**. This uses OpenAI's
[official ChatGPT plan usage flow](https://developers.openai.com/siwc/token-sharing-open-source/sign-in)
with dynamic client registration, PKCE, state, nonce and verified ID tokens.
Availability depends on OpenAI's current project/account eligibility and the
user granting ChatGPT plan usage. Models come from the connected account's
catalog; this does not read existing ChatGPT conversations.

ChatGPT sign-in requires HTTPS or localhost for browser cryptography. The
OAuth provider still requires a `127.0.0.1` callback. A static page cannot run a
loopback listener, so after authorizing, the final login tab will fail to open.
Copy that tab's **full address** into **ログイン後の戻り先 URL** and choose
**ログインを完了**. The browser validates state, PKCE, ID-token signature, nonce,
issuer, audience, expiry and granted scopes, then calls OpenAI directly. The
attempt expires after ten minutes. No code or token goes through the viewer's
hosting server, and no client secret is embedded in the site.

Sign-in does not request `offline_access`, so OpenAI issues no refresh token,
and the ID token is verified at sign-in without being retained. The access
token, its expiry and the verified account identity are kept in browser
`sessionStorage` for this tab together with the pending sign-in transaction,
allowing reloads until the token expires or the tab closes. When the access
token expires, the saved connection is cleared and you sign in again. If
browser storage is disabled, the connection lasts in memory until reload. The
stable, non-secret host ID is stored in `localStorage`. **接続解除** clears this tab's
connection. Server-side connections from earlier versions are not imported;
sign in once again after upgrading. No existing Codex credentials are reused.

Alternatively, expand **API キーで接続** and enter your own OpenAI API key. It is
held only in the tab's memory and sent directly to OpenAI. Reloading or
disconnecting removes it. API calls use that key's API billing. No key is
included in a static build or stored on the hosting server.

OpenAI's public JWKS endpoint does not currently allow browser CORS requests.
The site therefore ships public RS256 verification keys in `src/chat-jwks.ts`;
unknown signing keys are rejected. When OpenAI rotates signing keys, refresh
the public snapshot and rebuild:

```sh
python3 tools/update_viewer_chat_jwks.py
mise exec -- prettier --write tools/formalization-viewer/src/chat-jwks.ts
make viewer-build
```

Rebuild the static distribution after this refresh. Only public verification
keys are downloaded; this does not read or package authentication credentials.
The browser uses the public token and Responses endpoints with CORS and
`credentials: omit`. A CORS/network failure is reported to the user; it never
falls back to a server proxy or an unverified identity.

The live server also exposes the Japanese draft translation at:

```text
http://127.0.0.1:8765/polish-space-ja/
```

The book selector switches between all discovered project manifests. The
Japanese project shares the canonical English Lean workspace while its source
map projects each English formalization span onto the corresponding complete PO
message, refining highlights to aligned sentences when their mathematical anchors
agree. All chapters currently have Japanese draft translations.

The Japanese project opens with the Japanese rendered PDF immediately to the
left of the canonical English rendered PDF. The English PDF pane can be hidden
or restored from **View options → Panels** like the other viewer panes. Both
PDFs resolve the same formalization-marker destinations, so scrolling either
pane aligns the other at the corresponding passage rather than the same raw
page number. The English renderer follows the Japanese page width, keeping both
panes at the same visual zoom. Each PDF pane has its own marker-highlight
toggle, so either language can be read with or without linked-passage overlays.
Scrolling either PDF through a skipped region selects the owning Markdown file
and follows the same relative position in the Book source pane.
Internally, formalization entries and skips are two variants of the same
first-class navigation location. Every synchronized pane implements one
`nearest`/`supports`/`scrollTo` contract for both variants.

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

## Reading position: links and the stored session

The marker being read is written into the address bar, so copying the URL shares that passage:

```text
http://127.0.0.1:8765/polish-space/?marker=closed_subspace_polish~2
```

The id is the marker's Lean declaration name rather than its entry index, which shifts whenever a booklink is added earlier in the book. A declaration carrying several markers — a statement and its proof — qualifies each with a 1-based ordinal, `declName~2`; a bare name means the first. An entry whose sourcemap record has no declaration falls back to a positional `@index`. A skipped region is linked by its key instead, `?skip=polish-spaces-72`. Both are updated in place with `history.replaceState`, including while scrolling, so the back button still leaves the viewer rather than walking back through every marker passed. A link whose marker the book no longer has warns on the console and opens at the stored position.

Pane arrangement and PDF mode are URL-owned settings with format `v=1`.
`layout` uses a readable split expression with pane visibility, order,
direction, and size ratios; it is omitted for the book's default arrangement.

| Example                        | Arrangement                                       |
| ------------------------------ | ------------------------------------------------- |
| `layout=pdf`                   | PDF only                                          |
| `layout=row(pdf,md,lean)`      | PDF, Markdown, and Lean side by side              |
| `layout=col(pdf,md)`           | PDF above Markdown                                |
| `layout=row(pdf:3,md:1)`       | PDF and Markdown with widths in a 3:1 ratio       |
| `layout=row(pdf,col(md,lean))` | PDF on the left; Markdown above Lean on the right |
| `focus=pdf`                    | Maximize PDF and retain the layout to restore     |

Pane names are `pdf`, `pdf-peer`, `md`, `lean`, `tex`, and `infoview`.
Weights after `:` apply to the child immediately before them, including a nested
split. Equal weights are omitted; drag-generated ratios become small integer
proportions. Parentheses, commas, and colons stay readable in the URL.
Default layout plus maximization needs only `focus`; restoring removes it.
Previously copied JSON layout values remain readable and are rewritten to the
compact notation when the viewer updates the URL, still under `v=1`.

The hamburger menu's **Documents** section selects the book. PDF chapters or
editions, Markdown files, and Lean files are selected in their pane headers.
Opening a selector by pointer shows its list without focusing a text input;
tap the search field to type. Opening with Enter or an arrow key focuses search
immediately. Typing after pointer opening also begins search with that first
character. Search inputs use 16px text to avoid focus-triggered phone zoom.
View options → PDF uses segmented buttons to select **Chapter** (the default, omitted from the URL) or
**Full** (`pdfMode=full`) for both PDF panes. Changing these settings updates the URL in place.
Missing settings use defaults, never local storage. Older unversioned position
links still work, and unknown versions are preserved without interpreting them.

Appearance, color scheme, font, line numbers, marker highlights, link outlines,
and scroll sync remain in book-independent `localStorage` keys. Reading positions
and Markdown/Lean sources are per book under `formalization-viewer-session-v1:<mount>`.
Startup removes legacy layout/PDF-mode keys and saved session PDF selections.
A small blocking startup bundle applies
the theme and color scheme before the first paint; panes are revealed after their saved
configuration is ready, avoiding a flash of default tabs during reload.
Only visible panes load documents. Maximizing a pane defers hidden PDFs,
Markdown, Lean, TeX, and the Lean connection until those panes are shown.
Visible panes load independently and become readable as each finishes;
the global startup card ends once the layout and controls are ready.
Root overscroll is disabled, with a touch-edge fallback to prevent Safari's
pull-to-refresh. Ordinary page scrolling, nested-pane scrolling, pinch zoom,
and the viewer's chapter pull navigation remain available.
The startup card reports downloaded application modules before the application
has started, then follows book settings, the source map, document choices,
pane layout, PDF transfer and layout analysis, source rendering, and reading-position restoration.
PDF download progress uses actual transferred bytes; layout progress counts sampled pages.
During PDF updates, the current document stays readable while its replacement
is downloaded, laid out, and its first visible page rendered off screen.
The panes swap only after that preparation succeeds and retain the position
reached while waiting. Failed updates leave the previous document available.
PDF and map watch events received during a build are held until it finishes.

## Formalization-skip overlays

Book prose that is deliberately not a formalization obligation is bracketed in the `.md` sources with `<!-- formalization: skip ... -->` comments: `skip-begin`/`skip-end` mark a region, and a bare `skip` governs the single block that follows it. `tools/booklink_sourcemap.py` parses these into a top-level `skips` array on the source map, and the Markdown pane renders each as a neutral grey wash with a dashed left rail — distinct from the coloured booklink marks — so skipped regions read as "intentionally out of scope". The skip reason shows as a tooltip on hover. Clicking a skipped source span scrolls each visible PDF to the corresponding relative position inside its skip region; it does not select or replace the active formalization marker.

Each skip also gets a stable `key` (`<chapter-stem>-<offset>`), and the book filter wraps the region in the rendered TeX with `\SkipStart{key}`/`\SkipEnd{key}` — zero-width hypertargets (`skip-key-start` / `skip-key-end`) gated on the same `\booklinkhighlighttrue` debug flag as the Booklink coloring. So the **debug** PDF (the one the viewer loads) carries the anchors while the released book stays byte-for-byte unchanged. The PDF pane resolves those destinations and draws a translucent grey band over the skipped region — crossing page breaks into per-page segments — mirroring the Markdown grey wash. A non-debug PDF simply has no anchors, so no bands appear.

Scroll sync applies to the Markdown, Lean, TeX, and PDF panes through formalization markers and skip spans. PDF destinations are resolved from the rendered document.

## Syntax highlighting

The Lean pane is highlighted with the Lean tree-sitter grammar and the Markdown pane is parsed with the Markdown grammar; the TeX pane stays plain. Highlighting is computed on the Node side (`server/highlight-core.ts`) with the runtime, grammars (Lean, Markdown, Markdown-inline), and `highlights.scm` queries committed under `vendor/treesitter/`: the live server answers `highlight-cache/<path>.json` on demand, memoized by source hash, and a static distribution ships pregenerated files at the same URLs. The browser only fetches that JSON — it never loads `web-tree-sitter`. Static distributions exclude `vendor/treesitter/`; the runtime, grammars, and queries are used only while generating the highlight cache. Token colors compose over the source-map mark backgrounds, so scroll sync and click-to-activate are unaffected.

Refresh the vendored assets with:

```sh
make treesitter-assets
```

That runs `tools/fetch_treesitter_assets.sh`, which downloads the pinned `web-tree-sitter` runtime and Markdown grammar Wasm modules, and builds the Lean grammar to Wasm with the tree-sitter CLI from mise. Pinned versions live at the top of the script and in `vendor/treesitter/VERSIONS`.

The `.md` sources are Pandoc Markdown with heavy embedded LaTeX, which the Markdown grammar treats as plain prose. A LaTeX-aware overlay therefore colors `\commands`, `\begin{}`/`\end{}` environments, `$`/`$$` math delimiters, and `{}` grouping on top of the Markdown structure.

If highlight data is unavailable for a file (an older distribution, a failed request), that pane renders as plain text. A grammar or query regression instead fails static generation loudly, so broken highlighting cannot ship silently.

A Node smoke check loads the vendored runtime, grammars, and queries the same way the generator does and prints capture tallies for the fixtures:

```sh
node tools/formalization-viewer/check_highlights.mjs
```

## Lean infoview

View options → Editor provides segmented **Appearance** buttons (Light by default; System / Light / Dark), **Color
scheme** (Solarized by default, or Classic), and a shared **Font** for Markdown,
TeX, Lean, Infoview, and build logs. Font choices use locally installed faces
with a monospace fallback. These preferences apply to every book and persist
across reloads. Build-log output always has a black background.

Dark appearance selects a separate TeX-built `-debug-dark.pdf` or
`-preview-<chapter>-dark.pdf` for each visible book. The live server builds that
artifact on demand, including the corresponding parallel PDF. Light and dark
renders have the same layout and destinations; switching preserves the current
reading position, including while waiting for the first dark build. Release
PDFs retain their print appearance.

The Infoview pane shows live Lean goal state and diagnostics, like the VS Code infoview but rendered as text. It needs a backend, so the viewer is served by `tools/formalization-viewer/server/serve.ts` (started by `make formalization-viewer`) rather than `python -m http.server`. That server serves the repository statically _and_ bridges a shared `lake env lean --server` subprocess:

- `GET /lsp/info` — bridge health and the repository `file://` root.
- `GET /events` — Server-Sent Events stream; its `lsp` channel carries JSON-RPC messages from the Lean server, its `watch` channel file-watch notifications.
- `POST /lsp/send` — forwards one JSON-RPC message to the Lean server.

The two channels share one stream (`src/event-stream.ts`) so each tab pins a single connection: browsers cap concurrent HTTP/1.x connections per origin across all tabs, and with one stream per channel a few viewer tabs exhausted the cap and stalled every further request, including the LSP handshake itself.

The browser client (`src/lean-lsp.ts`) runs the LSP handshake, opens the selected Lean file, and queries `$/lean/plainGoal` / `$/lean/plainTermGoal`. Goals refresh automatically at the active booklink entry and when you click a line in the Lean pane; `textDocument/publishDiagnostics` populates the Messages section. Hovering a symbol in the Lean pane issues a debounced `textDocument/hover` and shows the type signature and docstring in a floating tooltip. `lake` must be on PATH (via mise/elan) and the project should be built so imports resolve from cached oleans. If the bridge is absent — for example when the viewer is served by plain `python -m http.server` — the pane shows an "unavailable" notice and the rest of the viewer works unchanged.

## Static distribution

A distribution exports one selected `BOOKLINK_PROJECT`, not every live mount.
The Makefile chooses the project explicitly; direct script invocation without
that environment variable uses the first discovered manifest. `--dist` must
point inside the repository to a new/empty directory or a previous viewer
output. Source trees, repository metadata, and paths escaping through symlinks
are rejected before replacement. Test sources and fixtures are not shipped.

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

Syntax highlights are pregenerated the same way (`highlight-cache/<path>.json`
under the mount, built by `tools/formalization-viewer/server/highlight-cache.ts`
into `polish-space/build/highlight-cache/`). Each file records the tree-sitter
spans and Lean fold ranges for one source file, keyed by the source's hash, so
regeneration only recomputes edited files; the live server answers the same
URLs on demand instead.

## Live reload

`tools/formalization-viewer/server/serve.ts` also runs `watchexec` (native inotify on Linux, FSEvents on macOS) over everything the viewer depends on and relays changed paths on the `watch` channel of the shared `GET /events` stream (`src/file-watch.ts`):

- **`src/**.md`, `polish-space/lean/PolishSpaceBook/**.lean`, `build/…-debug.tex`** — re-render the affected source pane in place (scroll preserved); a changed Lean file is also pushed to the LSP server so goals/diagnostics update.
- **`build/…*.pdf`** — reload the PDF.
- **booklink source map and `polish-space/src/polish-space-book.json` manifest** — reload the map, rebuild the entry list and file choices, and re-render.
- **the viewer's own `tools/formalization-viewer/*.{js,css,html}`** — full page reload.

`watchexec` runs through mise; if it is not on PATH the `watch` channel stays idle and the viewer works without live reload.

### Auto-build on Markdown and Lean edits

A Markdown or Lean change under a project's served source trees (`src/**.md` or `lean/**.lean`) also triggers `serve.ts` (`server/book-builder.ts`) to run that project's `make` build, so editing prose refreshes the rendered panes without a manual `make`. The regenerated `build/` files flow back through the same watcher as the reload events above; only Markdown and Lean source changes start a build, so the build's own TeX/PDF/JSON output never loops. Build requests share a debounce timer and are coalesced across affected projects: a save during an in-flight build queues exactly one rebuild.

The build **target is resolved from the PDF the tab is showing**. Each tab reports its selected PDF (`POST /build/select`, repo-relative path), and the builder rebuilds the matching `make` target — the debug PDF (manifest `pdf`) plus its source map (`sourceMap`), or a per-chapter preview PDF (`<stem>-preview-<chapter>.pdf`) — whichever is selected. The **release PDF is never auto-built**. The source map is always rebuilt so the Markdown/Lean/TeX marker overlays track the edit even when a preview PDF is the one selected. With no tab connected the debug PDF is the default for source-change builds. The **Chapter preview** dropdown entry tracks the chapter in the Markdown pane: it renders just that chapter via `\includeonly` instead of the whole-book debug PDF, and follows the source you switch to. The initial selection on page load, reconnecting to the server, and switching the PDF dropdown to a different render schedule a build of that target. Repeated reports of the same selection within a session do not schedule another build.

The debug PDF build runs LuaLaTeX, so it is not instant; disable the feature with `BOOKLINK_AUTOBUILD=0`, point it at a different build program with `BOOKLINK_MAKE=<executable>` (a single program name run without a shell, so it cannot carry arguments), or tune the debounce with `BOOKLINK_AUTOBUILD_DEBOUNCE_MS` (default 400).

While a build runs, the server relays its `{ dir, state }` status (`state: "building" | "done" | "failed"`) on a `build` channel of the `GET /events` stream, and the viewer (`src/build-status.ts`) shows a build-log icon in the PDF pane header, with a spinner while building and red on failure. Click the icon to open the build log, which streams output over `WebSocket /build/log?dir=<book-dir>` while open and follows new output when scrolled to the bottom. The server sends the latest log on connection, then pushes stdout/stderr as it arrives; a new build resets the display. Connections automatically reconnect and retain at most the latest 1 MiB of text. After completion the **Build log** button keeps the latest output accessible; failure logs remain accessible too. A tab only reacts to its own project's events. The in-flight set is replayed to each new stream, so a tab opened mid-build still shows it.

The **Highlights** and **Links** controls in **View options → Overlays** apply across all panes. Highlights control the booklink washes, PDF bands, and overview rails; Links control PDF link outlines. These preferences survive reloads and book switches.
The same global controls are available as icons beside the maximize button in
both PDF headers and beside the restore button while any pane is maximized.
All copies stay synchronized, including the settings in the hamburger menu.

## PDF chapter choices

Marker selection, passive scroll synchronization, and URL/session persistence share one current location, including skipped passages. Older asynchronous navigation cannot overwrite a newer selection. Rebuilds preserve the viewing offset around the URL marker, with page-position fallback when it is unavailable. A browser reload restores each pane's position for the same URL; a newly opened permalink still navigates to its requested passage.

Hover or focus a linked term or notation in either PDF pane to see an excerpt from its definition, with the book's mathematical typesetting preserved and the defined word or formula highlighted. Internal PDF jumps briefly highlight their destination after the page is rendered. These reading cues remain visible regardless of the marker-highlight setting. Right-click, press the context-menu key, or use Shift+F10 to choose **Go to definition** or **Show references in index**. The references action opens the term's index entry without redirecting to its definition. Unavailable destinations in an excerpt book are disabled. On a touchscreen, tap a linked term or notation to keep its definition preview open. Use **Go to definition** or **Show references in index** inside the preview to navigate, or **Close**, an outside tap, or scrolling the document to dismiss it. Escape also dismisses the popup; mouse clicks continue to prefer the definition.

The PDF selector's **Chapter** mode lists **Contents** before the source chapters, with **Index** and **References** after them. These entries use separate preview units configured by the book manifest's `previewSections`; the Japanese book labels them **目次**, **索引**, and **参考文献**. Selecting the contents or index first refreshes the complete debug PDF and reuses its table of contents or index entries and page numbers.

## Type checking

The browser modules are authored in TypeScript under `src/` and bundled with shared chunks by esbuild into the `.js` files index.html loads under `build/`; `make viewer-build` builds these bundles and `build/` is gitignored. `src/` and `build/` sit at the same depth, so the modules' `import.meta.url`-relative `../vendor/...` paths resolve identically whether `tsc` reads `src/` or the browser loads `build/`.

`make lint` type-checks the `src/` modules with `tsc` (pinned in `mise.toml`, configured by `tools/formalization-viewer/tsconfig.json`). `strict` is on for every viewer module. The vendored tree-sitter runtime under `vendor/` is shimmed out by `vendor/treesitter/web-tree-sitter.d.ts` and never checked. `make doctor` verifies `tsc` is available.

All viewer modules carry JSDoc types and the check is green; keep it that way by running `make lint` after editing them. A module can be temporarily opted out with a `// @ts-nocheck` header if needed.

## Module layout

`src/app.ts` wires the panes together and owns startup; everything else lives in one module per subsystem — the PDF panes (`pdf.ts` and `parallel-pdf.ts`, with the machinery they share in `pdf-pane.ts`), the chat assistant (`chat.ts`), the sync engine, permalink/session state, and so on. New subsystems follow the same shape: their own module rather than new code in `app.ts`, and initialization isolated so a failure is reported (`reportError`) instead of aborting `init()` — an auxiliary feature must not be able to take the viewer down at startup. The chat module is the reference example.

## Server

The server (`server/`) is TypeScript run directly by node's type-stripping — no build step: `serve.ts` (live HTTP + Lean LSP bridge + file watcher), `static-dist.ts` (the `dist/` builder), `lsp-cache.ts` (the static LSP cache generator), plus `free-port.ts` and small helpers. It uses only Node built-ins; `watchexec` (via mise) is the file-watch engine. `make lint` type-checks it with `tsc` against `server/tsconfig.json`, and `make test-node` runs the `node --test` unit tests (`request-trust`, the bridge race contract). tsc resolves the `node:` imports through `@types/node` (pinned in `mise.toml`); the Makefile symlinks it into `server/node_modules` (gitignored), which node itself does not need.

## End-to-end tests

`make test-e2e` drives the real SPA in a headless browser — the coverage the unit tests deliberately cannot reach: the DOM/async glue and the live server connection. It launches the live `serve.ts` (the HTTP + SSE bridge, **not** the static dist, which has no `/events` stream or LSP) and a headless Chrome, then exercises the rendered page: the source panes rendering with booklink marks, the live `/events` + `/lsp` connections, the custom dropdown filtering and switching files, and cross-pane marker activation.

The harness lives under `e2e/` and uses **no npm dependency**: `cdp.ts` speaks the Chrome DevTools Protocol over Node's global `WebSocket` (it spawns Chrome with `--remote-debugging-port` and attaches to a page target), and `viewer-server.ts` spawns `serve.ts` on an ephemeral port. It needs a Chrome/Chromium binary (auto-detected at the usual macOS/Linux paths; override with `CHROME=/path/to/chrome`) and the polish-space sourcemap + debug PDF, which the target builds as prerequisites. It is **not** part of `make test` because it needs a browser and is slower; run it explicitly. `make lint` type-checks the harness with `tsc` against `e2e/tsconfig.json`.

## Definitions and reference previews

`definitionRegistry` in the live and static manifests is the shared source for
term, notation, and chapter/section previews. It is generated from the chapters
listed by the book manifest, not from PDFs or a hand-maintained copy of the prose.
Each entry records its canonical ID, kind, label, chapter, exact source file and
UTF-16 range, and line number. Source hashes identify the text those ranges use.
Japanese ranges refer to the generated Japanese source itself.

`\termdefine` and `\termdefineas` identify actual term definitions.
`\forward` opens a first-use gate and never creates a definition.
`\define` records a notation declaration separately from its introduction:
each declared name binds independently to its first mathematical occurrence
after the declaration. A grouped declaration does not make the following
paragraph the definition of every name. Existing `\notationtype` and `\vars`
metadata disambiguate typed notation; simple macro wrappers declared in the
same group share the underlying mathematical introduction. When that block
also defines a term, the notation records its canonical term definition.
Comments, code examples, and metadata are excluded from preview text.

Section labels and term/notation index destinations are aliases to canonical
records. Generated Hyperref destinations are read from the current book's aux
files when available. They do not replace canonical IDs. Both PDF panes use
the registry belonging to their own book. Edits refresh the live registry and
close stale popups; static exports embed the same registry at export time.

Run `make lint-definitions` to audit every discovered book. The command saves
its report and registries under `build/validation/definitions-*/`. Missing
notation targets, colliding identities, and unreadable sources fail the check
instead of selecting an unrelated paragraph. The check is included in `make lint`.
The registry is derived data: edit the canonical Markdown and its translation
catalogs through the usual workflow, rather than editing a generated registry.

KaTeX CSS must retain each `@font-face` rule and the base `.katex` rule.
When updating the pinned KaTeX release, extract `dist/katex.min.css` from its
npm archive and run `python tools/prepare_katex_css.py INPUT OUTPUT` to retain
only woff2 sources. The transformer preserves declaration and rule boundaries;
`tests/test_katex_css.py` and the browser font test guard against lost fonts.

## Offline reading

On HTTPS or localhost, the viewer registers a Service Worker scoped to the
current book. The Cache API retains successfully loaded viewer assets, source
files, metadata, and complete PDFs. After the first online load has finished,
previously opened content can be reloaded with the server stopped or the network
disconnected, including URLs with reading-position parameters. Online requests
always try the server first so live rebuilds remain visible. A network failure
falls back to the saved response; HTTP errors are not replaced with stale data.

This is a cache of visited content, not a download of the whole book. Unopened
chapters, uncached PDF ranges, and files evicted by the browser still require a
connection. Lean's live LSP, chat, and builds require the server; static exports
can reuse previously loaded LSP-cache files. Cache storage is managed by the
browser and can be cleared in the site's storage settings. Plain remote HTTP
and `file://` do not support Service Workers.

Run the isolated browser regression with
`node --test tools/formalization-viewer/e2e/offline.e2e.ts` after
`make viewer-build`. It stops its fixture server and checks offline navigation,
first-visit assets, online updates, PDF range handling, and book isolation.

## Browser bundles

`make viewer-build` bundles browser modules with shared chunks. The public
entry points listed in `VIEWER_ENTRY_NAMES` in the Makefile remain available
for browser tooling and E2E tests; importing `build/state.js` observes the same
state used by `build/app.js`. Internal modules are included in those bundles.
Keep chunks flat under `build/`: PDF.js and other vendor URLs use
`import.meta.url` relative to that directory. The development watcher uses the
same entry points and options as the one-shot build. Restart a viewer started
before changing the build options so its watcher uses the current settings.

The blocking bootstrap contains only pre-paint setup and module-loading progress.
The live response and static export inline the generated bootstrap and minified
stylesheet in the HTML, avoiding render-blocking asset requests. Source maps stay
on the standalone development assets.
Full UI localization and legacy preference migration run in the shared application
graph, avoiding a second copy of the translation catalog and session helpers.
The live server and static export emit `modulepreload` links for the transitive
static imports of `app.js`; dynamic feature imports remain lazy.

`make viewer-build` also minifies `styles.css` to `build/styles.css`. Both live
and exported HTML embed that generated asset; edit the root stylesheet as before.

## CSS layout

Keep presentation in `styles.css`: responsive toolbar layout, PDF overlay hit
extensions, picker placement, and definition/context-menu placement use CSS.
Anchor Positioning follows the invoking control and chooses a viewport-safe
fallback. Older browsers get a centred CSS fallback instead of a second
JavaScript positioning engine.

PDF.js still parses and paints PDF pages, and JavaScript supplies PDF-derived
coordinates, data, navigation, and interaction state. Do not reintroduce DOM
cloning, dimension measurements, resize/scroll positioning listeners, or
synthetic link clicks for these CSS layouts. The original PDF link cores sit
above the CSS touch extensions, preserving access to densely spaced links.

PDF links show hover and keyboard-focus previews: definitions, notation, sections, bibliography entries, and other internal destinations. Bibliographic metadata is generated from the book bibliography at build time and included in the manifest. DOI and bibliography URLs reuse those entries; other external links display their URL without fetching remote pages.

## Browser agent integration

The viewer advertises an AI Catalog 1.0 at `./ai-catalog.json` through the HTML
`ai-catalog` link relation. The live server and static export also provide
`/.well-known/ai-catalog.json` at their deployment root. Relative HTML discovery
continues to work when the static export is hosted under a subdirectory.

The catalog embeds a first-party JSON descriptor of the browser tools. Its
media type is `application/json`: this descriptor describes WebMCP tools, not
an HTTP MCP server or an A2A agent. The catalog itself is served with
`application/ai-catalog+json` on the live server; ordinary JSON hosting also
supports the specification's discovery fallback.

In secure contexts with `document.modelContext.registerTool`, the viewer
registers seven WebMCP tools after its sources and reading position are ready:

| Tool                        | Result or action                                                                 |
| --------------------------- | -------------------------------------------------------------------------------- |
| `get_viewer_state`          | Selected book, visible panes, source files and stable marker                     |
| `list_markers`              | Filtered marker inventory, declaration names and correspondence                  |
| `get_marker`                | Book excerpt, Lean declaration and metadata line ranges, TeX span and PDF anchor |
| `find_markers_for_location` | Reverse lookup from a Markdown, Lean or TeX source line                          |
| `read_source`               | Up to 200 numbered lines from an exposed source file                             |
| `search_book`               | Whole-book search with source paths and line numbers                             |
| `navigate_marker`           | Navigate the existing viewer to a stable marker                                  |

WebMCP is an experimental browser API. Chromium testing requires enabling the
WebMCP feature; unsupported browsers keep their ordinary viewer UI and can
still discover the catalog. Registration uses AbortSignal cleanup and restores
registrations after a back/forward-cache restore. The tools reuse current
sourcemap status; they do not assert a new mathematical proof correspondence.
Tool results are marked as untrusted source data, and navigation is distinguished
from read-only tools. Authentication credentials and chat history are excluded.
Source reads accept only the book's exposed file choices.

References: [WebMCP draft](https://webmachinelearning.github.io/webmcp/) and
[AI Catalog specification](https://ai-catalog.io/spec/).
