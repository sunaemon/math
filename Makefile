# === mise — the version manager; every tool below runs through it. ===
MISE ?= $(shell command -v mise 2>/dev/null)
.DEFAULT_GOAL := pdfs

ifeq ($(strip $(MISE)),)
require-mise:
	@echo "mise not found on PATH. Run ./setup.sh --run and restart your shell, or pass MISE=/path/to/mise." >&2
	@exit 1
else
require-mise:
	@:
endif

# === Tools provided by mise (versions pinned in mise.toml). ===
PYTHON = $(MISE) exec -- python
CABAL = $(MISE) exec -- cabal
PANDOC = $(MISE) exec -- pandoc
TSC = $(MISE) exec -- tsc
ESBUILD = $(MISE) exec -- esbuild
NODE = $(MISE) exec -- node
PRETTIER = $(MISE) exec -- prettier
RUFF = $(MISE) exec -- ruff
FOURMOLU = $(MISE) exec -- fourmolu
HLINT = $(MISE) exec -- hlint
OXLINT = $(MISE) exec -- oxlint
SHFMT = $(MISE) exec -- shfmt
SHELLCHECK = $(MISE) exec -- shellcheck
TAPLO = $(MISE) exec -- taplo
ACTIONLINT = $(MISE) exec -- actionlint
# lefthook is the parallel runner for the lint / lint-fix / format groups (the
# groups themselves live in lefthook.yml and just call the make subtargets
# below). It also manages the git hooks installed by setup.sh.
LEFTHOOK = $(MISE) exec -- lefthook


# Prettier formats the whole repo; the scope (which extensions, what to skip) is
# governed by .prettierignore — build output, vendored/installed code, generated
# files, the book chapter markdown (owned by the book-filter linter), and test
# fixtures are excluded there. `make lint` checks; `make lint-fix` rewrites.
PRETTIER_TARGETS = .


# TeX is the repo-local TeX Live snapshot under .texlive/, built by ./setup.sh
# from a frozen, dated tlnet snapshot (see TLMGR_REPOSITORY in setup.sh). It is
# fully pinned and project-controlled; we invoke its binaries by absolute path
# and never use a system TeX. require-tex reports a clear error when it is
# missing. (mise's `tinytex` backend is not used: the asdf-tinytex plugin
# produces empty installs, and `mise exec -- lualatex` would silently fall
# through to a system TeX.)
TEX_BIN := $(firstword $(wildcard .texlive/texlive/bin/*))
TEX_ENV = env PATH=$(abspath $(TEX_BIN)):$(PATH)
MAKEINDEX = $(TEX_ENV) $(abspath $(TEX_BIN))/makeindex
LUALATEX_BASE_FLAGS = -interaction=nonstopmode -halt-on-error

# texfot wraps LuaLaTeX and filters its console output down to warnings, errors,
# and the "Output written" summary, dropping the package-load / page-number /
# font-path noise (all of which the .log still records in full). --ignore drops
# the benign pdf-backend "unreferenced destination" warnings emitted for the many
# index and term-index anchors. texfot is required (installed from setup.sh's
# package list; `./setup.sh --doctor` checks for it). Set LATEX_VERBOSE=1 to
# bypass texfot and see the raw log.
TEXFOT = $(abspath $(TEX_BIN))/texfot
TEXFOT_FLAGS = --quiet --ignore='unreferenced destination'
ifeq ($(strip $(LATEX_VERBOSE)),)
LUALATEX_FILTER = $(TEXFOT) $(TEXFOT_FLAGS)
endif
LUALATEX = $(TEX_ENV) $(LUALATEX_FILTER) $(abspath $(TEX_BIN))/lualatex

# Build recipes silence their (often very long) commands and print a short
# "  step target" label instead; the tools' own output (texfot summaries,
# makeindex/pandoc messages) still shows. Pass V=1 to echo the full commands.
ifeq ($(strip $(V)),)
Q := @
endif

ifeq ($(strip $(TEX_BIN)),)
require-tex:
	@echo "TeX Live not found under .texlive/. Run ./setup.sh --run to install it." >&2
	@exit 1
else
require-tex:
	@:
endif

# === Build layout: shared toolchain state in build/; per-book outputs in <book>/build/. ===
BUILD_DIR = build

# ---------------------------------------------------------------------------
# Books. Every <dir>/src/<stem>.json manifest defines a chaptered book whose
# master source is <dir>/src/<stem>.md and whose artifacts build into
# <dir>/build/<stem>.pdf. tools/books_mk.py turns all manifests into the
# generated include $(BOOKS_MK) (BOOK_STEMS plus per-book <stem>_DIR,
# <stem>_MANIFEST, <stem>_SOURCE, <stem>_CHAPTERS, <stem>_INPUTS, and the
# <stem>_PANDOC_INPUTS / <stem>_BOOKLINK_DEPS pair that routes booklink chapters
# through their injected copies), and the book-rules / book-dir-rules templates
# below instantiate the build rules, so adding a book is just adding its
# manifest and master source. Books are peers; none is privileged.
# ---------------------------------------------------------------------------
BOOK_MANIFESTS = $(sort $(wildcard */src/*.json))
# Lean files are scanned for booklink markers (which name the chapter each
# file formalizes), so BOOKLINK_LEANS / BOOKLINK_SOURCES and the per-book lean
# sets in $(BOOKS_MK) need no hand-kept registry. Symlinked lean trees are not
# followed; each Lean file is scanned once, in its owning book.
BOOKLINK_LEAN_FILES = $(sort $(shell find */lean -name '*.lean' 2>/dev/null))
BOOKS_MK = build/books.mk
# Bootstrap goals run before mise exists; including (and therefore remaking) the
# generated books.mk would trip require-mise and print a spurious "mise not
# found" error before setup even starts. Skip the generated include when the
# only goals requested are bootstrap targets.
BOOTSTRAP_GOALS = setup setup-run doctor
ifneq ($(strip $(MAKECMDGOALS)),)
ifeq ($(strip $(filter-out $(BOOTSTRAP_GOALS),$(MAKECMDGOALS))),)
SKIP_GENERATED_INCLUDES := 1
endif
endif
ifndef SKIP_GENERATED_INCLUDES
-include $(BOOKS_MK)
ifneq ($(BOOKS_MK_MANIFESTS),$(BOOK_MANIFESTS))
$(BOOKS_MK): FORCE
endif
ifneq ($(BOOKS_MK_LEAN_FILES),$(BOOKLINK_LEAN_FILES))
$(BOOKS_MK): FORCE
endif
endif
BOOK_DIRS = $(sort $(foreach stem,$(BOOK_STEMS),$($(stem)_DIR)))
BOOK_PDFS = $(foreach stem,$(BOOK_STEMS),$($(stem)_DIR)/build/$(stem).pdf)
BOOK_TEXS = $(foreach stem,$(BOOK_STEMS),$($(stem)_DIR)/build/$(stem).tex)
BOOK_DEBUG_PDFS = $(foreach stem,$(BOOK_STEMS),$($(stem)_DIR)/build/$(stem)-debug.pdf)

# Chapters with Lean formalizations build through injected copies under
# $(BUILD_DIR)/booklink-src/<real-path>/, keyed by each chapter's real
# repo-relative path so books sharing a chapter share one injected copy and
# separate books never collide. tools/books_mk.py resolves that per book and
# emits <stem>_PANDOC_INPUTS (the pandoc input list with booklink chapters
# swapped for their injected copies) and <stem>_BOOKLINK_DEPS (those copies as
# prerequisites), so the Makefile needs no canonical-owner remapping. The
# injection sourcemap is derived from the booklink markers in $(BOOKLINK_LEANS).
BOOKLINK_FILTER_SOURCEMAP = $(BUILD_DIR)/booklink-filter-sourcemap.json

FILTER_SRC = tools/book-filter/Main.hs tools/book-filter/DependencyGraph.hs tools/book-filter/SectionRef.hs

# Source trees the language formatters own. Ruff formats the repository Python
# (tools/, tests/, skill scripts); Fourmolu formats the book-filter Haskell plus
# the golden-test driver. `make lint` checks; `make lint-fix` rewrites.
RUFF_TARGETS = tools tests .codex
FOURMOLU_TARGETS = $(FILTER_SRC) tests/run-book-filter-golden.hs

# HLint lints the same Haskell sources (rules / extension overrides in .hlint.yaml).
HLINT_TARGETS = tools/book-filter tests/run-book-filter-golden.hs

# Oxlint lints the viewer's authored TypeScript (browser + server). It is a
# single mise-managed binary (no node_modules); rules come from .oxlintrc.json.
# `--deny-warnings` makes any finding fail, so `make lint` is a real gate.
OXLINT_TARGETS = tools/formalization-viewer/src tools/formalization-viewer/server tools/formalization-viewer/e2e tools/formalization-viewer/check_highlights.mjs

# Shell scripts: shfmt formats (2-space indent), shellcheck lints. `make lint`
# checks both (shfmt -d fails on any diff); `make lint-fix` rewrites with shfmt.
SHELL_SOURCES = $(shell git ls-files '*.sh')
SHFMT_FLAGS = -i 2

# taplo formats/lints the hand-edited TOML; actionlint lints the GitHub Actions
# workflows (auto-discovered under .github/workflows).
TAPLO_TARGETS = $(wildcard *.toml .codex/*.toml */lakefile.toml)

FILTER_BIN = $(BUILD_DIR)/book-filter

# The formalization viewer's browser modules are authored in TypeScript under
# src/ and transpiled to the .js files index.html loads under build/. esbuild
# only strips types (no bundling), so each module keeps its own relative
# imports and its import.meta.url-relative ../vendor/pdfjs loading; src/ and
# build/ sit at the same depth so those ../vendor paths resolve identically for
# tsc (reading src/) and the browser (loading build/). make lint runs the
# type-checking. The emitted build/ .js are gitignored build artifacts.
VIEWER_DIR = tools/formalization-viewer
# Node server, dist builder, LSP cache, and port helper for the viewer, run
# directly as TypeScript by node's type-stripping (no build step).
VIEWER_SERVER_DIR = $(VIEWER_DIR)/server
# tsc resolves @types/node (a pinned mise npm dev tool) through this gitignored
# node_modules symlink; node itself needs no resolution to run the .ts files.
VIEWER_SERVER_TYPES = $(VIEWER_SERVER_DIR)/node_modules
VIEWER_SRC_DIR = $(VIEWER_DIR)/src
VIEWER_BUILD_DIR = $(VIEWER_DIR)/build
# Browser modules to transpile; *.test.ts (node --test, see test-node) are not
# part of the bundle and are excluded.
VIEWER_TS = $(filter-out %.test.ts,$(wildcard $(VIEWER_SRC_DIR)/*.ts))
VIEWER_JS = $(patsubst $(VIEWER_SRC_DIR)/%.ts,$(VIEWER_BUILD_DIR)/%.js,$(VIEWER_TS))
VIEWER_SRC_TESTS = $(wildcard $(VIEWER_SRC_DIR)/*.test.ts)
VIEWER_E2E_DIR = $(VIEWER_DIR)/e2e
ESBUILD_FLAGS = --format=esm --target=esnext --sourcemap=inline
LATEX_LOCK = $(PYTHON) tools/latex_lock.py --
export TEXMFVAR ?= $(abspath $(BUILD_DIR)/texmf-var)
BOOK_LINE_LENGTH ?= 120
LINT_MAX_REPORTS ?= 40
# Per-book preview master .aux files, pre-warmed by `make preview-warm` so the
# first chapter preview after a fresh build is fast.
PREVIEW_MASTER_AUXES = $(foreach stem,$(BOOK_STEMS),$($(stem)_DIR)/build/$(stem)-preview-master.aux)
HYPERLINK_BORDER_FLAGS = \
	-V boxlinks=true \
	-V 'hyperrefoptions=pdfborder={0 0 1}' \
	-V 'hyperrefoptions=linkbordercolor={1 0 0}' \
	-V 'hyperrefoptions=citebordercolor={1 0 0}' \
	-V 'hyperrefoptions=urlbordercolor={1 0 0}' \
	-V 'hyperrefoptions=filebordercolor={1 0 0}' \
	-V 'hyperrefoptions=runbordercolor={1 0 0}' \
	-V 'hyperrefoptions=menubordercolor={1 0 0}'

pdfs: $(sort $(BOOK_PDFS))

# List the discovered book projects as `<stem> <book-dir> <master-source>`.
list-books: $(BOOKS_MK)
	@$(foreach stem,$(BOOK_STEMS),printf '%-20s %-18s %s\n' '$(stem)' '$($(stem)_DIR)' '$($(stem)_SOURCE)';)

debug-pdfs: $(sort $(BOOK_DEBUG_PDFS))

# Pre-warm every book's preview cross-reference aux (chapter previews are built
# on demand by the viewer / `make <stem>-preview-<chapter>.pdf`).
preview-warm: $(PREVIEW_MASTER_AUXES)

# Preferred viewer port. The formalization-viewer target resolves this through
# $(VIEWER_SERVER_DIR)/free-port.ts: it serves on this port when free and otherwise falls back
# to an OS-assigned free port, so a second instance (or a stale listener) never
# fails to bind. Set BOOKLINK_VIEWER_PORT=0 to always pick a free port.
BOOKLINK_VIEWER_PORT ?= 8765
BOOKLINK_DIST_DIR = dist
# Viewer projects (top-level directories with a manifest.json). The live
# server serves all of them at their mounts; BOOKLINK_PROJECT picks the one
# "/" redirects to and the one a STATIC=1 dist is built for. Each project
# lists its viewer artifacts here; the sourcemaps are built by the
# per-project rules below.
BOOKLINK_PROJECT ?=
ifeq ($(strip $(BOOKLINK_PROJECT)),)
BOOKLINK_PROJECT := $(firstword $(BOOK_DIRS))
endif
BOOKLINK_ALL_VIEWER_DEPS = $(foreach dir,$(BOOK_DIRS),$($(dir)_VIEWER_DEPS))
ifneq ($(strip $(BOOK_STEMS)),)
ifeq ($(strip $($(BOOKLINK_PROJECT)_VIEWER_DEPS)),)
$(error unknown BOOKLINK_PROJECT '$(BOOKLINK_PROJECT)'; expected a book directory with viewer artifacts)
endif
endif

# STATIC=1 builds a self-contained distribution under $(BOOKLINK_DIST_DIR)
# (viewer assets, allowlisted project files, and a pregenerated Lean LSP
# response cache) instead of serving the live bridge.
# Transpile the viewer's TypeScript modules to the .js files it serves.
$(VIEWER_BUILD_DIR)/%.js: $(VIEWER_SRC_DIR)/%.ts | require-mise
	@mkdir -p $(dir $@)
	$(ESBUILD) $< $(ESBUILD_FLAGS) --outfile=$@

viewer-build: $(VIEWER_JS)

# Build the static viewer distribution under $(BOOKLINK_DIST_DIR) without
# serving it — the build half of the STATIC=1 formalization-viewer target, for
# CI/CD. BOOKLINK_PROJECT selects the book; the Lean infoview cache it generates
# runs `lake build` over that book's package, so building the full polish-space
# dist also verifies all of its Lean. BOOKLINK_DIST_FLAGS can pass e.g.
# --skip-lsp-cache to skip the Lean cache (and its lake build).
dist: viewer-build $($(BOOKLINK_PROJECT)_VIEWER_DEPS) require-mise
	BOOKLINK_PROJECT=$(BOOKLINK_PROJECT) $(NODE) $(VIEWER_SERVER_DIR)/static-dist.ts --root . --dist $(BOOKLINK_DIST_DIR) $(BOOKLINK_DIST_FLAGS)

ifeq ($(STATIC),1)
formalization-viewer: viewer-build $($(BOOKLINK_PROJECT)_VIEWER_DEPS) require-mise
	BOOKLINK_PROJECT=$(BOOKLINK_PROJECT) BOOKLINK_VIEWER_PORT=$(BOOKLINK_VIEWER_PORT) $(NODE) $(VIEWER_SERVER_DIR)/static-dist.ts --root . --dist $(BOOKLINK_DIST_DIR)
	( port=$$($(NODE) $(VIEWER_SERVER_DIR)/free-port.ts $(BOOKLINK_VIEWER_PORT)); \
	echo "Formalization viewer: http://127.0.0.1:$$port/"; \
	if [ "$${BOOKLINK_OPEN_BROWSER:-1}" != "0" ]; then ( \
	  for i in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15; do \
	    $(PYTHON) -c "import socket,sys; s=socket.socket(); s.settimeout(0.3); sys.exit(0 if s.connect_ex(('127.0.0.1',$$port))==0 else 1)" && break; \
	    sleep 0.3; \
	  done; \
	  $(PYTHON) -m webbrowser "http://127.0.0.1:$$port/" >/dev/null 2>&1 || true \
	) & fi; \
	$(PYTHON) -m http.server $$port --bind 127.0.0.1 -d $(BOOKLINK_DIST_DIR) )
else
# Dev server with live reload on both sides:
#  - esbuild --watch rebuilds the viewer .js on every .ts edit; the file watcher
#    sees the change and reloads the page (assets are served no-store).
#  - watchexec --restart reruns the Python server whenever a tools/*.py file
#    changes (uvicorn-style). SIGTERM is clean: the server's finally reaps the
#    Lean bridges + inner watcher, and HTTPServer re-binds the port.
# The browser is opened once (after the port is up) with the server's own
# browser-open suppressed, so restarts don't spawn new tabs.
formalization-viewer: viewer-build $(BOOKLINK_ALL_VIEWER_DEPS) require-mise
	( port=$$($(NODE) $(VIEWER_SERVER_DIR)/free-port.ts $(BOOKLINK_VIEWER_PORT)); \
	echo "Formalization viewer: http://127.0.0.1:$$port/"; \
	$(ESBUILD) $(VIEWER_TS) $(ESBUILD_FLAGS) --outdir=$(VIEWER_BUILD_DIR) --watch & \
	esbuild_pid=$$!; trap 'kill $$esbuild_pid 2>/dev/null' EXIT INT TERM; \
	if [ "$${BOOKLINK_OPEN_BROWSER:-1}" != "0" ]; then ( \
	  for i in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15; do \
	    $(PYTHON) -c "import socket,sys; s=socket.socket(); s.settimeout(0.3); sys.exit(0 if s.connect_ex(('127.0.0.1',$$port))==0 else 1)" && break; \
	    sleep 0.3; \
	  done; \
	  $(PYTHON) -m webbrowser "http://127.0.0.1:$$port/" >/dev/null 2>&1 || true \
	) & fi; \
	BOOKLINK_OPEN_BROWSER=0 BOOKLINK_PROJECT=$(BOOKLINK_PROJECT) BOOKLINK_VIEWER_PORT=$$port \
	$(MISE) exec -- watchexec --restart --watch $(VIEWER_SERVER_DIR) --exts ts --debounce 200ms -- node $(VIEWER_SERVER_DIR)/serve.ts )
endif

# Refresh the committed tree-sitter assets for the formalization viewer. The viewer
# does not depend on this; the vendored assets under
# tools/formalization-viewer/vendor/treesitter/ are checked in.
treesitter-assets: require-mise
	$(CURDIR)/tools/fetch_treesitter_assets.sh

# Publish a public subset of the repo to DEST, containing only the named BOOKS
# (space-separated, e.g. BOOKS="polish-space-ch1") plus shared build/tooling
# files; see tools/publish_math.sh. Run `make list-books` for book names.
#   make publish DEST=../math BOOKS="polish-space-ch1"
publish:
	@test -n "$(DEST)"  || { echo 'usage: make publish DEST=<dir> BOOKS="<book> [book...]"' >&2; exit 2; }
	@test -n "$(BOOKS)" || { echo 'usage: make publish DEST=<dir> BOOKS="<book> [book...]"' >&2; exit 2; }
	$(CURDIR)/tools/publish_math.sh $(DEST) $(BOOKS)

$(BOOKS_MK): tools/books_mk.py tools/book_manifest.py tools/booklink_sourcemap.py $(BOOK_MANIFESTS) $(BOOKLINK_LEAN_FILES) | require-mise
	@mkdir -p $(dir $@)
	@echo "  books-mk $@"
	$(Q)$(PYTHON) tools/books_mk.py $(BOOK_MANIFESTS) --leans $(BOOKLINK_LEAN_FILES) > $@.tmp
	$(Q)mv $@.tmp $@

$(BUILD_DIR):
	mkdir -p $@

$(FILTER_BIN): $(FILTER_SRC) math-project.cabal | $(BUILD_DIR) require-mise
	@$(CABAL) build book-filter --builddir=$(BUILD_DIR) -v0
	@filter_bin=$$($(CABAL) list-bin --builddir=$(BUILD_DIR) book-filter) || exit 1; \
	if ! cmp -s "$$filter_bin" $(FILTER_BIN); then \
		cp "$$filter_bin" $(FILTER_BIN).tmp && mv -f $(FILTER_BIN).tmp $(FILTER_BIN); \
	fi

$(BOOKLINK_FILTER_SOURCEMAP): tools/booklink_sourcemap.py $(BOOKLINK_LEANS) $(BOOKLINK_SOURCES) | $(BUILD_DIR) require-mise
	@echo "  booklink-sourcemap $@"
	$(Q)$(PYTHON) tools/booklink_sourcemap.py $(BOOKLINK_LEANS) --out $@

# Inject booklinks into a chapter, keyed by its real repo-relative path: the
# target is $(BUILD_DIR)/booklink-src/<real>.md, the prerequisite is the real
# source <real>.md, and --source matches the sourcemap entry by that path.
$(BUILD_DIR)/booklink-src/%.md: %.md $(FILTER_BIN) $(BOOKLINK_FILTER_SOURCEMAP) | $(BUILD_DIR) require-mise
	@mkdir -p $(dir $@)
	@echo "  booklink-inject $@"
	$(Q)$(FILTER_BIN) inject-booklinks --sourcemap $(abspath $(BOOKLINK_FILTER_SOURCEMAP)) --source $(abspath $<) --out $@

tex: $(sort $(BOOK_TEXS))

# $(call book-dir-rules,<dir>): rules shared by every directory hosting at
# least one book: the build directory itself and the PDF compile rules, which
# hardcode -output-directory per directory.
define book-dir-rules
$(1)/build:
	mkdir -p $$@

# Debug PDFs (stem ending in -debug) are a fast preview artifact, so they reuse
# the previous build: when a prior debug run left its .aux behind, a single
# incremental LuaLaTeX pass resolves cross-references and the index from that aux
# (seconds, versus three full passes + makeindex). A cold debug build (no .aux
# yet), any non-debug book, or DEBUG_FULL=1 takes the full multi-pass build so
# the render is correct from scratch. The incremental case is folded into this
# one `%.pdf` rule rather than a separate `%-debug.pdf` pattern because GNU Make
# 3.81 (the macOS system make) breaks pattern-rule ties by definition order, not
# shortest stem, so a separate rule would be shadowed by this one. After large
# structural edits to a chapter, rebuild the debug PDF once more (or pass
# DEBUG_FULL=1) to settle references the single pass left stale.
$(1)/build/%.pdf: $(1)/build/%.tex | $(1)/build require-mise require-tex
	$$(Q)if [ -z "$$(DEBUG_FULL)" ] && [ -f $(1)/build/$$*.aux ] && case "$$*" in *-debug) true ;; *) false ;; esac; then \
		echo "  lualatex $$* (1 pass, incremental — reusing prior aux)"; \
		$$(LATEX_LOCK) $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$(abspath $(1)/build) $$<; \
	else \
		rm -f $(1)/build/$$*.synctex.gz $(1)/build/$$*.aux $(1)/build/$$*.out $(1)/build/$$*.toc $(1)/build/$$*.ind $(1)/build/$$*.ilg; \
		echo "  lualatex $$* (pass 1/3)"; \
		$$(LATEX_LOCK) $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$(abspath $(1)/build) $$< && \
		{ test ! -f $(1)/build/$$*.idx || { echo "  makeindex $$*"; $$(LATEX_LOCK) $$(MAKEINDEX) $(1)/build/$$*.idx; }; } && \
		{ echo "  lualatex $$* (pass 2/3)"; $$(LATEX_LOCK) $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$(abspath $(1)/build) $$<; } && \
		{ echo "  lualatex $$* (pass 3/3)"; $$(LATEX_LOCK) $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$(abspath $(1)/build) $$<; }; \
	fi
endef

# $(call book-rules,<stem>): build rules for one chaptered book. `make
# <stem>` builds its PDF.
define book-rules
.PHONY: $(1)
$(1): $($(1)_DIR)/build/$(1).pdf

$($(1)_DIR)/build/$(1).tex: tools/book_manifest.py $($(1)_MANIFEST) $($(1)_INPUTS) $(FILTER_BIN) $($(1)_BOOKLINK_DEPS) $($(1)_DIR)/tex/macros.tex $($(1)_DIR)/tex/references.bib | $($(1)_DIR)/build require-mise
	@echo "  pandoc $$@"
	$$(Q)$$(PANDOC) $($(1)_PANDOC_INPUTS) \
		-f markdown \
		--filter $$(FILTER_BIN) \
		--citeproc \
		-o $$@ \
		--standalone

$($(1)_DIR)/build/$(1)-debug.tex: tools/book_manifest.py tools/enable_booklink_highlight.py $($(1)_MANIFEST) $($(1)_INPUTS) $(FILTER_BIN) $($(1)_BOOKLINK_DEPS) $($(1)_DIR)/tex/macros.tex $($(1)_DIR)/tex/references.bib | $($(1)_DIR)/build require-mise
	@echo "  pandoc $$@"
	$$(Q)$$(PANDOC) $($(1)_PANDOC_INPUTS) \
		-f markdown \
		--filter $$(FILTER_BIN) \
		--citeproc \
		$$(HYPERLINK_BORDER_FLAGS) \
		-o $$@ \
		--standalone
	@echo "  booklink-highlight $$@"
	$$(Q)$$(PYTHON) tools/enable_booklink_highlight.py $$@

# --- Chapter preview ------------------------------------------------------
# A fast \includeonly render of the single chapter being edited, split (without
# changing content) from the debug tex. The whole-book debug PDF and source map
# are untouched; this is a separate iterative-editing artifact whose chapters
# keep the global booklink/skip anchor numbers, so the existing source map and
# the viewer overlays resolve against it unchanged.
$($(1)_DIR)/build/$(1)-preview-master.tex: tools/split_preview_tex.py $($(1)_DIR)/build/$(1)-debug.tex $($(1)_MANIFEST) $($(1)_CHAPTERS) | $($(1)_DIR)/build require-mise
	@echo "  split-preview $(1)"
	$$(Q)$$(PYTHON) tools/split_preview_tex.py --debug-tex $($(1)_DIR)/build/$(1)-debug.tex --manifest $($(1)_MANIFEST) --book-dir $($(1)_DIR) --stem $(1) --out-dir $($(1)_DIR)/build

# Warm every unit's .aux (full master, two passes to settle forward refs) so a
# single-chapter \includeonly resolves cross-chapter references. It is an
# order-only prerequisite of the chapter PDFs below: built once when missing,
# then reused — a Markdown edit must NOT trigger this whole-book pass (that would
# be slower than the debug PDF). Cross-chapter numbers may lag until it is
# rebuilt (delete it, or rebuild the debug PDF); within-chapter refs stay live.
# PREVIEW_TEX_ENV adds the unit dir to TEXINPUTS (so bare \include names resolve)
# via env, since LATEX_LOCK execs argv directly and cannot take a VAR=val prefix.
$(1)_PREVIEW_INPUTS = env TEXINPUTS="$$(abspath $($(1)_DIR)/build/$(1)-preview):"
$($(1)_DIR)/build/$(1)-preview-master.aux: | $($(1)_DIR)/build/$(1)-preview-master.tex require-tex
	@echo "  lualatex $(1)-preview-master (warm cross-ref aux)"
	$$(Q)$$(LATEX_LOCK) $$($(1)_PREVIEW_INPUTS) $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$$(abspath $($(1)_DIR)/build) -jobname=$(1)-preview-master $($(1)_DIR)/build/$(1)-preview-master.tex
	$$(Q)$$(LATEX_LOCK) $$($(1)_PREVIEW_INPUTS) $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$$(abspath $($(1)_DIR)/build) -jobname=$(1)-preview-master $($(1)_DIR)/build/$(1)-preview-master.tex

# One chapter, typeset alone via \includeonly, reusing the warm aux. The master
# is current (re-split when the debug tex changes), so the edited chapter renders
# fresh; the warm aux only supplies cross-chapter numbers.
#
# Seed this jobname's main .aux from the warm master .aux before the single pass.
# \includeonly restores an excluded chapter's counters from \cp@<unit> macros that
# LaTeX defines while reading the main .aux at \begin{document} — before it
# reopens that file for writing. With a fresh per-chapter jobname there is no
# prior main .aux on the only pass, so no checkpoints load: the chapter counter
# stays 0 and the lone included chapter renders as "Chapter 1" (and cross-chapter
# \refs come out ??). Copying the master .aux supplies those \@input{unit.aux}
# checkpoint directives (and cross-chapter labels), giving a correctly numbered
# one-pass render; lualatex then overwrites the file with this chapter's anchors.
$($(1)_DIR)/build/$(1)-preview-%.pdf: $($(1)_DIR)/build/$(1)-preview-master.tex | $($(1)_DIR)/build/$(1)-preview-master.aux require-tex
	@echo "  lualatex $(1)-preview-$$* (chapter)"
	$$(Q)cp $($(1)_DIR)/build/$(1)-preview-master.aux $($(1)_DIR)/build/$(1)-preview-$$*.aux
	$$(Q)$$(LATEX_LOCK) $$($(1)_PREVIEW_INPUTS) $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$$(abspath $($(1)_DIR)/build) -jobname=$(1)-preview-$$* "\def\PreviewOnly{$$*}\input{$($(1)_DIR)/build/$(1)-preview-master.tex}"
endef

# $(call book-sourcemap-rules,<stem>): the viewer sourcemap of a book whose
# chapters carry booklink markers, anchored against its debug tex. Booklink
# sources are book-local (the Lean file's own book src), so the emitted paths
# are already book-local and need no rewrite.
define book-sourcemap-rules
$($(1)_DIR)/build/$(1)-sourcemap.json: tools/booklink_sourcemap.py $($(1)_BOOKLINK_LEANS) $($(1)_DIR)/build/$(1)-debug.tex | $($(1)_DIR)/build require-mise
	@echo "  viewer-sourcemap $$@"
	$$(Q)$$(PYTHON) tools/booklink_sourcemap.py $($(1)_BOOKLINK_LEANS) --tex-file $($(1)_DIR)/build/$(1)-debug.tex --out $$@
endef

$(foreach dir,$(BOOK_DIRS),$(eval $(call book-dir-rules,$(dir))))
$(foreach stem,$(BOOK_STEMS),$(eval $(call book-rules,$(stem))))
$(foreach stem,$(BOOK_STEMS),$(if $($(stem)_BOOKLINK_LEANS),$(eval $(call book-sourcemap-rules,$(stem)))))

clean:
	rm -rf $(sort $(BUILD_DIR) $(foreach dir,$(BOOK_DIRS),$(dir)/build)) $(BOOKLINK_DIST_DIR) $(VIEWER_BUILD_DIR)

setup:
	./setup.sh --dry-run

setup-run:
	./setup.sh --run

doctor:
	./setup.sh --doctor

test: test-haskell test-python test-node test-highlights

test-haskell: $(FILTER_BIN) require-mise
	$(CABAL) test book-filter-golden --builddir=$(BUILD_DIR)

test-python: require-mise
	BOOKLINK_ROOT=$(CURDIR) $(PYTHON) -m unittest discover -s tests -p 'test_*.py'

# Node unit tests for the viewer: server (request-trust, bridge race contract)
# and browser src modules with no DOM deps (skip-band geometry).
test-node: require-mise
	$(NODE) --test $(VIEWER_SERVER_DIR)/*.test.ts $(VIEWER_SRC_TESTS)

# Browser-driven end-to-end tests for the viewer. Launches the live serve.ts
# server and a headless Chrome (driven over CDP with Node's global WebSocket, so
# no npm / browser-driver dependency) and exercises the real SPA: source
# rendering into the DOM, the live /events + /lsp connections, the custom
# dropdown widget, and cross-pane marker activation. Needs a Chrome/Chromium
# binary (set CHROME=/path/to/chrome if not at a standard location) and the
# polish-space sourcemap + debug PDF (the live server serves the debug PDF, never
# the release one). NOT part of `make test`: it needs a browser and is slower, so
# it is an explicit, opt-in target.
test-e2e: viewer-build polish-space/build/polish-space-book-sourcemap.json polish-space/build/polish-space-book-debug.pdf require-mise
	$(NODE) --test $(VIEWER_E2E_DIR)/*.e2e.ts

# Regenerate the vendored third-party notices from vendor/manifest.json. The
# matching consistency check runs as a Python test (tests/test_vendor_notices.py),
# so a stale THIRD-PARTY-NOTICES.md fails `make test`.
notices: require-mise
	$(PYTHON) tools/vendor_notices.py generate

# Smoke check for the vendored tree-sitter runtime, grammars, and highlight
# queries the browser highlighter loads. Asserts each fixture still produces
# captures, so a vendored-asset bump that breaks highlighting fails the build.
test-highlights: require-mise
	$(NODE) $(VIEWER_DIR)/check_highlights.mjs

# Refresh the @types/node symlink tsc resolves the server's `node:` imports
# through. mise's npm backend installs to a version-pinned path; `mise where`
# resolves it without hardcoding the version. node runs the .ts files without it.
$(VIEWER_SERVER_TYPES): mise.toml | require-mise
	@ln -sfn "$$($(MISE) where npm:@types/node)/lib/node_modules" $@

# lint / lint-fix / format delegate to lefthook, which runs the per-tool
# subtargets below as a `parallel: true` group (defined in lefthook.yml) and
# renders a colored per-command pass/fail summary. lefthook aggregates failures
# instead of stopping at the first, so one run surfaces every problem. The make
# layer stays the single source of truth for tool paths and target lists, and
# still builds the prerequisites (book-filter binary, @types/node symlink)
# *before* the parallel group so the concurrent commands never race on them.
# --no-auto-install keeps these runs from re-syncing git hooks as a side effect.
#
# Each subtarget runs its tool with quiet flags (prettier --log-level warn,
# ruff -q, fourmolu -q, taplo via RUST_LOG=warn) so a clean run stays terse and
# only real findings surface under lefthook's summary.
lint: $(FILTER_BIN) $(VIEWER_SERVER_TYPES) require-mise
	@$(LEFTHOOK) run lint --no-auto-install

lint-fix: $(FILTER_BIN) require-mise
	@$(LEFTHOOK) run lint-fix --no-auto-install

# Pure formatters in write mode only: no linters, no book-filter, no
# auto-fixable lint rules. This is the conventional `format` vs `lint-fix`
# split -- run `make format` to reflow code, `make lint-fix` to also apply
# fixable lint rules (ruff check --fix, oxlint --fix, book-filter --fix).
format: require-mise
	@$(LEFTHOOK) run format --no-auto-install

# --- Per-tool lint subtargets (check mode); the lefthook `lint` group runs
# these in parallel. book-filter / tsc carry their own build prerequisites so a
# direct `make lint-tsc` still works when invoked outside the group.
lint-book: $(FILTER_BIN) require-mise
	@$(foreach stem,$(BOOK_STEMS),$(FILTER_BIN) lint --macros=$($(stem)_DIR)/tex/macros.tex --max-line-length=$(BOOK_LINE_LENGTH) --max-reports=$(LINT_MAX_REPORTS) $($(stem)_INPUTS) &&) :

lint-tsc: $(VIEWER_SERVER_TYPES) require-mise
	@$(TSC) -p tools/formalization-viewer/tsconfig.json && $(TSC) -p tools/formalization-viewer/tsconfig.test.json && $(TSC) -p $(VIEWER_SERVER_DIR)/tsconfig.json && $(TSC) -p $(VIEWER_E2E_DIR)/tsconfig.json

lint-prettier: require-mise
	@$(PRETTIER) --check --log-level warn $(PRETTIER_TARGETS)

lint-ruff: require-mise
	@$(RUFF) format --check -q $(RUFF_TARGETS) && $(RUFF) check -q $(RUFF_TARGETS)

lint-fourmolu: require-mise
	@$(FOURMOLU) -q --mode check $(FOURMOLU_TARGETS)

lint-hlint: require-mise
	@$(HLINT) $(HLINT_TARGETS)

lint-oxlint: require-mise
	@$(OXLINT) --deny-warnings $(OXLINT_TARGETS)

lint-shell: require-mise
	@$(SHFMT) -d $(SHFMT_FLAGS) $(SHELL_SOURCES) && $(SHELLCHECK) $(SHELL_SOURCES)

lint-taplo: require-mise
	@RUST_LOG=warn $(TAPLO) fmt --check $(TAPLO_TARGETS)

lint-actionlint: require-mise
	@$(ACTIONLINT)

# --- Per-tool fix subtargets (write mode); the lefthook `lint-fix` group runs
# these in parallel. Each tool owns disjoint file types (prettier excludes the
# book-chapter markdown that book-filter owns), so concurrent writes don't race.
fix-book: $(FILTER_BIN) require-mise
	@$(foreach stem,$(BOOK_STEMS),$(FILTER_BIN) lint --fix --macros=$($(stem)_DIR)/tex/macros.tex --max-line-length=$(BOOK_LINE_LENGTH) --max-reports=$(LINT_MAX_REPORTS) $($(stem)_INPUTS) &&) :

fix-prettier: require-mise
	@$(PRETTIER) --write --log-level warn $(PRETTIER_TARGETS)

fix-ruff: require-mise
	@$(RUFF) format -q $(RUFF_TARGETS) && $(RUFF) check -q --fix $(RUFF_TARGETS)

fix-fourmolu: require-mise
	@$(FOURMOLU) -q --mode inplace $(FOURMOLU_TARGETS)

fix-oxlint: require-mise
	@$(OXLINT) --fix $(OXLINT_TARGETS)

fix-shell: require-mise
	@$(SHFMT) -w $(SHFMT_FLAGS) $(SHELL_SOURCES) && $(SHELLCHECK) $(SHELL_SOURCES)

fix-taplo: require-mise
	@RUST_LOG=warn $(TAPLO) fmt $(TAPLO_TARGETS)

# --- Formatter-only subtargets for the `format` group. The prettier / fourmolu
# / taplo steps are identical to their fix-* counterparts (those tools have no
# separate lint pass), so the group reuses them; ruff and shfmt drop the linter
# half (ruff check --fix, shellcheck) that `format` deliberately excludes.
format-ruff: require-mise
	@$(RUFF) format -q $(RUFF_TARGETS)

format-shfmt: require-mise
	@$(SHFMT) -w $(SHFMT_FLAGS) $(SHELL_SOURCES)


# Certify that the Lean development compiles against the pinned mathlib
# (polish-space/lakefile.toml + lake-manifest.json). `lake build` with no target
# builds the PolishSpaceBook root, which imports every chapter module, so all
# modules are covered automatically. Independent of the PDF book build; the
# first run fetches the mathlib olean cache (large), later runs are incremental.
# lake comes from the elan toolchain on mise's PATH. Every book that ships a
# standalone lakefile.toml is discovered and built (no hardcoded project list),
# so the published excerpt is verified on its own alongside the full book.
LAKE_PROJECTS = $(patsubst %/lakefile.toml,%,$(wildcard */lakefile.toml))

lean: require-mise
	@for proj in $(LAKE_PROJECTS); do \
	  echo "==> lean: $$proj"; \
	  ( cd $$proj && $(MISE) exec -- lake exe cache get && $(MISE) exec -- lake build ) || exit 1; \
	done

# Report book-source regions (statement environments and prose paragraphs) not
# yet covered by a Lean booklink, scanning every Lean file that carries booklink
# markers. Pass extra flags via BOOKLINK_COVERAGE_ARGS, for example
# `make booklink-coverage BOOKLINK_COVERAGE_ARGS='--statements-only'`.
booklink-coverage: tools/booklink_coverage.py tools/booklink_sourcemap.py $(BOOKLINK_LEANS) $(BOOKLINK_SOURCES) | require-mise
	$(PYTHON) tools/booklink_coverage.py $(BOOKLINK_LEANS) $(BOOKLINK_COVERAGE_ARGS)

FORCE:

.PHONY: clean tex test test-haskell test-python test-node test-highlights test-e2e notices lint lint-fix format \
	lint-book lint-tsc lint-prettier lint-ruff lint-fourmolu lint-hlint lint-oxlint lint-shell lint-taplo lint-actionlint \
	fix-book fix-prettier fix-ruff fix-fourmolu fix-oxlint fix-shell fix-taplo format-ruff format-shfmt \
	lean booklink-coverage viewer-build dist setup setup-run doctor require-mise require-tex pdfs list-books debug-pdfs preview-warm formalization-viewer treesitter-assets publish FORCE
