# Optional, generated Codex container configuration (never committed).
-include build/codex.mk

# === mise — the version manager; every tool below runs through it. ===
# A mise shim can point to a separately managed, older mise that does not know
# the installed tool backends. Prefer a direct executable; keep the shim only
# as a fallback when no direct installation is available.
MISE_ON_PATH := $(shell command -v mise 2>/dev/null)
MISE ?= $(firstword \
	$(filter-out %/shims/mise,$(MISE_ON_PATH)) \
	$(wildcard /opt/homebrew/bin/mise) \
	$(wildcard /usr/local/bin/mise) \
	$(wildcard /home/linuxbrew/.linuxbrew/bin/mise) \
	$(wildcard $(HOME)/.local/bin/mise) \
	$(wildcard $(HOME)/.cargo/bin/mise) \
	$(MISE_ON_PATH))
.DEFAULT_GOAL := pdfs
# A failed Pandoc/LaTeX invocation may have already written its target. Leaving
# that partial PDF or warm .aux in place makes the next make skip the failed
# step as up to date. Remove changed targets on failure so retries rebuild them.
.DELETE_ON_ERROR:

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
PANDOC_DATA_DIR = $(abspath $(BUILD_DIR)/pandoc)
PANDOC_TEMPLATE_STAMP = $(BUILD_DIR)/pandoc/.templates-stamp
PANDOC = $(MISE) exec -- pandoc --data-dir=$(PANDOC_DATA_DIR)
TSC = $(MISE) exec -- tsc
ESBUILD = $(MISE) exec -- esbuild
NODE = $(MISE) exec -- node
NPM = $(MISE) exec -- npm
PRETTIER = $(MISE) exec -- prettier
RUFF = $(MISE) exec -- ruff
FOURMOLU = $(MISE) exec -- fourmolu
HLINT = $(MISE) exec -- hlint
OXLINT = $(MISE) exec -- oxlint
SHFMT = $(MISE) exec -- shfmt
SHELLCHECK = $(MISE) exec -- shellcheck
TAPLO = $(MISE) exec -- taplo
ACTIONLINT = $(MISE) exec -- actionlint
# po4a is provisioned by mise's http backend (see mise.toml): the release is a
# Perl source tarball, so the install tree holds the `po4a` script plus its
# Locale::Po4a lib/. PERL5LIB must point at that lib/ and at the repo-local
# .perllib/ where setup.sh installs po4a's two non-core CPAN dependencies
# against the system Perl. Override PO4A_BIN only to test a different po4a.
PO4A_HOME := $(shell $(MISE) where http:po4a 2>/dev/null)
PO4A_BIN ?= $(if $(PO4A_HOME),$(PO4A_HOME)/po4a)
PERL_LOCAL_LIB := $(abspath .perllib)
PO4A_PERL5LIB = $(PERL_LOCAL_LIB)/lib/perl5$(if $(PO4A_HOME),:$(PO4A_HOME)/lib)
# GNU gettext is pinned in mise.toml (conda:gettext-tools). Override GETTEXT_BIN only
# to test a different gettext.
GETTEXT_HOME := $(shell $(MISE) where conda:gettext-tools 2>/dev/null)
GETTEXT_BIN ?= $(if $(GETTEXT_HOME),$(GETTEXT_HOME)/bin)
PO4A_ENV = env PATH="$(if $(GETTEXT_BIN),$(GETTEXT_BIN):)$(PATH)" PERL5LIB="$(PO4A_PERL5LIB)$(if $(PERL5LIB),:$(PERL5LIB))"
# lefthook is the parallel runner for the lint / lint-fix / format groups (the
# groups themselves live in lefthook.yml and just call the make subtargets
# below). It also manages the git hooks installed by setup.sh.
LEFTHOOK = $(MISE) exec -- lefthook
# On Linux the GHC links Haskell binaries against gmp; mise provides its headers
# and libgmp.so (conda:gmp, Linux only in mise.toml) so no -dev package is needed.
ifeq ($(shell uname -s),Linux)
GMP_HOME := $(shell $(MISE) where conda:gmp 2>/dev/null)
endif
CABAL_GMP_FLAGS = $(if $(GMP_HOME),--extra-lib-dirs=$(GMP_HOME)/lib --extra-include-dirs=$(GMP_HOME)/include)


# Prettier formats the whole repo; the scope (which extensions, what to skip) is
# governed by .prettierignore — build output, vendored/installed code, generated
# files, the book chapter markdown (owned by the book-filter linter), and test
# fixtures are excluded there. `make lint` checks; `make lint-fix` rewrites.
PRETTIER_TARGETS = .


# The default is the repo-local, dated TeX Live snapshot from setup.sh.
# The Codex profile explicitly selects system TeX with TEX_PROVIDER=system.
# Invoke the selected binaries by absolute path; do not silently switch between
# providers. require-tex reports when the selected provider is absent.
TEX_PROVIDER ?= repo
ifeq ($(TEX_PROVIDER),system)
TEX_BIN := $(patsubst %/lualatex,%,$(shell command -v lualatex 2>/dev/null))
else ifeq ($(TEX_PROVIDER),repo)
# The repo-local tree may carry binaries for several platforms (e.g. a checkout
# shared between macOS and a Linux VM), so pick the host's; fall back to the
# first bin dir only on hosts with no known TeX Live platform name.
TEX_PLATFORM := $(shell case "$$(uname -s)-$$(uname -m)" in \
	(Darwin-*) echo universal-darwin ;; \
	(Linux-aarch64|Linux-arm64) echo aarch64-linux ;; \
	(Linux-x86_64) echo x86_64-linux ;; esac)
TEX_BIN := $(if $(TEX_PLATFORM),$(wildcard .texlive/texlive/bin/$(TEX_PLATFORM)),$(firstword $(wildcard .texlive/texlive/bin/*)))
else
$(error TEX_PROVIDER must be repo or system)
endif
TEX_ENV = env PATH=$(abspath $(TEX_BIN)):$(PATH)
MAKEINDEX = $(TEX_ENV) $(abspath $(TEX_BIN))/makeindex
UPMENDEX = $(TEX_ENV) $(abspath $(TEX_BIN))/upmendex
LUALATEX_BASE_FLAGS = -interaction=nonstopmode -halt-on-error

# texfot wraps LuaLaTeX and filters its console output down to warnings, errors,
# and the "Output written" summary, dropping the package-load / page-number /
# font-path noise (all of which the .log still records in full). Keep all
# warnings visible, including missing index-link destinations. texfot is
# required (installed from setup.sh's package list; `./setup.sh --doctor`
# checks for it). Set LATEX_VERBOSE=1 to
# bypass texfot and see the raw log.
TEXFOT ?= $(abspath $(TEX_BIN))/texfot
TEXFOT_FLAGS = --quiet
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
	@echo "TeX Live not found (TEX_PROVIDER=$(TEX_PROVIDER)). Run ./setup.sh --run or bash tools/setup_codex.sh." >&2
	@exit 1
else
require-tex:
	@:
endif

require-po4a:
	@PATH="$(if $(GETTEXT_BIN),$(GETTEXT_BIN):)$(PATH)"; export PATH; \
	PERL5LIB="$(PO4A_PERL5LIB)$(if $(PERL5LIB),:$(PERL5LIB))"; export PERL5LIB; \
	test -n "$(PO4A_BIN)" && test -x "$(PO4A_BIN)" || { \
		echo "po4a not found; run ./setup.sh --run" >&2; exit 1; \
	}; \
	"$(PO4A_BIN)" --version >/dev/null 2>&1 || { \
		echo "po4a is not executable (missing Perl modules?); run ./setup.sh --run" >&2; exit 1; \
	}; \
	for tool in msgattrib msgcat msgcmp msgfmt msggrep msginit msgmerge; do \
		command -v "$$tool" >/dev/null 2>&1 || { \
			echo "$$tool not found; run ./setup.sh --run" >&2; exit 1; \
		}; \
	done

# === Copy-on-write copies (git worktrees). ===
# CP_COW is a recursive, mtime-preserving copy that clones file blocks where
# the filesystem supports it: clonefile(2) on macOS/APFS (cp -c falls back to
# copyfile(2) elsewhere), reflinks on Linux xfs/btrfs (--reflink=auto degrades
# to a plain copy on e.g. ext4). Preserved mtimes keep make from treating the
# cloned artifacts as stale. tools/worktree_caches.sh inherits this via the
# export and applies its own matching default when run outside make.
ifeq ($(shell uname -s),Darwin)
CP_COW ?= cp -Rpc
else
CP_COW ?= cp -Rp --reflink=auto
endif
export CP_COW

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
# Translation maintenance must run before generated book inputs are current.
# In particular, remaking books.mk would prepare the Japanese excerpt and
# validate stale catalogs before the requested update has a chance to run.
TRANSLATION_MAINTENANCE_GOALS = translation-ja-update-catalogs translation-ja-generate translation-ja-sync translation-ja-finish
ifneq ($(strip $(MAKECMDGOALS)),)
ifeq ($(strip $(filter-out $(BOOTSTRAP_GOALS) $(TRANSLATION_MAINTENANCE_GOALS),$(MAKECMDGOALS))),)
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
PILOT_BOOK_STEMS := polish-space-book-ja
BOOK_EDITABLE_STEMS := $(filter-out $(PILOT_BOOK_STEMS),$(BOOK_STEMS))
BOOK_PDFS = $(foreach stem,$(filter-out $(PILOT_BOOK_STEMS),$(BOOK_STEMS)),$($(stem)_DIR)/build/$(stem).pdf)
BOOK_TEXS = $(foreach stem,$(BOOK_STEMS),$($(stem)_DIR)/build/$(stem).tex)
BOOK_DEBUG_PDFS = $(foreach stem,$(BOOK_STEMS),$($(stem)_DIR)/build/$(stem)-debug.pdf)

JA_PO4A_CONFIG := polish-space-ja/l10n/po4a.cfg
# The configured chapters determine all translation dependencies.  New draft
# chapters enter the build only after their catalogs and source records exist.
JA_CHAPTER_NAMES := $(if $(wildcard $(JA_PO4A_CONFIG)),$(shell sed -n 's|^\[type: book-markdown\] $$(source)/\([^ ]*\).*|\1|p' $(JA_PO4A_CONFIG)))
JA_ENGLISH := $(addprefix polish-space/src/polish-space-book/,$(JA_CHAPTER_NAMES))
JA_TRANSLATED := $(addprefix polish-space-ja/src/polish-space-book/,$(JA_CHAPTER_NAMES))
JA_CATALOGS := $(addprefix polish-space-ja/l10n/ja/,$(JA_CHAPTER_NAMES:.md=.po))
JA_POTS := $(addprefix polish-space-ja/l10n/pot/,$(JA_CHAPTER_NAMES:.md=.pot))
JA_STATUS := polish-space-ja/l10n/translation-status.json
JA_GLOSSARY := polish-space-ja/l10n/glossary-ja.yaml
JA_CHECK_TOOLS := tools/check_translation_workflow.py tools/translation_validation_cache.py tools/check_translation_structure.py \
	tools/check_translation_terms.py tools/project_translation_sourcemap.py tools/book_manifest.py
JA_SOURCE_DIR := polish-space/src/polish-space-book
JA_TRANSLATED_DIR := polish-space-ja/src/polish-space-book
JA_PO4A_VARS := \
	--variable l10n=polish-space-ja/l10n \
	--variable source=$(JA_SOURCE_DIR) \
	--variable output=$(JA_TRANSLATED_DIR)
TRANSLATION_CACHE ?= 1
JA_WORKFLOW_CHECK = $(PYTHON) tools/check_translation_workflow.py \
	--po4a $(PO4A_BIN) \
	--config $(JA_PO4A_CONFIG) \
	--l10n-dir polish-space-ja/l10n \
	--translated-dir $(JA_TRANSLATED_DIR) \
	--status $(JA_STATUS) $(if $(filter 1,$(TRANSLATION_CACHE)),--cache-dir $(BUILD_DIR)/translation-cache)
JA_CATALOG_STAMP := $(BUILD_DIR)/translation-ja-catalogs.ok
JA_TRANSLATION_STAMP := $(BUILD_DIR)/translation-ja-generated.ok
JA_STRUCTURE_STAMP := $(BUILD_DIR)/translation-ja-structure.ok

# The Japanese viewer projects canonical English booklinks through the PO
# catalogs. Fully translated chapters get stable message-level spans; the
# English fallback symlinks retain exact offsets. The release PDF remains out
# of the viewer prerequisites while the edition is only a partial translation.
ifneq ($(filter polish-space-book-ja,$(BOOK_STEMS)),)
JA_CANONICAL_BOOKLINK_MAP := $(BUILD_DIR)/booklink-filter-sourcemap-polish-space-ja-canonical.json
JA_BOOKLINK_FILTER_SOURCEMAP := $(BUILD_DIR)/booklink-filter-sourcemap-polish-space-ja.json
JA_RAW_VIEWER_SOURCEMAP := $(BUILD_DIR)/polish-space-book-ja-sourcemap-raw.json
JA_VIEWER_SOURCEMAP := polish-space-ja/build/polish-space-book-ja-sourcemap.json
JA_BOOKLINK_SOURCES := $(patsubst $(BUILD_DIR)/booklink-src/polish-space/%,polish-space-ja/%,$(polish-space-book_BOOKLINK_DEPS))
JA_BOOKLINK_DEPS := $(addprefix $(BUILD_DIR)/booklink-src/,$(JA_BOOKLINK_SOURCES))
JA_PROJECTION_DEPS := \
	polish-space/src/polish-space-book.json \
	polish-space-ja/src/polish-space-book-ja.json \
	$(polish-space-book_INPUTS) \
	$(polish-space-book-ja_INPUTS) \
	$(JA_CATALOGS)
JA_PROJECTION_ARGS = \
	--source-manifest polish-space/src/polish-space-book.json \
	--translation-manifest polish-space-ja/src/polish-space-book-ja.json \
	--po-dir polish-space-ja/l10n/ja

polish-space-book-ja_BOOKLINK_DEPS := $(JA_BOOKLINK_DEPS)
polish-space-book-ja_PANDOC_INPUTS := $(foreach input,$(polish-space-book-ja_INPUTS),$(if $(filter $(input),$(JA_BOOKLINK_SOURCES)),$(BUILD_DIR)/booklink-src/$(input),$(input)))
polish-space-ja_VIEWER_DEPS := $(JA_VIEWER_SOURCEMAP) polish-space-ja/build/polish-space-book-ja-debug.pdf
endif

# Chapters with Lean formalizations build through injected copies under
# $(BUILD_DIR)/booklink-src/<real-path>/, keyed by each chapter's real
# repo-relative path so books sharing a chapter share one injected copy and
# separate books never collide. tools/books_mk.py resolves that per book and
# emits <stem>_PANDOC_INPUTS (the pandoc input list with booklink chapters
# swapped for their injected copies) and <stem>_BOOKLINK_DEPS (those copies as
# prerequisites), so the Makefile needs no canonical-owner remapping. The
# injection sourcemap is derived from the booklink markers in $(BOOKLINK_LEANS).
BOOKLINK_FILTER_SOURCEMAP = $(BUILD_DIR)/booklink-filter-sourcemap.json

FILTER_SRC = tools/book-filter/LeanSourceRanges.hs tools/book-filter/FormulaAnchors.hs tools/book-filter/SemanticInspection.hs tools/book-filter/SemanticAST.hs tools/book-filter/SemanticTrace.hs tools/book-filter/ChapterMappingRules.hs tools/book-filter/ChapterPreparation.hs tools/book-filter/SourceNormalization.hs tools/book-filter/SourceJSON.hs tools/book-filter/SourceScopes.hs tools/book-filter/VariableResolution.hs tools/book-filter/SemanticTranslation.hs tools/book-filter/SemanticExpr.hs tools/book-filter/StructuralSyntax.hs tools/book-filter/OperatorProbe.hs tools/book-filter/ProbeTemplates.hs tools/book-filter/OperatorEvidence.hs tools/book-filter/ProofContexts.hs tools/book-filter/ContextTemplates.hs tools/book-filter/Correspondence.hs tools/book-filter/LocatedMath.hs tools/book-filter/MathSyntaxCLI.hs tools/book-filter/MathSyntax.hs tools/book-filter/Main.hs tools/book-filter/DependencyGraph.hs tools/book-filter/SectionRef.hs

# Source trees the language formatters own. Ruff formats the repository Python
# (tools/, tests/, skill scripts); Fourmolu formats the book-filter Haskell plus
# the golden-test driver. `make lint` checks; `make lint-fix` rewrites.
RUFF_TARGETS = tools tests .codex
FOURMOLU_TARGETS = $(FILTER_SRC) $(wildcard tests/*.hs)

# HLint lints the same Haskell sources (rules / extension overrides in .hlint.yaml).
HLINT_TARGETS = tools/book-filter $(wildcard tests/*.hs)

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

# Bundle the viewer's browser modules with shared chunks. Keep entry points for
# browser integration and inspection separate so direct imports share the same
# state as app.js. Flat chunks preserve import.meta.url-relative vendor URLs.
VIEWER_DIR = tools/formalization-viewer
# Node server, dist builder, LSP cache, and port helper for the viewer, run
# directly as TypeScript by node's type-stripping (no build step).
VIEWER_SERVER_DIR = $(VIEWER_DIR)/server
# @types/node is a locked dev dependency of the server package. Keeping a real
# local node_modules tree lets every tsconfig resolve it through standard Node
# lookup instead of depending on mise's install layout.
VIEWER_SERVER_NODE_MODULES = $(VIEWER_SERVER_DIR)/node_modules
VIEWER_SRC_DIR = $(VIEWER_DIR)/src
VIEWER_BUILD_DIR = $(VIEWER_DIR)/build
# Internal modules are bundled into these browser entry points. Unit tests still
# import TypeScript sources directly; E2E and browser tools use these entries.
VIEWER_BOOTSTRAP = $(VIEWER_SRC_DIR)/view-bootstrap.ts
VIEWER_TS = $(filter-out %.test.ts $(VIEWER_BOOTSTRAP),$(wildcard $(VIEWER_SRC_DIR)/*.ts))
VIEWER_ENTRY_NAMES = app chat event-stream loading-progress offline parallel-pdf pdf pdf-document permalink select-dropdown session-store state sync term-preview safe-html safe-script-url search
VIEWER_ENTRIES = $(foreach name,$(VIEWER_ENTRY_NAMES),$(name)=$(VIEWER_SRC_DIR)/$(name).ts)
VIEWER_CSS = $(VIEWER_BUILD_DIR)/styles.css
VIEWER_BUNDLE_JS = $(patsubst $(VIEWER_SRC_DIR)/%.ts,$(VIEWER_BUILD_DIR)/%.js,$(VIEWER_ENTRIES))
VIEWER_JS = $(VIEWER_BUNDLE_JS) $(VIEWER_BUILD_DIR)/view-bootstrap.js $(VIEWER_CSS)
VIEWER_SRC_TESTS = $(wildcard $(VIEWER_SRC_DIR)/*.test.ts)
VIEWER_E2E_DIR = $(VIEWER_DIR)/e2e
ESBUILD_FLAGS = --bundle --splitting --format=esm --target=esnext --minify --sourcemap=linked
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

$(JA_CATALOG_STAMP): $(JA_CHECK_TOOLS) $(JA_GLOSSARY) \
		$(JA_PO4A_CONFIG) $(JA_ENGLISH) $(JA_CATALOGS) $(JA_POTS) $(JA_STATUS) | $(BUILD_DIR) require-po4a require-mise
	$(Q)$(PO4A_ENV) $(JA_WORKFLOW_CHECK) --catalogs-only
	@touch $@

$(JA_TRANSLATION_STAMP): $(JA_PO4A_CONFIG) $(JA_ENGLISH) $(JA_CATALOGS) $(JA_CATALOG_STAMP) | $(BUILD_DIR) require-po4a
	$(Q)$(PO4A_ENV) $(JA_WORKFLOW_CHECK) --write-generated
	@touch $@ $(JA_STRUCTURE_STAMP)

$(JA_TRANSLATED): $(JA_TRANSLATION_STAMP)
	@test -f $@

$(JA_STRUCTURE_STAMP): $(JA_CHECK_TOOLS) $(JA_GLOSSARY) \
		$(JA_PO4A_CONFIG) $(JA_ENGLISH) $(JA_CATALOGS) $(JA_POTS) $(JA_STATUS) $(JA_TRANSLATED) | $(BUILD_DIR) require-po4a require-mise
	$(Q)$(PO4A_ENV) $(JA_WORKFLOW_CHECK)
	@touch $@

translation-ja-update-catalogs: | require-po4a
	$(Q)$(PO4A_ENV) $(PO4A_BIN) --no-translations $(JA_PO4A_VARS) $(JA_PO4A_CONFIG)

# Reuse the fully checked temporary render instead of rendering once to check
# catalogs, again to generate Markdown, and again to check the generated files.
translation-ja-generate: | $(BUILD_DIR) require-po4a require-mise
	$(Q)$(PO4A_ENV) $(JA_WORKFLOW_CHECK) --write-generated
	@touch $(JA_CATALOG_STAMP) $(JA_TRANSLATION_STAMP) $(JA_STRUCTURE_STAMP)

ifneq ($(wildcard $(JA_PO4A_CONFIG)),)
translation-ja-check lint-translation: $(JA_CHECK_TOOLS) $(JA_GLOSSARY) \
		$(JA_PO4A_CONFIG) $(JA_ENGLISH) $(JA_CATALOGS) $(JA_POTS) $(JA_STATUS) $(JA_TRANSLATED) | require-po4a require-mise
	$(Q)$(PO4A_ENV) $(JA_WORKFLOW_CHECK)

else
translation-ja-check lint-translation:
	@echo "No Japanese translation catalogs in this checkout."
endif

translation-ja-sync:
	$(Q)$(MAKE) --no-print-directory translation-ja-update-catalogs
	$(Q)$(MAKE) --no-print-directory translation-ja-generate

# REVIEWED names only chapters already reviewed against the current English.
# The helper runs mutations and checks sequentially, stopping on first failure.
.PHONY: translation-ja-finish
translation-ja-finish: require-mise
	$(Q)$(PYTHON) tools/edit_translation.py finish $(foreach chapter,$(REVIEWED),--reviewed '$(chapter)') $(foreach book,$(BOOKS),--book '$(book)')

# Fast, read-only terminology gate without po4a rendering.
lint-translation-terms: $(JA_CHECK_TOOLS) $(JA_GLOSSARY) $(JA_CATALOGS) | require-mise
	$(Q)$(PYTHON) tools/check_translation_terms.py --glossary $(JA_GLOSSARY) $(JA_CATALOGS)

.PHONY: lint-translation-terms

debug-pdfs: $(sort $(BOOK_DEBUG_PDFS))

# Deterministic build/diagnostic reporting; BOOKS selects stems, defaulting to
# every book discovered in this checkout. No release or preview PDF is built.
validate-tex validate-debug: require-mise
	$(Q)$(PYTHON) tools/validate_book_build.py $(patsubst validate-%,%,$@) $(foreach stem,$(if $(strip $(BOOKS)),$(BOOKS),$(BOOK_STEMS)),--book $(stem))

.PHONY: validate-tex validate-debug

# Pre-warm every book's preview cross-reference aux (chapter previews are built
# on demand by the viewer / `make <stem>-preview-<chapter>.pdf`).
preview-warm: $(PREVIEW_MASTER_AUXES)

# Explicitly requested chapter distributions; BOOKS selects book stems.
CHAPTER_PDF_BOOKS = $(if $(strip $(BOOKS)),$(BOOKS),$(BOOK_STEMS))
chapter-pdfs: $(foreach stem,$(CHAPTER_PDF_BOOKS),$(foreach chapter,$($(stem)_CHAPTERS),$($(stem)_DIR)/build/$(stem)-preview-$(basename $(notdir $(chapter))).pdf) $(foreach unit,_contents _bibliography _index,$($(stem)_DIR)/build/$(stem)-preview-$(unit).pdf))

.PHONY: chapter-pdfs

# Preferred viewer port. The formalization-viewer target resolves this through
# $(VIEWER_SERVER_DIR)/free-port.ts: it serves on this port when free and otherwise falls back
# to an OS-assigned free port, so a second instance (or a stale listener) never
# fails to bind. Set BOOKLINK_VIEWER_PORT=0 to always pick a free port.
BOOKLINK_VIEWER_PORT ?= 8765
BOOKLINK_VIEWER_HOST ?= 127.0.0.1
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
ifneq ($(strip $(BOOK_STEMS)),)
ifeq ($(strip $($(BOOKLINK_PROJECT)_VIEWER_DEPS)),)
$(error unknown BOOKLINK_PROJECT '$(BOOKLINK_PROJECT)'; expected a book directory with viewer artifacts)
endif
endif

# STATIC=1 builds a self-contained distribution under $(BOOKLINK_DIST_DIR)
# (viewer assets, allowlisted project files, and a pregenerated Lean LSP
# response cache) instead of serving the live bridge.
# One build owns all entry points and shared chunks, including dependency edits.
$(VIEWER_BUNDLE_JS) $(VIEWER_CSS) &: $(VIEWER_TS) $(VIEWER_DIR)/styles.css Makefile | require-mise
	@mkdir -p $(VIEWER_BUILD_DIR)
	$(ESBUILD) $(VIEWER_ENTRIES) styles=$(VIEWER_DIR)/styles.css $(ESBUILD_FLAGS) --outdir=$(VIEWER_BUILD_DIR)

viewer-build: viewer-node-types $(VIEWER_JS)

$(VIEWER_BUILD_DIR)/view-bootstrap.js: $(VIEWER_BOOTSTRAP) $(VIEWER_SRC_DIR)/session-store.ts $(VIEWER_SRC_DIR)/i18n.ts Makefile | require-mise
	@mkdir -p $(dir $@)
	$(ESBUILD) $< --bundle --format=iife --target=esnext --minify --sourcemap=linked --outfile=$@

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
	( port=$$(BOOKLINK_VIEWER_HOST='$(BOOKLINK_VIEWER_HOST)' $(NODE) $(VIEWER_SERVER_DIR)/free-port.ts $(BOOKLINK_VIEWER_PORT)); \
	url_host='$(BOOKLINK_VIEWER_HOST)'; case "$$url_host" in *:*) url_host="[$$url_host]";; esac; \
	echo "Formalization viewer: http://$$url_host:$$port/"; \
	if [ "$${BOOKLINK_OPEN_BROWSER:-1}" != "0" ]; then ( \
	  for i in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15; do \
	    $(PYTHON) -c "import socket; socket.create_connection(('$(BOOKLINK_VIEWER_HOST)',$$port), timeout=0.3).close()" 2>/dev/null && break; \
	    sleep 0.3; \
	  done; \
	  $(PYTHON) -m webbrowser "http://$$url_host:$$port/" >/dev/null 2>&1 || true \
	) & fi; \
	$(PYTHON) -m http.server $$port --bind '$(BOOKLINK_VIEWER_HOST)' -d $(BOOKLINK_DIST_DIR) )
else
# Dev server with live reload on both sides:
#  - esbuild --watch rebuilds the viewer .js on every .ts edit; the file watcher
#    sees the change and reloads the page (assets are served no-store).
#  - watchexec --restart reruns the Node server whenever its TypeScript changes.
#    SIGTERM reaps the Lean bridges, builds, and inner watcher.
# The browser is opened once (after the port is up) with the server's own
# browser-open suppressed, so restarts don't spawn new tabs.
# Book artifacts are built lazily after the browser reports its PDF selection;
# serving the UI must not wait for every book's PDF and source map.
formalization-viewer: viewer-build require-mise
	( port=$$(BOOKLINK_VIEWER_HOST='$(BOOKLINK_VIEWER_HOST)' $(NODE) $(VIEWER_SERVER_DIR)/free-port.ts $(BOOKLINK_VIEWER_PORT)); \
	url_host='$(BOOKLINK_VIEWER_HOST)'; case "$$url_host" in *:*) url_host="[$$url_host]";; esac; \
	echo "Formalization viewer: http://$$url_host:$$port/"; \
	$(ESBUILD) $(VIEWER_ENTRIES) styles=$(VIEWER_DIR)/styles.css $(ESBUILD_FLAGS) --outdir=$(VIEWER_BUILD_DIR) --watch & \
	esbuild_pid=$$!; \
	$(ESBUILD) $(VIEWER_BOOTSTRAP) --bundle --format=iife --target=esnext --minify --sourcemap=linked --outfile=$(VIEWER_BUILD_DIR)/view-bootstrap.js --watch & \
	bootstrap_pid=$$!; trap 'kill $$esbuild_pid $$bootstrap_pid 2>/dev/null' EXIT INT TERM; \
	if [ "$${BOOKLINK_OPEN_BROWSER:-1}" != "0" ]; then ( \
	  for i in 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15; do \
	    $(PYTHON) -c "import socket; socket.create_connection(('$(BOOKLINK_VIEWER_HOST)',$$port), timeout=0.3).close()" 2>/dev/null && break; \
	    sleep 0.3; \
	  done; \
	  $(PYTHON) -m webbrowser "http://$$url_host:$$port/" >/dev/null 2>&1 || true \
	) & fi; \
	BOOKLINK_OPEN_BROWSER=0 BOOKLINK_PROJECT=$(BOOKLINK_PROJECT) BOOKLINK_VIEWER_HOST='$(BOOKLINK_VIEWER_HOST)' BOOKLINK_VIEWER_PORT=$$port \
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

$(BOOKS_MK): tools/books_mk.py tools/book_manifest.py tools/booklink_sourcemap.py tools/formalization_annotations.py $(BOOK_MANIFESTS) $(BOOKLINK_LEAN_FILES) | require-mise
	@mkdir -p $(dir $@)
	@echo "  books-mk $@"
	$(Q)books_tmp=$$(mktemp "$@.XXXXXX") || exit 1; \
		trap 'rm -f "$$books_tmp"' EXIT HUP INT TERM; \
		$(PYTHON) tools/books_mk.py $(BOOK_MANIFESTS) --leans $(BOOKLINK_LEAN_FILES) > "$$books_tmp" && \
		mv -f "$$books_tmp" "$@"

$(BUILD_DIR):
	mkdir -p $@

$(FILTER_BIN): $(FILTER_SRC) math-project.cabal | $(BUILD_DIR) require-mise
	@$(CABAL) build book-filter --builddir=$(BUILD_DIR) $(CABAL_GMP_FLAGS) -v0
	@filter_bin=$$($(CABAL) list-bin --builddir=$(BUILD_DIR) $(CABAL_GMP_FLAGS) book-filter) || exit 1; \
	if ! cmp -s "$$filter_bin" $(FILTER_BIN); then \
		cp "$$filter_bin" $(FILTER_BIN).tmp && mv -f $(FILTER_BIN).tmp $(FILTER_BIN); \
	fi

$(BOOKLINK_FILTER_SOURCEMAP): tools/booklink_sourcemap.py tools/formalization_annotations.py $(BOOKLINK_LEANS) $(BOOKLINK_SOURCES) $(BOOKLINK_SKIP_SOURCES) | $(BUILD_DIR) require-mise
	@echo "  booklink-sourcemap $@"
	$(Q)$(PYTHON) tools/booklink_sourcemap.py $(BOOKLINK_LEANS) --skip-source $(BOOKLINK_SKIP_SOURCES) --out $@

ifneq ($(filter polish-space-book-ja,$(BOOK_STEMS)),)
# English prose edits move booklink offsets even when no Lean marker changes.
# Rebuild the canonical map before projecting those offsets through the PO files.
$(JA_CANONICAL_BOOKLINK_MAP): tools/booklink_sourcemap.py tools/formalization_annotations.py $(polish-space-book_BOOKLINK_LEANS) $(polish-space-book_INPUTS) $(polish-space-book_SKIP_SOURCES) | $(BUILD_DIR) require-mise
	@echo "  booklink-sourcemap $@"
	$(Q)$(PYTHON) tools/booklink_sourcemap.py $(polish-space-book_BOOKLINK_LEANS) --skip-source $(polish-space-book_SKIP_SOURCES) --out $@

$(JA_BOOKLINK_FILTER_SOURCEMAP): tools/project_translation_sourcemap.py tools/check_translation_structure.py $(JA_CANONICAL_BOOKLINK_MAP) $(JA_PROJECTION_DEPS) | $(BUILD_DIR) require-mise
	@echo "  translation-sourcemap $@"
	$(Q)$(PYTHON) tools/project_translation_sourcemap.py \
		--source-map $(JA_CANONICAL_BOOKLINK_MAP) \
		$(JA_PROJECTION_ARGS) \
		--out $@

$(JA_BOOKLINK_DEPS): $(BUILD_DIR)/booklink-src/polish-space-ja/%.md: polish-space-ja/%.md $(FILTER_BIN) $(JA_BOOKLINK_FILTER_SOURCEMAP) | $(BUILD_DIR) require-mise
	@mkdir -p $(dir $@)
	@echo "  booklink-inject $@"
	$(Q)$(FILTER_BIN) inject-booklinks --sourcemap $(abspath $(JA_BOOKLINK_FILTER_SOURCEMAP)) --source $(abspath $<) --out $@

$(JA_RAW_VIEWER_SOURCEMAP): tools/booklink_sourcemap.py tools/formalization_annotations.py $(polish-space-book_BOOKLINK_LEANS) $(polish-space-book_SKIP_SOURCES) $(JA_BOOKLINK_FILTER_SOURCEMAP) polish-space-ja/build/polish-space-book-ja-debug.tex | $(BUILD_DIR) require-mise
	@echo "  viewer-sourcemap $@"
	$(Q)$(PYTHON) tools/booklink_sourcemap.py $(polish-space-book_BOOKLINK_LEANS) \
		--skip-source $(polish-space-book_SKIP_SOURCES) \
		--tex-file polish-space-ja/build/polish-space-book-ja-debug.tex \
		--injection-map $(JA_BOOKLINK_FILTER_SOURCEMAP) \
		--out $@

$(JA_VIEWER_SOURCEMAP): tools/project_translation_sourcemap.py tools/check_translation_structure.py $(JA_RAW_VIEWER_SOURCEMAP) $(JA_PROJECTION_DEPS) | polish-space-ja/build require-mise
	@echo "  translation-sourcemap $@"
	$(Q)$(PYTHON) tools/project_translation_sourcemap.py \
		--source-map $(JA_RAW_VIEWER_SOURCEMAP) \
		$(JA_PROJECTION_ARGS) \
		--out $@

# Same marker-band pairing as book-sourcemap-rules: the pilot's debug PDF and
# projected viewer sourcemap must not drift apart.
polish-space-ja/build/polish-space-book-ja-debug.pdf: $(JA_VIEWER_SOURCEMAP)
endif

# Inject booklinks into a chapter, keyed by its real repo-relative path: the
# target is $(BUILD_DIR)/booklink-src/<real>.md, the prerequisite is the real
# source <real>.md, and --source matches the sourcemap entry by that path.
$(BUILD_DIR)/booklink-src/%.md: %.md $(FILTER_BIN) $(BOOKLINK_FILTER_SOURCEMAP) $(wildcard tools/chapter-correspondence/chapters/*.json) | $(BUILD_DIR) require-mise
	@mkdir -p $(dir $@)
	@echo "  booklink-inject $@"
	$(Q)$(FILTER_BIN) inject-booklinks --sourcemap $(abspath $(BOOKLINK_FILTER_SOURCEMAP)) --source $(abspath $<) --out $@

tex: $(sort $(BOOK_TEXS))

# $(call book-dir-rules,<dir>): rules shared by every directory hosting at
# least one book: the build directory itself and the PDF compile rules, which
# hardcode -output-directory per directory.
define book-dir-rules
$(1)_INDEXER ?= $$(MAKEINDEX)

$(1)/build:
	mkdir -p $$@

# Debug PDFs refresh the index after a term or page number changes, including
# on a cold build. Repeat until the index and auxiliary files are stable and
# record the indexed digest for validation. DEBUG_FULL=1 discards previous
# auxiliaries before this convergence check. Non-debug books use three passes.
# Both cases share this `%.pdf` rule because GNU Make 3.81 (the macOS system
# make) breaks pattern-rule ties by definition order, not
# shortest stem, so a separate rule would be shadowed by this one.
$(1)/build/%.pdf: $(1)/build/%.tex tools/refresh_debug_pdf.py polish-space/tex/formula-overlays.lua Makefile | $(1)/build require-mise require-tex
	$$(Q)if case "$$*" in *-debug|*-debug-dark) true ;; *) false ;; esac; then \
		if [ -n "$$(DEBUG_FULL)" ]; then \
			rm -f $(1)/build/$$*.synctex.gz $(1)/build/$$*.aux $(1)/build/$$*.out $(1)/build/$$*.toc \
				$(1)/build/$$*.ind $(1)/build/$$*.ilg $(1)/build/$$*.index-sha256; \
		fi; \
		$$(LATEX_LOCK) $$(PYTHON) tools/refresh_debug_pdf.py --stem $(1)/build/$$* \
			--indexer "$$($(1)_INDEXER)" -- $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$(abspath $(1)/build) $$<; \
	else \
		rm -f $(1)/build/$$*.synctex.gz $(1)/build/$$*.aux $(1)/build/$$*.out $(1)/build/$$*.toc $(1)/build/$$*.ind $(1)/build/$$*.ilg; \
		echo "  lualatex $$* (pass 1/3)"; \
		$$(LATEX_LOCK) $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$(abspath $(1)/build) $$< && \
		{ test ! -f $(1)/build/$$*.idx || { echo "  index $$*"; $$(LATEX_LOCK) $$($(1)_INDEXER) $(1)/build/$$*.idx; }; } && \
		{ echo "  lualatex $$* (pass 2/3)"; $$(LATEX_LOCK) $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$(abspath $(1)/build) $$<; } && \
		{ echo "  lualatex $$* (pass 3/3)"; $$(LATEX_LOCK) $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$(abspath $(1)/build) $$<; }; \
	fi
endef

polish-space-ja_INDEXER := $(UPMENDEX)
# Pandoc only infers chapter-level headings for a small built-in set of class
# names. ltjsbook is book-compatible but needs the division stated explicitly.
polish-space-book-ja_PANDOC_FLAGS := --top-level-division=chapter

# The publication excerpt reads synchronized Japanese chapters without editing
# their committed mirrors. Prepare it before books_mk inspects the new manifest.
ifneq ($(wildcard polish-space-part1-ja/src/polish-space-part1-ja.json),)
PART1_RELEASE_PDF := polish-space-part1-ja/build/polish-space-part1-ja.pdf
# The submission PDF must use the index from its final page layout. Reuse the
# convergence runner so a cold build cannot retain first-pass index references.
$(PART1_RELEASE_PDF): polish-space-part1-ja/build/polish-space-part1-ja.tex tools/refresh_debug_pdf.py Makefile | require-mise require-tex
	$(Q)$(LATEX_LOCK) $(PYTHON) tools/refresh_debug_pdf.py --stem polish-space-part1-ja/build/polish-space-part1-ja \
		--indexer "$(polish-space-part1-ja_INDEXER)" -- $(LUALATEX) $(LUALATEX_BASE_FLAGS) -output-directory=$(abspath polish-space-part1-ja/build) $<

PART1_PRINT_TEMPLATE := output/print/templates/10mm_a5_musen_srgb.psd
PART1_PRINT_OUTPUTS := output/pdf/polish-space-part1-ja-body-a5.pdf \
	output/print/cover_spread_neko_A5_10mm_gray.psd output/print/cover_spread_312x216.pdf \
	output/print/cover_spread_preview.png output/print/cover_template_preview.png \
	output/print/cover-spec.json output/print/final-sha256.json output/print/README.txt

pdfs: print-part1
.PHONY: print-part1
print-part1: $(PART1_PRINT_OUTPUTS)

$(PART1_PRINT_TEMPLATE): | require-mise
	@mkdir -p $(dir $@)
	$(Q)set -e; archive=$$(mktemp); trap 'rm -f "$$archive"' EXIT; \
		curl -fsSL https://www.shippo.co.jp/neko/downloads/templates/books/A5_hyoushi_total.zip -o "$$archive"; \
		$(PYTHON) -c 'from pathlib import Path; from zipfile import ZipFile; import sys; Path(sys.argv[2]).write_bytes(ZipFile(sys.argv[1]).read("A5_hyoushi_total/A5hyoushi_srgb/10mm_a5_musen_srgb.psd"))' "$$archive" "$@"

# A single stamp coordinates the outputs even on the macOS system Make.
PART1_PRINT_STAMP := $(BUILD_DIR)/part1-print.ok
ifneq ($(words $(wildcard $(PART1_PRINT_OUTPUTS))),$(words $(PART1_PRINT_OUTPUTS)))
.PHONY: part1-print-missing
$(PART1_PRINT_STAMP): part1-print-missing
endif

$(PART1_PRINT_STAMP): $(PART1_RELEASE_PDF) $(PART1_PRINT_TEMPLATE) output/print/build_cover.py | $(BUILD_DIR) require-mise require-tex
	@rm -f $@
	$(Q)$(TEX_ENV) $(MISE) exec -- uv run --no-project --script output/print/build_cover.py $(PART1_RELEASE_PDF)
	$(Q)$(PRETTIER) --write --log-level warn output/print/cover-spec.json
	@touch $@
	@touch $(PART1_PRINT_OUTPUTS)

$(PART1_PRINT_OUTPUTS): $(PART1_PRINT_STAMP)
	@test -f $@

PART1_EDITION_CHAPTERS := polish-spaces cantor-baire-space concrete-cantor-baire-models borel-structure \
	baire-class-functions perfect-sets-standard-borel-coding cauchy-names-polish-representations polish-embeddings-borel-refinements
PART1_EDITION_OUTPUTS := $(addprefix polish-space-part1-ja/build/source/,$(addsuffix .md,$(PART1_EDITION_CHAPTERS)) body.md metadata.json cover-art.tex provenance.json)
$(BOOKS_MK): polish-space-part1-ja/build/source/polish-spaces.md
polish-space-part1-ja/build/source/source.ok: tools/prepare_part1_edition.py Makefile $(JA_TRANSLATED) $(JA_STRUCTURE_STAMP) \
		polish-space-ja/src/polish-space-book-ja.md polish-space-ja/src/polish-space-book-ja.json
	$(Q)$(PYTHON) tools/prepare_part1_edition.py
	@touch $@
	@touch $(PART1_EDITION_OUTPUTS)
$(PART1_EDITION_OUTPUTS): polish-space-part1-ja/build/source/source.ok
	@test -f $@ || { $(PYTHON) tools/prepare_part1_edition.py && touch $@; }
polish-space-part1-ja_PANDOC_FLAGS := --top-level-division=chapter --metadata-file=polish-space-part1-ja/build/source/metadata.json
polish-space-part1-ja_INDEXER := $(UPMENDEX)
PART1_EDITION_SOURCES := $(addprefix polish-space-part1-ja/build/source/,$(addsuffix .md,$(PART1_EDITION_CHAPTERS)))
PART1_FILTER_MAP := $(BUILD_DIR)/booklink-filter-sourcemap-polish-space-part1-ja.json
PART1_VIEWER_MAP := polish-space-part1-ja/build/polish-space-part1-ja-sourcemap.json
PART1_BOOKLINK_DEPS := $(addprefix $(BUILD_DIR)/booklink-src/,$(PART1_EDITION_SOURCES))
polish-space-part1-ja_BOOKLINK_DEPS := $(PART1_BOOKLINK_DEPS)
polish-space-part1-ja_PANDOC_INPUTS := polish-space-part1-ja/src/polish-space-part1-ja.md $(PART1_BOOKLINK_DEPS)
polish-space-part1-ja_VIEWER_DEPS := $(PART1_VIEWER_MAP) polish-space-part1-ja/build/polish-space-part1-ja-debug.pdf

$(PART1_FILTER_MAP): tools/project_part1_sourcemap.py $(JA_BOOKLINK_FILTER_SOURCEMAP) $(PART1_EDITION_OUTPUTS) | $(BUILD_DIR) require-mise
	$(Q)$(PYTHON) tools/project_part1_sourcemap.py --source-map $(JA_BOOKLINK_FILTER_SOURCEMAP) --out $@

$(PART1_BOOKLINK_DEPS): $(BUILD_DIR)/booklink-src/polish-space-part1-ja/build/source/%.md: polish-space-part1-ja/build/source/%.md $(FILTER_BIN) $(PART1_FILTER_MAP) | require-mise
	@mkdir -p $(dir $@)
	$(Q)$(FILTER_BIN) inject-booklinks --sourcemap $(abspath $(PART1_FILTER_MAP)) --source $(abspath $<) --out $@

$(PART1_VIEWER_MAP): tools/project_part1_sourcemap.py $(PART1_FILTER_MAP) polish-space-part1-ja/build/polish-space-part1-ja-debug.tex | require-mise
	$(Q)$(PYTHON) tools/project_part1_sourcemap.py --source-map $(JA_BOOKLINK_FILTER_SOURCEMAP) --tex-file polish-space-part1-ja/build/polish-space-part1-ja-debug.tex --out $@

polish-space-part1-ja/build/polish-space-part1-ja-debug.pdf: $(PART1_VIEWER_MAP)
polish-space-part1-ja/build/polish-space-part1-ja.tex polish-space-part1-ja/build/polish-space-part1-ja-debug.tex: \
	$(PART1_EDITION_OUTPUTS) $(wildcard polish-space-part1-ja/edition/*.tex) \
	polish-space-part1-ja/edition/public-viewer-qr.png

endif

# $(call book-rules,<stem>): build rules for one chaptered book. `make
# <stem>` builds its PDF.
define book-rules
.PHONY: $(1)
$(1): $($(1)_DIR)/build/$(1).pdf

# Include local TeX and citation styles, including symlinked shared inputs.
# Presentation changes must invalidate both Pandoc renders and previews.
$($(1)_DIR)/build/$(1).tex: $(PANDOC_TEMPLATE_STAMP) tools/book_manifest.py $(wildcard tools/pandoc/templates/*) $($(1)_MANIFEST) $($(1)_INPUTS) $(FILTER_BIN) $($(1)_BOOKLINK_DEPS) $(wildcard $($(1)_DIR)/tex/*.tex $($(1)_DIR)/tex/*.csl) $($(1)_DIR)/tex/references.bib | $($(1)_DIR)/build require-mise
	@echo "  pandoc $$@"
	$$(Q)DEPENDENCY_GRAPH_CACHE=$($(1)_DIR)/build/$(1)-dependency-graph-layout.cache $$(PANDOC) $($(1)_PANDOC_INPUTS) \
		-f markdown \
		--filter $$(FILTER_BIN) \
		--citeproc \
		$($(1)_PANDOC_FLAGS) \
		-o $$@ \
		--standalone

$($(1)_DIR)/build/$(1)-debug.tex: $(PANDOC_TEMPLATE_STAMP) tools/book_manifest.py tools/enable_booklink_highlight.py $(wildcard tools/pandoc/templates/*) $($(1)_MANIFEST) $($(1)_INPUTS) $(FILTER_BIN) $($(1)_BOOKLINK_DEPS) $(wildcard $($(1)_DIR)/tex/*.tex $($(1)_DIR)/tex/*.csl) $($(1)_DIR)/tex/references.bib | $($(1)_DIR)/build require-mise
	@echo "  pandoc $$@"
	$$(Q)DEPENDENCY_GRAPH_CACHE=$($(1)_DIR)/build/$(1)-dependency-graph-layout.cache $$(PANDOC) $($(1)_PANDOC_INPUTS) \
		-f markdown \
		--filter $$(FILTER_BIN) \
		--citeproc \
		$$(HYPERLINK_BORDER_FLAGS) \
		$($(1)_PANDOC_FLAGS) \
		-o $$@ \
		--standalone
	@echo "  booklink-highlight $$@"
	$$(Q)$$(PYTHON) tools/enable_booklink_highlight.py $$@

endef

# Shared by canonical books and isolated viewer layout variants.
define book-preview-rules
# --- Chapter preview ------------------------------------------------------
# Dark PDFs are separate viewer artifacts. Reuse the generated TeX verbatim,
# changing only the palette; the light PDF and its auxiliaries are untouched.
$($(1)_DIR)/build/$(1)-debug-dark.tex: $($(1)_DIR)/build/$(1)-debug.tex Makefile
	@printf '%s\n' '\def\BookDarkMode{1}' '\input{$($(1)_DIR)/build/$(1)-debug.tex}' > $$@

# A fast \includeonly render of the single chapter being edited, split (without
# changing content) from the debug tex. The whole-book debug PDF and source map
# are untouched; this is a separate iterative-editing artifact whose chapters
# keep the global booklink/skip anchor numbers, so the existing source map and
# the viewer overlays resolve against it unchanged.
$($(1)_DIR)/build/$(1)-preview-master.tex: tools/split_preview_tex.py $($(1)_DIR)/build/$(1)-debug.tex $($(1)_MANIFEST) $($(1)_CHAPTERS) | $($(1)_DIR)/build require-mise
	@echo "  split-preview $(1)"
	$$(Q)$$(LATEX_LOCK) $$(PYTHON) tools/split_preview_tex.py --debug-tex $($(1)_DIR)/build/$(1)-debug.tex --manifest $($(1)_MANIFEST) --book-dir $($(1)_DIR) --stem $(1) --out-dir $($(1)_DIR)/build

# Warm every unit's .aux (full master, two passes to settle forward refs) so a
# single-chapter \includeonly resolves cross-chapter references. It is an
# order-only prerequisite of the chapter PDFs below: built once when missing,
# then reused — a Markdown edit must NOT trigger this whole-book pass (that would
# be slower than the debug PDF). Cross-chapter numbers may lag until it is
# rebuilt (delete it, or rebuild the debug PDF); within-chapter refs stay live.
# The splitter invalidates it when the chapter-unit list changes, preventing
# removed or merged chapters from contributing stale duplicate labels.
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
# The index needs entries and page numbers from the complete book. Keep its
# preview tied to the current debug PDF and reuse that PDF's generated index.
$($(1)_DIR)/build/$(1)-preview-_index.pdf: $($(1)_DIR)/build/$(1)-debug.pdf

# This rule precedes the general preview pattern for GNU Make 3.81. The dark
# suffix belongs to the output name, never to the chapter's includeonly key.
$($(1)_DIR)/build/$(1)-preview-_index-dark.pdf: $($(1)_DIR)/build/$(1)-debug-dark.pdf

# Contents must read the complete book's TOC, including its linked destinations.
$($(1)_DIR)/build/$(1)-preview-_contents.pdf: $($(1)_DIR)/build/$(1)-debug.pdf
$($(1)_DIR)/build/$(1)-preview-_contents-dark.pdf: $($(1)_DIR)/build/$(1)-debug-dark.pdf

$($(1)_DIR)/build/$(1)-preview-%-dark.pdf: $($(1)_DIR)/build/$(1)-preview-master.tex | $($(1)_DIR)/build/$(1)-preview-master.aux require-tex
	@echo "  lualatex $(1)-preview-$$*-dark (chapter)"
	$$(Q)cp $($(1)_DIR)/build/$(1)-preview-master.aux $($(1)_DIR)/build/$(1)-preview-$$*-dark.aux
	$$(Q)if [ "$$*" = "_index" ]; then cp $($(1)_DIR)/build/$(1)-debug-dark.ind $($(1)_DIR)/build/$(1)-preview-$$*-dark.ind; fi
	$$(Q)if [ "$$*" = "_contents" ]; then cp $($(1)_DIR)/build/$(1)-debug-dark.toc $($(1)_DIR)/build/$(1)-preview-$$*-dark.toc; fi
	$$(Q)$$(LATEX_LOCK) $$($(1)_PREVIEW_INPUTS) $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$$(abspath $($(1)_DIR)/build) -jobname=$(1)-preview-$$*-dark "\def\BookDarkMode{1}\def\PreviewOnly{$$*}\input{$($(1)_DIR)/build/$(1)-preview-master.tex}"

$($(1)_DIR)/build/$(1)-preview-%.pdf: $($(1)_DIR)/build/$(1)-preview-master.tex | $($(1)_DIR)/build/$(1)-preview-master.aux require-tex
	@echo "  lualatex $(1)-preview-$$* (chapter)"
	$$(Q)cp $($(1)_DIR)/build/$(1)-preview-master.aux $($(1)_DIR)/build/$(1)-preview-$$*.aux
	$$(Q)if [ "$$*" = "_index" ]; then cp $($(1)_DIR)/build/$(1)-debug.ind $($(1)_DIR)/build/$(1)-preview-$$*.ind; fi
	$$(Q)if [ "$$*" = "_contents" ]; then cp $($(1)_DIR)/build/$(1)-debug.toc $($(1)_DIR)/build/$(1)-preview-$$*.toc; fi
	$$(Q)$$(LATEX_LOCK) $$($(1)_PREVIEW_INPUTS) $$(LUALATEX) $$(LUALATEX_BASE_FLAGS) -output-directory=$$(abspath $($(1)_DIR)/build) -jobname=$(1)-preview-$$* "\def\PreviewOnly{$$*}\input{$($(1)_DIR)/build/$(1)-preview-master.tex}"
endef

# $(call book-sourcemap-rules,<stem>): the viewer sourcemap of a book whose
# chapters carry booklink markers, anchored against its debug tex. Booklink
# sources are book-local (the Lean file's own book src), so the emitted paths
# are already book-local and need no rewrite.
define book-sourcemap-rules
$($(1)_DIR)/build/$(1)-sourcemap.json: tools/booklink_sourcemap.py tools/formalization_annotations.py $($(1)_BOOKLINK_LEANS) $($(1)_SKIP_SOURCES) $(BOOKLINK_FILTER_SOURCEMAP) $($(1)_DIR)/build/$(1)-debug.tex | $($(1)_DIR)/build require-mise
	@echo "  viewer-sourcemap $$@"
	$$(Q)$$(PYTHON) tools/booklink_sourcemap.py $($(1)_BOOKLINK_LEANS) --skip-source $($(1)_SKIP_SOURCES) --tex-file $($(1)_DIR)/build/$(1)-debug.tex --injection-map $(BOOKLINK_FILTER_SOURCEMAP) --out $$@

# Keep the marker-band pair fresh together: the debug PDF's anchors and the
# viewer sourcemap's entry numbering both derive from the debug tex, and a
# viewer pointed at a fresh copy of one goes silently wrong when only the
# other was rebuilt (bands land one booklink off). Requesting the debug PDF —
# the routine post-commit build — therefore also freshens the sourcemap.
$($(1)_DIR)/build/$(1)-debug.pdf: $($(1)_DIR)/build/$(1)-sourcemap.json
endef

$(foreach stem,$(BOOK_STEMS),$(eval $(call book-rules,$(stem))))
$(foreach stem,$(BOOK_STEMS),$(eval $(call book-preview-rules,$(stem))))
$(foreach stem,$(BOOK_STEMS),$(if $($(stem)_BOOKLINK_LEANS),$(eval $(call book-sourcemap-rules,$(stem)))))

# Viewer layout variants share canonical TeX/anchors but keep all auxiliary
# files in private build directories. Publish only the requested PDF at the
# flat, allowlisted viewer URL. No variant is part of the default book builds.
VIEWER_LAYOUT_PAPERS := default a4 a5 b5 b6
VIEWER_LAYOUT_FONTS := default 10 11 12

define viewer-layout-rules
$(1)-layout-$(2)-$(3)pt_DIR := $($(1)_DIR)/build/viewer-layout-$(2)-$(3)pt
$(1)-layout-$(2)-$(3)pt_MANIFEST := $($(1)_MANIFEST)
$(1)-layout-$(2)-$(3)pt_CHAPTERS := $($(1)_CHAPTERS)
$($(1)_DIR)/build/viewer-layout-$(2)-$(3)pt_INDEXER = $$($($(1)_DIR)_INDEXER)

$($(1)_DIR)/build/viewer-layout-$(2)-$(3)pt/build/$(1)-layout-$(2)-$(3)pt-debug.tex: $($(1)_DIR)/build/$(1)-debug.tex tools/viewer_layout_tex.py Makefile | require-mise
	$$(Q)$$(PYTHON) tools/viewer_layout_tex.py --source $$< --out $$@ --paper $(2) --font $(3)

$($(1)_DIR)/build/$(1)-layout-$(2)-$(3)pt-%.pdf: $($(1)_DIR)/build/viewer-layout-$(2)-$(3)pt/build/$(1)-layout-$(2)-$(3)pt-%.pdf
	$$(Q)cp $$< $$@.tmp && mv $$@.tmp $$@
endef

define register-viewer-layout
$(eval $(call viewer-layout-rules,$(1),$(2),$(3)))
$(eval $(call book-dir-rules,$($(1)_DIR)/build/viewer-layout-$(2)-$(3)pt))
$(eval $(call book-preview-rules,$(1)-layout-$(2)-$(3)pt))
endef
$(foreach stem,$(BOOK_STEMS),$(foreach paper,$(VIEWER_LAYOUT_PAPERS),$(foreach font,$(VIEWER_LAYOUT_FONTS),$(if $(filter default-default,$(paper)-$(font)),,$(eval $(call register-viewer-layout,$(stem),$(paper),$(font)))))))

# GNU Make 3.81 tries patterns in definition order. Register nested layout
# directories before the general <book>/build/%.pdf rule.
$(foreach dir,$(BOOK_DIRS),$(eval $(call book-dir-rules,$(dir))))

polish-space-ja/build/polish-space-book-ja.tex \
polish-space-ja/build/polish-space-book-ja-debug.tex: $(JA_STRUCTURE_STAMP)

clean:
ifdef CODEX_SETUP
	find $(BUILD_DIR) -mindepth 1 -maxdepth 1 ! -name codex ! -name codex.mk -exec rm -rf {} +
	rm -rf $(sort $(foreach dir,$(BOOK_DIRS),$(dir)/build)) $(BOOKLINK_DIST_DIR) $(VIEWER_BUILD_DIR)
else
	rm -rf $(sort $(BUILD_DIR) $(foreach dir,$(BOOK_DIRS),$(dir)/build)) $(BOOKLINK_DIST_DIR) $(VIEWER_BUILD_DIR)
endif

# Derive common.latex from this Pandoc version rather than freezing an upstream
# partial in the repository. Local font settings remain under tools/pandoc/.
$(PANDOC_TEMPLATE_STAMP): tools/prepare_pandoc_templates.py mise.toml $(wildcard tools/pandoc/templates/*) | require-mise
	$(Q)$(PYTHON) tools/prepare_pandoc_templates.py --output $(PANDOC_DATA_DIR) --pandoc $(MISE) exec -- pandoc
	@touch $@

# === Git worktrees. ===
# `make worktree DIR=../math-wt [BRANCH=name]` creates a linked worktree and
# CoW-clones the gitignored caches (.texlive/, */.lake/, build/ dirs, ...)
# into it, so the new worktree builds without reinstalling TeX Live or
# refetching mathlib. `make worktree-caches` runs just the cache clone inside
# an existing worktree (setup.sh also self-heals this); it is a no-op in the
# main checkout and never touches caches that already exist.
worktree:
	@test -n "$(DIR)" || { echo "usage: make worktree DIR=../path [BRANCH=name]" >&2; exit 1; }
	@if [ -n "$(BRANCH)" ] && ! git rev-parse --verify --quiet refs/heads/$(BRANCH) >/dev/null; then \
		git worktree add -b $(BRANCH) $(DIR); \
	else \
		git worktree add $(DIR) $(BRANCH); \
	fi
	@cd $(DIR) && $(CURDIR)/tools/worktree_caches.sh --fresh

worktree-caches:
	@tools/worktree_caches.sh

setup:
	$(if $(CODEX_SETUP),bash tools/setup_codex.sh --dry-run,./setup.sh --dry-run)

setup-run:
	$(if $(CODEX_SETUP),bash tools/setup_codex.sh --run,./setup.sh --run)

doctor:
	$(if $(CODEX_SETUP),bash tools/setup_codex.sh --doctor,./setup.sh --doctor)

test: test-haskell test-python test-node test-highlights test-notation-index test-debug-anchors

test-haskell: $(FILTER_BIN) require-mise
	$(CABAL) test book-filter-golden --builddir=$(BUILD_DIR) $(CABAL_GMP_FLAGS)

test-notation-index: require-mise require-tex
	$(Q)$(PYTHON) tests/check_notation_index.py --lualatex '$(LUALATEX)' --makeindex '$(MAKEINDEX)'

test-debug-anchors: require-mise require-tex
	$(Q)$(PYTHON) tests/check_debug_anchors.py --lualatex '$(LUALATEX)'

test-python: $(FILTER_BIN) require-mise
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
test-e2e: $(PART1_VIEWER_MAP) $(if $(PART1_VIEWER_MAP),polish-space-part1-ja/build/polish-space-part1-ja-debug.pdf)
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

.PHONY: viewer-node-types
viewer-node-types: $(VIEWER_SERVER_NODE_MODULES)/.viewer-dependencies

$(VIEWER_SERVER_NODE_MODULES)/.viewer-dependencies: $(VIEWER_SERVER_DIR)/package.json $(VIEWER_SERVER_DIR)/package-lock.json | require-mise
	@if [ -L "$(VIEWER_SERVER_NODE_MODULES)" ]; then unlink "$(VIEWER_SERVER_NODE_MODULES)"; fi
	@$(NPM) ci --prefix "$(VIEWER_SERVER_DIR)" --ignore-scripts --no-audit --no-fund
	@touch $@

# lint / lint-fix / format delegate to lefthook, which runs the per-tool
# subtargets below as a `parallel: true` group (defined in lefthook.yml) and
# renders a colored per-command pass/fail summary. lefthook aggregates failures
# instead of stopping at the first, so one run surfaces every problem. The make
# layer stays the single source of truth for tool paths and target lists, and
# still builds the book-filter prerequisite before the parallel group so the
# concurrent commands never race on it.
# --no-auto-install keeps these runs from re-syncing git hooks as a side effect.
#
# Each subtarget runs its tool with quiet flags (prettier --log-level warn,
# ruff -q, fourmolu -q, taplo via RUST_LOG=warn) so a clean run stays terse and
# only real findings surface under lefthook's summary.
lint: $(FILTER_BIN) require-mise
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

# Check source identities and notation bindings without rendering a book.
lint-definitions: require-mise
	@$(NODE) $(VIEWER_SERVER_DIR)/definition-audit.ts

lint-tsc: viewer-node-types require-mise
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
	@$(foreach stem,$(BOOK_EDITABLE_STEMS),$(FILTER_BIN) lint --fix --macros=$($(stem)_DIR)/tex/macros.tex --max-line-length=$(BOOK_LINE_LENGTH) --max-reports=$(LINT_MAX_REPORTS) $($(stem)_INPUTS) &&) :

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

# Fast iterative checks: Lake handles dependency freshness; no cache-get step.
validate-lean: require-mise
	$(Q)$(PYTHON) tools/validate_lean.py $(foreach proj,$(LEAN_PROJECTS),--project $(proj)) $(foreach module,$(LEAN_MODULES),--module $(module))

.PHONY: validate-lean

# One chapter is migrated at a time. Unknown configurations fail explicitly.
CHAPTER ?= polish-spaces
validate-correspondence: require-mise
	$(PYTHON) tools/chapter-correspondence/validate.py --chapter "$(CHAPTER)" $(CORRESPONDENCE_FLAGS)

suggest-correspondence: require-mise
	$(PYTHON) tools/chapter-correspondence/suggest.py --chapter "$(CHAPTER)"

.PHONY: validate-correspondence suggest-correspondence

lean: require-mise
	@for proj in $(LAKE_PROJECTS); do \
	  echo "==> lean: $$proj"; \
	  ( cd $$proj && $(MISE) exec -- lake exe cache get && $(MISE) exec -- lake build ) || exit 1; \
	done

# Report book-source regions (statement environments and prose paragraphs) not
# yet covered by a Lean booklink, scanning every Lean file that carries booklink
# markers. Pass extra flags via BOOKLINK_COVERAGE_ARGS, for example
# `make booklink-coverage BOOKLINK_COVERAGE_ARGS='--statements-only'`.
booklink-coverage: tools/booklink_coverage.py tools/booklink_sourcemap.py tools/formalization_annotations.py $(BOOKLINK_LEANS) $(BOOKLINK_SOURCES) | require-mise
	$(PYTHON) tools/booklink_coverage.py $(BOOKLINK_LEANS) $(BOOKLINK_COVERAGE_ARGS)

FORCE:

.PHONY: clean tex test test-notation-index test-debug-anchors test-haskell test-python test-node test-highlights test-e2e notices lint lint-fix format \
	lint-book lint-definitions lint-tsc lint-prettier lint-ruff lint-fourmolu lint-hlint lint-oxlint lint-shell lint-taplo lint-actionlint \
	fix-book fix-prettier fix-ruff fix-fourmolu fix-oxlint fix-shell fix-taplo format-ruff format-shfmt \
	lean booklink-coverage viewer-build dist setup setup-run doctor worktree worktree-caches require-mise require-tex require-po4a \
	translation-ja-update-catalogs translation-ja-generate translation-ja-check translation-ja-sync lint-translation \
	pdfs list-books debug-pdfs preview-warm formalization-viewer treesitter-assets publish FORCE

# Japanese index display names also depend on the terminology catalog.
polish-space-ja/build/polish-space-book-ja.tex polish-space-ja/build/polish-space-book-ja-debug.tex polish-space-ja/build/polish-space-book-ja-preview-master.tex: polish-space-ja/l10n/glossary-ja.yaml
