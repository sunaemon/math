# Mathematical Books

A collection of mathematical books written in Markdown and compiled to PDF via Pandoc and a custom Haskell filter, with accompanying Lean formalizations and a browser-based formalization viewer.

The formalization viewer is published live at <https://sunaemon.dev/math/>.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/sunaemon/math)

Launch a cloud dev environment from the badge above; it provisions the toolchain automatically (the devcontainer runs `make setup-run` on create). Pick at least an 8-core machine; the default 2-core Codespace makes provisioning (TeX Live, GHC, and friends) painfully slow.

## Setup

Preview the one-time setup commands:

```sh
make setup
```

Run the setup for real:

```sh
make setup-run
```

Check that the setup is already usable:

```sh
make doctor
```

The underlying `setup.sh` script is dry-run by default; the Makefile exposes that as `make setup`.

`mise` must be on your `PATH` for `make` to work; if `make` reports it missing, re-run setup and restart your shell.

## Building

Build everything:

```sh
make
```

Build a single document (run `make list-books` to see the available `<book>` and `<stem>` names):

```sh
make <book>/build/<stem>.pdf
```

The normal `build/*.pdf` targets are release builds: they omit SyncTeX debug output and clear stale SyncTeX sidecars.
Use targets such as `make <book>/build/<stem>-debug.pdf` only for diagnostic PDFs with visible hyperlink borders.

Generate debug PDFs for every discovered book manifest:

```sh
make debug-pdfs
```

Render a single chapter for a fast preview (a few pages via `\includeonly`, split
from the debug tex), or pre-warm every book's preview cross-reference aux:

```sh
make <book>/build/<stem>-preview-<chapter>.pdf
make preview-warm
```

Clean build artifacts:

```sh
make clean
```

## Checks and tools

Run the Haskell golden tests and Python unit tests:

```sh
make test
```

Run the source linter and viewer TypeScript check:

```sh
make lint
```

Apply automatic lint fixes where supported:

```sh
make lint-fix
```

Run the formalization viewer:

```sh
make formalization-viewer
```

It prints the URL it bound to and serves every discovered project at its own mount.

## Pipeline

```
<book>/src/<stem>.json + <book>/src/<stem>.md + chapter inputs
  → pandoc (with book-filter + citeproc)
  → <book>/build/<stem>.tex
  → <book>/build/<stem>.pdf (via lualatex and makeindex when needed)
```

Every `*/src/*.json` manifest defines one book. The manifest names the master source and chapter inputs, and `make` discovers these manifests automatically; run `make list-books` to see the discovered book projects.

`tools/book-filter/Main.hs` is a custom pandoc filter that checks watched notation, emits notation index entries and hyperlinks, resolves `§{sec:...}` section references, and supports local mathematical declaration metadata. Each book carries its own TeX support under `<book>/tex/` (`macros.tex`, `references.bib`); an excerpt book symlinks its `tex/` at the book it extracts.

## License

Different parts of this repository are licensed under different terms, with vendored third-party components retaining their own upstream licenses:

- **Source code** (build tooling, `tools/`, Lean and Python sources) — MIT License, see [LICENSE-MIT](LICENSE-MIT).
- **Written content** (Markdown book sources, TeX prose, figures, and rendered PDFs) — Creative Commons Attribution 4.0 International (CC BY 4.0), see [LICENSE-CC-BY-4.0](LICENSE-CC-BY-4.0).
- **Third-party components** under `tools/formalization-viewer/vendor/` are not covered by the above; see [tools/formalization-viewer/vendor/THIRD-PARTY-NOTICES.md](tools/formalization-viewer/vendor/THIRD-PARTY-NOTICES.md).

See [LICENSE](LICENSE) for the overview.
