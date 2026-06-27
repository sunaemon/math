# Agent Notes

## Writing Style

Avoid parenthesized section references in running prose unless the reference is genuinely secondary. Prefer making the section reference part of the sentence, such as "the construction in §{sec:...}" or "by §{sec:...}", instead of appending "(§{sec:...})" after a phrase.

Avoid prose parentheticals when they carry mathematical content or reading guidance. Fold the content into the sentence instead, or split it into a new sentence. Reserve parentheses for notation, short clarifications, and genuinely secondary asides.

Prefer natural predicate phrasing over blunt nominalizations when referring to mathematical properties. For example, write "§{sec:...} proves that this space is Polish" instead of "Polishness is shown in §{sec:...}" when the latter reads too compressed or abrupt.

## Build Workflow

This project builds each discovered `<book>/src/*.md` file through Pandoc and `tools/book-filter/Main.hs`. This `AGENTS.md` is shared between two checkouts, so name them explicitly rather than saying "this repo": the **private repo (`sunaemon/math-private`)** carries the full book under `polish-space/` (stem `polish-space-book`) alongside the chapter excerpt under `polish-space-ch1/` (stem `polish-space-ch1`), while the **public export (`sunaemon/math`)** ships only `polish-space-ch1` — there `polish-space/` holds just the shared `tex/` and the symlinked sources that excerpt needs, so no full-book build target exists. Books are discovered from per-book manifests, so the set present depends on the checkout: run `make list-books` in the current checkout to list them as `<stem> <book-dir> <master-source>`, and pick build targets from the books it reports rather than from a fixed name. Build targets named `polish-space/build/polish-space-book-*` below therefore work only in the private repo, while the `polish-space-ch1/build/polish-space-ch1-*` targets and plain `make`/`make lean` work in both.

Run repository build targets with plain `make`. Do not prefix build commands with a custom `PATH` or `TEXMFVAR`; `setup.sh` and the `Makefile` are responsible for finding `mise` and providing TeX with a writable cache path. If a plain `make` build fails because a tool cannot be found or because LuaLaTeX has no writable cache, fix `setup.sh` or `Makefile` instead of working around it in the command line.

The `book-build` and `book-section-review` skills referenced below live under `.codex/skills/` and are available to Codex. Agents without those skills (for example Claude Code, which discovers skills from `.claude/skills/`) should run the equivalent plain `make` commands instead: TeX-only verification is `make <book-dir>/build/<stem>.tex` (always available, `make polish-space-ch1/build/polish-space-ch1.tex`; in the private repo the full book is also `make polish-space/build/polish-space-book.tex`); the routine rendered check is a single chapter preview, `make <book-dir>/build/<stem>-preview-<chapter>.pdf` (where `<chapter>` is the edited chapter source's basename, e.g. `polish-spaces`); the post-commit debug render is `make <book-dir>/build/<stem>-debug.pdf`. Follow the same reporting contract either way.

In the private repo, the full-book master `polish-space/src/polish-space-book.md` is formatted as an A5 `book` document with `10pt`, `twoside`, and `openright` class options. Keep book-format changes in a book's master-source YAML header unless there is a strong reason to change the Pandoc template or the document class.

After changing a source file such as `polish-space/src/polish-space-book.md` or `polish-space-ch1/src/polish-space-ch1.md`, run the `book-build` workflow in TeX-only mode for the matching source and follow the TeX reporting contract. Also run this TeX-only verification before the final response after user-facing edits to `polish-space/tex/macros.tex`, `polish-space/tex/references.bib`, `tools/book-filter/Main.hs`, `Makefile`, `setup.sh`, or other build-pipeline files that affect a rendered `<book>/src/*.md` document. Build the affected source when it is clear; otherwise build the most comprehensive book the current checkout provides — the full `polish-space` book in the private repo, `polish-space-ch1` in the public export — because it exercises the shared macros, filter, bibliography, and build rules. The TeX target is the quick verification step for Markdown/Pandoc/citation issues. Do not start the normal whole-book PDF in the background as routine verification; the single-chapter preview PDF is the routine rendered check.

If a whole-book PDF build is still running from an earlier task, continue responding to the prompt and check/report the PDF result only when it becomes relevant. Do not wait on it merely because an iterative edit was made.

Do not build a normal release PDF as routine verification. A book's release PDF is `<book-dir>/build/<stem>.pdf` — `polish-space/build/polish-space-book.pdf` in the private repo — and it is the final-release artifact; build it only when the user explicitly asks for the release PDF.

After creating a commit that affects a rendered book source, `polish-space/tex/macros.tex`, `polish-space/tex/references.bib`, `tools/book-filter/Main.hs`, or the build pipeline, build the affected book's debug PDF instead with `make <book-dir>/build/<stem>-debug.pdf`. For the full book in the private repo, run:

```sh
make polish-space/build/polish-space-book-debug.pdf
```

In the public export the only book is `polish-space-ch1`, so run `make polish-space-ch1/build/polish-space-ch1-debug.pdf` there. Report whether the debug PDF build passed and link the generated file, such as `polish-space/build/polish-space-book-debug.pdf` or `polish-space-ch1/build/polish-space-ch1-debug.pdf`.

When the formalization viewer (`make formalization-viewer`) is running, it auto-rebuilds the rendered PDF currently selected in its PDF pane on any `<book>/src/**.md` change — the debug PDF together with its sourcemap, or the per-chapter preview PDF (the **Chapter preview** entry, which follows the chapter in the Markdown pane), whichever is selected; the release PDF is never auto-built. So with the viewer running, the PDF you are viewing already tracks your edits, the preview and debug renders are each current when selected, and the post-commit `make <book-dir>/build/<stem>-debug.pdf` is an incremental no-op freshness check. Still run that explicit build: it is a real build for headless/agent runs that have no viewer and after non-`.md` changes such as `polish-space/tex/macros.tex`, `polish-space/tex/references.bib`, `tools/book-filter/Main.hs`, or the build pipeline, which the auto-build does not watch, and it remains the booklink-straddle gate before a PR.

During iterative editing of a `<book>/src/*.md` document, do not render the normal whole-book PDF or the debug PDF after every source edit unless the user explicitly asks for it. For each iteration, run the required quick TeX verification in TeX-only mode and render the edited chapter's preview PDF, then stop and ask the user to review it or provide the next prompt. Treat the debug PDF as the post-commit rendered artifact: after committing changes that affect the rendered book or build pipeline, build the affected book's debug PDF, `make <book-dir>/build/<stem>-debug.pdf`. For the full book in the private repo, run:

```sh
make polish-space/build/polish-space-book-debug.pdf
```

and in the public export run `make polish-space-ch1/build/polish-space-ch1-debug.pdf`. Report whether that post-commit debug PDF build passed and link the generated file, such as `polish-space/build/polish-space-book-debug.pdf` or `polish-space-ch1/build/polish-space-ch1-debug.pdf`.

After finishing any user-facing edit to a `<book>/src/*.md` file, render the edited chapter's preview PDF unless the user explicitly asks not to: `make <book-dir>/build/<stem>-preview-<chapter>.pdf`, where `<chapter>` is the edited file's basename. This splits the already-built debug tex into an `\includeonly` master and renders just that chapter (a few pages, ~1s), carrying the same booklink/skip anchors as the debug PDF. The first preview after a fresh build also warms the cross-reference aux once (`make preview-warm` pre-warms it). At the end of the response, report whether the build passed and link the generated preview PDF, such as `polish-space/build/polish-space-book-preview-polish-spaces.pdf` in the private repo or `polish-space-ch1/build/polish-space-ch1-preview-polish-spaces.pdf` in the public export, and ask the user to review the result.

Use low-reasoning subagents for build-only work only when the user has explicitly allowed delegation in the current task and the build is non-blocking or independently summarizable. Otherwise run the relevant helper locally and report its summarized result. Keep immediate TeX verification in the main workflow through `book-build`, because later edits often depend on those diagnostics. If a build failure requires mathematical or structural judgment, inspect the relevant diagnostics in the main agent before deciding how to fix it.

## Index and Notation Workflow

The PDF build runs `makeindex` when an `.idx` file exists. The main source uses `makeidx` and prints the combined index at the end of the book. Do not hand-edit generated files under `build/`; update the source, `polish-space/tex/macros.tex`, `tools/book-filter/Main.hs`, or `Makefile` instead.

Use semantic macros for nontrivial mathematical notation instead of repeating raw LaTeX. Define the rendering in `polish-space/tex/macros.tex`, use the macro in the relevant `<book>/src/*.md` file, and add the macro name to the YAML `notation-watch` list when first-use tracking or notation-indexing should apply.

Before writing or rewriting notation-heavy prose, check the relevant definition in `polish-space/tex/macros.tex` instead of guessing how a macro renders. Do not expand a semantic macro again in the surrounding prose unless the equality itself is mathematically part of the sentence.

Prefer descriptive semantic macros in `polish-space/tex/macros.tex` for mathematical notation whenever practical. Use macros for constructions, restrictions, relations, spaces, coding devices, and recurring decorated symbols instead of repeating raw visual LaTeX such as subscripts, superscripts, font choices, or ad hoc delimiters throughout the source. For example, use a semantic restriction macro for genuine restricted standard sets, while remembering that this project takes `\NN` to include `0`, so `\RestrictedSet{\NN}{\ge 0}` should just be `\NN`.

Design semantic macros around mathematical concepts, not around incidental visual styling. A macro should abstract the operation, relation, construction, or named object it denotes; it should not silently manufacture part of an argument's mathematical name. In particular, keep object names and their chosen fonts in the source argument unless the macro itself is explicitly a naming macro.

For example, a Hom-set macro represents the notation "category-name applied to domain and codomain." The category name is an argument:

```tex
\HomSet{\mathcal C}{A}{B}
```

and the macro definition should preserve that separation:

```tex
\newcommand{\HomSet}[3]{#1(#2,#3)}
```

Do not define it as `\mathcal{#1}(#2,#3)`, because that mixes the category-name convention with the Hom-set construction. The same principle applies broadly: `\functorCat{\mathcal C}{\mathcal D}` may render as `\mathcal D^{\mathcal C}`, while `\mathcal C` and `\mathcal D` remain the category names supplied by the caller; `\catExp{A}{B}` may render as `B^A`, while `A` and `B` remain the objects supplied by the caller.

For watched notation, place a `mathmeta` `\define{name}` directive before the first mathematical use. Multiple names may be defined together, for example:

```tex
\begin{mathmeta}
  \define{bSigma,bPi,bDelta}
\end{mathmeta}
```

The Pandoc filter enforces this order and fails the build if watched notation appears before its `\define` directive.

When a notation must appear before the place where it is actually defined and indexed, place a `mathmeta` `\forward{name}` directive before the early use and keep `\define{name}` at the real definition. `\forward` only opens the first-use gate; it does not emit the notation-index entry.

Notation index display strings are derived from `polish-space/tex/macros.tex`. For macros whose index display cannot be inferred cleanly, put a comment immediately before the macro definition:

```tex
% notation-index: $\HomSet{\mathcal C}{A}{B}$
\newcommand{\HomSet}[3]{#1(#2,#3)}
```

The `Notation` block in the index is sorted before ordinary English index entries. It should render mathematical notation, not bare macro names.

## Term Index Workflow

Use semantic term macros for important terminology instead of raw bold text plus a separate `\index{...}` entry.

Use `\termdefine{term}` at the place where the text explicitly defines `term`. It renders the term in bold, links it to the term-index anchor, and records the "defined in" index entry.

Use `\termdefineas{term}{display}` when the defined term and the printed words differ. The first argument is the canonical index key and anchor; the second argument is what appears in the prose. For example:

```tex
A set is \termdefineas{nowhere dense set}{nowhere dense} if ...
```

Use `\termuse{term}` for later uses when the printed words are the same as the canonical term. It links to the definition and records a "referenced by" index entry.

Use `\termuseas{term}{display}` for later uses when the printed words differ from the canonical term. For example:

```tex
two \termuseas{meager set}{meager sets}
```

Do not use obsolete alias macros such as `\termidefine`, and do not write two-argument `\termuse{term}{display}`. The supported alias forms are `\termdefineas{term}{display}` and `\termuseas{term}{display}`.

## Theorem and Proof Workflow

Use the `amsthm` environments defined in `polish-space/tex/macros.tex` for genuine mathematical statements and proofs instead of raw Markdown bold labels. Prefer direct environment use in `*.md` source:

```tex
\begin{theorem*}[Name]
...
\end{theorem*}

\begin{proof}[Proof]
...
\end{proof}
```

For a named theorem whose heading is also the canonical term definition, put the term macro in the optional theorem title:

```tex
\begin{theorem*}[\termdefineas{Alexandrov's theorem}{Theorem (Alexandrov)}]
...
\end{theorem*}
```

The filter strips the environment heading from the display part before emitting the amsthm title, so this renders as a normal theorem heading while the term index anchor is attached to the theorem name.

Index theorem and lemma headings when the title is a stable named result, law, dichotomy, embedding, representation theorem, uniformization theorem, or a reusable internal lemma that later prose treats as infrastructure. Leave purely descriptive local bookkeeping titles plain unless they are intended lookup terms. When a sentence immediately before the theorem names the result informally, use `\termforward` there and keep `\termdefine` or `\termdefineas` in the theorem heading.

The available unnumbered statement environments are `theorem*`, `lemma*`, `proposition*`, `corollary*`, `claim*`, `fact*`, `recall*`, `definition*`, `example*`, `construction*`, `remark*`, and `statement*` for a genuinely custom heading. Use `proof` for proofs. Keep ordinary list labels, table labels, and short explanatory labels as prose unless they are real theorem/proof structure. Do not introduce raw labels such as `**Theorem.**`, `**Lemma.**`, `**Claim.**`, `**Corollary.**`, or `**Proof.**`, and do not reintroduce `\statementlabel`, `\prooflabel`, or command-form theorem wrappers.

## Lean Formalization Workflow

### Comment categories

Respect Lean's comment system and reserve a distinct marker for machine-targeted metadata. A comment is **machine metadata** when it is written for tooling or LLM consumption rather than a human reader; write it as an ordinary block comment whose body starts with `@`, that is `/-@ … -/`. The `@` sentinel keeps it distinct from Lean's doc comments (`/--`, `/-!`) and from human prose comments (`/- … -/`), and the formalization viewer folds `/-@ … -/` comments by default. Booklink markers use this form, `/-@ booklink: … -/`, and `tools/booklink_sourcemap.py` parses that opener. Keep genuine documentation in Lean's doc-comment syntax (`/--`, `/-!`) and human prose in plain `/- … -/`; do not fold or remarker those.

When formalizing book claims in Lean, make the Lean proof correspond to the proof written in the relevant `.md` source by default. Use the same main construction, intermediate reductions, named sets, metric choices, and proof direction whenever Lean reasonably permits it.

Formalization is also a tool for checking the book. If the Lean work exposes a mathematical error, a missing hypothesis, a hidden case split, or a genuinely cleaner proof, update the book proof instead of forcing Lean to follow the weaker text. In that case, make the `.md` proof and the Lean proof converge on the improved argument. Otherwise, keep the Lean development aligned with the book's notation and proof structure.

The formalization target is the mathematical content that the chapter actually proves or uses as local infrastructure. Do not treat clearly cited external theorems, motivational examples, broad classification results, or side remarks as proof gaps merely because they are mentioned in prose. Examples include Anderson--Kadec-type homeomorphism theorems, large-inductive or covering-dimension comparison theorems when the chapter only uses the clopen-basis characterization, and illustrative non-closure warnings such as quotient spaces unless the chapter presents a concrete proof or later depends on that result.

When comparing `.md` and Lean, distinguish "not formalized but out of scope" from "missing proof." A claim is in scope when it is stated as a theorem, claim, construction, proof step, example/non-example with an argument, or a lemma later used by the chapter. A claim is normally out of scope when it is explicitly cited to external literature, deferred to another chapter, included only as context, or names a standard background result whose proof is not part of this chapter's argument.

Use mathlib's canonical definitions for standard mathematical properties in theorem statements and public-facing Lean APIs. When the book states an equivalent formulation, such as "zero-dimensional" versus "has a clopen basis", add and use an explicit equivalence theorem connecting the mathlib definition to the book formulation. Prove via the book formulation after rewriting through that equivalence, rather than replacing the public statement with a local ad hoc predicate.

Do not replace a book proof by a one-line mathlib theorem, instance search, or a materially different argument merely because it proves the same final statement. Mathlib results may be used for standard local facts and infrastructure, but if the book explicitly proves a claim, also formalize that proof once in Lean, even if later callers use an equivalent mathlib theorem.

When the Lean proof must deviate from the book proof because of library constraints, make the deviation explicit in the surrounding code structure or report it to the user. Prefer adding helper lemmas that expose the book's implicit steps over hiding them behind broad automation.
