# Agent Notes

## Writing Style

Avoid parenthesized section references in running prose unless the reference is genuinely secondary. Prefer making the section reference part of the sentence, such as "the construction in §{sec:...}" or "by §{sec:...}", instead of appending "(§{sec:...})" after a phrase.

Avoid prose parentheticals when they carry mathematical content or reading guidance. Fold the content into the sentence instead, or split it into a new sentence. Reserve parentheses for notation, short clarifications, and genuinely secondary asides.

Prefer natural predicate phrasing over blunt nominalizations when referring to mathematical properties. For example, write "§{sec:...} proves that this space is Polish" instead of "Polishness is shown in §{sec:...}" when the latter reads too compressed or abrupt.

## Persistent Book Policies

Keep mathematical changes synchronized between the Lean proof, the canonical English text, and the Japanese translation in the same work batch. When formalization changes a construction, hypothesis, or proof, reflect it in both languages. Maintain Japanese translations through the PO catalogs and synchronization workflow below; do not edit generated Japanese Markdown directly. Keep terminology decisions in `polish-space-ja/l10n/README.md` and `glossary-ja.yaml` rather than relying on chat history.

Use lambda calculus as the book's computation model, in both prose and formalization. Computational constructions must be backed by lambda terms and beta/query derivations, preserving their parameters and distinguishing existence from computable selection. Do not introduce a second programming language or machine model as a substitute for these realizers. Ordinary mathematical infrastructure in Lean need not be executable lambda code.

Defer typesetting and visual review, review-coverage reconciliation, and page-break tuning until the pre-publication pass or an explicit user request. Routine editing checks build results and current diagnostics, including the required TeX and post-commit debug PDF validation; a successful build is not visual approval. Do not inspect PDF pages, clear or refresh `typesettingReview` flags after each edit, or dispatch review-status bookkeeping during routine work. Preserve existing review flags as prior review records and reconcile them against the final publication sources during the final pass. Mathematical correctness and translation review remain part of the normal editing workflow.

Do not build chapter-preview PDFs during routine editing, and do not stop for preview approval. Run the required TeX checks while iterating and the debug PDF validation after commits. Build a chapter preview or release PDF only when explicitly requested. This policy also applies when a skill describes a preview or release build as its default.

On continuation, use `todo.md`, the current source files, Git state, and current validation reports as the evidence. Keep handoff notes limited to the unfinished work, unresolved proof issues, and live process handles that cannot be recovered safely from the files. Do not repeat source-size counts or standalone reference audits routinely; run them when requested or relevant to the actual change. Treat recorded policies as settled on continuation: do not answer the same resolved question again or seek renewed confirmation. Report new changes, validation results, and unresolved issues unless the user explicitly asks to revisit the decision.

Use `todo.md` as the current backlog for the book goal. Keep unfinished work only; completion reports and implementation history belong in Git. Every carried-over task must correspond to an unfinished TODO item; record newly discovered necessary work there before carrying it into another turn. A new explicit user request can be handled immediately. Old conversation requests and handoff summaries are not independent task queues: do not reopen completed or withdrawn work from them without a new user request or concrete new evidence of a defect. Keep translation review history in Git, not in cumulative notes in `translation-status.json`; that file records only the current review status and source provenance. Conditional TODO items become active only when their stated condition applies.

## Planning major TODO items

Work through applicable items in `todo.md` from top to bottom by default. If dependencies, shared work, or other concrete evidence show that another order is more efficient, reorder `todo.md` as soon as that becomes clear, before proceeding in the revised order. Keep the file's order aligned with the actual execution plan rather than silently working out of order. Continue to respect conditions on deferred items and explicit user priorities.

Before starting a major item in `todo.md`, first assess whether it can be handled more efficiently by creating or reusing a skill and delegating bounded work to an appropriate model, or by writing and running a script for repeatable operations. Choose the model and reasoning level to match the work's difficulty, required judgment, and verification needs. When this approach is useful, prepare the skill or script before doing the substantive work, specify its inputs, scope, outputs, and checks, and then use it. Briefly state the chosen approach; do not create a skill, script, or delegation merely for ceremony. Follow the task-specific model routing and review boundaries below, and verify delegated or automated results before treating the TODO item as resolved.

## Lightweight book maintenance

For bounded review-status reconciliation or summaries of existing validation
reports, use `.codex/skills/book-maintenance/SKILL.md` and delegate the scoped
work to `gpt-6-luna` with low reasoning. The user has requested this routing for
book maintenance. Keep fresh visual review, mathematical judgments, and proof
correspondence in the main workflow. The skill defines the evidence and edit
boundaries; it does not replace `book-build` or authorize unrelated delegation.

## Build Workflow

This project builds each discovered `<book>/src/*.md` file through Pandoc and `tools/book-filter/Main.hs`. This `AGENTS.md` is shared between two checkouts, so name them explicitly rather than saying "this repo": the **private repo (`sunaemon/math-private`)** carries the full book under `polish-space/` (stem `polish-space-book`) alongside the chapter excerpt under `polish-space-ch1/` (stem `polish-space-ch1`), while the **public export (`sunaemon/math`)** defaults to the complete English book and the first-chapter excerpt. An explicit excerpt-only export still contains only the shared `tex/` and source files its symlinks need under `polish-space/`. Books are discovered from per-book manifests. Run `make list-books` in the current checkout to list them as `<stem> <book-dir> <master-source>` and select the available build targets.

Run repository build targets with plain `make`. Do not prefix build commands with a custom `PATH` or `TEXMFVAR`; `setup.sh` and the `Makefile` are responsible for finding `mise` and providing TeX with a writable cache path. If a plain `make` build fails because a tool cannot be found or because LuaLaTeX has no writable cache, fix `setup.sh` or `Makefile` instead of working around it in the command line.

The Codex skills live under `.codex/skills/`: `book-build` validates book builds, `book-section-review` reviews a named section, `book-proof-inventory` retrieves existing Lean interfaces, and `book-maintenance` summarizes validation evidence. Claude Code's review adapter lives under `.claude/skills/book-section-review/`, with fact-gathering in `.claude/skills/book-section-mechanical-checks/`. Both review adapters use the canonical checklist in `tools/book-section-review-checklist.md` and the shared extractor `tools/extract_book_section.py`; only model routing and invocation mechanics differ. Use `book-build` in TeX-only mode during editing. Agents without that skill should run the same plain `make validate-tex BOOKS="<stem> ..."` target. Use `make validate-debug BOOKS="<stem> ..."` for the post-commit rendered check, as detailed below.

### Japanese translation

The private repo also contains the peer Japanese book under `polish-space-ja/`, with stem `polish-space-book-ja`. English remains the canonical mathematical source. Japanese prose for translated chapters is maintained in `polish-space-ja/l10n/ja/*.po`; the corresponding Markdown under `polish-space-ja/src/polish-space-book/` is generated and committed so ordinary book builds stay self-contained. Edit the PO catalogs rather than the generated Japanese Markdown, then run `make translation-ja-sync` to refresh catalogs, reject incomplete translations, regenerate the translated chapters, and verify labels, citations, mathematics, theorem structure, notation metadata, canonical term identities, and the recorded English source blobs. After an English edit, run `make translation-ja-update-catalogs`, review and unfuzzy the affected entries, and update `translation-status.json` only after that review. `make lint-translation` performs a read-only temporary render and checks the committed mirror.

All chapters and appendices have Japanese draft translations maintained in PO catalogs; none currently falls back to an English-source symlink. Current translation review status and source provenance live in `polish-space-ja/l10n/translation-status.json`. The Japanese book remains excluded from the default release-PDF aggregate through the historical `PILOT_BOOK_STEMS` selector, but it is available in the formalization viewer at the `polish-space-ja` mount. `tools/project_translation_sourcemap.py` projects canonical English booklinks onto PO-message spans in translated chapters, refines a span to the aligned sentence when the English and Japanese sides split into equally many sentences whose inline formula and section-reference anchors agree, and keeps exact offsets for the English fallback symlinks; do not bypass this projection with English offsets. When a chapter preview is explicitly requested, render translated chapters with `make polish-space-ja/build/polish-space-book-ja-preview-preface.pdf` and `make polish-space-ja/build/polish-space-book-ja-preview-polish-spaces.pdf`. Describe the Japanese edition according to its current review status; complete draft coverage alone does not establish publication readiness.

In the private repo, the full-book master `polish-space/src/polish-space-book.md` is formatted as an A5 `book` document with `10pt`, `twoside`, and `openright` class options. Keep book-format changes in a book's master-source YAML header unless there is a strong reason to change the Pandoc template or the document class.

After changing a source file such as `polish-space/src/polish-space-book.md` or `polish-space-ch1/src/polish-space-ch1.md`, run the `book-build` workflow in TeX-only mode for the matching source and follow the TeX reporting contract. Also run this TeX-only verification before the final response after user-facing edits to `polish-space/tex/macros.tex`, `polish-space/tex/references.bib`, `tools/book-filter/Main.hs`, `Makefile`, `setup.sh`, or other build-pipeline files that affect a rendered `<book>/src/*.md` document. Build the affected source when it is clear; otherwise build the most comprehensive book the current checkout provides — the full `polish-space` book in the private repo, `polish-space-ch1` in the public export — because it exercises the shared macros, filter, bibliography, and build rules. The TeX target is the quick verification step for Markdown/Pandoc/citation issues. Follow Persistent Book Policies when selecting PDF artifacts. The rendered check is the post-commit debug validation.

If a whole-book PDF build is still running from an earlier task, continue responding to the prompt and check/report the PDF result only when it becomes relevant. Do not wait on it merely because an iterative edit was made.

As specified in Persistent Book Policies, a book's release PDF is `<book-dir>/build/<stem>.pdf` — `polish-space/build/polish-space-book.pdf` in the private repo — and it is the final-release artifact; build it only when the user explicitly asks for the release PDF.

For warning checks, inspect the final logs of the exact targets verified in the current task, plus their TeX-generation logs. Do not scan all historical `build/*.log` files and report old release, chapter-preview, or viewer diagnostics as current failures. After a fresh full debug build succeeds, remove superseded diagnostic logs from older builds when they are no longer needed; retain the current debug and TeX-generation logs, and never remove diagnostics from a running build or an unresolved failure. Log cleanup must not delete PDFs, sources, or build caches.

Use `make validate-tex BOOKS="<stem> ..."` for the required TeX-only workflow and `make validate-debug BOOKS="<stem> ..."` for the post-commit debug build and warning check. Omitting `BOOKS` selects every discovered book. These targets run the same plain `make` builds, check exit codes and current target diagnostics, and save the commands, durations, log snapshots, and result in a unique `build/validation/<run>/report.json`. The `book-build` helper delegates its TeX-only mode to this runner. Read its compact result first and inspect detailed logs only on failure; do not repeat the build or write ad hoc log scanners after a passing result. Debug validation includes final-pass LaTeX and index checks; temporary rerun warnings from earlier passes are not failures. Validation never builds release or chapter-preview PDFs, runs lint or Lean, commits, pushes, or deletes logs. Choose additional checks according to the actual change.

For iterative Lean checks, use `make validate-lean LEAN_PROJECTS=polish-space LEAN_MODULES="PolishSpaceBook.Module ..."`. Select the actual project in the current checkout; omit `LEAN_MODULES` to check its default targets, and omit both variables to check every discovered Lake project. This runner uses incremental `lake build`, records exit codes, elapsed time and fresh logs in `build/validation/<run>/report.json`, and fails on Lean warnings as well as build errors. It does not request mathlib cache downloads. Use `make lean` when the cache needs provisioning. Read the summary first; do not follow a passing check with another equivalent build or a custom log scan. A targeted module check does not replace a complete project check when integration validation is needed. Mathematical proof review and translation review remain separate from these deterministic checks.

After a commit affecting rendered book inputs, run `make validate-debug BOOKS="<stem> ..."`. The runner builds each selected `<book-dir>/build/<stem>-debug.pdf` target and checks its current diagnostics. In the private repo the full-book target is `polish-space/build/polish-space-book-debug.pdf`; in the public export it is `polish-space-ch1/build/polish-space-ch1-debug.pdf`. Report the validation result and link the generated debug PDF. Direct debug target commands below describe the runner's underlying freshness checks, not an additional required build.

When the formalization viewer (`make formalization-viewer`) is running, it auto-rebuilds the rendered PDF currently selected in its PDF pane on any `<book>/src/**.md` or `<book>/lean/**.lean` change — the debug PDF together with its sourcemap, or the per-chapter preview PDF (the **Chapter preview** entry, which follows the chapter in the Markdown pane), whichever is selected; the release PDF is never auto-built. A change to a source shared between books through symlinks — a Lean file behind `polish-space-ch1/lean` and `polish-space-ja/lean`, or an English chapter symlinked into the Japanese book — rebuilds every book that links to it, in one batched `make`. So with the viewer running, the PDF you are viewing already tracks your edits, including booklink-marker edits in Lean sources, the preview and debug renders are each current when selected, and the post-commit `make <book-dir>/build/<stem>-debug.pdf` is an incremental no-op freshness check. Still run `make validate-debug BOOKS="<stem> ..."` for that freshness check: it is a real build for headless/agent runs that have no viewer and after non-watched changes such as `polish-space/tex/macros.tex`, `polish-space/tex/references.bib`, `tools/book-filter/Main.hs`, or the build pipeline, and it remains the booklink-straddle gate before a PR. In headless runs, after editing booklink markers in a Lean file, rebuild the sourcemap of every book sharing that Lean tree — in the private repo `make polish-space/build/polish-space-book-sourcemap.json polish-space-ch1/build/polish-space-ch1-sourcemap.json polish-space-ja/build/polish-space-book-ja-sourcemap.json` — since a marker edit renumbers booklink entries in all of them.

During iterative editing, run the required TeX-only verification without starting a preview, release, or debug PDF. After a commit, use the debug validation described above. If the user explicitly requests a chapter preview, the target is `make <book-dir>/build/<stem>-preview-<chapter>.pdf`, where `<chapter>` is the chapter source's basename. Report and link a requested preview after it succeeds; do not make preview approval a prerequisite for continuing authorized work.

Use low-reasoning subagents for build-only work only when the user has explicitly allowed delegation in the current task and the build is non-blocking or independently summarizable. Otherwise run the relevant helper locally and report its summarized result. Keep immediate TeX verification in the main workflow through `book-build`, because later edits often depend on those diagnostics. If a build failure requires mathematical or structural judgment, inspect the relevant diagnostics in the main agent before deciding how to fix it.

Keep iterative validation scoped to the change. During Lean development, check the affected module and run the full Lean build once when the batch is ready. Before a normal commit, rely on the installed pre-commit hook for the full `make lint` gate instead of running the identical suite immediately beforehand; run it explicitly when no commit is planned or the hook is unavailable. Keep translation synchronization and the required TeX checks before committing, and keep the post-commit debug build. A debug PDF target already builds its sourcemap dependencies, so do not separately request the same maps immediately before that target unless they are needed for an earlier check. Do not disable hooks or omit validation to shorten the loop.

### Git validation and pushes

Keep ongoing chapter and section restructuring in a single open PR. Update that PR's branch for subsequent structural changes instead of opening parallel restructuring PRs, since manifests, prefaces, and translation catalogs overlap readily. After it is merged, base the next restructuring PR on the latest main.

Keep the pre-commit lint hook enabled and use ordinary `git commit` and `git push`. Do not bypass validation with `--no-verify`, hook-disabling environment variables, or changes to `core.hooksPath`. The private repo (`sunaemon/math-private`) does not need a local guard against pushing to `main`; the public export (`sunaemon/math`) enforces its branch restrictions on the server. Do not add a local pre-push branch guard in either checkout.

### Git worktrees

Linked worktrees receive copy-on-write clones of the gitignored build caches (`.texlive/`, `.perllib/`, `*/.lake/`, the `build/` directories, `dist-newstyle/`) from the main checkout, so a worktree builds without reinstalling TeX Live, po4a's Perl modules, or refetching mathlib. `tools/worktree_caches.sh` performs the clone: it locates the main checkout through git itself, copies only cache directories that are missing in the worktree, and is always safe to re-run. The content-addressed caches (`.texlive/`, `.perllib/`, `*/.lake/`) are cloned into any worktree; the mtime-derived build outputs (the `build/` directories, `dist-newstyle/`) are cloned only on the fresh-creation path (where the just-checked-out sources are newer than every artifact, so make re-derives anything source-dependent) or when both checkouts are clean at the same HEAD, because otherwise the preserved mtimes would make artifacts from the wrong source state look fresh to make. The copy command is `CP_COW`, defined in the `Makefile` and defaulting to `cp -Rpc` on macOS (APFS clonefile) and `cp -Rp --reflink=auto` on Linux (xfs/btrfs reflinks). Do not symlink or share cache directories between worktrees; concurrent `lake` or TeX builds would corrupt shared state.

Create a worktree manually with `make worktree DIR=../path [BRANCH=name]`, or heal an existing worktree with `make worktree-caches`. `setup.sh` also runs the cache clone automatically when invoked inside a worktree. For Claude Code, the checked-in `WorktreeCreate` hook in `.claude/settings.json` runs `tools/claude_worktree_create.sh` whenever a session or subagent requests worktree isolation; it creates the worktree under `<main>-worktrees/<branch>`, branches from the current HEAD, and clones the caches. Codex has no worktree hook, so there the `setup.sh` and `make` entry points are the coverage.

## Index and Notation Workflow

Keep each symbol's mathematical role consistent throughout a section. Resolve collisions by renaming the objects in the English prose, Japanese translation, and corresponding Lean references. Do not introduce local `mathmeta` scopes merely to make conflicting declarations pass the notation audit.

The PDF build runs the book's configured indexer when an `.idx` file exists: `makeindex` for English books and `upmendex` for the Japanese book. The main source uses `makeidx` and prints the combined index at the end of the book. Do not hand-edit generated files under `build/`; update the source, `polish-space/tex/macros.tex`, `tools/book-filter/Main.hs`, or `Makefile` instead.

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

When a semantic macro appears in a heading, give it readable PDF bookmark text
with a comment such as `% pdf-bookmark: EventualEqualityER = E₀` in the macros file.
The filter preserves the typeset formula and uses this text only for the bookmark;
numeric subscripts and superscripts in the heading are converted to Unicode.
Keep the label free of TeX commands. Check the rendered PDF outline when adding
heading notation that the bookmark conversion does not yet support.

The `Notation` block in the index is sorted before ordinary English index entries. It should render mathematical notation, not bare macro names.

Use `\Sequence{x_n}{n\in\omega}` for a sequence and `\IndexedFamily{U_i}{i\in I}` for a brace-displayed indexed
family. Specify the actual index range, including positive or finite ranges when appropriate. Prefer sequence notation
to `n\mapsto x_n` when referring to the sequence as an object; retain map-arrow notation when defining a map's action.
Register new uses through the existing notation workflow rather than writing raw indexed parentheses or braces.

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

Use `\termforward{term}` or `\termforwardas{term}{display}` for an informal mention before its later formal definition. Keep `\termdefine` at that definition; a forward mention opens the use gate without replacing the definition.

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

For repetitive internal-interpretation proofs of bounded set predicates, reuse the existing bounded-predicate reflection and graph-collection infrastructure. Prove the semantic correctness of a shared operation once, then instantiate it; keep construction-specific arguments and mathematical hypotheses explicit rather than duplicating formula-interpretation proofs at each call site.

### Comment categories

Respect Lean's comment system and reserve a distinct marker for machine-targeted metadata. A comment is **machine metadata** when it is written for tooling or LLM consumption rather than a human reader; write it as an ordinary block comment whose body starts with `@`, that is `/-@ … -/`. The `@` sentinel keeps it distinct from Lean's doc comments (`/--`, `/-!`) and from human prose comments (`/- … -/`), and the formalization viewer folds `/-@ … -/` comments by default. Booklink markers use this form, `/-@ booklink: … -/`, and `tools/booklink_sourcemap.py` parses that opener. Keep genuine documentation in Lean's doc-comment syntax (`/--`, `/-!`) and human prose in plain `/- … -/`; do not fold or remarker those.

When formalizing book claims in Lean, make the Lean proof correspond to the proof written in the relevant `.md` source by default. Use the same main construction, intermediate reductions, named sets, metric choices, and proof direction whenever Lean reasonably permits it.

Formalization is also a tool for checking the book. If the Lean work exposes a mathematical error, a missing hypothesis, a hidden case split, or a genuinely cleaner proof, update the book proof instead of forcing Lean to follow the weaker text. In that case, make the `.md` proof and the Lean proof converge on the improved argument. Otherwise, keep the Lean development aligned with the book's notation and proof structure.

The formalization target is the mathematical content that the chapter actually proves or uses as local infrastructure. Audit local arguments and the infrastructure they require. Do not treat clearly cited external theorems, survey material, motivational examples, broad classification results, or side remarks as proof gaps merely because they are mentioned in prose. Examples include Anderson--Kadec-type homeomorphism theorems, large-inductive or covering-dimension comparison theorems when the chapter only uses the clopen-basis characterization, and illustrative non-closure warnings such as quotient spaces unless the chapter presents a concrete proof or later depends on that result.

When the text derives a consequence from a cited external theorem whose proof is not available in Lean, formalize the local derivation with the required external statement as an explicit theorem parameter. Preserve the external theorem's hypotheses and its correspondence with the book's definitions. Keep the external proof outside the local obligation, but do not skip the derived consequence merely because its input is external. Describe the Lean result as conditional on that input; do not introduce an axiom or `sorry` to make it appear unconditional. An external theorem mentioned only for context needs no artificial downstream consequence.

When comparing `.md` and Lean, distinguish "not formalized but out of scope" from "missing proof." A claim is in scope when it is stated as a theorem, claim, construction, proof step, example/non-example with an argument, or a lemma later used by the chapter. A claim is normally out of scope when it is explicitly cited to external literature, deferred to another chapter, included only as context, or names a standard background result whose proof is not part of this chapter's argument.

Use mathlib's canonical definitions for standard mathematical properties in theorem statements and public-facing Lean APIs. When the book states an equivalent formulation, such as "zero-dimensional" versus "has a clopen basis", add and use an explicit equivalence theorem connecting the mathlib definition to the book formulation. Prove via the book formulation after rewriting through that equivalence, rather than replacing the public statement with a local ad hoc predicate.

Do not replace a book proof by a one-line mathlib theorem, instance search, or a materially different argument merely because it proves the same final statement. Mathlib results may be used for standard local facts and infrastructure, but if the book explicitly proves a claim, also formalize that proof once in Lean, even if later callers use an equivalent mathlib theorem.

When the Lean proof must deviate from the book proof because of library constraints, make the deviation explicit in the surrounding code structure or report it to the user. Prefer adding helper lemmas that expose the book's implicit steps over hiding them behind broad automation.
