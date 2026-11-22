# Book section review checklist

Prioritize findings that would justify a source change. Work through the
section in order; check every proof step by step, not just statements.

Run targeted greps yourself whenever a question arises — do not defer them
to "open questions" if a grep can settle them:

- A fact is asserted bare ("closed subsets of metric spaces are Gδ"): grep
  all chapters and the appendices for it. Not proved anywhere and not cited
  → finding.
- A result is stated as proved elsewhere: find the actual section label and
  check the reference (or its absence — a missing forward reference to an
  existing `sec:` label is a finding).
- A semantic macro would fix raw notation: grep for its `\define{...}` in a
  mathmeta block to confirm it is gate-legal at the use site (defined in an
  earlier chapter, or `\forward`-able).

**Mathematical correctness** (highest priority): false statements, missing
hypotheses, circular reasoning, invalid or unjustified proof steps, quantifier
scope errors, statement/proof mismatches. Typical catches worth actively
hunting for:

- _Misattributed citations_: a step credited to a theorem it does not use
  (e.g. crediting Baire for a purely definitional comeagerness step).
- _Quantifier slips_: a proof that fixes an object, constructs data relative
  to it, then draws a conclusion quantified over the fixed object.
- _Bare steps_: standard facts used without proof or citation when the book
  proves everything else at that level.
- _Vestigial setup_: choices ("pick metrics d_n ≤ 1 …") never used by the
  rest of the proof — the Lean proof is good evidence a sentence is dead.

**Lean correspondence**: for each booklinked statement/proof, compare the
Lean proof's construction with the book's. Distinguish:

- proved with the same construction, hypotheses, and direction (strong
  coherence evidence — say so);
- proved by a materially different route (e.g. book: Alexandrov + not-Gδ;
  Lean: direct Baire argument) — report the deviation and, when cheap, the
  one-line Lean corollary that would restore the book's route;
- delegated to a broad mathlib lemma although the book gives an explicit
  proof — acceptable for `recall*`-kind background, a finding for results
  the chapter itself proves;
- a stub that only imports and opens namespaces — say Lean coverage is
  stub-only.

Do not mark an `.md` proof gap resolved merely because mathlib has a theorem
with the same conclusion.

**Formalization-skip hygiene**: walk the `--show-exempt` list. A skip span is
healthy only if its content is genuinely out of scope (motivation, external
citations, restatements of formalized results). Findings:

- a skip that blankets claims the Lean file actually proves (narrow the skip
  and booklink the theorems instead — "minimize skip");
- a skip whose reason mislabels in-scope content as background;
- in-scope prose with real content that is neither covered nor exempt
  (the plain coverage run reports these as uncovered/partial).

**Conventions** (from `CLAUDE.md` / `AGENTS.md`):

- Term indexing: `\termdefine`/`\termdefineas` at definitions,
  `\termuse`/`\termuseas` at later uses, `\termforward` for informal earlier
  mentions. No obsolete alias macros.
- Notation gates: watched macros need a mathmeta `\define{...}` before first
  mathematical use, `\forward{...}` for legitimate early uses.
- Semantic macros over raw LaTeX for recurring notation; check
  `macros.tex` before proposing one. Remember `\NN` includes 0.
- Theorem/proof structure: `amsthm` environments, not bold labels; named
  results indexed via term macros in the optional title.
- Cross-references integrated into the sentence ("§{sec:...} proves"), not
  parenthesized; no parentheticals carrying mathematical content; predicate
  phrasing over blunt nominalizations.

## Output contract

Use a code-review stance:

1. Findings first, ordered by severity. No summary before them.
2. Each finding cites the source as `<file>:<line>` with precise line
   numbers, explains the issue, and gives the concrete source-level fix or
   the decision it calls for. Attach Lean evidence to a finding when it
   supports or contradicts it (declaration name and line).
3. After the findings, a **Lean comparison evidence** section: the exact
   check command and exit status, whether the file is a stub or a full
   development, the coverage counts, and an overall correspondence
   assessment naming the proofs that do follow the book faithfully.
4. A short **residual risk** note: external references not checked,
   stub-only coverage, or anything else limiting confidence.
5. If no issues are found, say so clearly and still include 3 and 4.
6. Open questions only when they affect a recommendation.

A review alone does not trigger rendered book builds. Use the repository's
scoped Lean validation for proof evidence; do not start PDF builds or fix source
findings unless the user asks.
