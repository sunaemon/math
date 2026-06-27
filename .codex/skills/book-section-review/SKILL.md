---
name: book-section-review
description: Review one specific section or subsection of the repository's split .md book sources by label, title, or line reference, and compare with the corresponding Lean file when present. Use when the user asks for a targeted review of a named section in an .md document, including mathematical correctness, exposition, notation, theorem/proof style, indexing, cross-references, Lean correspondence, and local consistency with the rest of the document.
---

# Book Section Review

## Scope

Use this skill for review-only passes on a specific part of the repository's `.md` book sources. Do not edit the source unless the user explicitly asks for edits after the review.

Use `xhigh` reasoning for this review workflow when model controls or subagent tooling are available. If escalation is unavailable, perform the review in the current agent and state that limitation in the final review.

The review should be local to the requested section, but may inspect nearby definitions, referenced sections, `polish-space/tex/macros.tex`, the corresponding Lean file under `polish-space/lean/PolishSpaceBook/`, and `AGENTS.md` when needed to judge correctness or style.

The book is currently split into chapter files listed in `polish-space/src/polish-space-book.json`. If the user does not name a source file, search those chapter files. Treat `polish-space/src/polish-space-book.md` as the top-level assembly source, not as the only place section text lives.

## Locate the Section

From the repository root, extract the requested section with:

```sh
python3 .codex/skills/book-section-review/scripts/extract_book_section.py "sec:label-or-title"
```

By default this searches the chapter files listed in `polish-space/src/polish-space-book.json` and reports the matching split source file, for example `polish-space/src/polish-space-book/polish-spaces.md`.

To pass the source explicitly, use `--source`:

```sh
python3 .codex/skills/book-section-review/scripts/extract_book_section.py --source polish-space/src/polish-space-book/polish-spaces.md "sec:label-or-title"
```

The argument may be:

- a section label such as `sec:alexandrov-theorem`
- a title fragment such as `Alexandrov's Theorem`
- a source line number such as `360`

Line-number queries require `--source` when searching the split chapter files, because the same line number exists in many chapters.

The helper prints the matching source file, heading, section range, and line-numbered section text. If there are multiple matches, rerun it with a more specific label or title fragment.

Use `rg` for related context:

```sh
rg -n 'sec:label-or-title|Title fragment' path/to/source.md polish-space/tex/macros.tex AGENTS.md
```

## Lean Correspondence

When a matching Lean file exists, use it as comparison evidence. The usual path is the PascalCase chapter name under `polish-space/lean/PolishSpaceBook/`; for example:

- `polish-space/src/polish-space-book/polish-spaces.md` -> `polish-space/lean/PolishSpaceBook/PolishSpaces.lean`
- `polish-space/src/polish-space-book/cantor-baire-space.md` -> `polish-space/lean/PolishSpaceBook/CantorBaireSpace.lean`
- `polish-space/src/polish-space-book/appendix-set-theory.md` -> `polish-space/lean/PolishSpaceBook/AppendixSetTheory.lean`

Also inspect any local `\lean{...}` annotations in the extracted section, because they are the strongest signal for intended correspondence between the prose proof and Lean declarations.

Check the Lean file with the repository's Lean command before using it as evidence. In this workspace, if `lake` is not on `PATH`, use:

```sh
/opt/homebrew/bin/mise exec -- lake env lean polish-space/lean/PolishSpaceBook/PolishSpaces.lean
```

When comparing `.md` and Lean:

- Treat proved Lean declarations that follow the same construction, hypotheses, and direction as strong coherence evidence.
- Distinguish proved correspondence from a Lean stub that only imports the previous chapter and opens the namespace.
- Distinguish local external `Prop` specifications from fully formalized proofs.
- Do not mark an `.md` proof gap resolved merely because mathlib has a broad theorem with the same conclusion; compare the book's stated proof and the Lean-side construction.
- If Lean exposes a missing hypothesis, hidden case split, or proof-shape mismatch, report it as a source issue and identify the Lean declaration or gap that revealed it.
- If a claim is intentionally external or proof-architecture-only in the book, say that Lean is out of scope rather than calling it a missing proof.

## Review Checklist

Prioritize findings that would justify a source change.

- Mathematical correctness: false statements, missing hypotheses, circular reasoning, invalid proof steps, ambiguous quantifier scope, or mismatches between statement and proof.
- Lean correspondence: whether the local `\lean{...}` declarations or chapter Lean file actually formalize the section, merely import/check, or encode a materially different proof.
- Local coherence: whether definitions, examples, theorem-like statements, and transitions support the section's stated purpose.
- Cross-references: stale, missing, misleading, or stylistically awkward references; prefer integrated references like "by §{sec:...}" over parenthesized references in running prose.
- Notation and macros: use semantic macros from `polish-space/tex/macros.tex`; do not guess macro renderings for notation-heavy prose.
- Indexing: use `\termdefine`, `\termdefineas`, `\termuse`, and `\termuseas` for important terms when the section defines or relies on them. A short informal use before the later formal definition is acceptable only when the informal occurrence itself uses `\termforward{...}` or `\termforwardas{...}{...}`; otherwise `\termuse{...}` before `\termdefine{...}` is a build error.
- Theorem/proof form: use `amsthm` environments for genuine mathematical statements and proofs; use transitional labels only when a full conversion is not practical.
- Prose style: avoid parentheticals that carry mathematical content or reading guidance; prefer direct predicate phrasing over compressed nominalizations.

## Output Format

Use a code-review stance:

1. Findings first, ordered by severity.
2. Each finding should cite the reviewed source file with a precise line number from the extracted section.
3. Explain the issue and the concrete source-level fix or decision it calls for.
4. Include Lean comparison evidence when available: command checked, matching declarations, whether the file is a stub, and whether Lean supports or weakens confidence in the `.md` proof.
5. Add open questions only when they affect the recommendation.
6. If no issues are found, say that clearly and mention any remaining residual risk, such as external references not checked or Lean coverage being stub-only.

Do not include a broad summary before findings. Keep the review focused on the requested section rather than the whole book.
