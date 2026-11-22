---
name: book-section-mechanical-checks
model: sonnet
description: Gather inputs and run the mechanical, non-judgment checks (Lean type-check, booklink coverage, notation-watch list) for a book chapter or section. Used as Phase 0/1 of book-section-review, and directly invokable on its own when only the mechanical/coverage state of a chapter is needed. Runs on Sonnet since none of this requires mathematical judgment.
---

# Book Section Mechanical Checks

Gather the inputs and run the mechanical checks needed to review a book
chapter or section. This is pure fact-gathering — do not evaluate,
critique, or draw conclusions; that judgment happens in book-section-review's
Phase 2. Return a single structured report (see Output contract) as your
final answer.

## Locate inputs

- Chapter sources live in `polish-space/src/polish-space-book/*.md` (the
  chapters listed in `polish-space/src/polish-space-book.json`). The
  `polish-space-ch1/` copy is a symlink; review the real file under
  `polish-space/src/`.
- For a single section (label, title fragment, or line number), extract it
  with:

  ```sh
  python3 tools/extract_book_section.py "sec:label-or-title"
  ```

  Add `--source <path>` to disambiguate; line-number queries require it.
  For a whole-chapter review, skip the helper and read the chapter file
  directly.

- The matching Lean file is the PascalCase chapter name under
  `polish-space/lean/PolishSpaceBook/`, e.g. `polish-spaces.md` →
  `PolishSpaces.lean`. If it does not exist, report that Lean coverage is
  absent.
- Read the chapter/section source, the Lean file (if present), and
  `polish-space/tex/macros.tex`. Never guess how a macro renders — check its
  definition and any `% notation-index:` comment.

## Mechanical checks

Use `mise exec --` where shown to select the repository-pinned interpreter.
Bare `lean` cannot see this project's mathlib without the Lake environment.

1. **Type-check the Lean file**:

   ```sh
   cd polish-space && mise exec -- lake env lean lean/PolishSpaceBook/<Chapter>.lean
   ```

   It MUST be run from `polish-space/` (the directory containing
   `lakefile.toml`). From the repo root it fails with
   `unknown module prefix 'Mathlib'` — that is a wrong-cwd error, not a
   broken file. Report the command and exit status.

2. **Booklink coverage** — run twice, plain and with exempt units:

   ```sh
   mise exec -- python3 tools/booklink_coverage.py polish-space/lean/PolishSpaceBook/<Chapter>.lean
   mise exec -- python3 tools/booklink_coverage.py --show-exempt polish-space/lean/PolishSpaceBook/<Chapter>.lean
   ```

   Older system Python versions may not support the tools; use the pinned
   mise Python consistently. Report the plain run's covered/partial/uncovered
   counts, and the full `--show-exempt` list verbatim — judging whether each
   skip reason is honest is Phase 2's job, not this skill's.

3. **Notation-watch list**: read the YAML header of
   `polish-space/src/polish-space-book.md` (roughly the first 80 lines) and
   report which macros are in `notation-watch`.

## Output contract

Report, as your final answer:

1. The resolved section text (or its exact file path/line range if too long
   to inline) and whether it came from the extractor or a direct chapter
   read.
2. The Lean file path, or a note that Lean coverage is absent.
3. The type-check command, its exit status, and any error output.
4. The booklink coverage counts, and the full `--show-exempt` output.
5. The notation-watch list.

Do not filter, summarize away, or interpret any of the above — the caller
needs the raw facts to make judgment calls.
