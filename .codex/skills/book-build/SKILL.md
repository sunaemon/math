---
name: book-build
description: Validate a discovered repository book's generated TeX during editing. Select the matching master source, run the shared validation runner, and report current diagnostics. PDF validation after commits uses the debug target; release and chapter-preview PDFs require an explicit user request.
---

# Book Build

From the repository root, run:

```sh
python3 .codex/skills/book-build/scripts/build_book_document.py --source polish-space/src/polish-space-book.md
```

The source must be a master listed by `make list-books`. Without `--source`,
the helper chooses the full canonical English book when present, otherwise the
first discovered book, including the public excerpt checkout. `--tex-only`
remains accepted for compatibility; TeX-only validation is always the default.
The helper runs plain `make validate-tex BOOKS="<stem>"` and shares its
diagnostics and unique `build/validation/<run>/report.json` report.

Read the compact result first. Inspect detailed logs only on failure. Report
the target, pass/fail, and report path; include current diagnostics on failure.
Do not repeat a passing build or scan historical logs as current failures.

After a commit affecting rendered inputs, run plain
`make validate-debug BOOKS="<stem>"`. Report the validation result and link the
generated `<book-dir>/build/<stem>-debug.pdf`. This is a rendered check, not
visual approval.

For an explicitly requested release or chapter preview, run its plain `make`
target described in AGENTS.md and await/report its result. The helper does not
launch background PDF workers or maintain a second lock implementation; the
Makefile serializes TeX commands with the shared repository lock.
