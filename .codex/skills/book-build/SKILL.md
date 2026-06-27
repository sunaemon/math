---
name: book-build
description: Build one repository polish-space/src/*.md document by first running its make <book-dir>/build/<stem>.tex target and extracting errors, then waiting for any previous skill-started PDF build for that document before starting make <book-dir>/build/<stem>.pdf in the background and extracting LaTeX errors. Use when Codex edits an .md source, needs the required TeX-then-PDF build workflow, must avoid overlapping PDF builds, or must summarize TeX/PDF build failures.
---

# Book Build

## Workflow

From the repository root, run:

```sh
python3 .codex/skills/book-build/scripts/build_book_document.py
```

By default this builds `polish-space/src/polish-space-book.md`. To pass the source explicitly, use `--source`:

```sh
python3 .codex/skills/book-build/scripts/build_book_document.py --source polish-space/src/polish-space-book.md
```

For a source `src/<stem>.md`, the helper performs this sequence:

1. Run `make <book-dir>/build/<stem>.tex` synchronously.
2. Save TeX-generation output to `<book-dir>/build/<stem>.tex-build.log`.
3. Extract likely Pandoc, filter, and TeX diagnostics from that log.
4. Wait for any previous PDF build for the same stem started by this skill to finish.
5. Start `make <book-dir>/build/<stem>.pdf` in the background.
6. Save PDF output to `<book-dir>/build/<stem>.pdf-build.log`.
7. Have the background worker extract LaTeX errors into `<book-dir>/build/<stem>.pdf-errors.txt` and write final status to `<book-dir>/build/<stem>.pdf-build.status`.

Use `--wait-pdf` only when the user explicitly wants the current response to wait for the PDF result:

```sh
python3 .codex/skills/book-build/scripts/build_book_document.py --wait-pdf
```

Use `--tex-only` only when the user asks to verify the Pandoc/filter/TeX target without starting a PDF build:

```sh
python3 .codex/skills/book-build/scripts/build_book_document.py --tex-only
```

## Reporting

Report whether `<book-dir>/build/<stem>.tex` passed. If it failed, include the extracted diagnostic blocks and link `<book-dir>/build/<stem>.tex-build.log`.

When the PDF result is known because `--wait-pdf` was used or because `<book-dir>/build/<stem>.pdf-build.status` is already final, report whether the PDF build passed and link `<book-dir>/build/<stem>.pdf` when relevant.

When the PDF build is started in the background, report the PID and these paths:

- `<book-dir>/build/<stem>.pdf-build.log`
- `<book-dir>/build/<stem>.pdf-build.status`
- `<book-dir>/build/<stem>.pdf-errors.txt`

If the helper reports that it waited for a previous skill-started PDF build, mention that. Do not launch `make <book-dir>/build/<stem>.pdf` manually while the helper lock is active; run the helper again so it can wait and serialize the builds.
