---
name: book-section-review
description: Review a chapter or a specific section of the repository's split .md book sources, comparing with the corresponding Lean file. Use when the user asks to review a book chapter or section (e.g. "review polish-spaces.md", "review sec:alexandrov-theorem"), covering mathematical correctness, exposition, notation, indexing, cross-references, Lean correspondence, and formalization-skip hygiene.
---

# Book Section Review

Review-only pass over a chapter or section of the split `.md` book sources.
Do not edit any source unless the user explicitly asks for edits after the
review. The deliverable is the findings report; write it to a file only if
asked.

Phase 0 (locate inputs) and Phase 1 (mechanical checks) are fact-gathering,
not judgment calls, so Sonnet is sufficient for them: dispatch both to a
subagent instead of running them in the main agent, and feed the returned
report into Phase 2 (the judgment review). Do not skip this step: several
finding classes (skip hygiene, notation gates, stale references) are only
visible in that report.

## Phase 0+1 — Gather inputs and mechanical checks

Spawn a subagent (Agent tool, `subagent_type: general-purpose`) with a
prompt along the lines of: "Invoke the `book-section-mechanical-checks`
skill for `<chapter or section>` and report back its full output verbatim."
Do not pass a `model` override in the Agent call — that skill pins itself to
Sonnet in its own frontmatter. Wait for its report before starting Phase 2.

## Judgment review and output

Read `tools/book-section-review-checklist.md` and apply its full checklist and
output contract to the returned mechanical evidence. This is the canonical
checklist shared with the Codex review adapter.
