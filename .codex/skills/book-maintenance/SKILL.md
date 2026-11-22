---
name: book-maintenance
description: Summarize existing Polish-space book validation reports with gpt-6-luna. Reconcile review flags only during the pre-publication pass or on explicit request; leave fresh visual and mathematical judgments to the main agent.
---

# Book maintenance

Use for evidence reconciliation and report summarization in `sunaemon/math-private`
or its public export. Read the checkout's `AGENTS.md` and relevant `todo.md` item.
Do not create new proof obligations or reopen completed work from old chats.

## Route to Luna

When a bounded maintenance task is useful, the coordinating agent delegates it to
`gpt-6-luna` with low reasoning and a fresh context. The user's request to use this
skill authorizes this bookkeeping delegation; it does not authorize other agents
or other tasks. With the collaboration tools, use `spawn_agent` with
`model="gpt-6-luna"`, `reasoning_effort="low"`, and `fork_turns="none"`.
Pass this skill's absolute path, the repository path, the concrete question,
relevant input paths, and permitted output paths. Do not fork the book's full
mathematical discussion. Default to read-only repository access and put a report
under `/tmp` if a file is needed.

A skill does not switch the calling agent's model. If Luna or delegation is
unavailable, keep the task on `todo.md` with its recommended model and report the
limitation. Avoid recursive delegation when already running as the Luna worker.

## Review-status reconciliation

This mode is deferred until the pre-publication pass or an explicit user request.
Do not invoke it merely because a source changed, a build finished, or a flag
might be stale. Routine maintenance summarizes builds instead. Preserve existing
review flags during ordinary editing; reconcile them with the final publication
sources in the final pass.

Read `polish-space-ja/l10n/translation-status.json`, the relevant source files,
and existing evidence in Git or explicitly supplied review artifacts. Locate
candidate evidence with scoped file/history searches. Match evidence to the
chapter or page range, the review kind, and the reviewed source/artifact revision.

Report each material discrepancy with its current flag, evidence location,
revision match, and proposed action. Distinguish an explicit matching review,
partial or older review evidence, and evidence not found in the searched sources.
Do not describe the current revision as reviewed when only a prior revision has
explicit evidence. Absence of evidence is not proof that review never happened.
Inspect actual later diffs, not just commit titles: distinguish visible prose,
mathematics, and layout inputs from TODO comments, PO reference offsets,
provenance fields, and Lean-only edits. Do not call metadata changes new content.

A successful build, a translated PO entry, a pre-existing true flag, or a commit
merely preserving that flag does not establish visual or mathematical review.
Do not infer typesetting approval from a sourceBlob: that field tracks the
canonical English translation provenance, not the reviewed PDF. Describe later
changes and let the main agent judge whether they invalidate a review. Do not
promote, clear, or refresh flags solely because a hash or date changed.

Default to proposed changes. When the coordinator explicitly requests a status
update supported by the evidence, edit only the specified fields. Keep history
in Git, not cumulative status notes. Do not edit generated Japanese Markdown.
New visual inspection, mathematical review, translation judgments, and changed
proof-correspondence decisions remain with the main agent.

## Existing validation reports

Use the explicitly supplied `build/validation/<run>/report.json` files. Report
check kind, exact targets or modules, pass/fail, diagnostics, and any freshness
limitation relative to the current changes. Inspect detailed logs only for a
failure or unresolved diagnostic. A targeted Lean pass does not establish a full
project pass. A TeX pass does not establish a rendered or visual review.
Do not rerun passing checks, scan historical logs as current failures, launch
builds, clean artifacts, commit, push, or change source as part of this mode.

## Handoff

Return a concise result with evidence paths or Git revisions, proposed updates,
and questions requiring judgment. The coordinating agent reviews the result and
owns any repository edits, source/translation synchronization, and required
validation. Carry unfinished necessary work only in an existing or newly
justified `todo.md` item; do not add cumulative maintenance history.
