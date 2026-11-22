---
name: book-proof-inventory
description: Locate existing Lean declarations for a specified book TODO and return a bounded, read-only inventory of signatures and evidence. Use before connecting existing proof infrastructure; mathematical adequacy remains with the coordinating agent.
---

# Book proof inventory

Given a TODO passage, named source files, and search terms, identify the existing
Lean interfaces that the coordinator can inspect and reuse. Search with `rg`,
then read each candidate declaration and its nearby definitions. Expand the
search only along imports or identifiers that explain the supplied candidates.

Delegate this retrieval to `gpt-6-luna` with low reasoning and fresh context.
Pass the repository path, exact passage, candidate paths, search terms, and a
permitted report path under `/tmp`. This delegation is read-only: do not edit
repository files, run builds, change review records, or create new proof tasks.

For each useful candidate, return its absolute path and line, exact signature,
required definitions, and directly visible dependency names. Distinguish a
signature that constructs an object from one that takes it as a hypothesis.
Mark an unlocated interface as not found within the searched scope. Do not
infer that it is absent from the repository or that the book claim is proved.

The coordinator reads the candidates and owns mathematical judgments, proof
correspondence, implementation, translation review, and validation. An inventory
or a matching theorem name cannot resolve a TODO on its own.

If the requested model or delegation is unavailable, leave the retrieval task
unfinished in `todo.md` and report the limitation. Do not claim an inventory was
verified or silently substitute a model for the requested routing.
