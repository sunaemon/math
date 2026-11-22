# Manthe Borel determinacy dependency

This directory contains the transitive Lean source dependencies of
`BorelDet.Proof.borel_determinacy` from Sven Manthe's
[A formalization of Borel determinacy in Lean](https://github.com/sven-manthe/A-formalization-of-Borel-determinacy-in-Lean),
pinned to commit `42bc874b2357ca7e7573b31854a0d09761e11e41`.
The accompanying paper is [arXiv:2502.03432v5](https://arxiv.org/abs/2502.03432v5).
The original Apache 2.0 license is retained in `LICENSE`.

`UPSTREAM.json` records the upstream and target Lean/mathlib revisions and the
SHA-256 checksum of every original source file. The checked-in files here are
the maintained port; ordinary builds neither download nor resolve a moving
upstream revision. The `BorelDet` library in `../../lakefile.toml` uses the same
fixed mathlib dependency as the book. The upstream root module and applications
outside the required import closure are intentionally not included.

The upstream project uses Lean `v4.28.0-rc1`; this port targets Lean `v4.35.0`.
The compatibility changes include the Lean module system, modern mathlib
concrete categories and bundled morphisms in `Type`, renamed library lemmas,
and explicit proofs where dependent rewriting or extensionality changed.
The library's two `backward.isDefEq.respectTransparency` settings restore older
elaboration behavior; they do not change kernel checking or introduce axioms.
The game, strategy, winning, covering, and unravelability definitions retain
their mathematical meaning. The book's separate adapter is
`../../lean/PolishSpaceBook/BorelDeterminacy.lean`.

From the private repository root, check the imported theorem and every required
vendor module with:

```sh
make validate-lean LEAN_PROJECTS=polish-space LEAN_MODULES=BorelDet.Proof.borel_determinacy
```

To inspect the exact upstream baseline, check out the recorded Git revision and
compare each path listed in `UPSTREAM.json` with its corresponding vendored path.
The per-file original checksums make accidental baseline changes detectable.
Keep any further port changes in this directory and preserve their provenance.
