# Separate AFK validation

The book uses Lean 4.35.0. The AFK comparison source at
`348f38d92c3cd67968ccfb79102f0c7a96d0be33` uses Lean 4.35.0-rc3 and its own
dependency manifest. These files are deliberately outside the main book's
Lean library.

Run `python3 tools/validate_afk_chart_limit.py` from the private repository.
The script prepares a separate checkout under `build/afk-validation`, checks
the pinned revision and toolchain, copies the book's `ChartAmalgamation.lean`
without editing it, and builds the adapter with AFK's toolchain. Install that
toolchain through elan first. An existing checkout can be selected with
`--source-dir`; `--prepare-only` prepares it without claiming a build.
Dependency caches may be provisioned in that checkout with
`elan run leanprover/lean4:v4.35.0-rc3 lake exe cache get`.

The adapter checks finiteness, joint embedding, amalgamation, and the
countable representative family of the actual published-definition chart
class. `BookAFK.exists_chart_limit` applies the book's limit construction
and proves countability, universality, extension over all charts, and capture
of every finite tuple in a chart. `chart_fixed` and
`fixed_of_chart_cover` now prove projection fixedness of each finite chart
and of a structure covered on every finite tuple by these charts.
`compatible_of_chart_cover` proves every structured-geometry and diagram-pair
condition without assuming ambient compatibility.
`exists_compatible_chart_limit` combines nonemptiness, compatibility, fixedness,
universality, and extension for the constructed limit. `density_of_extension`
proves every density axiom below the cutoff by projecting a donor and applying
chart extension. `exists_stage_chart_limit` is the full Lemma 4.33 endpoint:
countability, membership in the actual `templateStageClass`, universality,
and chart extension. The runner checks that this theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound` and saves its source hashes,
build log, axiom list, and result under `build/validation/afk-*`.
This proves the limit step, not an equivalence or spectrum transfer between
`templateSentence` and `densitySentence`.

The validation copies add a `BookAFK` library to the scratch checkout's Lake
configuration. They do not alter AFK's mathematical sources or the book's
dependency manifest. The external sources retain their own copyright and
Apache-2.0 license.

## Licensing and provenance

`ChartClass.lean` is the book's locally written adapter, licensed under MIT;
its license is reproduced in `LICENSE-MIT`. The AFK project by Nathanael
Ackerman, Cameron Freer, and Robin Knight is a separate Apache-2.0 dependency.
`LICENSE` is an unmodified copy of its license at the pinned revision
`348f38d92c3cd67968ccfb79102f0c7a96d0be33`, retrieved from
<https://github.com/cameronfreer/vaught-conjecture-counterexample>.
The upstream Lean sources are downloaded into the scratch checkout by the
validation runner; they are not copied into this directory.
The component list, versions, license scope, and license paths are recorded
in `../manifest.json` and displayed by the formalization viewer.
