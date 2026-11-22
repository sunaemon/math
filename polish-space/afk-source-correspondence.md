# AFK source correspondence and scope of use

This note records the evidence needed before importing the counterexample's construction into the book.
The book currently cites the existence result; it does not reproduce the construction.

## Fixed sources

- Published paper: [arXiv:2610.15217v1](https://arxiv.org/html/2610.15217v1), 10 October 2026,
  especially §1.2, Propositions 4.32, 4.34, 4.35, Lemma 4.33, and Theorem 4.36.
- Palomar proof: `cameronfreer/vaught-conjecture-palomar`,
  commit `032ccb7a25b0ff6227128aa0aeba549c5901ea9a`,
  [registered version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-07-000001&version=1).
- Revised proof: `cameronfreer/vaught-conjecture-counterexample`,
  commit `348f38d92c3cd67968ccfb79102f0c7a96d0be33`.
  Its proposition correspondence names an unpublished 7 October draft with source SHA-256
  `654b2780d08e9aee902d0553576c8f58f82730ccba7f4926757e45b1c02a755f`.
  That draft must not silently be identified with the published version.

The comparison below inspected source definitions and proof dependencies at these commits.
It is not a fresh local build or an independent verification of every imported lemma.
Palomar's registration applies to its pinned proof, not automatically to the revised repository.

## Existence theorem and proof routes

Both `Palomar/Solution.lean` in the first repository and `comparator/Solution.lean` in the second
prove the same externally stated existence claim: a countable relational infinitary sentence has
exactly aleph-one countably infinite isomorphism classes, no finite models, and no nonempty perfect
antichain in the ordinary space of relation truth tables.
The model predicate is actual sentence satisfaction and the equivalence relation is actual isomorphism.

The first witness is `knightSentence`, defined in `Knight/Sentence.lean` by separate structural
and extension clauses. `Knight/ExpansionDomainEndpoint.lean` counts classes through a decreasing
filtration with countable losses, Scott separation of the persistent core, and cofinally nonempty losses.
Its thinness proof separately uses countable back-and-forth quotients and analytic boundedness in
`Knight/BFBoundednessThinness.lean`.

The revised witness is `baseLanguage.densitySentence`, the conjunction of structural and receiving
clauses in `Language/Density.lean`. `MainTheorem/GrowthLevelRoute.lean` supplies the remaining
receiving-model hypotheses through replicated levels and the padded construction.
`MainTheorem/ReceivingRoute.lean` builds expansion domains; `MainTheorem/Assembly.lean` counts their
classes and obtains thinness from countable truth sides of sentences.
No equivalence of these two particular witness sentences was established by this comparison.

## Template correspondence

The revised repository also defines `templateSentence`, its transcription of the paper's `σ[L]`.
It is not the sentence used by the main existence endpoint.

### Checked definition dictionary

The following comparison uses the published 10 October text and the revised
repository at the pinned commit above. The relevant comparison is in
`Correspondence/Charts/LegalTemplate.lean`; the older
`Correspondence/Legal.lean` discusses a different draft and must not stand in
for the published legality definition.

| Published object                          | Pinned Lean interpretation                                                         | Important qualification                                                                                                                                                                                |
| ----------------------------------------- | ---------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Finite labeled template and cell renaming | `StageType α n`, `StageType.IsCellRenaming`, `TemplateClass α n`                   | The quotient renames cells; the ordered point set `Fin n` remains fixed. Chart enumerations account for changes of point names.                                                                        |
| Legal template, Definition 4.29           | `StageType.IsLegalTemplate ω₁`, equivalent to `IsStronglyCodedLegal` for `α ≤ ω₁`  | `isLegalTemplate_omega_one_iff_of_le` checks all five clauses, including the row-range bound. The label universe `ω₁` differs from the bound `α` on the template's labels.                             |
| Projection at index `β`                   | `TemplateClass.project` at `blockStage β`                                          | The cutoff is `ω + ω * β`; at index zero it is `ω`. `project_toClass_eq_iff` identifies fixed classes with bounded labels.                                                                             |
| Languages and atomic diagram              | `TemplateSymbol.closed`, `.invariant`, `.base`, `StageType.Holds`                  | `P`, `Q`, and `R` stay distinct. `Holds` requires an injective tuple and a defined closed face, then reads its class or its projection at `ω`.                                                         |
| Chart category, Definition 4.31           | `IsTemplateChart β G`, `StageType.embeddingEquivFace`                              | Charts have nonempty finite carriers. Embeddings correspond to face maps up to cell renaming. Heredity is for nonempty closed subsets.                                                                 |
| Base vocabulary                           | `ClassSymbol`, `baseTemplateLanguage`, `chosenVocabularyTarget`                    | Choosing representatives gives a bijective renaming of the printed `R` symbols. This is different from the many-to-one class-disjunction interpretation of positional structures.                      |
| Sentence, Definition 4.22                 | `templateSentence := planClause ⊓ structureClause ⊓ diagramClause ⊓ densityClause` | The four groups respectively encode the plan, typing/exclusivity/determination, atomic diagrams, and finite-cutoff extensions. The last clause uses raw finite truncation, not block-stage projection. |
| Countability at a stage                   | `StageType.countable_of_lt_omega_one`, `StageType.countable_sigma`                 | For countable `α`, finite cell schemes, coded rows, and labels at `α` give a countable type of finite templates. This does not assert countability of the full invariant language over all stages.     |

The legality comparison explicitly relates bountifulness in the published label
universe to the native predicate through finite block compression. It does not
silently replace the published condition by a stronger unverified assumption.
The chart correspondence supplies actual hereditary, joint-embedding, and
amalgamation proofs. It does not supply a Fraïssé limit.

Evidence at the fixed revision:
[legal-template comparison](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/348f38d92c3cd67968ccfb79102f0c7a96d0be33/VaughtConjecture/Correspondence/Charts/LegalTemplate.lean),
[classes and projection](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/348f38d92c3cd67968ccfb79102f0c7a96d0be33/VaughtConjecture/Correspondence/Charts/TemplateClass.lean),
[charts and embeddings](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/348f38d92c3cd67968ccfb79102f0c7a96d0be33/VaughtConjecture/Correspondence/Charts/Chart.lean),
[sentence clauses](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/348f38d92c3cd67968ccfb79102f0c7a96d0be33/VaughtConjecture/Correspondence/Sentence/TemplateSentence.lean),
[countable stage types](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/348f38d92c3cd67968ccfb79102f0c7a96d0be33/VaughtConjecture/Stage/Countable.lean).

This establishes the definition dictionary used in the limit check below. It does
not identify `templateSentence` with `densitySentence`, transfer their spectra,
or certify the published argument as a whole.

### Proposition interfaces

| Published item   | Revised declarations                                                                                   | Scope to retain                                                                                                                                           |
| ---------------- | ------------------------------------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Proposition 4.32 | `IsTemplateChart.hereditary`, `.jointEmbedding`, `.amalgamation` in `Correspondence/Charts/Chart.lean` | Finite nonempty charts; joint embedding and amalgamation assume a countable stage.                                                                        |
| Proposition 4.34 | `proposition434Target` in `Correspondence/Proposition434.lean`                                         | Bounded lift ranks, literal reconstruction over a fixed base, and lifting at nonzero limit stages. The zero-stage lift has a separate theorem.            |
| Proposition 4.35 | `proposition435Target` in `Correspondence/Maximality/Count.lean`                                       | At most countably many maximal structures at a fixed countable stage, up to full template-language isomorphism. Maximality allows unchanged higher lifts. |

These are proved declarations, not merely predicates named `Target`.
The hypotheses and conclusions must be checked against the published definitions when incorporating them.
In particular, Proposition 4.35 is distinct from the native theorem counting terminal realizations.

There is a concrete obstruction to one proposed bridge. In `Correspondence/Sentence/Dictionary.lean`,
`classStructureSeparationTarget` proves that the class-disjunction interpretation of **every**
`densitySentence` model fails `templateSentence`.
This refutes that interpretation, not every possible interpretation or the existence theorem.
The source does not claim a spectrum transfer between the sentences.

## Checked Fraïssé-limit step

### Countable amalgamation-chain argument

The following argument isolates the scheduling step. Its finite simultaneous
amalgamation step is implemented as
`PolishSpaceBook.ChartAmalgamation.finite_requests` in
`lean/PolishSpaceBook/ChartAmalgamation.lean` and passed targeted Lean validation.
The same module implements `bounded_requests`, `exists_request_chain`,
`embedding_factors`, and `limit_extension`: it constructs the request chain
and proves the limit extension property for the enumerated charts.
`exists_countable_universal_extension` assembles a countable structure,
universality for all class members, extension over all class members, and
capture of every finite tuple inside an embedded class member. Its
universality proof uses joint embedding after the chain construction:
amalgamate a chart already embedded in the limit with the desired chart,
replace the common target by its representative, and use extension.
Thus the Lean chain need not explicitly include `Cₙ₊₁` at each step.
This is the same amalgamation-chain route with a different placement of
the joint-embedding step. No hereditary closure is assumed.
The AFK chart-limit instantiation is now implemented separately as
`BookAFK.exists_chart_limit` in `vendor/afk-validation/ChartClass.lean`. It constructs
the nonempty countable representative family, applies the generic limit
theorem, and has passed compilation against the pinned AFK source. The
stage-class checks are complete. In particular, `chart_fixed` and
`fixed_of_chart_cover` now establish finite-chart and limit fixedness using
the actual existential definition of structure projection.
`compatible_of_chart_cover` now proves every geometry, invariant-typing,
exclusivity, determination, and diagram-pair condition. Its intersection proof
captures both closed tuples and the intersection tuple in one chart and
reflects the range equality through the chart embedding.
`exists_compatible_chart_limit` combines nonemptiness, compatibility, fixedness,
universality, and extension for the actual constructed limit.
`density_of_extension` projects each legal donor to the current stage and
realizes it by chart extension. `project_truncEquiv` verifies the required
raw truncation equivalence for every lower cutoff, including successors.
`exists_stage_chart_limit` combines these into a countable member of the
actual `templateStageClass`, with universality and extension for all charts.
Its only axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
The pinned external package
cannot be directly imported into the book's current Lake
project: its `lean-toolchain` is `v4.35.0-rc3`, while the book uses
`v4.35.0`. Its `lakefile.toml` also inherits a mathlib fork through
`InfinitaryLogic` rather than the book's mathlib release. The generic chain
proof above has been checked against the book's actual dependencies and
compiled unchanged in the separate AFK environment. The reproducible check is
`python3 tools/validate_afk_chart_limit.py`; its scope and separate-toolchain
boundary are documented in `vendor/afk-validation/README.md`. This does not change
the book's dependency manifest. It checks stage-class membership for the
published-definition route, not equivalence with `densitySentence`.
Let `C` be a nonempty family of nonempty finite relational structures in a
fixed finitary language. Assume that its isomorphism types are countable and
that it has joint embedding and amalgamation for structure embeddings.
No hereditary property is assumed. The relation-symbol set need not be
countable. Choose representatives `C₀, C₁, …` covering the isomorphism types,
repeating representatives if there are only finitely many types.

Construct a chain `M₀ → M₁ → …` of members of `C` as follows. Start with
`M₀ = C₀`. At stage `n`, form all requests `(i,j,h,e)` with `i,j ≤ n`,
`h : Cᵢ → Cⱼ` an embedding, and `e : Cᵢ → Mₙ` an embedding. There are finitely
many requests: all the carriers in each of the finitely many pairs are
finite. Enumerate these requests. Starting with `Mₙ`, handle a request by
amalgamating its donor `Cⱼ` with the current structure over `Cᵢ`, using the
composite of `e` with the embedding from `Mₙ` into the current structure.
Each step stays in `C`. Previously obtained commuting triangles remain
commuting after composition with later embeddings. Thus one finite sequence
of amalgamations yields a structure realizing every listed request.
Finally use joint embedding to include `Cₙ₊₁`; call the resulting structure
`Mₙ₊₁`. All witnesses survive this last embedding too. This defines the
chain by recursion using ordinary choice.

Take its relational direct limit `F`, with embeddings `qₙ : Mₙ → F`.
It is countable because it is a quotient of the countable disjoint union of
finite carriers. Every finite tuple of `F` lies in some `qₙ[Mₙ]`: choose
representatives for its finitely many entries and pass to a common stage.
In particular, every embedding of a finite structure into `F` factors
through some `qₙ` as an embedding. Reflection of relations follows from
reflection by `qₙ`; injectivity follows from injectivity of the original
embedding. Every member of `C` embeds into `F`, since its chosen
representative occurs in the chain.

For the extension property, first take an embedding `h : Cᵢ → Cⱼ` and an
embedding `e : Cᵢ → F`. Factor `e` through `Mₖ`. Choose `n ≥ k,i,j` and
transport that factor to `Mₙ`. The request at stage `n` supplies an embedding
`g : Cⱼ → Mₙ₊₁` whose composite with `h` is the transported factor.
Consequently `qₙ₊₁ ∘ g ∘ h = e`. Conjugating by isomorphisms to the chosen
representatives gives the same extension property for arbitrary members of
`C`. This proves universality and the extension property without applying
heredity to any finite subset of `F`.

The relevant reusable mathlib interfaces are in
`Mathlib/ModelTheory/DirectLimit.lean`: `DirectedSystem.natLERec` constructs
the transition maps, `DirectLimit.of` gives embeddings into the limit,
`DirectLimit.of_f` gives their coherence, and
`DirectLimit.exists_quotient_mk'_sigma_mk'_eq` captures a finite tuple at a
single stage. In contrast, `Language.IsFraisse` in
`Mathlib/ModelTheory/Fraisse.lean` requires ordinary hereditary closure and
cannot simply be instantiated with the published chart class.

For AFK, applying this argument requires the exact countable
representative family. More substantially,
universality and the extension property alone do not establish membership
in `Kβ`. One must check compatibility of the limit diagram, fixedness at
`blockStage β`, and the density axioms by matching legal template extensions
and their raw truncations. The following subsections give these mathematical
checks; their Lean implementation is included in the separate validation.

### Seed and projection checks for the AFK instantiation

There is an explicit seed; it need not be inferred from countability.
In `Correspondence/InvariantSystem.lean`, `intervalScheme n` has the
interval plan on `Fin n`, one cell per graded face, and bottom rows.
`isLegal_intervalScheme n` proves that its scheme is legal, using
`Rows.isConsistent_bot` and `Rows.isBountiful_bot`.
`exists_isLegal α n` then supplies its stage type with every label bottom.
The same seed is strongly coded: every row entry is bottom, which is the
first alternative of the strong row-range condition. Thus the published
legality equivalence in `Charts/LegalTemplate.lean` applies. Taking `n = 1`
at `α = blockStage β` gives a nonempty finite chart seed with labels fixed
at that cutoff. This strengthens the bare `exists_isLegal` conclusion by
checking its particular witness; arbitrary legal stage types need not be
strongly coded.

The same source supplies the following projection facts for a stage type
`p` at `ω₁`, with zero-or-limit cutoffs as required by each signature:

- `StageType.project_toScheme` says projection keeps the entire scheme,
  including its rows. Consequently it keeps strong coding.
- `StageType.IsLegal.project` preserves native legality. Together with
  unchanged strong coding and the published legality equivalence, this
  preserves published legality for cutoffs at most `ω₁`.
- `StageType.restrictFace_project` commutes projection with face maps,
  including their definedness. If a face `s` is already fixed at the cutoff,
  projecting a donor extending `s` still extends `s` literally.
- `StageType.project_project_of_le` and `.project_project_of_ge` prove
  absorption at ordered zero-or-limit cutoffs below `ω₁`.

These last two absorption theorems do not cover the arbitrary raw cutoffs
in the density axioms. In particular, they must not be used as though a
positive finite ordinal were a zero-or-limit stage. The raw-label identity
needed instead is checked below.

Source at the fixed revision:
[interval seed and projection proofs](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/348f38d92c3cd67968ccfb79102f0c7a96d0be33/VaughtConjecture/Correspondence/InvariantSystem.lean).
These are inspected source proofs; no local build of the external repository
is claimed.

### AFK limit argument at a fixed countable stage

Fix `β < ω₁` and put `λ = blockStage β`. Thus `λ < ω₁` and `λ` is a
limit ordinal. Take one representative chart for every strongly coded legal
stage type at `λ` on a positive finite number of points. This is a
countable family by `StageType.countable_sigma` and restriction to the legal
subtype. Every chart at this stage is isomorphic to one of these by its
defining enumeration; duplicate representatives do not matter. The seed
above makes the family nonempty. Proposition 4.32 supplies joint embedding
and amalgamation, so the chain argument constructs a countable nonempty
limit `F` with universality and the extension property for these charts.

Here are the mathematical checks on that limit. Nonemptiness, compatibility,
fixedness, and density have now been implemented and checked in the separate
AFK validation project.

**Compatibility.** Every finite tuple of `F` lies in a chain chart, and
the map from that chart into `F` preserves and reflects every relation.
The closed-tuple, permutation, exclusivity, determination, and diagram-pair
conditions therefore hold by their validity in that chart. For the
intersection condition, put both closed tuples and the enumeration of
their intersection in one chart; injectivity of the stage embedding
preserves the asserted intersection of their ranges. For existence of a
closed extension of an injective tuple, put it in a chart and enumerate
the whole chart with the given tuple first. The whole chart is closed,
and its enumeration has a legal invariant. These witnesses remain valid
in `F`. This checks the existential closed-extension and invariant-typing
conditions too, rather than appealing to preservation of arbitrary
infinitary sentences under unions. Thus `F` is template-compatible.

**Fixedness.** Every realized invariant in `F` is realized in a chain
chart. Its template is a closed face of the chart template, so all its
labels lie at `λ`. The fixed-class characterization shows that this
invariant is fixed by projection at `β`. In `projectStructure`, an
invariant `Q_c` holds precisely when some realized `Q_d` has projection
`c`. All such realized `d` are fixed, so this is equivalent to the
original `Q_c`. Closed and base relations are unchanged by definition.
Hence `projectStructure β F = F` as structures on the same carrier.

**Raw truncation.** For every ordinal `δ ≤ λ` and label `a`,
`Label.reduce δ (Label.reduce λ a) = Label.reduce δ a`.
This is exactly `Label.reduce_reduce_of_le` in `Label/Basic.lean`; it
assumes only the inequality, not that `δ` is zero or a limit. Directly,
if `a < λ`, the inner reduction keeps `a`. Otherwise it produces the
formal top; both sides then equal top since `δ ≤ λ ≤ a`. Bottom is
kept and formal top remains top. Projection keeps the scheme and rows,
so applying this identity to each cell proves raw truncation equivalence
between a donor and its projection to `λ`, for every `δ < λ`.

**Density.** Fix `δ < λ` and an instance of `D[δ]`: an invariant `t`
realized by a positive-length tuple `x` and a legal donor `u` extending
`t` on its first places. Fixedness makes `t` a `λ`-fixed class. Project
`u` to `λ`, obtaining a legal, `λ`-fixed class `v`. Projection commutes
with faces, so the first face of `v` is still `t`. Choose enumerated
chart representatives and align their cells along this face using
`TemplateClass.exists_renaming_restrictFace_eq`; the chart-face
correspondence gives the required embedding of the chart of `t` into
the chart of `v`. Diagram compatibility makes `x` an embedding of the
chart of `t` into `F`. The extension property supplies an embedding of
the chart of `v` into `F` restricting to `x`. Its remaining coordinates
give `y`, with `Q_v(x,y)` true. The raw truncation identity above gives
`v.TruncEquiv δ u`, so `v` and `y` witness the required disjunct in
`D[δ]`. This includes zero additional coordinates. No empty base chart
is needed, because the density instance has a positive-length base.

Thus the chain construction, with these checks, gives the mathematical
argument for `F ∈ Kβ` and the chart extension property in Lemma 4.33.
The implementation constructs the limit and proves its stage-class membership;
neither `F ∈ Kβ` nor its extension property is assumed as input.
For the density proof it takes the actual face of the projected donor as the
base chart, whose global class is the original invariant. This avoids a
separate representative-renaming step without changing the construction.
This does not establish a spectrum transfer between
the two different witness sentences.

Additional fixed-revision evidence:
[raw labels and unrestricted absorption](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/348f38d92c3cd67968ccfb79102f0c7a96d0be33/VaughtConjecture/Label/Basic.lean),
[density and the stage class](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/348f38d92c3cd67968ccfb79102f0c7a96d0be33/VaughtConjecture/Correspondence/Density/Density.lean),
[compatibility and structure projection](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/348f38d92c3cd67968ccfb79102f0c7a96d0be33/VaughtConjecture/Correspondence/Density/Language.lean).

The published Theorem 4.36 concerns its particular `σ[L]` and also uses the Fraïssé-limit step of Lemma 4.33.
The definition dictionary alone does not supply that lemma or an identification of the
published construction with the main formalized witness. The separate validation
now supplies the lemma using the published-definition dictionary.
The direct-route Lean implementation now constructs a countable chain of charts meeting every embedding
request, forms its limit, and verifies compatibility, fixedness at `blockStage β`,
and every density axiom below that cutoff.
Ordinary hereditary closure under all finite substructures must not be
assumed: the published hereditary property is restricted to nonempty closed subsets.
The existence result can continue to be cited without presenting those unestablished correspondences as facts.
