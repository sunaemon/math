module

public import PolishSpaceBook.LusinSuslinRefinement
public import PolishSpaceBook.EffrosBorelTrees
public import PolishSpaceBook.PerfectSetsStandardBorelCoding

@[expose] public section

/-! # Local consequences and the codomain boundary of Lusin–Suslin -/
namespace PolishSpaceBook
open Set Function TopologicalSpace Topology MeasureTheory
universe u v

/-- Equal generated sigma algebras give exactly the same measurable maps. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, a Borel-preserving topology refinement cannot turn a non-Borel selector
    into a Borel map, since it leaves the Borel sets unchanged.
-/
theorem measurable_iff_of_borel_eq {X : Type u} {Y : Type v}
    (t t' : TopologicalSpace X) (s s' : TopologicalSpace Y)
    (hX : @borel X t = @borel X t') (hY : @borel Y s = @borel Y s') (f : X → Y) :
    @Measurable X Y (@borel X t) (@borel Y s) f ↔
      @Measurable X Y (@borel X t') (@borel Y s') f := by
  rw [hX, hY]

section StandardBorel
variable {X : Type u} {Y : Type v}
  [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]

/-- Choose compatible Polish presentations and apply the preceding
Lusin–Suslin theorem to every Borel subset of the domain. -/
theorem measurable_injection_embedding {f : X → Y} (hf : Measurable f) (hi : Injective f) :
    MeasurableEmbedding f := by
  let := upgradeStandardBorel X
  let := upgradeStandardBorel Y
  exact ⟨hi, hf, fun A hA => (lusinSuslin hA hf hi.injOn).1⟩

/-- The right-inverse equation gives injectivity; Lusin–Suslin then supplies
Borel range and the canonical standard-Borel structure on that subspace. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A *Borel section* of a Borel map between standard Borel spaces has Borel range: as a right inverse,
        it is injective, so Lusin--Suslin applies. The chosen representatives therefore form a standard Borel subspace.
-/
theorem measurable_section_range {r : Y → X} {s : X → Y}
    (hs : Measurable s) (hsec : RightInverse s r) :
    Injective s ∧ MeasurableSet (range s) ∧ StandardBorelSpace (range s) := by
  have hi : Injective s := by
    intro a b h
    simpa only [hsec a, hsec b] using congrArg r h
  have hm : MeasurableEmbedding s := measurable_injection_embedding hs hi
  have hr := hm.measurableSet_range
  exact ⟨hi, hr, hr.standardBorel⟩

/-- Borel injections become measurable embeddings by Lusin–Suslin; the existing
iterate-and-patch construction then gives Borel Schröder–Bernstein. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    It is the engine of the *Borel Schröder–Bernstein theorem* used in the proof of Kuratowski's isomorphism theorem
        in §{sec:kuratowski-isomorphism}: the two Borel injections produced there have Borel images precisely by
        Lusin–Suslin.
-/
theorem borel_schroeder_bernstein_of_injections {f : X → Y} {g : Y → X}
    (hf : Measurable f) (hg : Measurable g) (hi : Injective f) (hj : Injective g) :
    Nonempty (X ≃ᵐ Y) :=
  borelSchroederBernstein_exists (measurable_injection_embedding hf hi) (measurable_injection_embedding hg hj)

/-- Inverse preimages are the Borel images given by Lusin–Suslin. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    It is the reason a *Borel bijection* between Polish spaces is automatically a Borel isomorphism — its inverse is
        Borel for free, with no need to construct it explicitly.
-/
theorem measurable_equiv_inverse (e : X ≃ Y) (he : Measurable e) : Measurable e.symm := by
  have hm : MeasurableEmbedding e := measurable_injection_embedding he e.injective
  intro A hA
  have him := hm.measurableSet_image' hA
  simpa only [e.image_eq_preimage_symm] using him

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    It is the reason a *Borel bijection* between Polish spaces is automatically a Borel isomorphism — its inverse is
        Borel for free, with no need to construct it explicitly.
-/
theorem measurable_bijection_inverse {f : X → Y} (hf : Measurable f) (hb : Bijective f) :
    Measurable (Equiv.ofBijective f hb).symm :=
  measurable_equiv_inverse (Equiv.ofBijective f hb) hf

end StandardBorel

/-- Embed the separable metrizable codomain in the Hilbert cube, apply the
Polish-codomain theorem, then pull the image back along that embedding. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The codomain hypothesis can be relaxed from Polish to separable metrizable by embedding the codomain into a
    Polish space.
-/
theorem lusinSuslin_separable_metrizable_codomain
    {X : Type u} {Y : Type v} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [MetrizableSpace Y]
    [SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} {B : Set X}
    (hB : MeasurableSet B) (hf : Measurable f) (hi : InjOn f B) :
    MeasurableSet (f '' B) := by
  let := metrizableSpaceMetric Y
  obtain ⟨e, he⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := Y)
  let : PolishSpace hilbert_cube := hilbert_cube_polish
  have him : MeasurableSet ((e ∘ f) '' B) :=
    (lusinSuslin hB (he.continuous.measurable.comp hf)
      (fun a ha b hb h => hi ha hb (he.injective h))).1
  have hp := he.continuous.measurable him
  have heq : e ⁻¹' ((e ∘ f) '' B) = f '' B := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, he.injective hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rwa [heq] at hp

/-- Only a compatible Polish presentation of the source is needed. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    What the proof fundamentally uses on the source side is its standard Borel
    structure.
-/
theorem lusinSuslin_standardBorel_metrizable_codomain
    {X : Type u} {Y : Type v} [MeasurableSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y} {B : Set X}
    (hB : MeasurableSet B) (hf : Measurable f) (hi : InjOn f B) :
    MeasurableSet (f '' B) := by
  let := upgradeStandardBorel X
  exact lusinSuslin_separable_metrizable_codomain hB hf hi

/-- The only open generators of the indiscrete topology are empty and universal. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For arbitrary topological codomains, however, the conclusion can fail even though Borelness remains
    well-defined. For example, give an uncountable Polish space $X$ the indiscrete topology in the codomain. The identity
    from the original Polish $X$ to this codomain is Borel and injective, but the image of a nontrivial Borel subset of $X$
    is not Borel in the indiscrete codomain.
-/
theorem borel_indiscrete (X : Type u) : @borel X ⊤ = ⊥ := by
  apply le_antisymm ?_ bot_le
  change MeasurableSpace.generateFrom {U | IsOpen[⊤] U} ≤ ⊥
  apply MeasurableSpace.generateFrom_le
  intro U hU
  exact MeasurableSpace.measurableSet_bot_iff.mpr ((TopologicalSpace.isOpen_top_iff U).mp hU)

/-- The identity into the indiscrete topology is a Borel injection, but a proper
nonempty singleton image is not Borel there. In particular this applies to
any uncountable Polish space, with exactly the codomain change in the book. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For arbitrary topological codomains, however, the conclusion can fail even though Borelness remains
    well-defined. For example, give an uncountable Polish space $X$ the indiscrete topology in the codomain. The identity
    from the original Polish $X$ to this codomain is Borel and injective, but the image of a nontrivial Borel subset of $X$
    is not Borel in the indiscrete codomain.
-/
theorem indiscrete_codomain_counterexample (X : Type u) [TopologicalSpace X]
    [T1Space X] [Nontrivial X] :
    @Measurable X X (borel X) (@borel X ⊤) id ∧ Injective (id : X → X) ∧
      ∃ B : Set X, @MeasurableSet X (borel X) B ∧
        ¬ @MeasurableSet X (@borel X ⊤) (id '' B) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  have hm : @Measurable X X (borel X) (@borel X ⊤) id := by
    rw [borel_indiscrete]
    intro U hU
    rcases MeasurableSpace.measurableSet_bot_iff.mp hU with rfl | rfl <;> simp
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  refine ⟨hm, injective_id, {x}, measurableSet_singleton x, ?_⟩
  rw [image_id, borel_indiscrete, MeasurableSpace.measurableSet_bot_iff]
  rintro (h | h)
  · exact singleton_ne_empty x h
  · have hy : y ∈ ({x} : Set X) := h.symm ▸ mem_univ y
    exact hxy (mem_singleton_iff.mp hy).symm

section Effros
attribute [local instance] EffrosBorel.measurableSpace

/-- The cylinder-hit construction already gives an actual measurable
isomorphism, including the empty closed set and the empty pruned tree. -/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *Trees as a Borel parameter space.* The Baire-space case identifies $\ClosedSets{\BaireSpace}$ with the standard Borel
    space of
    pruned trees. Constructions parameterized by a closed set — the analytic-set scheme of
    §{sec:souslin-operation-suslin-schemes}, the Lusin--Suslin prefix proof of §{sec:lusin-souslin-proof}, and the
    \termuseas{perfect kernel}{Cantor–Bendixson kernel} of §{sec:cantor-bendixson} — thereby become constructions
    parameterized by an element of a standard Borel space, with all the ordinary descriptive-set-theoretic machinery
    available.
-/
noncomputable def closedBaire_prunedTree_measurableEquiv :
    TopologicalSpace.Closeds (ℕ → ℕ) ≃ᵐ EffrosBorel.prunedIndicators :=
  EffrosBorel.closedIndicatorMeasurableEquiv

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *Trees as a Borel parameter space.* The Baire-space case identifies $\ClosedSets{\BaireSpace}$ with the standard Borel
    space of
    pruned trees. Constructions parameterized by a closed set — the analytic-set scheme of
    §{sec:souslin-operation-suslin-schemes}, the Lusin--Suslin prefix proof of §{sec:lusin-souslin-proof}, and the
    \termuseas{perfect kernel}{Cantor–Bendixson kernel} of §{sec:cantor-bendixson} — thereby become constructions
    parameterized by an element of a standard Borel space, with all the ordinary descriptive-set-theoretic machinery
    available.
-/
theorem closedBaire_standardBorel_from_prunedTrees :
    StandardBorelSpace (TopologicalSpace.Closeds (ℕ → ℕ)) :=
  EffrosBorel.baire_standardBorel_via_pruned_trees

end Effros
end PolishSpaceBook
