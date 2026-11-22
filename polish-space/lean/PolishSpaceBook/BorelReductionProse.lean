module

public import PolishSpaceBook.LusinSuslinRefinement
public import PolishSpaceBook.E0Nonsmooth
public import PolishSpaceBook.ConcreteCantorBaireModels
public import PolishSpaceBook.SilverDichotomy
public import PolishSpaceBook.PerfectSetsStandardBorelCoding

@[expose] public section

namespace PolishSpaceBook.BorelReductionProse
noncomputable section
open Set MeasureTheory MeasurableSpace Function Cardinal

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Equality on any standard Borel space is trivially smooth.
-/
/-- Identity is a standard-Borel-valued complete invariant for equality. -/
theorem equality_smooth {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] :
    Smooth (Eq : X → X → Prop) :=
  smooth_of_standardBorel_completeInvariant measurable_id (fun _ _ => Iff.rfl)

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Any Borel equivalence relation with countably many classes is \termuse{smooth}: enumerate the classes and assign
        each $x$ its index. Each class is Borel because it is a section of $E$, so the index map is Borel.
-/
/-- Enumerate quotient classes, prove their sections Borel, and use the index
as the complete invariant. No Borel choice of representatives is assumed. -/
theorem smooth_of_countable_quotient {X : Type*} [MeasurableSpace X]
    (E : Setoid X) [Countable (Quotient E)]
    (hE : MeasurableSet {p : X × X | E.r p.1 p.2}) : Smooth E.r := by
  classical
  let : Encodable (Quotient E) := Encodable.ofCountable _
  let f : X → ℕ := fun x => Encodable.encode (Quotient.mk E x)
  have hclass (z : Quotient E) : MeasurableSet {x | E.r x z.out} :=
    hE.preimage (measurable_id.prodMk measurable_const)
  have hf : Measurable f := by
    intro B _
    have he : f ⁻¹' B = ⋃ z : {q : Quotient E // Encodable.encode q ∈ B},
        {x | E.r x z.val.out} := by
      ext x
      constructor
      · intro hx
        refine mem_iUnion.mpr ⟨⟨Quotient.mk E x, hx⟩, ?_⟩
        exact Quotient.exact (Quotient.out_eq (Quotient.mk E x)).symm
      · intro hx
        obtain ⟨z, hz⟩ := mem_iUnion.mp hx
        have hq : Quotient.mk E x = z.val :=
          (Quotient.sound hz).trans (Quotient.out_eq z.val)
        change Encodable.encode (Quotient.mk E x) ∈ B
        rw [hq]
        exact z.property
    rw [he]
    exact MeasurableSet.iUnion fun z => hclass z.val
  apply smooth_of_standardBorel_completeInvariant hf
  intro x y
  exact ⟨fun h => congrArg Encodable.encode (Quotient.sound h),
    fun h => Quotient.exact (Encodable.encode_injective h)⟩

/-- The actual continued-fraction homeomorphism, rather than an arbitrary
Borel coding, embeds Baire space into the irrational real line. -/
theorem continued_fraction_embedding :
    ∃ f : baire_space → ℝ, Continuous f ∧ Injective f ∧ range f = {x | Irrational x} ∧
      MeasurableSet (range f) := by
  obtain ⟨θ⟩ := continuedFractionBaireHomeomorphismFact
  let f : baire_space → ℝ := fun p => (θ.symm p).val
  refine ⟨f, continuous_subtype_val.comp θ.symm.continuous,
    Subtype.val_injective.comp θ.symm.injective, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact (θ.symm p).property
    · intro hx
      exact ⟨θ ⟨x, hx⟩, by simp [f]⟩
  · have hc : Continuous f := continuous_subtype_val.comp θ.symm.continuous
    have hi : Injective f := Subtype.val_injective.comp θ.symm.injective
    simpa only [image_univ] using
      (lusinSuslin_via_prefix_refinement MeasurableSet.univ hc.measurable hi.injOn).1

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    For example, equality on $\BaireSpace$ is smooth: the continued-fraction homeomorphism
    $\BaireSpace\cong\SetDifference{\R}{\QQ}$ from §{sec:simple-continued-fractions} embeds $\BaireSpace$ into $\R$ as a
    Borel
    subset, and equality of Baire-space codes becomes ordinary equality of the corresponding irrational reals.
-/
/-- This specific real-valued complete invariant is supplied by continued
fractions, in the same direction as in the book. -/
theorem baire_equality_smooth_via_continued_fractions :
    Smooth (Eq : baire_space → baire_space → Prop) := by
  obtain ⟨f, hf, hi, _⟩ := continued_fraction_embedding
  exact ⟨f, hf.measurable, fun _ _ => ⟨congrArg f, fun h => hi h⟩⟩

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    A Borel equivalence relation $E$ on a standard Borel space $X$ is a \termdefine{countable Borel equivalence relation} if
    every $E$-class is countable.
-/
/-- Canonical Borelness of the relation together with countability of each section. -/
def CountableBorelEquivalenceRelation {X : Type*} [MeasurableSpace X] (E : Setoid X) : Prop :=
  MeasurableSet {p : X × X | E.r p.1 p.2} ∧ ∀ x, {y | E.r x y}.Countable

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    In the latter case $|X/E| = 2^{\alephNull}$, so the cardinality of $X/E$ never lands strictly between $\alephNull$
    and $2^{\alephNull}$ — even when CH fails.
-/
/-- A Cantor antichain gives the lower bound and the quotient map from a
Polish space gives the matching upper bound, independently of CH. -/
theorem quotient_cardinal_of_cantor_antichain {X : Type} [TopologicalSpace X]
    [PolishSpace X] (E : Setoid X) (π : cantor_space → X)
    (hanti : ∀ a b, a ≠ b → ¬ E.r (π a) (π b)) : #(Quotient E) = 𝔠 := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨g, _, hg⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated X
  have hX : #X ≤ #cantor_space := Cardinal.mk_le_of_injective hg
  have hQ : #(Quotient E) ≤ #X :=
    Cardinal.mk_le_of_surjective (show Surjective (Quotient.mk E) from Quotient.mk_surjective)
  have hi : Injective (fun a => Quotient.mk E (π a)) := by
    intro a b hab
    by_contra hn
    exact hanti a b hn (Quotient.exact hab)
  have hlow : #cantor_space ≤ #(Quotient E) := Cardinal.mk_le_of_injective hi
  rw [← cantorSpace_cardinal]
  exact le_antisymm (hQ.trans hX) hlow

/-- Restriction to the first N coordinates injects each finite E0 stage into
exactly 2^N binary strings, giving the stated numerical bound. -/
theorem e0At_class_card_le (N : ℕ) (x : ℕ → Bool) :
    Nat.card {y // E0At N x y} ≤ 2 ^ N := by
  let f : {y // E0At N x y} → (Fin N → Bool) := fun y i => y.val i
  have hi : Injective f := by
    intro y z h
    apply Subtype.ext
    funext n
    by_cases hn : n < N
    · exact congrFun h ⟨n, hn⟩
    · exact (y.property n (by omega)).symm.trans (z.property n (by omega))
  have h := Nat.card_le_card_of_injective f hi
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using h

/-- This concrete Borel countable relation is not smooth. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    $\EventualEqualityER$ itself
    is countable,
    but countability of classes does not imply smoothness
-/
theorem e0_countable_borel_nonsmooth :
    MeasurableSet {p : cantor_space × cantor_space | E0 p.1 p.2} ∧
      (∀ x, {y | E0 x y}.Countable) ∧ ¬ Smooth E0 :=
  ⟨measurableSet_e0, e0_class_countable, e0_not_smooth⟩

/-- The explicit finite approximations carry both the hyperfinite structure
and the numerical class-size bound. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    ; each $E_n$-class has size at most $2^n$, and $\bigcup_n
    E_n=\EventualEqualityER$.
-/
theorem e0_hyperfinite_with_bounds : Hyperfinite E0 ∧
    ∀ n x, Nat.card {y // E0At n x y} ≤ 2 ^ n :=
  ⟨e0_hyperfinite, e0At_class_card_le⟩

end
end PolishSpaceBook.BorelReductionProse
