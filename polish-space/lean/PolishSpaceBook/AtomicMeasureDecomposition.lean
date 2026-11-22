module

public import PolishSpaceBook.MeasureAlgebra
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Order.Atoms

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Atoms and the atomic/nonatomic decomposition

Use the countable point-separating family from the book to concentrate every
measure-algebra atom on a singleton. Restriction to the positive-mass points
and their complement then gives the two factors of the measure algebra.
-/

noncomputable section
namespace PolishSpaceBook.AtomicMeasureDecomposition

open Set Filter MeasureTheory MeasurableSpace Function
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- A Boolean atom chooses one side of every measurable test. -/
lemma atom_le_or_le_compl {a c : MeasureAlgebra μ} (ha : IsAtom a) : a ≤ c ∨ a ≤ cᶜ := by
  rcases ha.le_iff.mp (inf_le_left : a ⊓ c ≤ a) with h | h
  · exact Or.inr (le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr h))
  · exact Or.inl (h ▸ (inf_le_right : a ⊓ c ≤ c))

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    First let $E$ be an atom, and choose a countable point-separating Borel family $\Sequence{G_n}{n\in\omega}$.
    For each $n$, put
    $$V_n:=
    \begin{cases}
    G_n,&\mu(E\cap G_n)=\mu(E),\\
    \SetDifference{X}{G_n},&\mu(E\cap G_n)=0.
    \end{cases}$$
    Then $\mu(\SetDifference{E}{V_n})=0$. Consequently
    $$C:=E\cap\bigcap_n V_n\qquad\text{satisfies}\qquad\mu(C)=\mu(E)>0.$$
    All points of $C$ have the same membership pattern in the separating family, so $C$ has at most one point.
    Thus $C=\{x\}$ for some $x$, and $\mu(\SetDifference{E}{\{x\}})=0$. Every atom is therefore concentrated at a point.
-/
/-- Every measure-algebra atom has a singleton representative. -/
theorem atom_is_singleton [CountablyGenerated X] [SeparatesPoints X] [MeasurableSingletonClass X]
    {a : MeasureAlgebra μ} (ha : IsAtom a) :
    ∃ x : X, 0 < μ {x} ∧ a = MeasureAlgebra.mk {x} (measurableSet_singleton x) := by
  classical
  let S : Set X := MeasureAlgebra.representative a
  have hS : MeasurableSet S := (MeasureAlgebra.representative a).property
  have hrep : MeasureAlgebra.mk S hS = a := MeasureAlgebra.mk_representative a
  let G (n : ℕ) := natGeneratingSequence X n
  have hG n : MeasurableSet (G n) := measurableSet_natGeneratingSequence n
  let V (n : ℕ) := if a ≤ MeasureAlgebra.mk (G n) (hG n) then G n else (G n)ᶜ
  have hV n : MeasurableSet (V n) := by
    dsimp [V]
    split_ifs
    · exact hG n
    · exact (hG n).compl
  have hle n : S ≤ᵐ[μ] V n := by
    change (MeasureAlgebra.mk S hS : MeasureAlgebra μ) ≤ MeasureAlgebra.mk (V n) (hV n)
    rw [hrep]
    dsimp [V]
    split_ifs with h
    · exact h
    · exact (atom_le_or_le_compl μ ha).resolve_left h
  let C : Set X := S ∩ ⋂ n, V n
  have hC : MeasurableSet C := hS.inter (MeasurableSet.iInter hV)
  have hEq : C =ᵐ[μ] S := by
    filter_upwards [ae_all_iff.mpr hle] with x hx
    apply propext
    exact ⟨And.left, fun h => ⟨h, mem_iInter.mpr fun n => hx n h⟩⟩
  have hsingle : C.Subsingleton := by
    intro x hx y hy
    apply injective_mapNatBool X
    funext n
    have hxV := mem_iInter.mp hx.2 n
    have hyV := mem_iInter.mp hy.2 n
    dsimp [V] at hxV hyV
    split_ifs at hxV hyV with h
    · change x ∈ G n at hxV
      change y ∈ G n at hyV
      simpa only [G, mapNatBool] using congrArg (fun b : Prop => decide b) (propext (iff_of_true hxV hyV))
    · change x ∉ G n at hxV
      change y ∉ G n at hyV
      simpa only [G, mapNatBool] using congrArg (fun b : Prop => decide b) (propext (iff_of_false hxV hyV))
  have hmass : μ C ≠ 0 := by
    intro hz
    apply ha.ne_bot
    rw [← hrep, ← (MeasureAlgebra.mk_eq_mk hC hS).mpr hEq]
    exact (MeasureAlgebra.mk_eq_bot C hC).mpr hz
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hmass
  have hc : C = {x} := hsingle.eq_singleton_of_mem hx
  have heq : a = MeasureAlgebra.mk {x} (measurableSet_singleton x) := by
    rw [← hrep]
    apply (MeasureAlgebra.mk_eq_mk _ _).mpr
    simpa only [hc] using hEq.symm
  exact ⟨x, pos_iff_ne_zero.mpr (hc ▸ hmass), heq⟩

/-- A singleton of positive mass is an atom in the canonical quotient order. -/
theorem singleton_isAtom [MeasurableSingletonClass X] {x : X} (hx : 0 < μ {x}) :
    IsAtom (MeasureAlgebra.mk {x} (measurableSet_singleton x) : MeasureAlgebra μ) := by
  apply isAtom_iff_le_of_ge.mpr
  refine ⟨fun h => hx.ne' ((MeasureAlgebra.mk_eq_bot _ _).mp h), ?_⟩
  intro b hb hle
  induction b using Quotient.inductionOn with
  | h T =>
    change (T : Set X) ≤ᵐ[μ] ({x} : Set X) at hle
    by_cases hxt : x ∈ (T : Set X)
    · exact Eventually.of_forall fun y hy => by
        have heq : y = x := mem_singleton_iff.mp hy
        exact heq.symm ▸ hxt
    · exfalso
      apply hb
      apply (MeasureAlgebra.mk_eq_bot _ _).mpr
      apply ae_eq_empty.mp
      filter_upwards [hle] with y hy
      apply propext
      refine ⟨fun h => ?_, False.elim⟩
      have heq : y = x := mem_singleton_iff.mp (hy h)
      exact (hxt (heq ▸ h)).elim

/-- The measure-algebra and point-mass meanings of atom agree in a countably
separated measurable space. -/
theorem isAtom_iff_singleton [CountablyGenerated X] [SeparatesPoints X] [MeasurableSingletonClass X]
    (a : MeasureAlgebra μ) :
    IsAtom a ↔ ∃ x : X, 0 < μ {x} ∧ a = MeasureAlgebra.mk {x} (measurableSet_singleton x) := by
  constructor
  · exact atom_is_singleton μ
  · rintro ⟨x, hx, rfl⟩
    exact singleton_isAtom μ hx

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    The atoms are the only extra data in the finite-measure case. For a finite Borel measure $\mu$, an
    \termdefine{atom of a measure} is a Borel set $E$ with $\mu(E)>0$ such that every Borel $F\IncludedIn E$ satisfies
    $\mu(F)=0$ or $\mu(F)=\mu(E)$. Equivalently, its class is an atom of the Boolean algebra $\MeasureAlg{X}{\mu}$.
-/
/-- The usual measurable-set definition of an atom agrees with `IsAtom` in
the measure algebra. Finiteness converts equal mass into equality modulo null sets. -/
theorem isAtom_mk_iff [IsFiniteMeasure μ] {E : Set X} (hE : MeasurableSet E) :
    IsAtom (MeasureAlgebra.mk E hE : MeasureAlgebra μ) ↔
      0 < μ E ∧ ∀ B : Set X, MeasurableSet B → B ⊆ E → μ B = 0 ∨ μ B = μ E := by
  constructor
  · intro ha
    refine ⟨pos_iff_ne_zero.mpr (fun hz => ha.ne_bot ((MeasureAlgebra.mk_eq_bot E hE).mpr hz)), ?_⟩
    intro B hB hBE
    have hle : (MeasureAlgebra.mk B hB : MeasureAlgebra μ) ≤ MeasureAlgebra.mk E hE :=
      Eventually.of_forall hBE
    rcases ha.le_iff.mp hle with h | h
    · exact Or.inl ((MeasureAlgebra.mk_eq_bot B hB).mp h)
    · exact Or.inr (congrArg MeasureAlgebra.mass h)
  · rintro ⟨hpos, hatom⟩
    apply isAtom_iff_le_of_ge.mpr
    refine ⟨fun h => hpos.ne' ((MeasureAlgebra.mk_eq_bot E hE).mp h), ?_⟩
    intro b hb hle
    induction b using Quotient.inductionOn with
    | h T =>
      have hTE : ((T : Set X) ∩ E : Set X) =ᵐ[μ] (T : Set X) := by
        filter_upwards [hle] with x hx
        apply propext
        exact ⟨And.left, fun h => ⟨h, hx h⟩⟩
      have hn : μ ((T : Set X) ∩ E) ≠ 0 := by
        intro hz
        apply hb
        have hm : μ (T : Set X) = 0 := (measure_congr hTE).symm.trans hz
        exact (MeasureAlgebra.mk_eq_bot _ _).mpr hm
      have hm := (hatom _ (T.property.inter hE) inter_subset_right).resolve_left hn
      have hEq := ae_eq_of_subset_of_measure_ge inter_subset_right hm.ge
        (T.property.inter hE).nullMeasurableSet (measure_ne_top μ E)
      exact le_of_eq (Quotient.sound (hTE.symm.trans hEq)).symm

/-- Points carrying positive mass. -/
def atomicPoints : Set X := {x | 0 < μ {x}}

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For each $n\ge1$, the set
    $$A_n:=\{x\in X:\mu(\{x\})\ge1/n\}$$
    is finite: any $k$ distinct members would contribute total mass at least $k/n$, bounded by $\mu(X)$.
    Since $A=\bigcup_{n\ge1}A_n$, the set $A$ is countable and Borel.
-/
lemma finite_heavy_points [IsFiniteMeasure μ] [MeasurableSingletonClass X] (n : ℕ) :
    {x : X | (n : ℝ≥0∞)⁻¹ ≤ μ {x}}.Finite := by
  apply Measure.finite_const_le_meas_of_disjoint_iUnion μ
    (pos_iff_ne_zero.mpr (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)))
    (fun x => measurableSet_singleton x) (fun x y h => by simpa using h)
  exact measure_ne_top _ _

lemma atomicPoints_countable [IsFiniteMeasure μ] [MeasurableSingletonClass X] :
    (atomicPoints μ).Countable := by
  apply (countable_iUnion fun n => (finite_heavy_points μ n).countable).mono
  intro x hx
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hx.ne'
  exact mem_iUnion.mpr ⟨n, hn.le⟩

lemma atomicPoints_measurable [IsFiniteMeasure μ] [MeasurableSingletonClass X] :
    MeasurableSet (atomicPoints μ) := (atomicPoints_countable μ).measurableSet

/-- The measure on the measurable subspace, rather than an ambient measure
that merely vanishes outside it. -/
def subspaceMeasure (S : Set X) : Measure S := μ.comap Subtype.val

/-- Restrict a quotient class to a measurable part. -/
def toPart (S : Set X) (hS : MeasurableSet S) :
    MeasureAlgebra μ → MeasureAlgebra (subspaceMeasure μ S) :=
  Quotient.lift (fun T => MeasureAlgebra.mk (Subtype.val ⁻¹' (T : Set X))
    (T.property.preimage measurable_subtype_coe)) (by
      intro T U h
      apply Quotient.sound
      exact (ae_restrict_iff_subtype hS).mp (ae_restrict_of_ae h))

@[simp] lemma toPart_mk (S : Set X) (hS : MeasurableSet S) (T : Set X) (hT : MeasurableSet T) :
    toPart μ S hS (MeasureAlgebra.mk T hT) =
      MeasureAlgebra.mk (Subtype.val ⁻¹' T) (hT.preimage measurable_subtype_coe) := rfl

/-- The two restrictions, with the complementary part first. -/
def splitMap (S : Set X) (hS : MeasurableSet S) (a : MeasureAlgebra μ) :
    MeasureAlgebra (subspaceMeasure μ Sᶜ) × MeasureAlgebra (subspaceMeasure μ S) :=
  (toPart μ Sᶜ hS.compl a, toPart μ S hS a)

lemma splitMap_le_iff (S : Set X) (hS : MeasurableSet S) (a b : MeasureAlgebra μ) :
    splitMap μ S hS a ≤ splitMap μ S hS b ↔ a ≤ b := by
  induction a using Quotient.inductionOn with
  | h A =>
    induction b using Quotient.inductionOn with
    | h B =>
      change ((Subtype.val ⁻¹' (A : Set X)) ≤ᵐ[subspaceMeasure μ Sᶜ]
        (Subtype.val ⁻¹' (B : Set X))) ∧
        ((Subtype.val ⁻¹' (A : Set X)) ≤ᵐ[subspaceMeasure μ S]
        (Subtype.val ⁻¹' (B : Set X))) ↔ (A : Set X) ≤ᵐ[μ] (B : Set X)
      constructor
      · rintro ⟨hc, hs⟩
        exact ae_of_ae_restrict_of_ae_restrict_compl S
          ((ae_restrict_iff_subtype hS).mpr hs) ((ae_restrict_iff_subtype hS.compl).mpr hc)
      · intro h
        exact ⟨(ae_restrict_iff_subtype hS.compl).mp (ae_restrict_of_ae h),
          (ae_restrict_iff_subtype hS).mp (ae_restrict_of_ae h)⟩

lemma splitMap_surjective (S : Set X) (hS : MeasurableSet S) : Surjective (splitMap μ S hS) := by
  intro z
  let C := MeasureAlgebra.representative z.1
  let D := MeasureAlgebra.representative z.2
  let E : Set X := (Subtype.val '' (C : Set ↥(Sᶜ))) ∪ (Subtype.val '' (D : Set S))
  have hE : MeasurableSet E :=
    ((MeasurableEmbedding.subtype_coe hS.compl).measurableSet_image' C.property).union
      ((MeasurableEmbedding.subtype_coe hS).measurableSet_image' D.property)
  refine ⟨MeasureAlgebra.mk E hE, ?_⟩
  apply Prod.ext
  · change MeasureAlgebra.mk (Subtype.val ⁻¹' E) _ = z.1
    rw [← MeasureAlgebra.mk_representative z.1]
    apply (MeasureAlgebra.mk_eq_mk _ _).mpr
    apply Eventually.of_forall
    intro x
    apply propext
    change x.val ∈ E ↔ x ∈ (C : Set ↥(Sᶜ))
    dsimp [E]
    simp only [mem_union, Subtype.coe_injective.mem_set_image]
    constructor
    · rintro (h | ⟨y, _, heq⟩)
      · exact h
      · exact (x.property (heq ▸ y.property)).elim
    · exact Or.inl
  · change MeasureAlgebra.mk (Subtype.val ⁻¹' E) _ = z.2
    rw [← MeasureAlgebra.mk_representative z.2]
    apply (MeasureAlgebra.mk_eq_mk _ _).mpr
    apply Eventually.of_forall
    intro x
    apply propext
    change x.val ∈ E ↔ x ∈ (D : Set S)
    dsimp [E]
    simp only [mem_union, Subtype.coe_injective.mem_set_image]
    constructor
    · rintro (⟨y, _, heq⟩ | h)
      · exact (y.property (heq.symm ▸ x.property)).elim
      · exact h
    · exact Or.inr

/-- Splitting by a measurable set gives an order isomorphism, hence a Boolean
algebra isomorphism. -/
def splitEquiv (S : Set X) (hS : MeasurableSet S) :
    MeasureAlgebra μ ≃o
      MeasureAlgebra (subspaceMeasure μ Sᶜ) × MeasureAlgebra (subspaceMeasure μ S) where
  toEquiv := Equiv.ofBijective (splitMap μ S hS)
    ⟨fun a b h => le_antisymm ((splitMap_le_iff μ S hS a b).mp h.le)
      ((splitMap_le_iff μ S hS b a).mp h.ge), splitMap_surjective μ S hS⟩
  map_rel_iff' := splitMap_le_iff μ S hS _ _

lemma split_mass (S : Set X) (hS : MeasurableSet S) (a : MeasureAlgebra μ) :
    MeasureAlgebra.mass a = MeasureAlgebra.mass (splitEquiv μ S hS a).1 +
      MeasureAlgebra.mass (splitEquiv μ S hS a).2 := by
  induction a using Quotient.inductionOn with
  | h T =>
    change μ (T : Set X) = (subspaceMeasure μ Sᶜ) (Subtype.val ⁻¹' (T : Set X)) +
      (subspaceMeasure μ S) (Subtype.val ⁻¹' (T : Set X))
    rw [subspaceMeasure, subspaceMeasure,
      (MeasurableEmbedding.subtype_coe hS.compl).comap_preimage,
      (MeasurableEmbedding.subtype_coe hS).comap_preimage]
    simp only [Subtype.range_coe]
    exact (measure_inter_add_sdiff (T : Set X) hS).symm.trans (by rw [add_comm]; rfl)

/-- At a point of positive mass an almost-everywhere assertion must hold. -/
lemma forall_of_ae_positive_singletons (hpos : ∀ x : X, 0 < μ {x})
    {p : X → Prop} (h : ∀ᵐ x ∂μ, p x) : ∀ x, p x := by
  intro x
  by_contra hx
  have hle : μ {x} ≤ μ {y | ¬ p y} := measure_mono (singleton_subset_iff.mpr hx)
  exact (hpos x).not_ge (hle.trans_eq (ae_iff.mp h))

/-- On a countable space whose points all have positive mass, the measure
algebra is exactly its powerset, with no further identifications. -/
def discreteEquiv [Countable X] [MeasurableSingletonClass X]
    (hpos : ∀ x : X, 0 < μ {x}) : MeasureAlgebra μ ≃o Set X where
  toFun := Quotient.lift (fun T => (T : Set X)) (fun _ _ h =>
    funext (forall_of_ae_positive_singletons μ hpos h))
  invFun S := MeasureAlgebra.mk S S.to_countable.measurableSet
  left_inv a := Quotient.inductionOn a fun _ => rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro a b
    induction a using Quotient.inductionOn with
    | h A =>
      induction b using Quotient.inductionOn with
      | h B =>
        change (A : Set X) ⊆ (B : Set X) ↔ (A : Set X) ≤ᵐ[μ] (B : Set X)
        exact ⟨Eventually.of_forall, forall_of_ae_positive_singletons μ hpos⟩

lemma discreteEquiv_mass [Countable X] [MeasurableSingletonClass X]
    (hpos : ∀ x : X, 0 < μ {x}) (a : MeasureAlgebra μ) :
    MeasureAlgebra.mass a = μ (discreteEquiv μ hpos a) :=
  Quotient.inductionOn a fun _ => rfl

/-- Canonical `NullSingletonClass` agrees with the absence of Boolean atoms in the book's
countably separated setting. -/
theorem noAtoms_iff_no_algebra_atoms [CountablyGenerated X] [SeparatesPoints X]
    [MeasurableSingletonClass X] : NullSingletonClass μ ↔ ∀ a : MeasureAlgebra μ, ¬ IsAtom a := by
  constructor
  · intro h a ha
    let := h
    obtain ⟨x, hx, _⟩ := atom_is_singleton μ ha
    simp only [measure_singleton, lt_self_iff_false] at hx
  · intro h
    refine ⟨fun x => ?_⟩
    by_contra hx
    exact h _ (singleton_isAtom μ (pos_iff_ne_zero.mpr hx))

section Finite

variable [IsFiniteMeasure μ] [MeasurableSingletonClass X]

lemma atomic_singleton (a : atomicPoints μ) :
    subspaceMeasure μ (atomicPoints μ) {a} = μ {a.val} := by
  rw [subspaceMeasure, comap_subtype_coe_apply (atomicPoints_measurable μ), image_singleton]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Every point of $X_{\mathrm{na}}$ has zero $\mu_{\mathrm{na}}$-mass. If this restricted measure had an atom,
    the preceding argument would produce a point of positive mass, a contradiction.
-/
/-- The complementary subspace has no point masses. -/
theorem nonatomic_noAtoms : NullSingletonClass (subspaceMeasure μ (atomicPoints μ)ᶜ) := by
  refine ⟨fun x => ?_⟩
  rw [subspaceMeasure, comap_subtype_coe_apply (atomicPoints_measurable μ).compl, image_singleton]
  exact le_antisymm (le_of_not_gt x.property) bot_le

/-- The atomic factor is the powerset of the countable set of positive-mass points. -/
def atomicEquiv : MeasureAlgebra (subspaceMeasure μ (atomicPoints μ)) ≃o Set (atomicPoints μ) := by
  letI : Countable (atomicPoints μ) := (atomicPoints_countable μ).to_subtype
  exact discreteEquiv _ (fun x => by rw [atomic_singleton]; exact x.property)

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    The isomorphism is
    $$[B]\longmapsto\bigl([B\cap X_{\mathrm{na}}],\,B\cap A\bigr).$$
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Changing a representative on a null set changes neither the first class nor the second set, because every point of
    $A$ has positive mass. Its inverse sends $([C],S)$ to $[C\cup S]$; every subset of the countable Borel set $A$ is
    Borel. These maps preserve Boolean operations because $X_{\mathrm{na}}$ and $A$ partition $X$.
    They preserve measure since
-/
/-- The explicit atomic/nonatomic product decomposition of the measure algebra. -/
def decomposition : MeasureAlgebra μ ≃o
    MeasureAlgebra (subspaceMeasure μ (atomicPoints μ)ᶜ) × Set (atomicPoints μ) :=
  (splitEquiv μ (atomicPoints μ) (atomicPoints_measurable μ)).trans
    { toEquiv := (Equiv.refl _).prodCongr (atomicEquiv μ).toEquiv
      map_rel_iff' := by
        intro a b
        exact and_congr Iff.rfl (atomicEquiv μ).map_rel_iff }

/-- On a representative, take its nonatomic restriction and the atomic points it contains. -/
lemma decomposition_mk (B : Set X) (hB : MeasurableSet B) :
    decomposition μ (MeasureAlgebra.mk B hB) =
      (MeasureAlgebra.mk (Subtype.val ⁻¹' B) (hB.preimage measurable_subtype_coe),
        {a : atomicPoints μ | a.val ∈ B}) := rfl

/-- The weight of an arbitrary set of atomic points is the sum of their masses. -/
def atomicWeight (S : Set (atomicPoints μ)) : ℝ≥0∞ := ∑' a : S, μ {a.val.val}

lemma atomic_measure_eq_weight (S : Set (atomicPoints μ)) :
    subspaceMeasure μ (atomicPoints μ) S = atomicWeight μ S := by
  let : Countable (atomicPoints μ) := (atomicPoints_countable μ).to_subtype
  have h := tsum_measure_preimage_singleton (μ := subspaceMeasure μ (atomicPoints μ))
    S.to_countable (f := id) (fun x _ => measurableSet_singleton x)
  simpa only [preimage_id, atomic_singleton, atomicWeight] using h.symm

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    $$\begin{aligned}
    \mu(B)&=\mu_{\mathrm{na}}(B\cap X_{\mathrm{na}})+w(B\cap A)\\
    &=\mu_{\mathrm{na}}(B\cap X_{\mathrm{na}})
      +\sum_{x\in B\cap A}\mu(\{x\}).
    \end{aligned}$$
-/
/-- The product decomposition preserves the measure, including the weights
of the atomic factor. -/
theorem decomposition_mass (a : MeasureAlgebra μ) :
    MeasureAlgebra.mass a = MeasureAlgebra.mass (decomposition μ a).1 +
      atomicWeight μ (decomposition μ a).2 := by
  let : Countable (atomicPoints μ) := (atomicPoints_countable μ).to_subtype
  have h := split_mass μ (atomicPoints μ) (atomicPoints_measurable μ) a
  change MeasureAlgebra.mass a =
    MeasureAlgebra.mass (splitEquiv μ (atomicPoints μ) (atomicPoints_measurable μ) a).1 +
    atomicWeight μ (atomicEquiv μ (splitEquiv μ (atomicPoints μ) (atomicPoints_measurable μ) a).2)
  rw [h]
  congr 1
  exact (discreteEquiv_mass _ _ _).trans (atomic_measure_eq_weight μ _)

/-- In the standard countably separated setting, the first factor has no Boolean atoms. -/
theorem nonatomic_no_algebra_atoms [CountablyGenerated X] [SeparatesPoints X]
    (a : MeasureAlgebra (subspaceMeasure μ (atomicPoints μ)ᶜ)) : ¬ IsAtom a :=
  (noAtoms_iff_no_algebra_atoms _).mp (nonatomic_noAtoms μ) a

end Finite

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: proposition
  title: Atomic decomposition
-/
/-- The book's complete decomposition for a finite measure on a standard Borel
space, including its canonical nonatomic condition and the weighted mass formula. -/
theorem standardBorel_decomposition [StandardBorelSpace X] [IsFiniteMeasure μ] :
    ∃ e : MeasureAlgebra μ ≃o
      MeasureAlgebra (subspaceMeasure μ (atomicPoints μ)ᶜ) × Set (atomicPoints μ),
      (atomicPoints μ).Countable ∧ NullSingletonClass (subspaceMeasure μ (atomicPoints μ)ᶜ) ∧
      (∀ b : MeasureAlgebra (subspaceMeasure μ (atomicPoints μ)ᶜ), ¬ IsAtom b) ∧
      ∀ a, MeasureAlgebra.mass a = MeasureAlgebra.mass (e a).1 + atomicWeight μ (e a).2 :=
  ⟨decomposition μ, atomicPoints_countable μ, nonatomic_noAtoms μ,
    nonatomic_no_algebra_atoms μ, decomposition_mass μ⟩

end PolishSpaceBook.AtomicMeasureDecomposition
