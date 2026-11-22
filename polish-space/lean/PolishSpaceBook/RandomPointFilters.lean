module

public import PolishSpaceBook.RandomGenericReals
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.Order.Zorn

@[expose] public section

/-!
# Reconstructing random filters from points

Maximal antichains are taken in the full positive measure algebra. A dense set
in an arbitrary Boolean subalgebra need not be predense in that full order.
The point construction below keeps that distinction explicit; it does not
construct a transitive model or identify an internal quotient with the ambient one.
-/

namespace PolishSpaceBook
open MeasureTheory Set Filter
open scoped ENNReal symmDiff

namespace MeasureAlgebra
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A dense family in the full positive algebra contains a disjoint predense
family, constructed by taking the union of chains and applying Zorn's lemma. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Predense antichains and conull covers
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Fix a dense set and order its pairwise incompatible subfamilies by inclusion. The union of a chain of such subfamilies is again pairwise incompatible:
    any two members occur together in one subfamily of the chain. Zorn's lemma therefore gives a maximal such subfamily.
    If a positive condition were incompatible with every member, strengthen it into the dense set and adjoin that strengthening, contradicting maximality.
    Thus the antichain is predense, and the ccc makes it countable.

    For a countable predense family, form the Borel union of its representatives. If the complement had positive measure,
    its class would be a positive condition incompatible with every member of the family. This contradicts predensity,
    so the union is conull. The argument uses countability to obtain a Borel union, and does not require the representatives to be literally disjoint.
    \end{proof}
-/
theorem exists_disjoint_predense_subset (D : Set (Positive μ)) (hd : IsCoinitial D) :
    ∃ A ⊆ D, A.Pairwise (fun p q => Disjoint p.val q.val) ∧
      ∀ p : Positive μ, ∃ q ∈ A, p.val ⊓ q.val ≠ ⊥ := by
  classical
  let S : Set (Set (Positive μ)) := {A | A ⊆ D ∧ A.Pairwise (fun p q => Disjoint p.val q.val)}
  obtain ⟨A, hA, hmax⟩ := zorn_subset S (by
    intro C hC hc
    refine ⟨⋃₀ C, ⟨?_, ?_⟩, fun B hB => subset_sUnion_of_mem hB⟩
    · rintro p ⟨B, hB, hp⟩
      exact (hC hB).1 hp
    · rintro p ⟨B, hB, hp⟩ q ⟨E, hE, hq⟩ hpq
      rcases hc.total hB hE with hBE | hEB
      · exact (hC hE).2 (hBE hp) hq hpq
      · exact (hC hB).2 hp (hEB hq) hpq)
  refine ⟨A, hA.1, hA.2, ?_⟩
  intro p
  by_contra! hn
  obtain ⟨q, hqD, hqp⟩ := hd p
  have hqdis (a) (ha : a ∈ A) : Disjoint q.val a.val :=
    (disjoint_iff.mpr (hn a ha)).mono_left hqp
  have hi : insert q A ∈ S := by
    refine ⟨insert_subset hqD hA.1, ?_⟩
    intro a ha b hb hab
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact False.elim (hab rfl)
      · exact hqdis b hb
    · rcases hb with rfl | hb
      · exact (hqdis a ha).symm
      · exact hA.2 ha hb hab
  have hqA : q ∈ A := (hmax hi (subset_insert q A)) (mem_insert q A)
  have hzero := (hqdis q hqA).eq_bot
  exact q.property (by simpa using hzero)

/-- The ccc applies to positive conditions as well as to their Boolean values. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Predense antichains and conull covers
-/
theorem countable_positive_pairwiseDisjoint [IsFiniteMeasure μ] (A : Set (Positive μ))
    (hA : A.Pairwise (fun p q => Disjoint p.val q.val)) : A.Countable := by
  have himage : (Subtype.val '' A : Set (MeasureAlgebra μ)).Pairwise Disjoint := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
    exact hA hp hq (fun h => hpq (congrArg Subtype.val h))
  have hpos : (⊥ : MeasureAlgebra μ) ∉ Subtype.val '' A := by
    rintro ⟨p, _, hp⟩
    exact p.property hp
  have hc := countable_pairwiseDisjoint _ himage hpos
  have hp : ((fun p : Positive μ => p.val) ⁻¹' (Subtype.val '' A)).Countable :=
    Set.Countable.preimage hc Subtype.val_injective
  exact Set.Countable.mono (fun a ha => mem_image_of_mem Subtype.val ha) hp

/-- Predensity forces the supremum of the antichain values to be one. -/
theorem iSup_eq_top_of_predense [IsFiniteMeasure μ] (A : Set (Positive μ))
    (hA : ∀ p : Positive μ, ∃ q ∈ A, p.val ⊓ q.val ≠ ⊥) :
    (⨆ q : A, q.val.val) = ⊤ := by
  by_contra hn
  have hcomp : (⨆ q : A, q.val.val)ᶜ ≠ ⊥ := by simpa using hn
  obtain ⟨q, hq, hpq⟩ := hA ⟨_, hcomp⟩
  apply hpq
  apply le_bot_iff.mp
  calc
    (⨆ a : A, a.val.val)ᶜ ⊓ q.val ≤ (⨆ a : A, a.val.val)ᶜ ⊓ (⨆ a : A, a.val.val) :=
      inf_le_inf_left _ (le_iSup (fun a : A => a.val.val) ⟨q, hq⟩)
    _ = ⊥ := compl_inf_self _

/-- Representatives of a countable predense family cover a conull measurable set. -/
theorem conull_iUnion_of_predense [IsFiniteMeasure μ] (A : Set (Positive μ))
    (hc : A.Countable)
    (hA : ∀ p : Positive μ, ∃ q ∈ A, p.val ⊓ q.val ≠ ⊥)
    (R : A → MeasuredSets μ) (hR : ∀ a, mk (R a) (R a).property = a.val.val) :
    μ (⋃ a, (R a : Set X))ᶜ = 0 := by
  have : Countable A := hc.to_subtype
  have hu : MeasurableSet (⋃ a, (R a : Set X)) := MeasurableSet.iUnion (fun a => (R a).property)
  have hclass : (mk (⋃ a, (R a : Set X)) hu : MeasureAlgebra μ) = ⊤ := by
    calc
      _ = ⨆ a, mk (R a) (R a).property := mk_iUnion _ (fun a => (R a).property)
      _ = ⨆ a : A, a.val.val := by simp only [hR]
      _ = ⊤ := iSup_eq_top_of_predense A hA
  apply (mk_eq_bot _ hu.compl).mp
  rw [← mk_compl _ hu, hclass, compl_top]

variable (A : BooleanSubalgebra (MeasureAlgebra μ))

/-- The explicit null defects of a chosen system of representatives: zero,
one, finite intersection, and complement. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Let $A\IncludedIn Q$ be a countable Boolean subalgebra, and choose a Borel representative $B_a$ of each $a\in A$.
    These choices need not preserve Boolean operations as literal set operations.
    \begin{mathmeta}
      \define{SymmetricDifference}
    \end{mathmeta}
    Write $\SymmetricDifference{B}{C}$ for the symmetric difference of two sets. Define the defect set
    $$\begin{aligned}
    N_A:={}&B_0\cup B_1^c\\
    &{}\cup\bigcup_{a,b\in A}\left(\SymmetricDifference{B_{a\wedge b}}{(B_a\cap B_b)}\right)\\
    &{}\cup\bigcup_{a\in A}\left(\SymmetricDifference{B_{a^c}}{B_a^c}\right).
    \end{aligned}$$
-/
def representativeDefect (R : A → MeasuredSets μ) : Set X :=
  (R ⊥ : Set X) ∪ (R ⊤ : Set X)ᶜ ∪
    (⋃ a : A, ⋃ b : A, (R (a ⊓ b) : Set X) ∆ ((R a : Set X) ∩ (R b : Set X))) ∪
    (⋃ a : A, (R aᶜ : Set X) ∆ (R a : Set X)ᶜ)

theorem representativeDefect_measurable [Countable A] (R : A → MeasuredSets μ) :
    MeasurableSet (representativeDefect A R) :=
  (((R ⊥).property.union (R ⊤).property.compl).union
    (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      (R (a ⊓ b)).property.symmDiff ((R a).property.inter (R b).property))).union
    (MeasurableSet.iUnion fun a => (R aᶜ).property.symmDiff (R a).property.compl)

/-- The countability assumption allows all Boolean identities to hold away
from one measurable null set. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Coherent representatives
-/
theorem representativeDefect_null [Countable A] (R : A → MeasuredSets μ)
    (hR : ∀ a, mk (R a) (R a).property = a.val) : μ (representativeDefect A R) = 0 := by
  have hb : μ (R ⊥ : Set X) = 0 := (mk_eq_bot _ _).mp (hR ⊥)
  have ht : μ (R ⊤ : Set X)ᶜ = 0 := by
    apply (mk_eq_bot _ (R ⊤).property.compl).mp
    calc
      mk (R ⊤ : Set X)ᶜ _ = (mk (R ⊤) (R ⊤).property : MeasureAlgebra μ)ᶜ := rfl
      _ = (⊤ : MeasureAlgebra μ)ᶜ := congrArg Compl.compl (hR ⊤)
      _ = ⊥ := compl_top
  have hi (a b : A) : μ ((R (a ⊓ b) : Set X) ∆ ((R a : Set X) ∩ R b)) = 0 := by
    apply measure_symmDiff_eq_zero_iff.mpr
    apply (mk_eq_mk (R (a ⊓ b)).property ((R a).property.inter (R b).property)).mp
    calc
      (mk (R (a ⊓ b)) _ : MeasureAlgebra μ) = (a ⊓ b).val := hR _
      _ = mk (R a) (R a).property ⊓ mk (R b) (R b).property :=
        congrArg₂ (· ⊓ ·) (hR a).symm (hR b).symm
      _ = mk ((R a : Set X) ∩ R b) _ := rfl
  have hc (a : A) : μ ((R aᶜ : Set X) ∆ (R a : Set X)ᶜ) = 0 := by
    apply measure_symmDiff_eq_zero_iff.mpr
    apply (mk_eq_mk (R aᶜ).property (R a).property.compl).mp
    calc
      (mk (R aᶜ) _ : MeasureAlgebra μ) = aᶜ.val := hR _
      _ = (mk (R a) (R a).property)ᶜ := congrArg Compl.compl (hR a).symm
      _ = mk (R a : Set X)ᶜ _ := rfl
  simp only [representativeDefect, measure_union_null_iff, measure_iUnion_null_iff]
  exact ⟨⟨⟨hb, ht⟩, hi⟩, hc⟩

/-- Outside the defect set, membership is a Boolean valuation. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Coherent representatives
-/
theorem outside_representativeDefect (R : A → MeasuredSets μ) {x : X}
    (hx : x ∉ representativeDefect A R) :
    x ∉ (R ⊥ : Set X) ∧ x ∈ (R ⊤ : Set X) ∧
      (∀ a b : A, x ∈ (R (a ⊓ b) : Set X) ↔ x ∈ (R a : Set X) ∧ x ∈ (R b : Set X)) ∧
      ∀ a : A, x ∈ (R aᶜ : Set X) ↔ x ∉ (R a : Set X) := by
  simp only [representativeDefect, mem_union, mem_compl_iff, mem_iUnion,
    mem_symmDiff, mem_inter_iff, not_or, not_exists] at hx
  refine ⟨hx.1.1.1, not_not.mp hx.1.1.2, ?_, ?_⟩
  · intro a b
    have h := hx.1.2 a b
    tauto
  · intro a
    have h := hx.2 a
    tauto

/-- Positive elements of the fragment, with the canonical inherited order. -/
abbrev FragmentPositive := {a : A // a ≠ ⊥}

/-- A point outside the null defects defines a genuine order filter on the
positive part of the Boolean fragment. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Coherent representatives
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Each symmetric difference in the definition is null because its two sets represent the same element of the measure algebra.
    The sets representing zero and the complement of one are also null. All these sets are Borel, and there are only countably many of them.
    Outside their union, zero is false, one is true, membership in a meet is simultaneous membership, and membership in a complement is nonmembership.
    Thus the filter contains one. If two positive elements belong to it, their meet also contains the point and cannot be zero, so it is a common strengthening in the filter.
    If an element lies below another, its meet with that other element equals itself. Preservation of meets therefore makes the filter upward closed.
    \end{proof}
-/
def pointFragmentFilter (R : A → MeasuredSets μ) (x : X)
    (hx : x ∉ representativeDefect A R) : Order.PFilter (FragmentPositive A) := by
  have h := outside_representativeDefect A R hx
  have htop : (⊤ : A) ≠ ⊥ := by intro he; exact h.1 (he ▸ h.2.1)
  exact (Order.IsPFilter.of_def
    (F := {a : FragmentPositive A | x ∈ (R a.val : Set X)})
    ⟨⟨⊤, htop⟩, h.2.1⟩
    (by
      intro a ha b hb
      have hi := (h.2.2.1 a.val b.val).mpr ⟨ha, hb⟩
      have hn : a.val ⊓ b.val ≠ ⊥ := by intro he; exact h.1 (he ▸ hi)
      exact ⟨⟨a.val ⊓ b.val, hn⟩, hi,
        (show a.val ⊓ b.val ≤ a.val from inf_le_left),
        (show a.val ⊓ b.val ≤ b.val from inf_le_right)⟩)
    (by
      intro a b hab ha
      have he : a.val ⊓ b.val = a.val := inf_eq_left.mpr hab
      exact ((h.2.2.1 a.val b.val).mp (he.symm ▸ ha)).2)).toPFilter

@[simp] theorem mem_pointFragmentFilter (R : A → MeasuredSets μ) (x : X)
    (hx : x ∉ representativeDefect A R) (a : FragmentPositive A) :
    a ∈ pointFragmentFilter A R x hx ↔ x ∈ (R a.val : Set X) := Iff.rfl

/-- Different choices of representatives agree at every point outside the
countable union of their symmetric differences. -/
def representativeChangeDefect (R T : A → MeasuredSets μ) : Set X :=
  ⋃ a : A, (R a : Set X) ∆ (T a : Set X)

theorem representativeChangeDefect_measurable [Countable A] (R T : A → MeasuredSets μ) :
    MeasurableSet (representativeChangeDefect A R T) :=
  MeasurableSet.iUnion fun a => (R a).property.symmDiff (T a).property

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The construction is also independent of a second choice of representatives $C_a$, outside the additional Borel null set
    $$\bigcup_{a\in A}\left(\SymmetricDifference{B_a}{C_a}\right).$$
    Indeed, each symmetric difference is null, and outside their union the two membership tests agree for every element of the algebra.
-/
theorem representativeChangeDefect_null [Countable A] (R T : A → MeasuredSets μ)
    (hR : ∀ a, mk (R a) (R a).property = a.val)
    (hT : ∀ a, mk (T a) (T a).property = a.val) :
    μ (representativeChangeDefect A R T) = 0 := by
  apply measure_iUnion_null
  intro a
  exact measure_symmDiff_eq_zero_iff.mpr
    ((mk_eq_mk (R a).property (T a).property).mp ((hR a).trans (hT a).symm))

/-- Agreement of all membership tests transfers Boolean coherence to the
second representative system; its defects need not be excluded separately. -/
theorem outside_representativeDefect_of_change (R T : A → MeasuredSets μ) {x : X}
    (hR : x ∉ representativeDefect A R)
    (hx : x ∉ representativeChangeDefect A R T) : x ∉ representativeDefect A T := by
  have heq (a : A) : x ∈ (R a : Set X) ↔ x ∈ (T a : Set X) := by
    have hn : x ∉ (R a : Set X) ∆ (T a : Set X) := fun h => hx (mem_iUnion.mpr ⟨a, h⟩)
    simp only [mem_symmDiff, not_or] at hn
    tauto
  have hdef : x ∈ representativeDefect A R ↔ x ∈ representativeDefect A T := by
    simp only [representativeDefect, mem_union, mem_iUnion, mem_symmDiff, mem_compl_iff, mem_inter_iff]
    simp_rw [heq]
  exact fun ht => hR (hdef.mpr ht)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The construction is also independent of a second choice of representatives $C_a$, outside the additional Borel null set
    $$\bigcup_{a\in A}\left(\SymmetricDifference{B_a}{C_a}\right).$$
    Indeed, each symmetric difference is null, and outside their union the two membership tests agree for every element of the algebra.
-/
theorem pointFragmentFilter_independent (R T : A → MeasuredSets μ) (x : X)
    (hR : x ∉ representativeDefect A R) (hT : x ∉ representativeDefect A T)
    (hx : x ∉ representativeChangeDefect A R T) :
    pointFragmentFilter A R x hR = pointFragmentFilter A T x hT := by
  apply SetLike.ext
  intro a
  change x ∈ (R a.val : Set X) ↔ x ∈ (T a.val : Set X)
  have hn : x ∉ (R a.val : Set X) ∆ (T a.val : Set X) :=
    fun h => hx (mem_iUnion.mpr ⟨a.val, h⟩)
  simp only [mem_symmDiff, not_or] at hn
  tauto

/-- A countable measurable family whose values meet every positive condition
has conull union. The complement would otherwise be a missed positive condition. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Predense antichains and conull covers
-/
theorem conull_iUnion_of_meets [IsFiniteMeasure μ] {ι : Type*} [Countable ι]
    (R : ι → MeasuredSets μ)
    (hR : ∀ p : Positive μ, ∃ i, p.val ⊓ mk (R i) (R i).property ≠ ⊥) :
    μ (⋃ i, (R i : Set X))ᶜ = 0 := by
  have hu : MeasurableSet (⋃ i, (R i : Set X)) := MeasurableSet.iUnion fun i => (R i).property
  let u : MeasureAlgebra μ := mk (⋃ i, (R i : Set X)) hu
  by_contra hn
  have hcomp : uᶜ ≠ ⊥ := fun h => hn ((mk_eq_bot _ hu.compl).mp h)
  obtain ⟨i, hi⟩ := hR ⟨uᶜ, hcomp⟩
  have hle : mk (R i) (R i).property ≤ u :=
    Eventually.of_forall (subset_iUnion (fun i => (R i : Set X)) i)
  apply hi
  exact le_bot_iff.mp ((inf_le_inf_left uᶜ hle).trans_eq (compl_inf_self u))

/-- Add the missed covers of specified predense families to the Boolean defects. -/
def pointGenericDefect {ι : Type*} (R : A → MeasuredSets μ)
    (D : ι → Set (FragmentPositive A)) : Set X :=
  representativeDefect A R ∪ ⋃ i, (⋃ a : D i, (R a.val.val : Set X))ᶜ

theorem pointGenericDefect_measurable [Countable A] {ι : Type*} [Countable ι]
    (R : A → MeasuredSets μ) (D : ι → Set (FragmentPositive A)) :
    MeasurableSet (pointGenericDefect A R D) :=
  (representativeDefect_measurable A R).union
    (MeasurableSet.iUnion fun i => (MeasurableSet.iUnion fun a : D i => (R a.val.val).property).compl)

/-- Predensity is in the full measure algebra, not merely in the fragment.
That is precisely the hypothesis ensuring each missed cover is null. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Point filters meeting prescribed families
-/
theorem pointGenericDefect_null [IsFiniteMeasure μ] [Countable A] {ι : Type*} [Countable ι]
    (R : A → MeasuredSets μ) (hR : ∀ a, mk (R a) (R a).property = a.val)
    (D : ι → Set (FragmentPositive A))
    (hd : ∀ i, ∀ p : Positive μ, ∃ a ∈ D i, p.val ⊓ a.val.val ≠ ⊥) :
    μ (pointGenericDefect A R D) = 0 := by
  apply measure_union_null (representativeDefect_null A R hR)
  apply measure_iUnion_null
  intro i
  apply conull_iUnion_of_meets (fun a : D i => R a.val.val)
  intro p
  obtain ⟨a, ha, hpa⟩ := hd i p
  refine ⟨⟨a, ha⟩, ?_⟩
  simpa only [hR] using hpa

/-- Outside the explicit null exceptional set, point membership gives a filter
meeting every prescribed predense family. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Point filters meeting prescribed families
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Each family is countable because the algebra is countable. Its representatives have conull union by the predense-family argument.
    Thus the displayed set is a countable union of Borel null sets. A point outside it is outside the Boolean defects, so it defines the filter already constructed.
    For each family, it also lies in some representative of a member, placing that member in the filter.
    \end{proof}
-/
theorem pointFragmentFilter_meets {ι : Type*} (R : A → MeasuredSets μ)
    (D : ι → Set (FragmentPositive A)) (x : X) (hx : x ∉ pointGenericDefect A R D) :
    ∃ G : Order.PFilter (FragmentPositive A),
      (∀ a, a ∈ G ↔ x ∈ (R a.val : Set X)) ∧ ∀ i, ∃ a ∈ G, a ∈ D i := by
  have hbase : x ∉ representativeDefect A R := fun h => hx (Or.inl h)
  refine ⟨pointFragmentFilter A R x hbase, fun _ => Iff.rfl, ?_⟩
  intro i
  have hcover : x ∈ ⋃ a : D i, (R a.val.val : Set X) := by
    by_contra hn
    exact hx (Or.inr (mem_iUnion.mpr ⟨i, hn⟩))
  obtain ⟨a, ha⟩ := mem_iUnion.mp hcover
  exact ⟨a.val, ha, a.property⟩

/-- The representatives used in the construction may always be taken from
the canonical quotient selector; they are not extra mathematical data. -/
noncomputable def fragmentRepresentatives : A → MeasuredSets μ := fun a => representative a.val

theorem fragmentRepresentatives_class (a : A) :
    mk (fragmentRepresentatives A a) (fragmentRepresentatives A a).property = a.val :=
  mk_representative a.val

/-- A countable fragment with specified full-order predense families has a
measurable null exceptional set outside which all the point filters exist. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Point filters meeting prescribed families
-/
theorem exists_null_exception_point_filters [IsFiniteMeasure μ] [Countable A]
    {ι : Type*} [Countable ι] (D : ι → Set (FragmentPositive A))
    (hd : ∀ i, ∀ p : Positive μ, ∃ a ∈ D i, p.val ⊓ a.val.val ≠ ⊥) :
    ∃ N : Set X, MeasurableSet N ∧ μ N = 0 ∧ ∀ x ∉ N,
      ∃ G : Order.PFilter (FragmentPositive A),
        (∀ a, a ∈ G ↔ x ∈ (representative a.val.val : Set X)) ∧
        ∀ i, ∃ a ∈ G, a ∈ D i := by
  refine ⟨pointGenericDefect A (fragmentRepresentatives A) D,
    pointGenericDefect_measurable A _ D,
    pointGenericDefect_null A _ (fragmentRepresentatives_class A) D hd, ?_⟩
  intro x hx
  exact pointFragmentFilter_meets A _ D x hx

end MeasureAlgebra
end PolishSpaceBook
