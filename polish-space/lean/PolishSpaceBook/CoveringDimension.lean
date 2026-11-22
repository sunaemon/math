module

public import PolishSpaceBook.PolishSpaces
public import Mathlib.Data.Set.Card

@[expose] public section

/-! # Finite covering dimension

Finite refinements may have their own index type. Their multiplicity is the
number of indices whose open set contains the point. The zero case is connected
to the existing API by regrouping a refinement according to its original cover.
-/
namespace PolishSpaceBook
open Set
universe u

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: statement
  kind: definition
  title: Lebesgue covering dimension
-/
/-- Every finite open cover has a finite open refinement of multiplicity at most n+1. -/
def coveringDimensionBound (X : Type u) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ {I : Type} [Finite I] (U : I → Set X), (∀ i, IsOpen (U i)) →
    (⋃ i, U i) = univ → ∃ (J : Type) (_ : Finite J) (V : J → Set X),
      (∀ j, IsOpen (V j)) ∧ (⋃ j, V j) = univ ∧
      (∀ j, ∃ i, V j ⊆ U i) ∧ ∀ x, {j | x ∈ V j}.ncard ≤ n + 1

/-- Increasing the permitted multiplicity preserves a bound. -/
theorem coveringDimensionBound_mono (X : Type u) [TopologicalSpace X]
    {n m : ℕ} (h : coveringDimensionBound X n) (hnm : n ≤ m) : coveringDimensionBound X m := by
  intro I _ U hU hc
  obtain ⟨J, hJ, V, hV, hVc, hr, hm⟩ := h U hU hc
  exact ⟨J, hJ, V, hV, hVc, hr, fun x => (hm x).trans (by omega)⟩

/-- In multiplicity one, a refinement can be regrouped into a disjoint family
indexed by the original cover without changing its coverage. -/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $\CoveringDimension{X}\le 0$, the refinement must therefore have pairwise disjoint members.
    After empty members are discarded, it is a partition into clopen sets: the complement of each member is the union of the
    others.
    All three dimensions are $-1$ exactly for the empty space, so for a nonempty space the corresponding bound by $0$ means
    that the dimension is $0$.
-/
theorem coveringDimensionBound_zero_iff (X : Type u) [TopologicalSpace X] :
    coveringDimensionBound X 0 ↔ HasCoveringDimensionLEZero X := by
  classical
  constructor
  · intro h I _ U hU hc
    obtain ⟨J, hJ, V, hV, hVc, hr, hm⟩ := h U hU hc
    let : Finite J := hJ
    choose a ha using hr
    let W : I → Set X := fun i => ⋃ j : {j : J // a j = i}, V j.val
    have hdis : Pairwise (fun j k => Disjoint (V j) (V k)) := by
      intro j k hjk
      apply Set.disjoint_left.mpr
      intro x hxj hxk
      have hsub : ({j | x ∈ V j} : Set J).Subsingleton :=
        (Set.ncard_le_one_iff_subsingleton).mp (by simpa using hm x)
      exact hjk (hsub hxj hxk)
    refine ⟨W, fun i => isOpen_iUnion (fun j => hV j.val), ?_, ?_, ?_⟩
    · apply eq_univ_of_forall
      intro x
      obtain ⟨j, hxj⟩ := mem_iUnion.mp (hVc ▸ mem_univ x)
      exact mem_iUnion.mpr ⟨a j, mem_iUnion.mpr ⟨⟨j, rfl⟩, hxj⟩⟩
    · intro i k hik
      apply Set.disjoint_left.mpr
      intro x hxi hxk
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxi
      obtain ⟨l, hxl⟩ := mem_iUnion.mp hxk
      have hjl : j.val ≠ l.val := by
        intro he
        exact hik (j.property.symm.trans ((congrArg a he).trans l.property))
      exact Set.disjoint_left.mp (hdis hjl) hxj hxl
    · intro i x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact j.property ▸ ha j.val hxj
  · intro h I hI U hU hc
    obtain ⟨V, hV, hVc, hd, hr⟩ := h U hU hc
    refine ⟨I, hI, V, hV, hVc, fun i => ⟨i, hr i⟩, ?_⟩
    intro x
    apply (Set.ncard_le_one_iff_subsingleton).mpr
    intro i hi j hj
    by_contra hij
    exact Set.disjoint_left.mp (hd hij) hi hj

/-- Every empty space satisfies every finite covering bound. -/
theorem coveringDimensionBound_of_isEmpty (X : Type u) [TopologicalSpace X] [IsEmpty X]
    (n : ℕ) : coveringDimensionBound X n := by
  intro I _ U _ _
  refine ⟨Empty, inferInstance, fun j => isEmptyElim j, fun j => isEmptyElim j, ?_,
    fun j => isEmptyElim j, fun x => isEmptyElim x⟩
  exact eq_univ_of_forall (fun x => isEmptyElim x)

/-- Empty spaces have value -1; otherwise take the least natural bound, or infinity. -/
noncomputable def coveringDimension (X : Type u) [TopologicalSpace X] : WithTop ℤ := by
  classical
  exact if IsEmpty X then (-1 : ℤ) else
    if h : ∃ n, coveringDimensionBound X n then (Nat.find h : ℤ) else ⊤

/-- The numeric value has exactly the finite upper bounds from the definition. -/
theorem coveringDimension_le_iff (X : Type u) [TopologicalSpace X] (n : ℕ) :
    coveringDimension X ≤ (n : ℤ) ↔ coveringDimensionBound X n := by
  classical
  by_cases he : IsEmpty X
  · let := he
    rw [coveringDimension, ite_eq_left he]
    exact iff_of_true (by exact_mod_cast (show (-1 : ℤ) ≤ n by omega))
      (coveringDimensionBound_of_isEmpty X n)
  · rw [coveringDimension, ite_eq_right he]
    by_cases h : ∃ k, coveringDimensionBound X k
    · rw [dite_eq_left h]
      constructor
      · intro hle I hI U hU hc
        have hm : Nat.find h ≤ n := by exact_mod_cast (WithTop.coe_le_coe.mp hle)
        exact coveringDimensionBound_mono X (n := Nat.find h) (m := n) (Nat.find_spec h) hm U hU hc
      · intro hn
        apply WithTop.coe_le_coe.mpr
        exact_mod_cast Nat.find_min' h hn
    · rw [dite_eq_right h]
      constructor
      · intro hle
        exact ((not_le_of_gt (WithTop.coe_lt_top (n : ℤ))) hle).elim
      · intro hn
        exact (h ⟨n, hn⟩).elim

/-- The zero-dimensional API is the zero bound of the general numeric dimension. -/
theorem coveringDimension_le_zero_iff (X : Type u) [TopologicalSpace X] :
    coveringDimension X ≤ (0 : ℤ) ↔ HasCoveringDimensionLEZero X :=
  (coveringDimension_le_iff X 0).trans (coveringDimensionBound_zero_iff X)

/-- The finite dimension is the least natural bound on a nonempty space. -/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $\CoveringDimension{X}\le 0$, the refinement must therefore have pairwise disjoint members.
    After empty members are discarded, it is a partition into clopen sets: the complement of each member is the union of the
    others.
    All three dimensions are $-1$ exactly for the empty space, so for a nonempty space the corresponding bound by $0$ means
    that the dimension is $0$.
-/
theorem coveringDimension_eq_of_least (X : Type u) [TopologicalSpace X] [Nonempty X]
    {n : ℕ} (hn : coveringDimensionBound X n) (hmin : ∀ k < n, ¬coveringDimensionBound X k) :
    coveringDimension X = (n : ℤ) := by
  classical
  have h : ∃ k, coveringDimensionBound X k := ⟨n, hn⟩
  rw [coveringDimension, ite_eq_right (not_isEmpty_of_nonempty X), dite_eq_left h,
    (Nat.find_eq_iff h).mpr ⟨hn, hmin⟩]

/-- Exactly the empty spaces have dimension -1. -/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $\CoveringDimension{X}\le 0$, the refinement must therefore have pairwise disjoint members.
    After empty members are discarded, it is a partition into clopen sets: the complement of each member is the union of the
    others.
    All three dimensions are $-1$ exactly for the empty space, so for a nonempty space the corresponding bound by $0$ means
    that the dimension is $0$.
-/
theorem coveringDimension_eq_neg_one_iff (X : Type u) [TopologicalSpace X] :
    coveringDimension X = (-1 : ℤ) ↔ IsEmpty X := by
  classical
  unfold coveringDimension
  split_ifs with he h
  · simp [he]
  · constructor
    · intro heq
      have heq' : (Nat.find h : ℤ) = -1 := WithTop.coe_injective heq
      omega
    · exact fun hh => (he hh).elim
  · constructor
    · intro hfalse
      cases hfalse
    · exact fun hh => (he hh).elim

/-- Infinity occurs precisely on a nonempty space with no finite bound. -/
theorem coveringDimension_eq_top_iff (X : Type u) [TopologicalSpace X] :
    coveringDimension X = ⊤ ↔ ¬IsEmpty X ∧ ¬∃ n, coveringDimensionBound X n := by
  classical
  unfold coveringDimension
  split_ifs <;> simp_all

end PolishSpaceBook
