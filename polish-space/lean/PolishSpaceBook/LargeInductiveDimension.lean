module

public import PolishSpaceBook.PolishSpaces

@[expose] public section

/-! # Large inductive dimension at every finite bound

The natural-number index is shifted: index zero denotes the bound -1,
and index `n + 1` denotes the bound n. Recursion decreases this index,
while each boundary is equipped with its subspace topology.
-/
namespace PolishSpaceBook
open Set
universe u

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: statement
  kind: definition
  title: Large inductive dimension
-/
/-- The book's recursive bounds for large inductive dimension. -/
def largeInductiveDimensionBound (X : Type u) [TopologicalSpace X] : ℕ → Prop
  | 0 => IsEmpty X
  | n + 1 => ∀ (F U : Set X), IsClosed F → IsOpen U → F ⊆ U →
      ∃ V : Set X, IsOpen V ∧ F ⊆ V ∧ V ⊆ U ∧
        largeInductiveDimensionBound (frontier V) n

/-- Increasing the recursion index preserves an upper bound. -/
theorem largeInductiveDimensionBound_step (n : ℕ) :
    ∀ (X : Type u) [TopologicalSpace X],
      largeInductiveDimensionBound X n → largeInductiveDimensionBound X (n + 1) := by
  induction n with
  | zero =>
    intro X _ h F U _ _ _
    let : IsEmpty X := h
    refine ⟨∅, isOpen_empty, ?_, empty_subset U, ?_⟩
    · exact subset_empty_iff.mpr (eq_empty_of_isEmpty F)
    · change IsEmpty (frontier (∅ : Set X))
      rw [frontier_empty]
      infer_instance
  | succ n ih =>
    intro X _ h F U hF hU hFU
    obtain ⟨V, hV, hFV, hVU, hb⟩ := h F U hF hU hFU
    exact ⟨V, hV, hFV, hVU, ih _ hb⟩

/-- The least finite bound, or infinity when no finite bound holds.
Subtracting one converts the recursion index to the integer dimension. -/
noncomputable def largeInductiveDimension (X : Type u) [TopologicalSpace X] : WithTop ℤ := by
  classical
  exact if h : ∃ n, largeInductiveDimensionBound X n then
    ((Nat.find h : ℤ) - 1 : ℤ) else ⊤

/-- A least recursion index determines the dimension value. -/
theorem largeInductiveDimension_eq_of_least (X : Type u) [TopologicalSpace X]
    {m : ℕ} (hm : largeInductiveDimensionBound X m)
    (hmin : ∀ k < m, ¬largeInductiveDimensionBound X k) :
    largeInductiveDimension X = ((m : ℤ) - 1 : ℤ) := by
  classical
  have h : ∃ n, largeInductiveDimensionBound X n := ⟨m, hm⟩
  rw [largeInductiveDimension, dite_eq_left h, (Nat.find_eq_iff h).mpr ⟨hm, hmin⟩]

/-- The infinite value is used precisely when there is no finite bound. -/
theorem largeInductiveDimension_eq_top_iff (X : Type u) [TopologicalSpace X] :
    largeInductiveDimension X = ⊤ ↔ ¬∃ n, largeInductiveDimensionBound X n := by
  classical
  unfold largeInductiveDimension
  split_ifs <;> simp_all

/-- The least-value definition recovers every recursively defined integer bound. -/
theorem largeInductiveDimension_le_iff (X : Type u) [TopologicalSpace X] (n : ℕ) :
    largeInductiveDimension X ≤ (n : ℤ) ↔ largeInductiveDimensionBound X (n + 1) := by
  classical
  by_cases h : ∃ k, largeInductiveDimensionBound X k
  · rw [largeInductiveDimension, dite_eq_left h]
    constructor
    · intro he
      have he' : (Nat.find h : ℤ) - 1 ≤ (n : ℤ) := WithTop.coe_le_coe.mp he
      have hm : Nat.find h ≤ n + 1 := by omega
      exact Nat.le_induction (Nat.find_spec h)
        (fun k _ hk => largeInductiveDimensionBound_step k X hk) (n + 1) hm
    · intro hb
      have hm := Nat.find_min' h hb
      apply WithTop.coe_le_coe.mpr
      omega
  · rw [largeInductiveDimension, dite_eq_right h]
    constructor
    · intro he
      exact False.elim ((not_le_of_gt (WithTop.coe_lt_top (n : ℤ))) he)
    · intro hb
      exact (h ⟨n + 1, hb⟩).elim

/-- Empty boundary is equivalent to clopenness for an open set. -/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Consequently, $\LargeInductiveDimension{X}\le 0$ means that a clopen set can be inserted between any closed set and any
    open set containing it.
-/
theorem largeInductiveDimensionBound_one_iff (X : Type u) [TopologicalSpace X] :
    largeInductiveDimensionBound X 1 ↔ HasBigInductiveDimensionLEZero X := by
  constructor
  · intro h F U hF hU hFU
    obtain ⟨V, hV, hFV, hVU, hb⟩ := h F U hF hU hFU
    have he : frontier V = ∅ := isEmpty_coe_sort.mp hb
    refine ⟨V, ⟨?_, hV⟩, hFV, hVU⟩
    rw [← closure_subset_iff_isClosed]
    have hd : closure V \ V = ∅ := hV.frontier_eq ▸ he
    exact sdiff_eq_empty.mp hd
  · intro h F U hF hU hFU
    obtain ⟨V, hV, hFV, hVU⟩ := h hF hU hFU
    refine ⟨V, hV.isOpen, hFV, hVU, ?_⟩
    change IsEmpty (frontier V)
    rw [hV.frontier_eq]
    infer_instance

/-- Empty spaces have value -1. -/
theorem largeInductiveDimension_of_isEmpty (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    largeInductiveDimension X = (-1 : ℤ) := by
  simpa using largeInductiveDimension_eq_of_least X (m := 0) (show IsEmpty X from inferInstance) (by simp)

/-- Only the empty space has dimension -1. -/
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
theorem largeInductiveDimension_eq_neg_one_iff (X : Type u) [TopologicalSpace X] :
    largeInductiveDimension X = (-1 : ℤ) ↔ IsEmpty X := by
  classical
  constructor
  · intro he
    by_cases h : ∃ n, largeInductiveDimensionBound X n
    · rw [largeInductiveDimension, dite_eq_left h] at he
      have he' : (Nat.find h : ℤ) - 1 = -1 := WithTop.coe_injective he
      have hm : Nat.find h = 0 := by omega
      have hb := Nat.find_spec h
      rw [hm] at hb
      exact hb
    · rw [largeInductiveDimension, dite_eq_right h] at he
      cases he
  · intro h
    let := h
    exact largeInductiveDimension_of_isEmpty X

/-- On a nonempty space, the zero-bound condition has value zero. -/
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
theorem largeInductiveDimension_zero_of_bound (X : Type u) [TopologicalSpace X] [Nonempty X]
    (h : HasBigInductiveDimensionLEZero X) : largeInductiveDimension X = (0 : ℤ) := by
  apply (largeInductiveDimension_eq_of_least X
    ((largeInductiveDimensionBound_one_iff X).mpr h) ?_).trans
  · norm_num
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    change ¬IsEmpty X
    exact not_isEmpty_of_nonempty X

end PolishSpaceBook
