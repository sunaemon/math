module

public import PolishSpaceBook.PolishSpaces
import all Mathlib.Topology.InductiveDimension.Functions

@[expose] public section

/-! # The book's neighborhood recursion and the standard small inductive dimension

Use mathlib's dimension and bounds throughout. The least recursion index has
index zero for dimension -1 and index `n + 1` for dimension n.
-/
namespace PolishSpaceBook
open Set TopologicalSpace

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: statement
  kind: definition
  title: Small inductive dimension
-/
/-- The topological-basis recursion is exactly the point-and-neighborhood recursion. -/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, $\SmallInductiveDimension{X}\le 0$ means that each point $x$ and its open neighborhood $U$ admit an open
    set $V$ with
    $$x\in V\IncludedIn U,\qquad \AmbientBoundary{X}{V}=\emptyset.$$
    Indeed, the boundary must have dimension $-1$, so it must be empty. Thus every open neighborhood of a point contains a
    clopen neighborhood of that point.
-/
theorem smallInductiveDimension_succ_iff (X : Type) [TopologicalSpace X] (n : ℕ) :
    HasSmallInductiveDimensionLT X (n + 1) ↔
      ∀ (x : X) (U : Set X), x ∈ U → IsOpen U →
        ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
          HasSmallInductiveDimensionLT (frontier V) n := by
  constructor
  · intro h x U hx hU
    cases h with
    | succ _ s hs hb =>
      obtain ⟨V, hV, hxV, hVU⟩ := hs.exists_subset_of_mem_open hx hU
      exact ⟨V, hs.isOpen hV, hxV, hVU, hb V hV⟩
  · intro h
    let s : Set (Set X) := {V | IsOpen V ∧ HasSmallInductiveDimensionLT (frontier V) n}
    have hs : IsTopologicalBasis s := by
      apply isTopologicalBasis_of_isOpen_of_nhds (fun V hV => hV.1)
      intro x U hx hU
      obtain ⟨V, hVo, hxV, hVU, hb⟩ := h x U hx hU
      exact ⟨V, ⟨hVo, hb⟩, hxV, hVU⟩
    exact .succ n s hs (fun V hV => hV.2)

/-- Increasing the bound preserves the dimension condition. -/
theorem smallInductiveDimensionBound_step (n : ℕ) :
    ∀ (X : Type) [TopologicalSpace X], HasSmallInductiveDimensionLT X n →
      HasSmallInductiveDimensionLT X (n + 1) := by
  induction n with
  | zero =>
    intro X _ h
    let : IsEmpty X := (hasSmallInductiveDimensionLT_zero_iff (X := X)).mp h
    exact (smallInductiveDimension_succ_iff X 0).mpr (fun x => isEmptyElim x)
  | succ n ih =>
    intro X _ h
    cases h with
    | succ _ s hs hb =>
      exact .succ (n + 1) s hs (fun V hV => ih _ (hb V hV))

/-- Any larger recursion index is also a bound. -/
theorem smallInductiveDimensionBound_mono (X : Type) [TopologicalSpace X]
    {m k : ℕ} (hm : HasSmallInductiveDimensionLT X m) (hmk : m ≤ k) :
    HasSmallInductiveDimensionLT X k :=
  Nat.le_induction hm (fun n _ hn => smallInductiveDimensionBound_step n X hn) k hmk

/-- A finite least bound gives the canonical dimension value n. -/
theorem smallInductiveDimension_eq_of_least_succ (X : Type) [TopologicalSpace X]
    (n : ℕ) (hn : HasSmallInductiveDimensionLT X (n + 1))
    (hmin : ∀ k < n + 1, ¬HasSmallInductiveDimensionLT X k) :
    smallInductiveDimension X = (n : ℕ∞) := by
  unfold smallInductiveDimension
  apply le_antisymm
  · apply sInf_le
    intro i hi
    have hni : n < i := by exact_mod_cast hi
    exact smallInductiveDimensionBound_mono X hn hni
  · apply le_sInf
    intro a ha
    by_contra hna
    have hlt : a < ((n : ℕ∞) : WithBot ℕ∞) := lt_of_not_ge hna
    exact hmin n (by omega) (ha n hlt)

/-- The canonical value is -1, encoded by bottom, on the empty space. -/
theorem smallInductiveDimension_of_isEmpty (X : Type) [TopologicalSpace X] [IsEmpty X] :
    smallInductiveDimension X = ⊥ := by
  unfold smallInductiveDimension
  apply bot_unique
  apply sInf_le
  intro i _
  exact smallInductiveDimensionBound_mono X .zero (Nat.zero_le i)

/-- Without a finite bound the canonical dimension is infinity. -/
theorem smallInductiveDimension_of_no_bound (X : Type) [TopologicalSpace X]
    (h : ¬∃ n, HasSmallInductiveDimensionLT X n) : smallInductiveDimension X = ⊤ := by
  unfold smallInductiveDimension
  apply top_unique
  apply le_sInf
  intro a ha
  cases a using WithBot.recBotCoe with
  | bot => exact (h ⟨0, ha 0 (by simp)⟩).elim
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact le_rfl
    | coe n =>
      exact (h ⟨n + 1, ha (n + 1) (by exact_mod_cast Nat.lt_succ_self n)⟩).elim

/-- The standard dimension is precisely the book's least integer bound, or infinity. -/
theorem smallInductiveDimension_least_value (X : Type) [TopologicalSpace X] :
    smallInductiveDimension X = (by
      classical
      exact if h : ∃ n, HasSmallInductiveDimensionLT X n then
        match Nat.find h with
        | 0 => ⊥
        | n + 1 => ((n : ℕ∞) : WithBot ℕ∞)
      else ⊤) := by
  classical
  split_ifs with h
  · have hm := Nat.find_spec h
    have hmin : ∀ k < Nat.find h, ¬HasSmallInductiveDimensionLT X k :=
      fun k hk => Nat.find_min h hk
    generalize he : Nat.find h = m at *
    cases m with
    | zero =>
      let : IsEmpty X := (hasSmallInductiveDimensionLT_zero_iff (X := X)).mp hm
      exact smallInductiveDimension_of_isEmpty X
    | succ n => exact smallInductiveDimension_eq_of_least_succ X n hm hmin
  · exact smallInductiveDimension_of_no_bound X h

/-- For a nonempty space, the existing zero-bound API gives dimension exactly zero. -/
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
theorem smallInductiveDimension_zero_of_bound (X : Type) [TopologicalSpace X] [Nonempty X]
    (h : HasSmallInductiveDimensionLE X 0) : smallInductiveDimension X = (0 : ℕ∞) := by
  apply smallInductiveDimension_eq_of_least_succ X 0 h
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  intro hb
  have : IsEmpty X := (hasSmallInductiveDimensionLT_zero_iff (X := X)).mp hb
  exact not_isEmpty_of_nonempty X inferInstance

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
/-- The bottom value represents dimension -1, and occurs exactly on empty spaces. -/
theorem smallInductiveDimension_bottom_iff (X : Type) [TopologicalSpace X] :
    smallInductiveDimension X = ⊥ ↔ IsEmpty X :=
  _root_.smallInductiveDimension_eq_bot

end PolishSpaceBook
