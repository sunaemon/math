module

public import PolishSpaceBook.SetTheoryProperClasses
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Least elements and the elementary examples of well-orders -/

namespace PolishSpaceBook.SetTheoryModels
universe u v

/-- For a linear order, well-ordering says that every nonempty subset has a least element. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{well-order} on a set is a total order in which every nonempty subset has a least element. The natural
    numbers under $<$ are the prototype. By contrast $\ZZ$ under $<$ is not well-ordered because $\ZZ$ itself has no least
    element, and $\R$ under $<$ is not well-ordered because the open interval $(0,1) \StrictlyIncludedIn \R$ has no least
    element. Two
    well-orders are \termdefine{order-isomorphic} if some bijection between them preserves $<$.
-/
theorem wellOrder_iff_least {α : Type u} [LinearOrder α] :
    IsWellOrder α (· < ·) ↔ ∀ s : Set α, s.Nonempty → ∃ m, IsLeast s m := by
  constructor
  · intro h s hs
    obtain ⟨m, hm, hmin⟩ := h.wf.has_min s hs
    exact ⟨m, hm, fun x hx => le_of_not_gt (hmin x hx)⟩
  · intro h
    apply WellFounded.isWellOrder_iff_exists_not_lt_and_eq_or_gt.mpr
    intro s hs
    obtain ⟨m, hm, hmin⟩ := h s hs
    exact ⟨m, hm, fun x hx => ⟨not_lt_of_ge (hmin hx), (hmin hx).eq_or_lt⟩⟩

/-- The usual strict order on the natural numbers is a well-order. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{well-order} on a set is a total order in which every nonempty subset has a least element. The natural
    numbers under $<$ are the prototype. By contrast $\ZZ$ under $<$ is not well-ordered because $\ZZ$ itself has no least
    element, and $\R$ under $<$ is not well-ordered because the open interval $(0,1) \StrictlyIncludedIn \R$ has no least
    element. Two
    well-orders are \termdefine{order-isomorphic} if some bijection between them preserves $<$.
-/
theorem nat_isWellOrder : IsWellOrder ℕ (· < ·) := inferInstance

/-- The whole set of integers has no least element. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{well-order} on a set is a total order in which every nonempty subset has a least element. The natural
    numbers under $<$ are the prototype. By contrast $\ZZ$ under $<$ is not well-ordered because $\ZZ$ itself has no least
    element, and $\R$ under $<$ is not well-ordered because the open interval $(0,1) \StrictlyIncludedIn \R$ has no least
    element. Two
    well-orders are \termdefine{order-isomorphic} if some bijection between them preserves $<$.
-/
theorem integers_no_least : ¬ ∃ m : ℤ, IsLeast Set.univ m := by
  rintro ⟨m, _, h⟩
  have hbad := h (show m - 1 ∈ (Set.univ : Set ℤ) from Set.mem_univ _)
  omega

/-- Therefore the usual order on the integers is not a well-order. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{well-order} on a set is a total order in which every nonempty subset has a least element. The natural
    numbers under $<$ are the prototype. By contrast $\ZZ$ under $<$ is not well-ordered because $\ZZ$ itself has no least
    element, and $\R$ under $<$ is not well-ordered because the open interval $(0,1) \StrictlyIncludedIn \R$ has no least
    element. Two
    well-orders are \termdefine{order-isomorphic} if some bijection between them preserves $<$.
-/
theorem integers_not_wellOrder : ¬ IsWellOrder ℤ (· < ·) := by
  intro h
  exact integers_no_least ((wellOrder_iff_least.mp h) Set.univ Set.univ_nonempty)

/-- The open unit interval has no least real number, as halving any point stays inside it. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{well-order} on a set is a total order in which every nonempty subset has a least element. The natural
    numbers under $<$ are the prototype. By contrast $\ZZ$ under $<$ is not well-ordered because $\ZZ$ itself has no least
    element, and $\R$ under $<$ is not well-ordered because the open interval $(0,1) \StrictlyIncludedIn \R$ has no least
    element. Two
    well-orders are \termdefine{order-isomorphic} if some bijection between them preserves $<$.
-/
theorem open_unit_interval_no_least : ¬ ∃ m : ℝ, IsLeast (Set.Ioo 0 1) m := by
  rintro ⟨m, ⟨hm0, hm1⟩, h⟩
  have hhalf : m / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith
  have hbad := h hhalf
  linarith

/-- The interval witnesses failure of well-ordering for the usual order on the reals. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{well-order} on a set is a total order in which every nonempty subset has a least element. The natural
    numbers under $<$ are the prototype. By contrast $\ZZ$ under $<$ is not well-ordered because $\ZZ$ itself has no least
    element, and $\R$ under $<$ is not well-ordered because the open interval $(0,1) \StrictlyIncludedIn \R$ has no least
    element. Two
    well-orders are \termdefine{order-isomorphic} if some bijection between them preserves $<$.
-/
theorem reals_not_wellOrder : ¬ IsWellOrder ℝ (· < ·) := by
  intro h
  apply open_unit_interval_no_least
  apply (wellOrder_iff_least.mp h) (Set.Ioo 0 1)
  exact ⟨1 / 2, by constructor <;> norm_num⟩

/-- Order-isomorphism uses a bijection preserving and reflecting the strict relations. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{well-order} on a set is a total order in which every nonempty subset has a least element. The natural
    numbers under $<$ are the prototype. By contrast $\ZZ$ under $<$ is not well-ordered because $\ZZ$ itself has no least
    element, and $\R$ under $<$ is not well-ordered because the open interval $(0,1) \StrictlyIncludedIn \R$ has no least
    element. Two
    well-orders are \termdefine{order-isomorphic} if some bijection between them preserves $<$.
-/
abbrev WellOrderIsomorphism {α : Type u} {β : Type v}
    (r : α → α → Prop) (s : β → β → Prop) := r ≃r s

end PolishSpaceBook.SetTheoryModels
