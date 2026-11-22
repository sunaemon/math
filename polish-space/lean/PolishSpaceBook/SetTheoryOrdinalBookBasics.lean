module

public import PolishSpaceBook.SetTheoryFiniteOrdinals
public import PolishSpaceBook.SetTheoryProperClasses
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

/-! # The initial-segment argument for von Neumann ordinals -/

namespace PolishSpaceBook.SetTheoryModels
universe u

/-- A proper transitive initial part of an ordinal is its least omitted element. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In symbols, the von Neumann definition is the ZFC formula
    $$\begin{aligned}
    \mathrm{Ord}(x) \;&:\equiv\; \mathrm{Trans}(x) \;\wedge\; (\forall y \in x)\,\mathrm{Trans}(y), \\
    \mathrm{Trans}(x) \;&:\equiv\; (\forall y \in x)(\forall z \in y)\; z \in x.
    \end{aligned}$$
    This formula is equivalent in ZF to the definition above. First, two ordinals are comparable by membership:
    their intersection is an initial segment of each, and a proper initial segment of an ordinal is the predecessor
    set of its least omitted element, hence that element itself. If the intersection were proper in both, it would
    belong to itself, contradicting Foundation. Now apply membership induction to a transitive set all of whose
    elements are transitive. Each of its elements has the same property and is therefore an ordinal by induction.
    Comparability of ordinals and Foundation then make membership a well-order on the original transitive set.
    The complexity classification and its forcing consequences appear in §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
theorem ordinal_proper_transitive_subset {a i : ZFSet.{u}} (ha : a.IsOrdinal)
    (hi : i.IsTransitive) (hsub : i ⊆ a) (hne : i ≠ a) : i ∈ a := by
  classical
  have hnot : ¬a ⊆ i := fun h => hne (ZFSet.ext fun z => ⟨fun hz => hsub hz, fun hz => h hz⟩)
  obtain ⟨m, hm, hmin⟩ := ZFSet.mem_wf.has_min (a \ i) (Set.sdiff_nonempty.mpr hnot)
  have hma : m ∈ a := hm.1
  have hmi : m ∉ i := hm.2
  have heq : m = i := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hzm
      by_contra hzi
      exact hmin z ⟨ha.mem_trans hzm hma, hzi⟩ hzm
    · intro hzi
      let := ha.isWellOrder
      rcases trichotomous_of (Subrel (· ∈ ·) (· ∈ a))
          (⟨z, hsub hzi⟩ : a) ⟨m, hma⟩ with hzm | he | hmz
      · exact hzm
      · have hze : z = m := congrArg Subtype.val he
        exact False.elim (hmi (hze ▸ hzi))
      · exact False.elim (hmi (hi.mem_trans hmz hzi))
  exact heq ▸ hma

/-- Comparing the intersection of two ordinals proves comparability by membership. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In symbols, the von Neumann definition is the ZFC formula
    $$\begin{aligned}
    \mathrm{Ord}(x) \;&:\equiv\; \mathrm{Trans}(x) \;\wedge\; (\forall y \in x)\,\mathrm{Trans}(y), \\
    \mathrm{Trans}(x) \;&:\equiv\; (\forall y \in x)(\forall z \in y)\; z \in x.
    \end{aligned}$$
    This formula is equivalent in ZF to the definition above. First, two ordinals are comparable by membership:
    their intersection is an initial segment of each, and a proper initial segment of an ordinal is the predecessor
    set of its least omitted element, hence that element itself. If the intersection were proper in both, it would
    belong to itself, contradicting Foundation. Now apply membership induction to a transitive set all of whose
    elements are transitive. Each of its elements has the same property and is therefore an ordinal by induction.
    Comparability of ordinals and Foundation then make membership a well-order on the original transitive set.
    The complexity classification and its forcing consequences appear in §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
theorem ordinals_comparable_by_intersection {a b : ZFSet.{u}}
    (ha : a.IsOrdinal) (hb : b.IsOrdinal) : a ∈ b ∨ a = b ∨ b ∈ a := by
  classical
  let i := a ∩ b
  have hi : i.IsTransitive := by
    intro x hx y hy
    exact ZFSet.mem_inter.mpr ⟨ha.mem_trans hy (ZFSet.mem_inter.mp hx).1,
      hb.mem_trans hy (ZFSet.mem_inter.mp hx).2⟩
  have hia : i ⊆ a := fun _ hx => (ZFSet.mem_inter.mp hx).1
  have hib : i ⊆ b := fun _ hx => (ZFSet.mem_inter.mp hx).2
  by_cases hea : i = a
  · by_cases hab : a = b
    · exact Or.inr (Or.inl hab)
    · exact Or.inl (ordinal_proper_transitive_subset hb ha.isTransitive (hea ▸ hib) hab)
  · by_cases heb : i = b
    · exact Or.inr (Or.inr (ordinal_proper_transitive_subset ha hb.isTransitive (heb ▸ hia)
        (fun h => hea (heb.trans h))))
    · have hia' := ordinal_proper_transitive_subset ha hi hia hea
      have hib' := ordinal_proper_transitive_subset hb hi hib heb
      exact False.elim (ZFSet.mem_irrefl i (ZFSet.mem_inter.mpr ⟨hia', hib'⟩))

/-- Membership induction turns a transitive set of transitive sets into an ordinal. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In symbols, the von Neumann definition is the ZFC formula
    $$\begin{aligned}
    \mathrm{Ord}(x) \;&:\equiv\; \mathrm{Trans}(x) \;\wedge\; (\forall y \in x)\,\mathrm{Trans}(y), \\
    \mathrm{Trans}(x) \;&:\equiv\; (\forall y \in x)(\forall z \in y)\; z \in x.
    \end{aligned}$$
    This formula is equivalent in ZF to the definition above. First, two ordinals are comparable by membership:
    their intersection is an initial segment of each, and a proper initial segment of an ordinal is the predecessor
    set of its least omitted element, hence that element itself. If the intersection were proper in both, it would
    belong to itself, contradicting Foundation. Now apply membership induction to a transitive set all of whose
    elements are transitive. Each of its elements has the same property and is therefore an ordinal by induction.
    Comparability of ordinals and Foundation then make membership a well-order on the original transitive set.
    The complexity classification and its forcing consequences appear in §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
theorem ordinal_of_transitive_members (a : ZFSet.{u})
    (ha : a.IsTransitive) (hm : ∀ x ∈ a, x.IsTransitive) : a.IsOrdinal := by
  induction a using ZFSet.inductionOn with
  | h a ih =>
    apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
    refine ⟨ha, ?_⟩
    intro x hx
    exact ih x hx (hm x hx) (fun y hy => hm y (ha.mem_trans hy hx))

/-- The displayed transitive-of-transitives predicate and the book's well-order definition agree. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termdefineas{von Neumann ordinal}{Von Neumann's construction} packages well-order types as canonical sets. An
    \termdefine{ordinal} is a transitive set well-ordered by $\in$, where *transitive* means every element is also a subset.
    The first few:
    $$
    \begin{aligned}
    0 &:= \emptyset, &
    1 &:= \{0\}, &
    2 &:= \{0,1\},\\
    &\ldots, &
    n &:= \{0,1,\ldots,n-1\}, &
    \omega &:= \{0,1,2,\ldots\}.
    \end{aligned}
    $$
    Each ordinal $\alpha$ is the set of strictly smaller ordinals, $\alpha = \{\beta : \beta < \alpha\}$, and the order $<$
    on ordinals coincides with $\in$. The class $\mathrm{Ord}$ of all ordinals is itself well-ordered by $\in$ but is a
    proper class, not a set, by the Burali-Forti paradox. Every well-order is in fact order-isomorphic to a unique ordinal —
    see §{sec:ordinals-representation} after the recursion principle is in place.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In symbols, the von Neumann definition is the ZFC formula
    $$\begin{aligned}
    \mathrm{Ord}(x) \;&:\equiv\; \mathrm{Trans}(x) \;\wedge\; (\forall y \in x)\,\mathrm{Trans}(y), \\
    \mathrm{Trans}(x) \;&:\equiv\; (\forall y \in x)(\forall z \in y)\; z \in x.
    \end{aligned}$$
    This formula is equivalent in ZF to the definition above. First, two ordinals are comparable by membership:
    their intersection is an initial segment of each, and a proper initial segment of an ordinal is the predecessor
    set of its least omitted element, hence that element itself. If the intersection were proper in both, it would
    belong to itself, contradicting Foundation. Now apply membership induction to a transitive set all of whose
    elements are transitive. Each of its elements has the same property and is therefore an ordinal by induction.
    Comparability of ordinals and Foundation then make membership a well-order on the original transitive set.
    The complexity classification and its forcing consequences appear in §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
theorem ordinal_predicate_iff_wellOrder (a : ZFSet.{u}) :
    (a.IsTransitive ∧ ∀ x ∈ a, x.IsTransitive) ↔
      a.IsTransitive ∧ IsWellOrder a (Subrel (· ∈ ·) (· ∈ a)) := by
  constructor
  · rintro ⟨ha, hm⟩
    exact ⟨ha, (ordinal_of_transitive_members a ha hm).isWellOrder⟩
  · intro h
    exact ZFSet.isOrdinal_iff_forall_mem_isTransitive.mp
      (ZFSet.isOrdinal_iff_isWellOrder.mpr h)

/-- The members of an ordinal are precisely the set representatives of its smaller ordinals. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termdefineas{von Neumann ordinal}{Von Neumann's construction} packages well-order types as canonical sets. An
    \termdefine{ordinal} is a transitive set well-ordered by $\in$, where *transitive* means every element is also a subset.
    The first few:
    $$
    \begin{aligned}
    0 &:= \emptyset, &
    1 &:= \{0\}, &
    2 &:= \{0,1\},\\
    &\ldots, &
    n &:= \{0,1,\ldots,n-1\}, &
    \omega &:= \{0,1,2,\ldots\}.
    \end{aligned}
    $$
    Each ordinal $\alpha$ is the set of strictly smaller ordinals, $\alpha = \{\beta : \beta < \alpha\}$, and the order $<$
    on ordinals coincides with $\in$. The class $\mathrm{Ord}$ of all ordinals is itself well-ordered by $\in$ but is a
    proper class, not a set, by the Burali-Forti paradox. Every well-order is in fact order-isomorphic to a unique ordinal —
    see §{sec:ordinals-representation} after the recursion principle is in place.
-/
theorem mem_ordinal_iff_smaller {a b : ZFSet.{u}} (ha : a.IsOrdinal) :
    b ∈ a ↔ ∃ β : Ordinal.{u}, β < a.rank ∧ β.toZFSet = b := by
  simpa only [ha.toZFSet_rank_eq] using
    (Ordinal.mem_toZFSet_iff (o := a.rank) (x := b))

/-- Membership well-orders the class of ordinals, represented as a subtype rather than a set. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termdefineas{von Neumann ordinal}{Von Neumann's construction} packages well-order types as canonical sets. An
    \termdefine{ordinal} is a transitive set well-ordered by $\in$, where *transitive* means every element is also a subset.
    The first few:
    $$
    \begin{aligned}
    0 &:= \emptyset, &
    1 &:= \{0\}, &
    2 &:= \{0,1\},\\
    &\ldots, &
    n &:= \{0,1,\ldots,n-1\}, &
    \omega &:= \{0,1,2,\ldots\}.
    \end{aligned}
    $$
    Each ordinal $\alpha$ is the set of strictly smaller ordinals, $\alpha = \{\beta : \beta < \alpha\}$, and the order $<$
    on ordinals coincides with $\in$. The class $\mathrm{Ord}$ of all ordinals is itself well-ordered by $\in$ but is a
    proper class, not a set, by the Burali-Forti paradox. Every well-order is in fact order-isomorphic to a unique ordinal —
    see §{sec:ordinals-representation} after the recursion principle is in place.
-/
theorem ordinal_class_isWellOrder :
    IsWellOrder {a : ZFSet.{u} // a.IsOrdinal} (fun a b => a.val ∈ b.val) where
  wf := InvImage.wf (fun a : {a : ZFSet.{u} // a.IsOrdinal} => a.val) ZFSet.mem_wf
  trichotomous a b := by
    intro hnab hnba
    rcases ordinals_comparable_by_intersection a.property b.property with hab | he | hba
    · exact False.elim (hnab hab)
    · exact Subtype.ext he
    · exact False.elim (hnba hba)

/-- Adding one gives the von Neumann successor: adjoining the ordinal itself. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{successor} of an ordinal $\alpha$ is $\alpha + 1 := \alpha \cup \{\alpha\}$, the next-larger ordinal. An
    ordinal is a \termuse{successor} if it equals $\beta + 1$ for some $\beta$. A \termdefine{limit ordinal} is a nonzero
    ordinal that is not a successor; the smallest limit ordinal is $\omega$. Larger limit ordinals built from arithmetic
    appear in §{sec:ordinals-arithmetic}.
-/
theorem ordinal_successor_as_set (α : Ordinal.{u}) :
    (α + 1).toZFSet = insert α.toZFSet α.toZFSet := Ordinal.toZFSet_add_one α

/-- The canonical limit predicate says exactly nonzero and not a successor. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{successor} of an ordinal $\alpha$ is $\alpha + 1 := \alpha \cup \{\alpha\}$, the next-larger ordinal. An
    ordinal is a \termuse{successor} if it equals $\beta + 1$ for some $\beta$. A \termdefine{limit ordinal} is a nonzero
    ordinal that is not a successor; the smallest limit ordinal is $\omega$. Larger limit ordinals built from arithmetic
    appear in §{sec:ordinals-arithmetic}.
-/
theorem ordinal_limit_iff_nonzero_not_successor (α : Ordinal.{u}) :
    Order.IsSuccLimit α ↔ α ≠ 0 ∧ ∀ β : Ordinal.{u}, β + 1 ≠ α := by
  rw [Ordinal.isSuccLimit_iff, Order.isSuccPrelimit_iff_succ_ne]
  simp only [Order.succ_eq_add_one]

/-- Omega is the least nonzero limit ordinal. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The \termdefine{successor} of an ordinal $\alpha$ is $\alpha + 1 := \alpha \cup \{\alpha\}$, the next-larger ordinal. An
    ordinal is a \termuse{successor} if it equals $\beta + 1$ for some $\beta$. A \termdefine{limit ordinal} is a nonzero
    ordinal that is not a successor; the smallest limit ordinal is $\omega$. Larger limit ordinals built from arithmetic
    appear in §{sec:ordinals-arithmetic}.
-/
theorem omega_least_limit :
    Order.IsSuccLimit (Ordinal.omega0 : Ordinal.{u}) ∧
      ∀ α : Ordinal.{u}, Order.IsSuccLimit α → Ordinal.omega0 ≤ α :=
  ⟨Ordinal.isSuccLimit_omega0, fun _ h => Ordinal.omega0_le_of_isSuccLimit h⟩

end PolishSpaceBook.SetTheoryModels
