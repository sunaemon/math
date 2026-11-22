module

public import PolishSpaceBook.ForcingOpenDense

@[expose] public section

/-! # The order conventions of the forcing appendix

The condition order is refinement, so density is coinitiality and filters are
mathlib's order filters. A ground forcing notion carries an actual internal
ordered-pair code, rather than only an external order on an internal carrier.
-/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingAtomic
universe u

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{forcing notion} in $M$ is a nonempty partially ordered set $(P,\le) \in M$. Its elements are
    \termdefineas{condition}{conditions}. The order is read as refinement:
    $$q \le p \quad\text{means that } q \text{ is stronger than } p.$$
-/
structure GroundForcingNotion (M : ZFSet.{u}) where
  conditions : ZFSet.{u}
  relation : ZFSet.{u}
  code_mem : ZFSet.pair conditions relation ∈ M
  relation_subset : relation ⊆ ZFSet.prod conditions conditions
  order : PartialOrder (Condition conditions)
  nonempty : Nonempty (Condition conditions)
  relation_iff : ∀ p q : Condition conditions,
    ZFSet.pair p.val q.val ∈ relation ↔ order.le p q

theorem GroundForcingNotion.conditions_mem {M : ZFSet.{u}} (F : GroundForcingNotion M)
    (hM : M.IsTransitive) : F.conditions ∈ M := by
  have hs : ({F.conditions} : ZFSet.{u}) ∈ M :=
    hM.mem_trans (by simp [ZFSet.pair]) F.code_mem
  exact hM.mem_trans (by simp) hs

theorem GroundForcingNotion.relation_mem {M : ZFSet.{u}} (F : GroundForcingNotion M)
    (hM : M.IsTransitive) : F.relation ∈ M := by
  have hs : ({F.conditions, F.relation} : ZFSet.{u}) ∈ M :=
    hM.mem_trans (by simp [ZFSet.pair]) F.code_mem
  exact hM.mem_trans (by simp) hs

/-- Compatibility is an actual common strengthening. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Two conditions $p,q$ are \termdefine{compatible}, written $p \parallel q$, if they have a common strengthening $r \le
    p,q$; otherwise they are \termdefine{incompatible}, written $p \perp q$.
-/
def ForcingCompatible {P : Type*} [Preorder P] (p q : P) : Prop :=
  ∃ r : P, r ≤ p ∧ r ≤ q

theorem incompatible_iff_not_compatible {P : ZFSet.{u}} [Preorder (Condition P)]
    (p q : Condition P) : incompatible P p q ↔ ¬ForcingCompatible p q := Iff.rfl

/-- Use the canonical order predicates for density and downward openness. -/
def ForcingOpenDense {P : Type*} [Preorder P] (D : Set P) : Prop :=
  IsCoinitial D ∧ IsLowerSet D

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   \termdefine{predense below p} if every $q \le p$ is compatible with some element of $D$.
-/
def ForcingPredenseBelow {P : Type*} [Preorder P] (D : Set P) (p : P) : Prop :=
  ∀ q ≤ p, ∃ d ∈ D, ForcingCompatible q d

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   \termdefine{dense} if every $p \in P$ has some $q \le p$ with $q \in D$;
-/
theorem forcing_dense_iff {P : Type*} [Preorder P] (D : Set P) :
    IsCoinitial D ↔ ∀ p, ∃ q ≤ p, q ∈ D := by
  constructor
  · intro h p
    obtain ⟨q, hq, hqp⟩ := h p
    exact ⟨q, hqp, hq⟩
  · intro h p
    obtain ⟨q, hqp, hq⟩ := h p
    exact ⟨q, hq, hqp⟩

/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   \termdefine{open dense} if it is dense and downward closed: $p \in D$ and $q \le p$ imply $q \in D$;
-/
theorem forcing_open_dense_iff {P : Type*} [Preorder P] (D : Set P) :
    ForcingOpenDense D ↔ (∀ p, ∃ q ≤ p, q ∈ D) ∧
      ∀ p ∈ D, ∀ q ≤ p, q ∈ D := by
  rw [ForcingOpenDense, forcing_dense_iff]
  constructor
  · rintro ⟨hd, hl⟩
    exact ⟨hd, fun _ hp _ hqp => hl hqp hp⟩
  · rintro ⟨hd, hl⟩
    exact ⟨hd, fun p q hqp hp => hl p hp q hqp⟩

/-- The book's two filter clauses and nonemptiness are precisely IsPFilter. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{filter} on $P$ is a nonempty set $G \IncludedIn P$ satisfying:
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    1.  $G$ is upward closed toward weaker conditions: if $p \in G$ and $p \le q$, then $q \in G$;
    2.  $G$ is directed downward: if $p,q \in G$, then some $r \in G$ satisfies $r \le p,q$.
-/
theorem forcing_filter_iff {P : Type*} [Preorder P] (G : Set P) :
    Order.IsPFilter G ↔ G.Nonempty ∧
      (∀ p ∈ G, ∀ q, p ≤ q → q ∈ G) ∧
      (∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, r ≤ p ∧ r ≤ q) := by
  constructor
  · intro h
    let F := h.toPFilter
    refine ⟨F.nonempty, ?_, F.directed⟩
    intro p hp q hpq
    exact F.mem_of_le hpq hp
  · rintro ⟨hne, hup, hdir⟩
    exact Order.IsPFilter.of_def hne hdir (fun hpq hp => hup _ hp _ hpq)

end PolishSpaceBook.SetTheoryModels
