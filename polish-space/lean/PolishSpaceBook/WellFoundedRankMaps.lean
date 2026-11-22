module

public import Mathlib.SetTheory.Ordinal.Rank

@[expose] public section

/-!
# Well-founded ranks under relation-preserving maps

Shared rank infrastructure for the two directions of tree comparison.
-/

namespace PolishSpaceBook

universe u

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    For (1), an infinite branch through $T$ would map to an infinite strict-extension chain in $S$.
    Once $T$ is known to be
    well founded, induction upward from the terminal nodes gives
    $$
    \rho_T(t)\leq\rho_S(f(t))
    $$
    for every $t\in T$, and applying this at the roots gives the rank inequality.
-/
/-- A map preserving the direction of a relation transfers well-foundedness
from its target relation back to its source relation. This is the abstract
content of the branch argument in the tree-rank comparison lemma. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{tree-rank comparison lemma}{Tree-rank comparison}]
-/
theorem wellFounded_of_relation_preserving
    {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
    (hs : WellFounded s) (f : α → β)
    (hf : ∀ ⦃a b⦄, r a b → s (f a) (f b)) :
    WellFounded r :=
  hs.onFun.mono fun _ _ hab ↦ hf hab

/-- A relation-preserving map cannot increase rank between well-founded
relations. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{tree-rank comparison lemma}{Tree-rank comparison}]
-/
theorem wellFoundedRank_le_of_relation_preserving
    {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
    [WellFounded r] [WellFounded s]
    (f : α → β) (hf : ∀ ⦃a b⦄, r a b → s (f a) (f b)) (a : α) :
    WellFounded.rank r a ≤ WellFounded.rank s (f a) := by
  induction a using (inferInstance : WellFounded r).induction with
  | h a ih =>
      rw [WellFounded.rank_eq, WellFounded.rank_eq]
      refine Ordinal.iSup_le fun b ↦ ?_
      have hrank : WellFounded.rank r b.1 ≤ WellFounded.rank s (f b.1) :=
        ih b.1 b.2
      refine (Order.succ_le_succ hrank).trans ?_
      exact Ordinal.le_iSup
        (fun c : {c // s c (f a)} ↦ Order.succ (WellFounded.rank s c.1))
        ⟨f b.1, hf b.2⟩

end PolishSpaceBook
