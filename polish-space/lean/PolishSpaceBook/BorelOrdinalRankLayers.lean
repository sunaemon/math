module

public import PolishSpaceBook.WellFoundedRankMaps
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.SetTheory.Cardinal.Aleph

@[expose] public section

/-!
# Borel rank layers by countable ordinal recursion

Accessibility is included in the layer predicate. The construction uses only
countable unions, intersections and complements of the edge sets; it does not
invoke analytic separation or Suslin's theorem.
-/

namespace PolishSpaceBook
namespace OrdinalRankLayer

open Set MeasureTheory

/-- Local well-foundedness and a bound on the accessible-node rank. -/
def Holds {N : Type} (E : N → N → Prop) (α : Ordinal) (s : N) : Prop :=
  ∃ hs : Acc E s, hs.rank ≤ α

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    To prove Borelness of the rank layers directly, let $E_x(t,s)$ mean that $s,t\in T_x$ and $s\properPrefixOf t$.
    For each fixed pair of words, the edge event $E_{t,s}:=\{x:E_x(t,s)\}$ is Borel, because the two node-membership
    conditions are open. Treat words outside the tree as isolated nodes of this relation. Define
    $\OrdinalRankLayer{\alpha}{s}$ to consist of the $x$ for which the relation below $s$ is well founded and its rank at
    $s$ is at most $\alpha$. Then
    $$
    \OrdinalRankLayer{\alpha}{s}
    =\bigcap_{t\in\finseq{\omega}}\left(
    E_{t,s}^{\complement}\cup\bigcup_{\beta<\alpha}\OrdinalRankLayer{\beta}{t}\right).
    $$
-/
/-- Each predecessor must lie in a layer with strictly smaller ordinal bound. -/
theorem iff_children {N : Type} (E : N → N → Prop) (α : Ordinal) (s : N) :
    Holds E α s ↔ ∀ t, E t s → ∃ β < α, Holds E β t := by
  constructor
  · rintro ⟨hs, hα⟩ t ht
    exact ⟨(hs.inv ht).rank, (Acc.rank_lt_of_rel hs ht).trans_le hα, hs.inv ht, le_rfl⟩
  · intro h
    have hs : Acc E s := by
      constructor
      intro t ht
      obtain ⟨β, _, hacc, _⟩ := h t ht
      exact hacc
    refine ⟨hs, ?_⟩
    rw [hs.rank_eq]
    apply Ordinal.iSup_le
    rintro ⟨t, ht⟩
    obtain ⟨β, hβα, hacc, hβ⟩ := h t ht
    exact Order.succ_le_iff.mpr (hβ.trans_lt hβα)

/-- The ordinals below a countable ordinal form a countable index set. -/
theorem countable_Iio (α : Ordinal) (hα : α < Ordinal.omega 1) : (Iio α).Countable := by
  have hc : α.card ≤ Cardinal.aleph0 :=
    Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_omega_iff_card_lt.mp hα)
  apply Cardinal.le_aleph0_iff_set_countable.mp
  rw [Cardinal.mk_Iio_ordinal]
  simpa using Cardinal.lift_le.mpr hc

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    For the forward inclusion, a predecessor in the relation has rank strictly below the rank at $s$, so its
    rank itself supplies a bound $\beta<\alpha$. Conversely, if every predecessor has a well-founded relation below it,
    then the same holds at $s$. If each predecessor rank is at most some $\beta<\alpha$, the successor ordinal of each
    predecessor rank
    is at most $\alpha$, so their supremum is at most $\alpha$. This proves the recursion, including $\alpha=0$, when the
    inner union
    is empty. Transfinite induction now makes every $\OrdinalRankLayer{\alpha}{s}$ Borel for countable $\alpha$: the set
    of smaller ordinals and the set of words are both countable. In particular,
    $$C_{\le\alpha}=\OrdinalRankLayer{\alpha}{\emptySeq}$$
    is Borel. This argument uses no separation theorem.
-/
/-- Transfinite recursion on the bound proves Borelness directly. -/
theorem measurableSet {X : Type*} {N : Type} [MeasurableSpace X] [Countable N]
    (E : X → N → N → Prop) (hE : ∀ t s, MeasurableSet {x | E x t s})
    (α : Ordinal) (hα : α < Ordinal.omega 1) (s : N) :
    MeasurableSet {x | Holds (E x) α s} := by
  induction α using WellFoundedLT.induction generalizing s with
  | ind α ih =>
    let := (countable_Iio α hα).to_subtype
    have heq : {x | Holds (E x) α s} =
        ⋂ t, ({x | E x t s}ᶜ ∪ ⋃ β : Iio α, {x | Holds (E x) β.val t}) := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, mem_iUnion]
      rw [iff_children]
      constructor
      · intro h t
        by_cases ht : E x t s
        · obtain ⟨β, hβ, hb⟩ := h t ht
          exact Or.inr ⟨⟨β, hβ⟩, hb⟩
        · exact Or.inl ht
      · intro h t ht
        obtain ⟨β, hb⟩ := (h t).resolve_left (not_not.mpr ht)
        exact ⟨β.val, β.property, hb⟩
    rw [heq]
    exact MeasurableSet.iInter fun t => (hE t s).compl.union
      (MeasurableSet.iUnion fun β => ih β.val β.property (β.property.trans hα) t)

end OrdinalRankLayer
end PolishSpaceBook
