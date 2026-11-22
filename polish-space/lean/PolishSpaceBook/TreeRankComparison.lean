module

public import PolishSpaceBook.WellFoundedRankMaps
public import PolishSpaceBook.CantorBaireSpace

@[expose] public section

/-!
# Constructing tree maps from rank inequalities

The construction follows the book: send the root to the root and choose a
strict target extension for each immediate source successor, maintaining
the rank inequality. Images of different successors need not be distinct.
-/

namespace PolishSpaceBook
open Set

/-- The descending relation used to rank a prefix tree. -/
def strictTreeExtension (T : Set (finseq ℕ)) (u v : T) : Prop :=
  prefixOf v.val u.val ∧ v.val.length < u.val.length

theorem strictTreeExtension_trans {T : Set (finseq ℕ)} {u v w : T}
    (huv : strictTreeExtension T u v) (hvw : strictTreeExtension T v w) :
    strictTreeExtension T u w :=
  ⟨hvw.1.trans huv.1, hvw.2.trans huv.2⟩

/-- A rank strictly below that of a node is bounded by the rank of some
strict successor. This is the local choice in the book's recursion. -/
theorem exists_successor_of_lt_rank {α : Type*} {r : α → α → Prop}
    [WellFounded r] (a : α) (o : Ordinal) (h : o < WellFounded.rank r a) :
    ∃ b, r b a ∧ o ≤ WellFounded.rank r b := by
  rw [WellFounded.rank_eq, Ordinal.lt_iSup_iff] at h
  obtain ⟨⟨b, hb⟩, h⟩ := h
  exact ⟨b, hb, Order.lt_succ_iff.mp h⟩

noncomputable def advanceByRank {α : Type*} (r : α → α → Prop)
    [WellFounded r] (a : α) (o : Ordinal) : α := by
  classical
  exact if h : o < WellFounded.rank r a then
    (exists_successor_of_lt_rank a o h).choose else a

theorem advanceByRank_spec {α : Type*} (r : α → α → Prop)
    [WellFounded r] (a : α) (o : Ordinal) (h : o < WellFounded.rank r a) :
    r (advanceByRank r a o) a ∧ o ≤ WellFounded.rank r (advanceByRank r a o) := by
  classical
  simpa [advanceByRank, h] using (exists_successor_of_lt_rank a o h).choose_spec

section TreeMap

variable (T S : Set (finseq ℕ))
variable [WellFounded (strictTreeExtension T)] [WellFounded (strictTreeExtension S)]

/-- Define the map on words by recursion from left to right. Invalid source
words are ignored; only values on the tree are used by the final map. -/
noncomputable def treeRankMapWords (root : S) (t : finseq ℕ) : S := by
  classical
  exact List.reverseRecOn t root (fun u a previous =>
    if h : u ++ [a] ∈ T then
      advanceByRank (strictTreeExtension S) previous
        (WellFounded.rank (strictTreeExtension T) ⟨u ++ [a], h⟩)
    else previous)

theorem treeRankMapWords_nil (root : S) : treeRankMapWords T S root [] = root := by
  simp [treeRankMapWords]

theorem treeRankMapWords_step (root : S) (t : finseq ℕ) (a : ℕ) (ht : t ++ [a] ∈ T) :
    treeRankMapWords T S root (t ++ [a]) =
      advanceByRank (strictTreeExtension S) (treeRankMapWords T S root t)
        (WellFounded.rank (strictTreeExtension T) ⟨t ++ [a], ht⟩) := by
  classical
  simp [treeRankMapWords, ht]

variable (hT : IsSubtree T) (hrootT : [] ∈ T) (root : S)
variable (hrank : WellFounded.rank (strictTreeExtension T) ⟨[], hrootT⟩ ≤
  WellFounded.rank (strictTreeExtension S) root)

include hT hrootT hrank

theorem treeRankMapWords_rank (t : finseq ℕ) (ht : t ∈ T) :
    WellFounded.rank (strictTreeExtension T) ⟨t, ht⟩ ≤
      WellFounded.rank (strictTreeExtension S) (treeRankMapWords T S root t) := by
  induction t using List.reverseRecOn with
  | nil => simpa [treeRankMapWords_nil] using hrank
  | append_singleton t a ih =>
    have hparent : t ∈ T := hT ht (List.prefix_append t [a])
    have hchild : strictTreeExtension T ⟨t ++ [a], ht⟩ ⟨t, hparent⟩ :=
      ⟨List.prefix_append t [a], by simp⟩
    have hlt := (WellFounded.rank_lt_of_rel hchild).trans_le (ih hparent)
    rw [treeRankMapWords_step T S root t a ht]
    exact (advanceByRank_spec _ _ _ hlt).2

theorem treeRankMapWords_immediate (t : finseq ℕ) (a : ℕ) (ht : t ++ [a] ∈ T) :
    strictTreeExtension S (treeRankMapWords T S root (t ++ [a]))
      (treeRankMapWords T S root t) := by
  have hparent : t ∈ T := hT ht (List.prefix_append t [a])
  have hchild : strictTreeExtension T ⟨t ++ [a], ht⟩ ⟨t, hparent⟩ :=
    ⟨List.prefix_append t [a], by simp⟩
  have hlt := (WellFounded.rank_lt_of_rel hchild).trans_le
    (treeRankMapWords_rank T S hT hrootT root hrank t hparent)
  rw [treeRankMapWords_step T S root t a ht]
  exact (advanceByRank_spec _ _ _ hlt).1

theorem treeRankMapWords_preserves {u v : finseq ℕ} (hu : u ∈ T)
    (hvu : prefixOf v u) (hlen : v.length < u.length) :
    strictTreeExtension S (treeRankMapWords T S root u) (treeRankMapWords T S root v) := by
  induction u using List.reverseRecOn with
  | nil => simp at hlen
  | append_singleton u a ih =>
    have hstep := treeRankMapWords_immediate T S hT hrootT root hrank u a hu
    have hle : v.length ≤ u.length := by simpa using hlen
    have hvu' : prefixOf v u := by
      exact List.prefix_iff_eq_take.mpr
        ((List.prefix_iff_eq_take.mp hvu).trans (List.take_append_of_le_length hle))
    rcases hle.eq_or_lt with heq | hlt
    · have heq' : v = u := hvu'.eq_of_length heq
      simpa [heq'] using hstep
    · exact strictTreeExtension_trans hstep (ih (hT hu (List.prefix_append u [a])) hvu' hlt)

end TreeMap

/-- Converse tree-rank comparison: rank inequality gives a root-preserving
map preserving every strict extension, with no injectivity requirement. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    For (2), send the root of $T$ to the root of $S$ and recurse down $T$. Maintain
    $\rho_T(t)\leq\rho_S(f(t))$. If $u$ is an immediate successor of $t$, then
    $\rho_T(u)<\rho_S(f(t))$. The definition of the rank at $f(t)$ therefore supplies a strict extension $v$ of $f(t)$
    with $\rho_T(u)\leq\rho_S(v)$. Put $f(u)=v$. Choices for different successors may coincide, which is harmless because
    only strict-extension preservation is required.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{tree-rank comparison lemma}{Tree-rank comparison}]
-/
theorem exists_tree_map_of_rank_le (T S : Set (finseq ℕ))
    [WellFounded (strictTreeExtension T)] [WellFounded (strictTreeExtension S)]
    (hT : IsSubtree T) (hrootT : [] ∈ T) (hrootS : [] ∈ S)
    (hrank : WellFounded.rank (strictTreeExtension T) ⟨[], hrootT⟩ ≤
      WellFounded.rank (strictTreeExtension S) ⟨[], hrootS⟩) :
    ∃ f : T → S, f ⟨[], hrootT⟩ = ⟨[], hrootS⟩ ∧
      ∀ u v, strictTreeExtension T u v → strictTreeExtension S (f u) (f v) := by
  refine ⟨fun t => treeRankMapWords T S ⟨[], hrootS⟩ t.val, ?_, ?_⟩
  · exact treeRankMapWords_nil T S _
  · intro u v h
    exact treeRankMapWords_preserves T S hT hrootT ⟨[], hrootS⟩ hrank u.property h.1 h.2

end PolishSpaceBook
