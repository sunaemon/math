module

public import PolishSpaceBook.TreeWellFounded

@[expose] public section

/-!
# The tree-comparison separator

These are the semantic parts of the book's effective separation argument:
the two map predicates are complementary if one tree is well founded, and
they separate disjoint branch-existence sets. The companion modules
`LambdaTreeMapPrograms` and `LambdaEffectiveSeparation` supply the canonical
lambda decision programs and index transformations. The arguments here are
purely semantic.
-/

namespace PolishSpaceBook
open Set

structure RootedPrefixTree where
  tree : Set (finseq ℕ)
  downward : IsSubtree tree
  root_mem : [] ∈ tree

def RootedPrefixTree.root (T : RootedPrefixTree) : T.tree := ⟨[], T.root_mem⟩

def TreeComparisonLe (T S : RootedPrefixTree) : Prop :=
  ∃ f : T.tree → S.tree, f T.root = S.root ∧
    ∀ u v, strictTreeExtension T.tree u v → strictTreeExtension S.tree (f u) (f v)

def TreeComparisonLt (T S : RootedPrefixTree) : Prop :=
  ∃ f : T.tree → S.tree, (f T.root).val ≠ [] ∧
    ∀ u v, strictTreeExtension T.tree u v → strictTreeExtension S.tree (f u) (f v)

theorem treeComparisonLe_of_branch (T S : RootedPrefixTree)
    (hS : ∃ p, p ∈ treeBody S.tree) : TreeComparisonLe T S := by
  obtain ⟨p, hp⟩ := hS
  obtain ⟨f, hf, hmap⟩ := tree_map_along_branch T.tree S.tree T.root_mem hp 0
  exact ⟨f, by simpa [RootedPrefixTree.root, seqPrefix] using hf, hmap⟩

theorem treeComparisonLt_of_branch (T S : RootedPrefixTree)
    (hS : ∃ p, p ∈ treeBody S.tree) : TreeComparisonLt T S := by
  obtain ⟨p, hp⟩ := hS
  obtain ⟨f, hf, hmap⟩ := tree_map_along_branch T.tree S.tree T.root_mem hp 1
  refine ⟨f, ?_, hmap⟩
  change (f ⟨[], T.root_mem⟩).val ≠ []
  rw [hf]
  intro h
  have := congrArg List.length h
  simp [seqPrefix_length] at this

theorem branch_of_not_wellFounded (T : RootedPrefixTree)
    (h : ¬ WellFounded (strictTreeExtension T.tree)) : ∃ p, p ∈ treeBody T.tree := by
  by_contra hn
  exact h ((prefixTreeWellFounded_iff T.tree T.downward).mp hn)

section WellFounded

variable (T S : RootedPrefixTree)
variable [WellFounded (strictTreeExtension T.tree)]
variable [WellFounded (strictTreeExtension S.tree)]

theorem treeComparisonLe_iff_rank_le : TreeComparisonLe T S ↔
    WellFounded.rank (strictTreeExtension T.tree) T.root ≤
      WellFounded.rank (strictTreeExtension S.tree) S.root := by
  constructor
  · rintro ⟨f, hf, hmap⟩
    have h := wellFoundedRank_le_of_relation_preserving f (fun {_ _} h => hmap _ _ h) T.root
    rwa [hf] at h
  · intro h
    exact exists_tree_map_of_rank_le T.tree S.tree T.downward T.root_mem S.root_mem h

theorem treeComparisonLt_iff_rank_lt : TreeComparisonLt T S ↔
    WellFounded.rank (strictTreeExtension T.tree) T.root <
      WellFounded.rank (strictTreeExtension S.tree) S.root := by
  constructor
  · rintro ⟨f, hf, hmap⟩
    have hle := wellFoundedRank_le_of_relation_preserving f (fun {_ _} h => hmap _ _ h) T.root
    have hrel : strictTreeExtension S.tree (f T.root) S.root :=
      ⟨List.nil_prefix, List.length_pos_iff.mpr hf⟩
    exact hle.trans_lt (WellFounded.rank_lt_of_rel hrel)
  · intro h
    let a := advanceByRank (strictTreeExtension S.tree) S.root
      (WellFounded.rank (strictTreeExtension T.tree) T.root)
    have ha := advanceByRank_spec (strictTreeExtension S.tree) S.root
      (WellFounded.rank (strictTreeExtension T.tree) T.root) h
    refine ⟨fun t => treeRankMapWords T.tree S.tree a t.val, ?_, ?_⟩
    · change (treeRankMapWords T.tree S.tree a []).val ≠ []
      rw [treeRankMapWords_nil]
      intro he
      have hlen := ha.1.2
      change 0 < a.val.length at hlen
      simp [he] at hlen
    · intro u v huv
      exact treeRankMapWords_preserves T.tree S.tree T.downward T.root_mem a ha.2
        u.property huv.1 huv.2

end WellFounded

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Take $D=\pi_0([C_{=}(S,T)])$ and $D'=\pi_0([C_{\ne}(T,S)])$, where the subscripts specify the two
    root tests. At least one of $T_x,S_x$ is well founded. If both are well founded, the tree-rank comparison
    lemma identifies the two conditions with $\rho(S_x)\le\rho(T_x)$ and $\rho(T_x)<\rho(S_x)$.
    If just one is ill founded, a branch supplies the map into that tree, and a map in the other direction
    would produce a branch in a well-founded tree. Thus the two conditions are complementary and give the
    required inclusions. For indices, first use the delayed tree presentations, which form a jointly decidable
    family on all indices. Apply the two comparison constructions to this family, then specialize each joint
    decision program by inserting the paired input index into its fixed syntax. The specialization construction
    of §{sec:edst-pair-tree-indices} is itself lambda-computable and preserves the projections.
    No decision of disjointness and no enlargement of $\varepsilon$ occurs.
    \end{proof}
-/
/-- The non-strict reverse map and the strict forward map are mutually
exclusive and exhaustive whenever at least one tree is well founded. -/
theorem treeComparison_complement (T S : RootedPrefixTree)
    (h : WellFounded (strictTreeExtension T.tree) ∨ WellFounded (strictTreeExtension S.tree)) :
    TreeComparisonLe S T ↔ ¬ TreeComparisonLt T S := by
  by_cases hT : WellFounded (strictTreeExtension T.tree)
  · let : WellFounded (strictTreeExtension T.tree) := hT
    by_cases hS : WellFounded (strictTreeExtension S.tree)
    · let : WellFounded (strictTreeExtension S.tree) := hS
      rw [treeComparisonLe_iff_rank_le, treeComparisonLt_iff_rank_lt]
      exact not_lt.symm
    · have hlt := treeComparisonLt_of_branch T S (branch_of_not_wellFounded S hS)
      constructor
      · rintro ⟨f, _, hmap⟩
        exact False.elim (hS (wellFounded_of_relation_preserving hT f
          (fun {_ _} h => hmap _ _ h)))
      · intro hn
        exact False.elim (hn hlt)
  · have hS := h.resolve_left hT
    have hle := treeComparisonLe_of_branch S T (branch_of_not_wellFounded T hT)
    constructor
    · intro _ hlt
      obtain ⟨f, _, hmap⟩ := hlt
      exact hT (wellFounded_of_relation_preserving hS f (fun {_ _} h => hmap _ _ h))
    · intro _
      exact hle

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Take $D=\pi_0([C_{=}(S,T)])$ and $D'=\pi_0([C_{\ne}(T,S)])$, where the subscripts specify the two
    root tests. At least one of $T_x,S_x$ is well founded. If both are well founded, the tree-rank comparison
    lemma identifies the two conditions with $\rho(S_x)\le\rho(T_x)$ and $\rho(T_x)<\rho(S_x)$.
    If just one is ill founded, a branch supplies the map into that tree, and a map in the other direction
    would produce a branch in a well-founded tree. Thus the two conditions are complementary and give the
    required inclusions. For indices, first use the delayed tree presentations, which form a jointly decidable
    family on all indices. Apply the two comparison constructions to this family, then specialize each joint
    decision program by inserting the paired input index into its fixed syntax. The specialization construction
    of §{sec:edst-pair-tree-indices} is itself lambda-computable and preserves the projections.
    No decision of disjointness and no enlargement of $\varepsilon$ occurs.
    \end{proof}
-/
/-- Disjoint branch-existence sets are separated by the map comparison.
This proves the inclusions and complementarity; it makes no unproved claim
that the separator already has a uniform effective index. -/
theorem tree_comparison_separates {X : Type*} (T S : X → RootedPrefixTree)
    (hd : Disjoint {x | ∃ p, p ∈ treeBody (T x).tree} {x | ∃ p, p ∈ treeBody (S x).tree}) :
    {x | ∃ p, p ∈ treeBody (T x).tree} ⊆ {x | TreeComparisonLe (S x) (T x)} ∧
    {x | TreeComparisonLe (S x) (T x)} ⊆ {x | ∃ p, p ∈ treeBody (S x).tree}ᶜ ∧
    {x | TreeComparisonLe (S x) (T x)} = {x | TreeComparisonLt (T x) (S x)}ᶜ := by
  have hw x : WellFounded (strictTreeExtension (T x).tree) ∨
      WellFounded (strictTreeExtension (S x).tree) := by
    by_cases hT : WellFounded (strictTreeExtension (T x).tree)
    · exact Or.inl hT
    · right
      apply (prefixTreeWellFounded_iff _ (S x).downward).mp
      intro hS
      exact Set.disjoint_left.mp hd (branch_of_not_wellFounded (T x) hT) hS
  refine ⟨fun x hx => treeComparisonLe_of_branch _ _ hx, ?_, ?_⟩
  · intro x hx hS
    exact (treeComparison_complement _ _ (hw x)).mp hx
      (treeComparisonLt_of_branch _ _ hS)
  · ext x
    exact treeComparison_complement _ _ (hw x)

end PolishSpaceBook
