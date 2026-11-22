module

public import Mathlib.Order.WellFounded
public import PolishSpaceBook.TreeRankComparison
public import PolishSpaceBook.AnalyticConditionFusion
public import PolishSpaceBook.EffectiveDSTLightfaceHierarchies

@[expose] public section

/-!
# Branches and relational well-foundedness of prefix trees

A strict extension chain determines a branch by stabilization of every
finite coordinate. Conversely, the successive prefixes of a branch give
a descending chain in the relation used for the ordinal rank.
-/

namespace PolishSpaceBook
open Set

theorem branch_of_strictExtension_chain {T : Set (finseq ℕ)} (hT : IsSubtree T)
    (f : ℕ → T) (hf : ∀ n, strictTreeExtension T (f (n + 1)) (f n)) :
    ∃ p, p ∈ treeBody T := by
  have hlen (n : ℕ) : n ≤ (f n).val.length := by
    induction n with
    | zero => omega
    | succ n ih => have h := (hf n).2; omega
  let s : ∀ n, FusionPrefix n := fun n i =>
    (f n).val[i.val]'(i.isLt.trans_le (hlen n))
  have hs : ∀ n (i : Fin n), s (n + 1) i.castSucc = s n i := by
    intro n i
    exact ((hf n).1.getElem (i.isLt.trans_le (hlen n))).symm
  let p := coherentPrefixLimit s
  refine ⟨p, fun n => ?_⟩
  have hp : p ∈ fusionCylinder (s n) := coherentPrefixLimit_mem s hs n
  have heq : seqPrefix p n = (f n).val.take n := by
    apply List.ext_getElem
    · simp [seqPrefix_length, List.length_take, Nat.min_eq_left (hlen n)]
    · intro i hi hi'
      have hin : i < n := by simpa [seqPrefix_length] using hi
      simpa [seqPrefix, s] using hp ⟨i, hin⟩
  rw [heq]
  exact hT (f n).property (List.take_prefix n _)

theorem strictExtension_chain_of_branch {T : Set (finseq ℕ)} {p : ℕ → ℕ}
    (hp : p ∈ treeBody T) :
    ∃ f : ℕ → T, ∀ n, strictTreeExtension T (f (n + 1)) (f n) := by
  refine ⟨fun n => ⟨seqPrefix p n, hp n⟩, fun n => ?_⟩
  exact ⟨seqPrefix_prefixOf_of_le p (Nat.le_succ n), by simp [seqPrefix_length]⟩

/-- The branch-based convention in the effective chapter agrees with
mathlib's relational well-foundedness used by the rank construction. -/
theorem prefixTreeWellFounded_iff (T : Set (finseq ℕ)) (hT : IsSubtree T) :
    PrefixTreeWellFounded T ↔ WellFounded (strictTreeExtension T) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  · intro h
    exact ⟨fun ⟨f, hf⟩ => h (branch_of_strictExtension_chain hT f hf)⟩
  · intro h hp
    obtain ⟨p, hp⟩ := hp
    obtain ⟨f, hf⟩ := strictExtension_chain_of_branch hp
    exact h.false ⟨f, hf⟩

/-- A branch in the target supplies a map from any source tree. A positive
offset puts the image of the source root strictly below the target root. -/
theorem tree_map_along_branch (T S : Set (finseq ℕ)) (hrootT : [] ∈ T)
    {p : ℕ → ℕ} (hp : p ∈ treeBody S) (k : ℕ) :
    ∃ f : T → S, f ⟨[], hrootT⟩ = ⟨seqPrefix p k, hp k⟩ ∧
      ∀ u v, strictTreeExtension T u v → strictTreeExtension S (f u) (f v) := by
  refine ⟨fun t => ⟨seqPrefix p (k + t.val.length), hp _⟩, ?_, ?_⟩
  · apply Subtype.ext
    simp
  · intro u v h
    exact ⟨seqPrefix_prefixOf_of_le p (Nat.add_le_add_left h.2.le k),
      by simpa [seqPrefix_length] using Nat.add_lt_add_left h.2 k⟩

end PolishSpaceBook
