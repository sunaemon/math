module

public import PolishSpaceBook.TreeComparisonSeparation

@[expose] public section

/-! # Tree-map witnesses independently of their numerical coding -/
namespace PolishSpaceBook

/-- The conditions on a total word map that matter on the source tree. -/
def IsTreeMapWitness (T S : RootedPrefixTree) (f : finseq ℕ → finseq ℕ) : Prop :=
  (∀ u ∈ T.tree, f u ∈ S.tree) ∧
  ∀ u ∈ T.tree, ∀ v, prefixOf v u → v.length < u.length →
    prefixOf (f v) (f u) ∧ (f v).length < (f u).length

theorem treeMapWitness_of_map (T S : RootedPrefixTree) (f : T.tree → S.tree)
    (hf : ∀ u v, strictTreeExtension T.tree u v → strictTreeExtension S.tree (f u) (f v)) :
    ∃ g : finseq ℕ → finseq ℕ, IsTreeMapWitness T S g ∧
      ∀ t : T.tree, g t.val = (f t).val := by
  classical
  let g := fun t => if h : t ∈ T.tree then (f ⟨t, h⟩).val else []
  have hg (t : T.tree) : g t.val = (f t).val := by simp [g, t.property]
  refine ⟨g, ⟨?_, ?_⟩, hg⟩
  · intro u hu
    rw [hg ⟨u, hu⟩]
    exact (f ⟨u, hu⟩).property
  · intro u hu v hv hlen
    have hvT := T.downward hu hv
    rw [hg ⟨u, hu⟩, hg ⟨v, hvT⟩]
    exact hf ⟨u, hu⟩ ⟨v, hvT⟩ ⟨hv, hlen⟩

end PolishSpaceBook
