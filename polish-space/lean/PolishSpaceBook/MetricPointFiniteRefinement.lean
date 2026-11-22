module

public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

/-! # Point-finite refinements on the union of an open family

The union need not be closed or the entire ambient metric space. Refinement is
performed in that open subspace, so no properness assumption is introduced.
-/
namespace PolishSpaceBook
open Set Topology
universe u v

/-- An open family has an open precise refinement with the same union and
finitely many members through each point of that union. -/
theorem metric_pointFinite_refinement {Y : Type u} [MetricSpace Y] {I : Type v}
    (w : I → Set Y) (hw : ∀ i, IsOpen (w i)) :
    ∃ v : I → Set Y, (∀ i, IsOpen (v i)) ∧ (∀ i, v i ⊆ w i) ∧
      (⋃ i, v i) = ⋃ i, w i ∧ ∀ y ∈ ⋃ i, v i, {i | y ∈ v i}.Finite := by
  let O := ⋃ i, w i
  have hO : IsOpen O := isOpen_iUnion hw
  let w' : I → Set O := fun i => Subtype.val ⁻¹' w i
  have hopen : ∀ i, IsOpen (w' i) := fun i => (hw i).preimage continuous_subtype_val
  have hcover : (⋃ i, w' i) = univ := by
    ext y
    simpa only [w', mem_iUnion, mem_preimage, mem_univ, iff_true] using (show y.val ∈ ⋃ i, w i from y.property)
  obtain ⟨v', hvopen, hvcover, hvfinite, hvsub⟩ := precise_refinement w' hopen hcover
  let v : I → Set Y := fun i => Subtype.val '' v' i
  have hvsub' (i : I) : v i ⊆ w i := by
    rintro y ⟨z, hz, rfl⟩
    exact hvsub i hz
  have hveq : (⋃ i, v i) = O := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨i, hvsub' i hi⟩
    · intro y hy
      have h : (⟨y,hy⟩ : O) ∈ ⋃ i, v' i := hvcover.symm ▸ mem_univ _
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact mem_iUnion.mpr ⟨i, ⟨⟨y,hy⟩, hi, rfl⟩⟩
  refine ⟨v, fun i => hO.isOpenEmbedding_subtypeVal.isOpenMap _ (hvopen i), hvsub', hveq, ?_⟩
  intro y hy
  have hyO : y ∈ O := hveq ▸ hy
  apply (hvfinite.point_finite (⟨y,hyO⟩ : O)).subset
  rintro i ⟨z, hz, he⟩
  have heq : z = (⟨y,hyO⟩ : O) := Subtype.ext he
  exact heq ▸ hz

end PolishSpaceBook
