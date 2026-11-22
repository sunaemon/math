module

public import PolishSpaceBook.CantorInternalMeasureCutCode
public import PolishSpaceBook.BorelInternalCylinderCodes
public import PolishSpaceBook.SetTheoryInternalListCodes

@[expose] public section

/-! # Uniform internal intersections with numbered cylinders

An old point is a function graph. Requiring a finite word graph to be a subset
of it recognizes exactly membership in the corresponding Baire cylinder.
This supplies a bounded uniform definition of intersections with a fixed
internal Borel interpretation, without assuming a whole family of new codes.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
open NamedLambda
universe u

def cylinderSlice (A : ZFSet.{u}) (s : List ℕ) : ZFSet.{u} :=
  A.sep (fun g => wordGraph s ⊆ g)

lemma mem_cylinderSlice (A : ZFSet.{u}) (s : List ℕ) (g : ZFSet.{u}) :
    g ∈ cylinderSlice A s ↔ g ∈ A ∧ wordGraph s ⊆ g := ZFSet.mem_sep

/-- Parameters words, decoder, fixed set, numerical cylinder index, candidate slice. -/
def cylinderSlicePredicate : BoundedSetPredicate 5 :=
  .ex 0 (.conj (.pairMember 1 3 5)
    (.conj (.subset 4 2) (.all 2 (.iff (.member 6 4) (.subset 5 6)))))

lemma eval_cylinderSlicePredicate (A : ZFSet.{u}) (j : ℕ) (S : ZFSet.{u}) :
    cylinderSlicePredicate.eval ![finiteSequences, listDecodeGraph, A, natOrdinal j, S] ↔
      S = cylinderSlice A (NatListCode.decode j) := by
  change (∃ w ∈ finiteSequences, pair (natOrdinal j) w ∈ listDecodeGraph ∧
    S ⊆ A ∧ ∀ g ∈ A, g ∈ S ↔ w ⊆ g) ↔ _
  rw [exists_mem_finiteSequences]
  simp only [pair_mem_listDecodeGraph, exists_eq_left]
  constructor
  · rintro ⟨hS, h⟩
    ext g
    exact ⟨fun hg => mem_cylinderSlice _ _ _ |>.mpr ⟨hS hg, (h g (hS hg)).mp hg⟩,
      fun hg => (h g (mem_cylinderSlice _ _ _ |>.mp hg).1).mpr (mem_cylinderSlice _ _ _ |>.mp hg).2⟩
  · rintro rfl
    exact ⟨fun _ hg => (mem_cylinderSlice _ _ _ |>.mp hg).1,
      fun g hg => mem_cylinderSlice _ _ _ |>.trans (and_iff_right hg)⟩

lemma cylinderSlice_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    {A : ZFSet.{u}} (hA : A ∈ M) (s : List ℕ) : cylinderSlice A s ∈ M := by
  let w : M := ⟨wordGraph s, hM.mem_trans (mem_finiteSequences.mpr ⟨s, rfl⟩)
    (finiteSequences_mem hM hinf hpair hunion hpower hsep)⟩
  exact (BoundedSetPredicate.subset (0 : Fin 2) 1).separation_mem hM (hsep _) ![w] hA

/-- The bounded slice is the original Borel code intersected with leaf j. -/
theorem internalInterpretation_inf_leaf (M : ZFSet.{u}) (c : Code) (j : ℕ) :
    internalInterpretation M (Code.inf c (Code.leaf j)).val (Code.inf c (Code.leaf j)).property.2.2.2.2.2
      NatListCode.decode [] =
    cylinderSlice (internalInterpretation M c.val c.property.2.2.2.2.2 NatListCode.decode [])
      (NatListCode.decode j) := by
  ext g
  constructor
  · intro hg
    have hgB := (ZFSet.mem_sep.mp hg).1
    obtain ⟨x, hx, _⟩ := mem_internalBaire.mp hgB
    rw [← hx, pointGraph_mem_internalInterpretation] at hg
    change pointGraph x ∈ M ∧ x ∈ (Code.inf c (Code.leaf j)).value cylinderBasis at hg
    rw [Code.value_inf, Code.value_leaf] at hg
    rw [← hx, mem_cylinderSlice, pointGraph_mem_internalInterpretation, wordGraph_subset_pointGraph]
    exact ⟨⟨hg.1, hg.2.1⟩, hg.2.2⟩
  · intro hg
    obtain ⟨hgA, hword⟩ := (mem_cylinderSlice _ _ _).mp hg
    obtain ⟨x, hx, _⟩ := mem_internalBaire.mp (ZFSet.mem_sep.mp hgA).1
    rw [← hx, pointGraph_mem_internalInterpretation] at hgA
    rw [← hx, wordGraph_subset_pointGraph] at hword
    rw [← hx, pointGraph_mem_internalInterpretation]
    change pointGraph x ∈ M ∧ x ∈ (Code.inf c (Code.leaf j)).value cylinderBasis
    rw [Code.value_inf, Code.value_leaf]
    exact ⟨hgA.1, hgA.2, hword⟩

end PolishSpaceBook.BorelExpression
