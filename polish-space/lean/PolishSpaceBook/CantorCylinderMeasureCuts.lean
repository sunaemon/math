module

public import PolishSpaceBook.BorelInternalCylinderSlices
public import PolishSpaceBook.BorelCanonicalBasis

@[expose] public section

/-! # One internal formula for all rational cylinder-intersection measure cuts -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory
open NamedLambda
universe u

/-- The common Borel-measure parameters and the standard finite-word decoder. -/
def cylinderMeasureBaseValues (M : ZFSet.{u}) (c : Code) : Fin 9 → ZFSet.{u} :=
  Fin.snoc (borelMeasureCutBaseValues M c.val c.property.2.2.2.2.2) listDecodeGraph

lemma cylinderMeasureBaseValues_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {i : ℕ} (φ : ForcingFormulas.Formula (i + 1)), M ⊨ separationSentence φ)
    (c : Code) (hc : c.val.labelGraph ∈ M) (i : Fin 9) : cylinderMeasureBaseValues M c i ∈ M := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact listDecodeGraph_mem hM hinf hpair hunion hpower hsep
  · simpa only [cylinderMeasureBaseValues, Fin.snoc_castSucc] using
      borelMeasureCutBaseValues_mem hM hinf hpair hunion hpower hsep c.val
      c.property.2.2.2.2.2 hc j

def cylinderMeasureQueryValues (M : ZFSet.{u}) (c : Code) (j a b : ℕ) : Fin 12 → ZFSet.{u} :=
  Fin.snoc (Fin.snoc (Fin.snoc (cylinderMeasureBaseValues M c) (natOrdinal j)) (natOrdinal a)) (natOrdinal b)

/-- The slice is an internal existential witness, uniformly defined by the decoded word. -/
def cylinderMeasureLowerCutFormula : ForcingFormulas.Formula 12 :=
  (reindex cylinderSlicePredicate.compile ![3,8,5,9,12] ⊓
    reindex borelMeasureLowerCutFormula ![0,1,2,3,4,12,6,7,10,11]).ex

theorem realize_cylinderMeasureLowerCutFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : Code) (hc : c.val.labelGraph ∈ M)
    (j a b : ℕ) (hb : 0 < b) (ps : Fin 12 → M)
    (hps : Subtype.val ∘ ps = cylinderMeasureQueryValues M c j a b) :
    cylinderMeasureLowerCutFormula.Realize Empty.elim ps ↔
      (a : ℝ) / b < fairCoinProduct.real (Code.inf c (Code.leaf j)).cantor := by
  let cc := Code.inf c (Code.leaf j)
  have hcc : cc.val.labelGraph ∈ M := Code.inf_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _ _ hc
    (basic_labelGraph_mem hM hinf hpair hunion hpower hsep hrep j)
  let A := internalInterpretation M c.val c.property.2.2.2.2.2 NatListCode.decode []
  let row (S : M) : Fin 13 → M := Fin.snoc ps S
  let cut (S : M) : Fin 10 → M := row S ∘ ![0,1,2,3,4,12,6,7,10,11]
  have hv (i : Fin 12) : (ps i).val = cylinderMeasureQueryValues M c j a b i := congrFun hps i
  have hslice (S : M) :
      (reindex cylinderSlicePredicate.compile ![3,8,5,9,12]).Realize Empty.elim (row S) ↔
        S.val = cylinderSlice A (NatListCode.decode j) := by
    rw [realize_reindex, cylinderSlicePredicate.realize_compile hM]
    have he : Subtype.val ∘ (row S ∘ ![(3 : Fin 13),8,5,9,12]) =
        ![finiteSequences, listDecodeGraph, A, natOrdinal j, S.val] := by
      funext i
      fin_cases i
      · exact hv 3
      · exact hv 8
      · exact hv 5
      · exact hv 9
      · rfl
    rw [he, eval_cylinderSlicePredicate]
  have hcut (S : M) (hS : S.val = cylinderSlice A (NatListCode.decode j)) :
      (reindex borelMeasureLowerCutFormula ![0,1,2,3,4,12,6,7,10,11]).Realize Empty.elim (row S) ↔
        (a : ℝ) / b < fairCoinProduct.real cc.cantor := by
    rw [realize_reindex]
    apply realize_borelMeasureLowerCutFormula hM hinf hpair hunion hpower hsep hrep hchoice
      cc.val cc.property hcc a b hb (cut S)
    funext i
    fin_cases i
    · exact hv 0
    · exact hv 1
    · exact hv 2
    · exact hv 3
    · exact hv 4
    · exact hS.trans (internalInterpretation_inf_leaf M c j).symm
    · exact hv 6
    · exact hv 7
    · exact hv 10
    · exact hv 11
  simp only [cylinderMeasureLowerCutFormula, BoundedFormula.realize_ex, BoundedFormula.realize_inf]
  change (∃ S : M, _ ∧ _) ↔ _
  constructor
  · rintro ⟨S, hs, hq⟩
    exact (hcut S ((hslice S).mp hs)).mp hq
  · intro hq
    have hA : A ∈ M := internalInterpretation_mem hM hinf hpair hunion hpower hsep c.val
      c.property.2.2.2.2.2 NatListCode.decode hc (canonicalBasisWordGraph_mem hM hinf hpair hunion hpower hsep) []
    let S : M := ⟨_, cylinderSlice_mem hM hinf hpair hunion hpower hsep hA (NatListCode.decode j)⟩
    exact ⟨S, (hslice S).mpr rfl, (hcut S rfl).mpr hq⟩

end PolishSpaceBook.CantorTreeMeasure
