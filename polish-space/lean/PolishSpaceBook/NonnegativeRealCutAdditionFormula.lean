module

public import PolishSpaceBook.NonnegativeRealCutInternalAddition

@[expose] public section

/-! # A bounded formula for equality with the sum of two complete real codes -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

/-- Parameters omega, multiplication, addition, zero, natural pairs, C,D,E. -/
def sumCutValuePredicate : BoundedSetPredicate 8 :=
  setComprehension 4 7 (sumCutPredicate.rename ![0, 1, 2, 3, 5, 6, 8])

lemma eval_sumCutValuePredicate (C D E : ZFSet.{u}) :
    sumCutValuePredicate.eval ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun a b => a * b), naturalBinaryGraph (fun a b => a + b), ∅,
      prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, C, D, E] ↔ E = sumCutCode C D := by
  let ps : Fin 8 → ZFSet.{u} := ![Ordinal.omega0.toZFSet,
    naturalBinaryGraph (fun a b => a * b), naturalBinaryGraph (fun a b => a + b), ∅,
    prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, C, D, E]
  apply eval_setComprehension_iff_eq (4 : Fin 8) 7 _ ps
  · intro z hz
    unfold sumCutCode naturalPairSet at hz
    exact (ZFSet.mem_sep.mp hz).1
  · intro z _
    rw [eval_rename]
    have he : Fin.snoc ps z ∘ ![(0 : Fin 9), 1, 2, 3, 5, 6, 8] =
        ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun a b => a * b),
          naturalBinaryGraph (fun a b => a + b), ∅, C, D, z] := by
      funext i; fin_cases i <;> rfl
    rw [he, eval_sumCutPredicate]
    exact (mem_naturalPairSet _ _).symm

/-- The arithmetic parameters and the three input codes are the only model parameters. -/
theorem realize_sumCutValuePredicate {M : ZFSet.{u}} (hM : M.IsTransitive)
    (ps : Fin 8 → M) (C D E : ZFSet.{u})
    (hp : Subtype.val ∘ ps = ![Ordinal.omega0.toZFSet,
      naturalBinaryGraph (fun a b => a * b), naturalBinaryGraph (fun a b => a + b), ∅,
      prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, C, D, E]) :
    sumCutValuePredicate.compile.Realize Empty.elim ps ↔ E = sumCutCode C D := by
  rw [sumCutValuePredicate.realize_compile hM, hp, eval_sumCutValuePredicate]

end PolishSpaceBook.CantorTreeMeasure
