module

public import PolishSpaceBook.LambdaNumericalQueries
public import PolishSpaceBook.LambdaOracleRecursion

@[expose] public section

/-! # Iterating a total numerical update with the input name retained -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- Adapt a stage program on paired numerical arguments to the curried recursor. -/
def nameRecursionStep (H : AlphaTerm) : AlphaTerm :=
  lam 61 (lam 62 (lam 63 (app (app H (var 61))
    (app (app numericalPairTerm (var 62)) (var 63)))))

theorem nameRecursionStep_closed {H : AlphaTerm} (hH : H.Closed) :
    (nameRecursionStep H).Closed := by
  unfold nameRecursionStep Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [hH,numericalPairTerm_closed]
  decide

theorem nameRecursionStep_start {H : AlphaTerm} (hH : H.Closed) (k r : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app (nameRecursionStep H) (var 0)) (numeral k)) (numeral r))
      (app (app H (var 0)) (numeral (Nat.pair k r))) := by
  have h₁ : Beta (app (nameRecursionStep H) (var 0))
      (lam 62 (lam 63 (app (app H (var 0))
        (app (app numericalPairTerm (var 62)) (var 63))))) := by
    convert Beta.contract 61 (lam 62 (lam 63 (app (app H (var 61))
      (app (app numericalPairTerm (var 62)) (var 63))))) (var 0) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 62 61 (by decide) (by simp [fv_var]),
      subst_lam_fresh _ _ 63 61 (by decide) (by simp [fv_var])]
    simp [subst_app,subst_var,subst_closed _ _ _ hH,
      subst_closed _ _ _ numericalPairTerm_closed]
  have h₂ : Beta
      (app (lam 62 (lam 63 (app (app H (var 0))
        (app (app numericalPairTerm (var 62)) (var 63))))) (numeral k))
      (lam 63 (app (app H (var 0))
        (app (app numericalPairTerm (numeral k)) (var 63)))) := by
    convert Beta.contract 62 (lam 63 (app (app H (var 0))
      (app (app numericalPairTerm (var 62)) (var 63)))) (numeral k) using 1
    rw [subst_lam_fresh _ _ 63 62 (by decide) (by rw [numeral_closed]; simp)]
    simp [subst_app,subst_var,subst_closed _ _ _ hH,
      subst_closed _ _ _ numericalPairTerm_closed]
  have h₃ : Beta (app (lam 63 (app (app H (var 0))
      (app (app numericalPairTerm (numeral k)) (var 63)))) (numeral r))
      (app (app H (var 0)) (app (app numericalPairTerm (numeral k)) (numeral r))) := by
    convert Beta.contract 63 (app (app H (var 0))
      (app (app numericalPairTerm (numeral k)) (var 63))) (numeral r) using 1
    simp [subst_app,subst_var,subst_closed _ _ _ hH,
      subst_closed _ _ _ numericalPairTerm_closed,subst_closed _ _ _ (numeral_closed k)]
  exact (Relation.ReflTransGen.tail (.tail (.single (.app_left _ (.app_left _ h₁))) (.app_left _ h₂)) h₃).trans
    (beta_steps_app_right _ (numericalPairTerm_apply k r))

def nameRecursionProgram (a : ℕ) (H : AlphaTerm) : AlphaTerm :=
  parameterRecursor (numericalConstant a) (nameRecursionStep H)

theorem UniformNumericalComputes.recursion {H : AlphaTerm} {h : (ℕ → ℕ) → ℕ → ℕ}
    (hH : UniformNumericalComputes H h) (a : ℕ) :
    UniformNumericalComputes (nameRecursionProgram a H)
      (fun p => primitiveRec a (fun k r => h p (Nat.pair k r))) := by
  refine ⟨parameterRecursor_closed (numericalConstant_computes a).1
    (nameRecursionStep_closed hH.1),fun p n => ?_⟩
  apply parameterRecursor_oracle_apply (numericalConstant_computes a).1
    (nameRecursionStep_closed hH.1) a (fun k r => h p (Nat.pair k r))
  · apply beta_steps_oracle
    exact .single (by simpa [numericalConstant,subst_closed _ _ _ (numeral_closed a)] using
      (Beta.contract 40 (numeral a) (var 0)))
  · intro k r
    exact (beta_steps_oracle (nameRecursionStep_start hH.1 k r)).trans (hH.2 p (Nat.pair k r))

end PolishSpaceBook.NamedLambda.AlphaTerm
