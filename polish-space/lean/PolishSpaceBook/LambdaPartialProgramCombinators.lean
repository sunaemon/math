module

public import PolishSpaceBook.LambdaInputParameters
public import PolishSpaceBook.LambdaUniformInterpreter
public import PolishSpaceBook.LambdaOutputSearch
public import PolishSpaceBook.LambdaRelativeComposition

@[expose] public section

/-! # Pointwise composition without totality assumptions on unused branches -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

theorem uncurryNumerical_closed {B : AlphaTerm} (hB : B.Closed) : (uncurryNumerical B).Closed := by
  unfold uncurryNumerical numericalCombine Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [hB,numericalProjectionTerm_closed,numericalProjectionTerm_closed]
  decide

theorem uncurryNumerical_start {B : AlphaTerm} (hB : B.Closed) (n : ℕ) :
    Relation.ReflTransGen Beta (app (uncurryNumerical B) (numeral n))
      (app (app B (numeral n.unpair.1)) (numeral n.unpair.2)) := by
  have hb : Beta (app (uncurryNumerical B) (numeral n))
      (app (app B (app (numericalProjectionTerm true) (numeral n)))
        (app (numericalProjectionTerm false) (numeral n))) := by
    simpa only [uncurryNumerical,numericalCombine,subst_app,subst_var,ite_true,
      subst_closed _ _ _ hB,subst_closed _ _ _ (numericalProjectionTerm_closed true),
      subst_closed _ _ _ (numericalProjectionTerm_closed false)] using
      Beta.contract 40 (app (app B (app (numericalProjectionTerm true) (var 40)))
        (app (numericalProjectionTerm false) (var 40))) (numeral n)
  exact (Relation.ReflTransGen.single hb).trans (beta_steps_app
    (beta_steps_app_right B (numericalProjectionTerm_apply true n)) (numericalProjectionTerm_apply false n))

theorem dataInputAccessor_runs_of {A : AlphaTerm} (hA : A.Closed) {p : ℕ → ℕ} {z k m : ℕ}
    (h : OracleRuns p A (Nat.pair z k) m) :
    Relation.ReflTransGen (OracleStep p)
      (app (dataInputAccessor A (var 0) (numeral z)) (numeral k)) (numeral m) := by
  have hb : Beta (app (dataInputAccessor A (var 0) (numeral z)) (numeral k))
      (app (app A (var 0)) (app (app numericalPairTerm (numeral z)) (numeral k))) := by
    convert Beta.contract 43 _ (numeral k) using 1 <;> try rfl
    simp [subst_app,subst_var,subst_closed _ _ _ hA,
      subst_closed _ _ _ numericalPairTerm_closed,subst_closed _ _ _ (numeral_closed z)]
  exact (Relation.ReflTransGen.single (.beta hb)).trans
    ((oracle_steps_app_right _ (beta_steps_oracle (numericalPairTerm_apply z k))).trans h)

theorem dataInputProgram_runs_of {P A : AlphaTerm} (hP : P.Closed) (hA : A.Closed)
    {p q : ℕ → ℕ} {z m : ℕ} (h : OracleRuns q P z m)
    (hq : ∀ k, OracleRuns p A (Nat.pair z k) (q k)) :
    OracleRuns p (dataInputProgram P A) z m := by
  apply (beta_steps_oracle (dataInputProgram_start hP hA z)).trans
  have hs := oracle_steps_subst_input h (fun k => dataInputAccessor_runs_of hA (hq k))
  simpa only [subst_app,subst_var,ite_true,subst_closed _ _ _ hP,
    subst_closed _ _ _ (numeral_closed z),subst_closed _ _ _ (numeral_closed m)] using hs

/-- The numerical test is pure. Only the selected output program is run. -/
def ifZeroProgram (C X Y : AlphaTerm) : AlphaTerm := lam 1 (lam 2
  (app (app (app zeroTestTerm (app C (var 2))) (app (app X (var 1)) (var 2)))
    (app (app Y (var 1)) (var 2))))

theorem ifZeroProgram_closed {C X Y : AlphaTerm} (hC : C.Closed) (hX : X.Closed) (hY : Y.Closed) :
    (ifZeroProgram C X Y).Closed := by
  unfold ifZeroProgram Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [zeroTestTerm_closed,hC,hX,hY]
  decide

theorem ifZeroProgram_start {C X Y : AlphaTerm} (hC : C.Closed) (hX : X.Closed) (hY : Y.Closed)
    (n : ℕ) : Relation.ReflTransGen Beta (app (app (ifZeroProgram C X Y) (var 0)) (numeral n))
      (app (app (app zeroTestTerm (app C (numeral n))) (app (app X (var 0)) (numeral n)))
        (app (app Y (var 0)) (numeral n))) := by
  have h₁ : Beta (app (ifZeroProgram C X Y) (var 0)) (lam 2
      (app (app (app zeroTestTerm (app C (var 2))) (app (app X (var 0)) (var 2)))
        (app (app Y (var 0)) (var 2)))) := by
    unfold ifZeroProgram
    convert Beta.contract 1 _ (var 0) using 1
    rw [subst_lam_fresh _ _ 2 1 (by decide) (by simp [fv_var])]
    simp [subst_app,subst_var,subst_closed _ _ _ hC,subst_closed _ _ _ hX,
      subst_closed _ _ _ hY,subst_closed _ _ _ zeroTestTerm_closed]
  have h₂ : Beta (app (lam 2
      (app (app (app zeroTestTerm (app C (var 2))) (app (app X (var 0)) (var 2)))
        (app (app Y (var 0)) (var 2)))) (numeral n))
      (app (app (app zeroTestTerm (app C (numeral n))) (app (app X (var 0)) (numeral n)))
        (app (app Y (var 0)) (numeral n))) := by
    convert Beta.contract 2 _ (numeral n) using 1
    simp [subst_app,subst_var,subst_closed _ _ _ hC,subst_closed _ _ _ hX,
      subst_closed _ _ _ hY,subst_closed _ _ _ zeroTestTerm_closed]
  exact .tail (.single (.app_left _ h₁)) h₂

theorem ifZeroProgram_runs_zero {C X Y : AlphaTerm} (hC : C.Closed) (hX : X.Closed) (hY : Y.Closed)
    {p : ℕ → ℕ} {n m : ℕ} (hc : Relation.ReflTransGen Beta (app C (numeral n)) (numeral 0))
    (hx : OracleRuns p X n m) : OracleRuns p (ifZeroProgram C X Y) n m := by
  apply (beta_steps_oracle (ifZeroProgram_start hC hX hY n)).trans
  apply (beta_steps_oracle (beta_steps_app_left (beta_steps_app_left
    (beta_steps_app_right zeroTestTerm hc) _) _)).trans
  apply (beta_steps_oracle (branch_zero _ _ ?_)).trans hx
  simp only [fv_app,fv_var]
  rw [hX,numeral_closed]
  decide

theorem ifZeroProgram_runs_one {C X Y : AlphaTerm} (hC : C.Closed) (hX : X.Closed) (hY : Y.Closed)
    {p : ℕ → ℕ} {n m : ℕ} (hc : Relation.ReflTransGen Beta (app C (numeral n)) (numeral 1))
    (hy : OracleRuns p Y n m) : OracleRuns p (ifZeroProgram C X Y) n m := by
  apply (beta_steps_oracle (ifZeroProgram_start hC hX hY n)).trans
  apply (beta_steps_oracle (beta_steps_app_left (beta_steps_app_left
    (beta_steps_app_right zeroTestTerm hc) _) _)).trans
  exact (beta_steps_oracle (branch_succ 0 _ _)).trans hy

end PolishSpaceBook.NamedLambda.AlphaTerm
