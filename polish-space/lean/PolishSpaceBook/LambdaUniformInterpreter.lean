module

public import PolishSpaceBook.LambdaOracleOutputSearch

@[expose] public section

/-! # A paired-input universal lambda program and index specialization -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm
set_option maxRecDepth 4096

def interpreterBody (O Z : AlphaTerm) : AlphaTerm :=
  app (app (app oracleOutputSearchTerm O) (app (numericalProjectionTerm true) Z))
    (app (numericalProjectionTerm false) Z)

theorem interpreterBody_fv (O Z : AlphaTerm) :
    (interpreterBody O Z).fv = O.fv ∪ Z.fv := by
  ext x
  simp only [interpreterBody, fv_app,
    (show oracleOutputSearchTerm.fv = ∅ from oracleOutputSearchTerm_closed),
    (show (numericalProjectionTerm true).fv = ∅ from numericalProjectionTerm_closed true),
    (show (numericalProjectionTerm false).fv = ∅ from numericalProjectionTerm_closed false),
    Finset.mem_union, Finset.notMem_empty]
  tauto

theorem interpreterBody_subst (O Z W : AlphaTerm) (x : ℕ) :
    (interpreterBody O Z).subst x W = interpreterBody (O.subst x W) (Z.subst x W) := by
  simp only [interpreterBody, subst_app, subst_closed _ _ _ oracleOutputSearchTerm_closed,
    subst_closed _ _ _ (numericalProjectionTerm_closed true),
    subst_closed _ _ _ (numericalProjectionTerm_closed false)]

def uniformInterpreterProgram : AlphaTerm := lam 40 (lam 41 (interpreterBody (var 40) (var 41)))

@[simp] theorem uniformInterpreterProgram_closed : uniformInterpreterProgram.Closed := by
  unfold uniformInterpreterProgram Closed
  simp only [fv_lam, interpreterBody_fv, fv_var]
  decide

theorem uniformInterpreterProgram_start (p : ℕ → ℕ) (z : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app uniformInterpreterProgram (var 0)) (numeral z))
      (app (app (app oracleOutputSearchTerm (var 0)) (numeral (Nat.unpair z).1))
        (numeral (Nat.unpair z).2)) := by
  have h₁ : Beta (app uniformInterpreterProgram (var 0))
      (lam 41 (interpreterBody (var 0) (var 41))) := by
    have he : (lam 41 (interpreterBody (var 40) (var 41))).subst 40 (var 0) =
        lam 41 (interpreterBody (var 0) (var 41)) := by
      rw [subst_lam_fresh _ _ 41 40 (by decide) (by change 41 ∉ ({0} : Finset ℕ); decide),
        interpreterBody_subst]
      simp only [subst_var, ite_true, show (41 = 40) = False by decide, ite_false]
    unfold uniformInterpreterProgram
    rw [← he]
    exact Beta.contract 40 (lam 41 (interpreterBody (var 40) (var 41))) (var 0)
  have h₂ : Beta (app (lam 41 (interpreterBody (var 0) (var 41))) (numeral z))
      (interpreterBody (var 0) (numeral z)) := by
    convert Beta.contract 41 (interpreterBody (var 0) (var 41)) (numeral z) using 1
    simp [interpreterBody_subst, subst_var]
  apply (beta_steps_oracle (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂)).trans
  exact beta_steps_oracle (beta_steps_app
    (beta_steps_app_right (app oracleOutputSearchTerm (var 0)) (numericalProjectionTerm_apply true z))
    (numericalProjectionTerm_apply false z))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Uniform lambda interpretation and specialization
-/

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The outer abstractions bind every free variable. For the paired input, two beta contractions and the two projection computations reach $\LambdaQueryOutputSearch\,o\,\ChurchNumeral{e}\,\ChurchNumeral{n}$. For the specialized term, one beta contraction reaches this same term. Each reduction can be prepended to an evaluator output. Conversely, if either starting term has a numeral output, confluence gives a common reduct of that numeral and the evaluator term. A numeral admits no further beta/query step, so the evaluator reduces to that very numeral. The exact universal-evaluation theorem now gives both equivalences, including the case of no numeral output.
    \end{proof}
-/

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    The evaluator just constructed takes its index and numerical input separately. The single-input convention of
    §{sec:type-two-lambda-realizers} is recovered by the closed term
    $$\LambdaUniformInterpreter:=\lambdaab{o}{\lambdaab{z}{
     \LambdaQueryOutputSearch\,o\,(\LambdaNumericProjection{1}\,z)\,
     (\LambdaNumericProjection{2}\,z)}}.$$
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The universal interpreter in §{sec:lambda-program-specialization} evaluates a supplied program index on a supplied
    numerical input with the same name argument. It preserves both numerical outputs and undefinedness, and fixing
    the program index is a primitive-recursive transformation of syntax codes. We use it below to evaluate function names.
-/
theorem uniformInterpreterProgram_runs_iff (p : ℕ → ℕ) (e n m : ℕ) :
    OracleRuns p uniformInterpreterProgram (Nat.pair e n) m ↔
      OracleRuns p (Term.closedProgram e) n m := by
  have hs := uniformInterpreterProgram_start p (Nat.pair e n)
  simp only [Nat.unpair_pair] at hs
  constructor
  · intro h
    exact (oracleOutputSearchTerm_runs_iff p e n m).mp (oracle_numeral_after_reduction hs h)
  · intro h
    exact hs.trans ((oracleOutputSearchTerm_runs_iff p e n m).mpr h)

theorem uniformInterpreterProgram_domain_iff (p : ℕ → ℕ) (e n : ℕ) :
    (∃ m, OracleRuns p uniformInterpreterProgram (Nat.pair e n) m) ↔
      ∃ m, OracleRuns p (Term.closedProgram e) n m :=
  exists_congr (fun m => uniformInterpreterProgram_runs_iff p e n m)

/-- Fix the first numerical argument of a curried program; the input name stays free
until the outer abstraction receives it. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a closed term $P$ with its input name and first numerical argument supplied in that order, define
    $$\LambdaIndexSpecialization{P}{e}:=
     \lambdaab{x_{40}}{P\,x_{40}\,\ChurchNumeral{e}}.$$
    Since $P$ is closed, this fixed binder captures no free occurrence in $P$. The argument $e$ is fixed in the syntax,
    while the input name and remaining numerical input are still supplied at run time.
-/
def specializeProgram (P : AlphaTerm) (e : ℕ) : AlphaTerm :=
  lam 40 (app (app P (var 40)) (numeral e))

theorem specializeProgram_closed {P : AlphaTerm} (hP : P.Closed) (e : ℕ) :
    (specializeProgram P e).Closed := by
  unfold specializeProgram Closed
  rw [fv_lam, fv_app, fv_app, hP, numeral_closed, fv_var]
  simp

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a closed term $P$ with its input name and first numerical argument supplied in that order, define
    $$\LambdaIndexSpecialization{P}{e}:=
     \lambdaab{x_{40}}{P\,x_{40}\,\ChurchNumeral{e}}.$$
    Since $P$ is closed, this fixed binder captures no free occurrence in $P$. The argument $e$ is fixed in the syntax,
    while the input name and remaining numerical input are still supplied at run time.
-/
theorem specializeProgram_start {P : AlphaTerm} (hP : P.Closed) (p : ℕ → ℕ) (e n : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (specializeProgram P e) (var 0)) (numeral n))
      (app (app (app P (var 0)) (numeral e)) (numeral n)) := by
  have hb : Beta (app (specializeProgram P e) (var 0))
      (app (app P (var 0)) (numeral e)) := by
    simpa only [specializeProgram, subst_app, subst_var, ite_true,
      subst_closed _ _ _ hP, subst_closed _ _ _ (numeral_closed e)] using
      Beta.contract 40 (app (app P (var 40)) (numeral e)) (var 0)
  exact .single (.beta (.app_left _ hb))

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Uniform lambda interpretation and specialization
-/
theorem specializedEvaluator_runs_iff (p : ℕ → ℕ) (e n m : ℕ) :
    OracleRuns p (specializeProgram oracleOutputSearchTerm e) n m ↔
      OracleRuns p (Term.closedProgram e) n m := by
  have hs := specializeProgram_start oracleOutputSearchTerm_closed p e n
  constructor
  · intro h
    exact (oracleOutputSearchTerm_runs_iff p e n m).mp (oracle_numeral_after_reduction hs h)
  · intro h
    exact hs.trans ((oracleOutputSearchTerm_runs_iff p e n m).mpr h)

theorem specializedEvaluator_domain_iff (p : ℕ → ℕ) (e n : ℕ) :
    (∃ m, OracleRuns p (specializeProgram oracleOutputSearchTerm e) n m) ↔
      ∃ m, OracleRuns p (Term.closedProgram e) n m :=
  exists_congr (fun m => specializedEvaluator_runs_iff p e n m)

end PolishSpaceBook.NamedLambda.AlphaTerm
