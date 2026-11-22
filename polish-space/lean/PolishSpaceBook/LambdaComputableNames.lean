module

public import PolishSpaceBook.LambdaNumericalQueries

@[expose] public section

/-! # Substituting an ordinary computable name

A closed numerical lambda term supplies every digit of a computable input name.
Substitution simulates each query; closedness then excludes query steps from
the resulting computation, leaving an ordinary beta reduction.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm

namespace NamedLambda.AlphaTerm

theorem oracle_steps_beta_of_closed {p : ℕ → ℕ} {M N : AlphaTerm}
    (h : Relation.ReflTransGen (OracleStep p) M N) (hM : M.Closed) :
    Relation.ReflTransGen Beta M N := by
  induction h with
  | refl => exact .refl
  | tail hs ht ih => exact ih.tail (ht.beta_of_closed (closed_of_beta_steps hM ih))

/-- Ordinary application replaces every query by a finite beta computation. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: proposition
  title: Substitution of a computable input name
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Use the preceding substitution argument with replacement $A$. Every input query is replaced by the given finite
    beta reduction computing that digit. Beta steps remain beta steps under substitution, and the same fresh-binder
    argument handles abstractions. Equivalently, apply the beta/query substitution result with any auxiliary input
    name: after substitution the initial term is closed, so no query step is possible. A query requires a free
    occurrence of $o$, whereas beta reduction preserves closedness. Induction through the finite reduction therefore
    leaves only ordinary beta steps. Closedness of $PA$ and uniqueness of numerical outputs give the last assertion.
-/
theorem OracleRuns.apply_numerical {p : ℕ → ℕ} {P A : AlphaTerm} {n m : ℕ}
    (h : OracleRuns p P n m) (hP : P.Closed) (hA : NumericalComputes A p) :
    Relation.ReflTransGen Beta (app (app P A) (numeral n)) (numeral m) := by
  have hs := oracle_steps_subst_input (p := fun _ => 0) h
    (fun k => beta_steps_oracle (hA.2 k))
  have ht : Relation.ReflTransGen (OracleStep (fun _ => 0))
      (app (app P A) (numeral n)) (numeral m) := by
    simpa only [subst_app, subst_var, ite_true, subst_closed P A 0 hP,
      subst_closed _ A 0 (numeral_closed n), subst_closed _ A 0 (numeral_closed m)] using hs
  apply oracle_steps_beta_of_closed ht
  unfold Closed
  rw [fv_app, fv_app, hP, hA.1, numeral_closed]; rfl

/-- A uniform numerical program answers every input query by its first argument. -/
def constantInputProgram (P : AlphaTerm) : AlphaTerm :=
  lam 41 (app P (lam 40 (var 41)))

theorem constantInputProgram_closed {P : AlphaTerm} (hP : P.Closed) :
    (constantInputProgram P).Closed := by
  unfold constantInputProgram Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [hP]; decide

theorem constantInputProgram_apply {P : AlphaTerm} (hP : P.Closed) (i k : ℕ) :
    Relation.ReflTransGen Beta (app (app (constantInputProgram P) (numeral i)) (numeral k))
      (app (app P (numericalConstant i)) (numeral k)) := by
  apply beta_steps_app_left (Relation.ReflTransGen.single ?_) _
  simpa only [constantInputProgram,subst_app,subst_closed P (numeral i) 41 hP,
    subst_lam_fresh (var 41) (numeral i) 40 41 (by decide) (by rw [numeral_closed]; simp),
    subst_var,ite_true,numericalConstant] using
    Beta.contract 41 (app P (lam 40 (var 41))) (numeral i)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    For a uniform family of constant input names $p_i(n)=i$, put
    $$K_i:=\lambdaab{u}{\ChurchNumeral{i}},\qquad H:=\lambdaab{a}{P\,(\lambdaab{u}{a})}.$$
    One beta step gives $\BetaConvertible{H\ChurchNumeral{i}}{PK_i}$. Thus whenever $P$ terminates on every constant name,
    $H\ChurchNumeral{i}\ChurchNumeral{k}$ returns the program's $k$th output on $p_i$ by ordinary beta reduction.
    The single closed term
    $$\lambdaab{z}{H\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)}$$
    computes these outputs jointly from $\NatPair{i}{k}$. No decision procedure for the program's domain of names is
    needed: validity of the constant names alone supplies termination.
-/
theorem constantInputProgram_computes {P : AlphaTerm} (hP : P.Closed) (f : ℕ → ℕ → ℕ)
    (hf : ∀ i k, OracleRuns (fun _ => i) P k (f i k)) :
    NumericalComputes (uncurryNumerical (constantInputProgram P))
      (fun z => f z.unpair.1 z.unpair.2) :=
  uncurryNumerical_computes (constantInputProgram_closed hP) f (fun i k =>
    (constantInputProgram_apply hP i k).trans
      ((hf i k).apply_numerical hP (numericalConstant_computes i)))

end NamedLambda.AlphaTerm

/-- A fixed realizer applied to an ordinary computable name is ordinary computable. -/
theorem TypeTwoComputes.numerical_output {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)}
    {P A : AlphaTerm} (hP : TypeTwoComputes P F) (p : D) (hA : NumericalComputes A p.val) :
    NumericalComputes (app P A) (F p) := by
  refine ⟨?_,fun n => ((hP.2 p n _).mpr rfl).apply_numerical hP.1 hA⟩
  unfold Closed
  rw [fv_app,hP.1,hA.1]; rfl

end PolishSpaceBook
