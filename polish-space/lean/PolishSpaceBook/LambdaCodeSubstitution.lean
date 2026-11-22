module

public import PolishSpaceBook.LambdaFreshVariables

@[expose] public section

/-! # Capture-avoiding substitution as a closed lambda program

The numerical recursor iterates functions of a term code, a variable index,
and a replacement code. Each iteration implements exactly one layer of
`Term.substFuel`, including its two calls at the smaller budget in the
renaming case. The syntax-node counter supplies a sufficient budget.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

def call3 (R E X D : AlphaTerm) : AlphaTerm := app (app (app R E) X) D
def testZero (T A B : AlphaTerm) : AlphaTerm := app (app (app zeroTestTerm T) A) B

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    For a prospective smaller-budget function $r$ and code arguments $e,i,d$, use the following abbreviations for the variable and application branches:
    $$\begin{aligned}
    V(e,i,d)&:=\LambdaZeroTest\,(\LambdaEqual\,(\LambdaSyntaxPayload\,e)\,i)\,e\,d,\\
    A(r,e,i,d)&:=\LambdaTaggedCode{1}\,
     \bigl(r(\LambdaSyntaxField{1}\,e)\,i\,d\bigr)\\
     &\qquad\bigl(r(\LambdaSyntaxField{2}\,e)\,i\,d\bigr).
    \end{aligned}$$
    In the abstraction branch, write $b$ for the body code and $y$ for the binder index. Define
    $$\begin{aligned}
    Q(r,b,y,i,d,z)&:=\LambdaTaggedCode{2}\,z\,
     \bigl(r\bigl(r\,b\,y\,(\LambdaVarCode\,z)\bigr)\,i\,d\bigr),\\
    U(r,b,y,i,d)&:=\LambdaZeroTest\,(\LambdaFreeVarTest\,d\,y)\\
     &\qquad\bigl(\LambdaTaggedCode{2}\,y\,(r\,b\,i\,d)\bigr)\\
     &\qquad Q(r,b,y,i,d,\LambdaFreshVar\,b\,d\,i),\\
    L(r,e,i,d)&:=\LambdaZeroTest\,(\LambdaEqual\,(\LambdaSyntaxField{1}\,e)\,i)\\
     &\qquad U(r,\LambdaSyntaxField{2}\,e,\LambdaSyntaxField{1}\,e,i,d)\,e,\\
    B(r,e,i,d)&:=\LambdaSyntaxCase{e}{V(e,i,d)}{A(r,e,i,d)}{L(r,e,i,d)}.
    \end{aligned}$$
    Thus $L$ returns the original abstraction when its binder is the variable being replaced. Otherwise $U$ tests whether the binder occurs freely in the replacement. If it does, $Q$ first renames the body's free occurrences of that binder, then substitutes the intended replacement into the renamed body. Both calls use the same function $r$.
-/
def substitutionVariable (E X D : AlphaTerm) : AlphaTerm :=
  testZero (app (app equalityTerm (app syntaxPayloadTerm E)) X) E D

def substitutionApplication (R E X D : AlphaTerm) : AlphaTerm :=
  app (app applicationCodeTerm (call3 R (app (syntaxFieldTerm true) E) X D))
    (call3 R (app (syntaxFieldTerm false) E) X D)

def substitutionRename (R B Y X D Z : AlphaTerm) : AlphaTerm :=
  app (app abstractionCodeTerm Z)
    (call3 R (call3 R B Y (app variableCodeTerm Z)) X D)

def substitutionUnderBinder (R B Y X D : AlphaTerm) : AlphaTerm :=
  testZero (app (app freeVariableTerm D) Y)
    (app (app abstractionCodeTerm Y) (call3 R B X D))
    (substitutionRename R B Y X D (call3 freshVariableTerm B D X))

def substitutionAbstraction (R E X D : AlphaTerm) : AlphaTerm :=
  testZero (app (app equalityTerm (app (syntaxFieldTerm true) E)) X)
    (substitutionUnderBinder R (app (syntaxFieldTerm false) E)
      (app (syntaxFieldTerm true) E) X D) E

def substitutionBody (R E X D : AlphaTerm) : AlphaTerm :=
  syntaxCases E (substitutionVariable E X D)
    (substitutionApplication R E X D) (substitutionAbstraction R E X D)

private theorem applicationCode_closed : applicationCodeTerm.Closed := taggedPairCodeTerm_closed 1
private theorem abstractionCode_closed : abstractionCodeTerm.Closed := taggedPairCodeTerm_closed 2

theorem substitutionVariable_fv (E X D : AlphaTerm) :
    (substitutionVariable E X D).fv = E.fv ∪ X.fv ∪ D.fv := by
  simp only [testZero, substitutionVariable, fv_app]
  simp only [(show zeroTestTerm.fv = ∅ from zeroTestTerm_closed), (show equalityTerm.fv = ∅ from equalityTerm_closed), (show syntaxPayloadTerm.fv = ∅ from syntaxPayloadTerm_closed), Finset.empty_union]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem substitutionApplication_fv (R E X D : AlphaTerm) :
    (substitutionApplication R E X D).fv = R.fv ∪ E.fv ∪ X.fv ∪ D.fv := by
  simp only [call3, substitutionApplication, fv_app]
  simp only [(show applicationCodeTerm.fv = ∅ from applicationCode_closed), (show (syntaxFieldTerm true).fv = ∅ from syntaxFieldTerm_closed true), (show (syntaxFieldTerm false).fv = ∅ from syntaxFieldTerm_closed false), Finset.empty_union]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem substitutionRename_fv (R B Y X D Z : AlphaTerm) :
    (substitutionRename R B Y X D Z).fv = R.fv ∪ B.fv ∪ Y.fv ∪ X.fv ∪ D.fv ∪ Z.fv := by
  simp only [call3, substitutionRename, fv_app]
  simp only [(show variableCodeTerm.fv = ∅ from variableCodeTerm_closed), (show abstractionCodeTerm.fv = ∅ from abstractionCode_closed), Finset.empty_union]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem substitutionUnderBinder_fv (R B Y X D : AlphaTerm) :
    (substitutionUnderBinder R B Y X D).fv = R.fv ∪ B.fv ∪ Y.fv ∪ X.fv ∪ D.fv := by
  simp only [call3, testZero, substitutionRename, substitutionUnderBinder, fv_app]
  simp only [(show zeroTestTerm.fv = ∅ from zeroTestTerm_closed), (show freeVariableTerm.fv = ∅ from freeVariableTerm_closed), (show freshVariableTerm.fv = ∅ from freshVariableTerm_closed), (show variableCodeTerm.fv = ∅ from variableCodeTerm_closed), (show abstractionCodeTerm.fv = ∅ from abstractionCode_closed), Finset.empty_union]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem substitutionAbstraction_fv (R E X D : AlphaTerm) :
    (substitutionAbstraction R E X D).fv = R.fv ∪ E.fv ∪ X.fv ∪ D.fv := by
  simp only [call3, testZero, substitutionRename, substitutionUnderBinder, substitutionAbstraction, fv_app]
  simp only [(show zeroTestTerm.fv = ∅ from zeroTestTerm_closed), (show equalityTerm.fv = ∅ from equalityTerm_closed), (show freeVariableTerm.fv = ∅ from freeVariableTerm_closed), (show freshVariableTerm.fv = ∅ from freshVariableTerm_closed), (show variableCodeTerm.fv = ∅ from variableCodeTerm_closed), (show abstractionCodeTerm.fv = ∅ from abstractionCode_closed), (show (syntaxFieldTerm true).fv = ∅ from syntaxFieldTerm_closed true), (show (syntaxFieldTerm false).fv = ∅ from syntaxFieldTerm_closed false), Finset.empty_union]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem substitutionBody_fv (R E X D : AlphaTerm) :
    (substitutionBody R E X D).fv = R.fv ∪ E.fv ∪ X.fv ∪ D.fv := by
  simp only [call3, testZero, substitutionVariable, substitutionApplication, substitutionRename, substitutionUnderBinder, substitutionAbstraction, substitutionBody, syntaxCases_fv, fv_app]
  simp only [(show zeroTestTerm.fv = ∅ from zeroTestTerm_closed), (show equalityTerm.fv = ∅ from equalityTerm_closed), (show syntaxPayloadTerm.fv = ∅ from syntaxPayloadTerm_closed), (show freeVariableTerm.fv = ∅ from freeVariableTerm_closed), (show freshVariableTerm.fv = ∅ from freshVariableTerm_closed), (show variableCodeTerm.fv = ∅ from variableCodeTerm_closed), (show applicationCodeTerm.fv = ∅ from applicationCode_closed), (show abstractionCodeTerm.fv = ∅ from abstractionCode_closed), (show (syntaxFieldTerm true).fv = ∅ from syntaxFieldTerm_closed true), (show (syntaxFieldTerm false).fv = ∅ from syntaxFieldTerm_closed false), Finset.empty_union]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem substitutionBody_subst (R E X D W : AlphaTerm) (x : ℕ) :
    (substitutionBody R E X D).subst x W =
      substitutionBody (R.subst x W) (E.subst x W) (X.subst x W) (D.subst x W) := by
  simp only [substitutionBody, syntaxCases_subst, substitutionVariable,
    substitutionApplication, substitutionAbstraction, substitutionUnderBinder,
    substitutionRename, call3, testZero, subst_app,
    subst_closed _ _ _ zeroTestTerm_closed,
    subst_closed _ _ _ equalityTerm_closed,
    subst_closed _ _ _ syntaxPayloadTerm_closed,
    subst_closed _ _ _ freeVariableTerm_closed,
    subst_closed _ _ _ freshVariableTerm_closed,
    subst_closed _ _ _ variableCodeTerm_closed,
    subst_closed _ _ _ applicationCode_closed,
    subst_closed _ _ _ abstractionCode_closed,
    subst_closed _ _ _ (syntaxFieldTerm_closed true),
    subst_closed _ _ _ (syntaxFieldTerm_closed false)]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Expand all these abbreviations inside the abstractions below, choosing the displayed binders distinct from one another. Define closed terms
    $$\begin{aligned}
    \LambdaSubstBase&:=\lambdaab{e}{\lambdaab{i}{\lambdaab{d}{e}}},\\
    \LambdaSubstStep&:=\lambdaab{k}{\lambdaab{r}{\lambdaab{e}{\lambdaab{i}{\lambdaab{d}{B(r,e,i,d)}}}}},\\
    \LambdaSubstFuel&:=\LambdaRecursor\,\LambdaSubstStep\,\LambdaSubstBase,\\
    \LambdaSubstCode&:=\lambdaab{e}{\lambdaab{i}{\lambdaab{d}{
     \LambdaSubstFuel\,(\LambdaSyntaxNodes\,e)\,e\,i\,d}}}.
    \end{aligned}$$
    The step term ignores its numerical argument $k$; its function argument $r$ already carries the smaller budget. The final program computes a sufficient budget from the source code, so the caller supplies no bound.
-/
def substitutionBase : AlphaTerm := lam 22 (lam 23 (lam 24 (var 22)))

def substitutionStep : AlphaTerm := lam 20 (lam 21 (lam 22 (lam 23 (lam 24
  (substitutionBody (var 21) (var 22) (var 23) (var 24))))))

@[simp] theorem substitutionBase_closed : substitutionBase.Closed := by
  unfold substitutionBase Closed
  simp only [fv_lam, fv_var]
  decide

@[simp] theorem substitutionStep_closed : substitutionStep.Closed := by
  unfold substitutionStep Closed
  simp only [fv_lam, substitutionBody_fv, fv_var]
  decide

theorem substitutionBase_apply (e x d : ℕ) :
    Relation.ReflTransGen Beta (call3 substitutionBase (numeral e) (numeral x) (numeral d))
      (numeral e) := by
  have h0 : Beta (app (lam 22 (lam 23 (lam 24 (var 22)))) (numeral e)) (lam 23 (lam 24 (numeral e))) := by
    convert Beta.contract 22 (lam 23 (lam 24 (var 22))) (numeral e) using 1

    simp [subst_lam_fresh, subst_var, (show ∀ n, (numeral n).fv = ∅ from numeral_closed)]
  have h1 : Beta (app (lam 23 (lam 24 (numeral e))) (numeral x)) (lam 24 (numeral e)) := by
    convert Beta.contract 23 (lam 24 (numeral e)) (numeral x) using 1

    simp [subst_lam_fresh, numeral_closed, subst_closed, (show ∀ n, (numeral n).fv = ∅ from numeral_closed)]
  have h2 : Beta (app (lam 24 (numeral e)) (numeral d)) (numeral e) := by
    convert Beta.contract 24 (numeral e) (numeral d) using 1

    simp [numeral_closed, subst_closed]
  exact (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) (numeral x)) (numeral d)).trans ((beta_steps_app_left (Relation.ReflTransGen.single h1) (numeral d)).trans ((Relation.ReflTransGen.single h2)))

theorem substitutionStep_apply (k : ℕ) {R : AlphaTerm} (hR : R.Closed) (e x d : ℕ) :
    Relation.ReflTransGen Beta (call3 (app (app substitutionStep (numeral k)) R) (numeral e) (numeral x) (numeral d))
      (substitutionBody R (numeral e) (numeral x) (numeral d)) := by
  have h0 : Beta (app (lam 20 (lam 21 (lam 22 (lam 23 (lam 24 (substitutionBody (var 21) (var 22) (var 23) (var 24))))))) (numeral k)) (lam 21 (lam 22 (lam 23 (lam 24 (substitutionBody (var 21) (var 22) (var 23) (var 24)))))) := by
    convert Beta.contract 20 (lam 21 (lam 22 (lam 23 (lam 24 (substitutionBody (var 21) (var 22) (var 23) (var 24)))))) (numeral k) using 1

    simp [subst_lam_fresh, subst_var, substitutionBody_subst, (show ∀ n, (numeral n).fv = ∅ from numeral_closed)]
  have h1 : Beta (app (lam 21 (lam 22 (lam 23 (lam 24 (substitutionBody (var 21) (var 22) (var 23) (var 24)))))) R) (lam 22 (lam 23 (lam 24 (substitutionBody R (var 22) (var 23) (var 24))))) := by
    convert Beta.contract 21 (lam 22 (lam 23 (lam 24 (substitutionBody (var 21) (var 22) (var 23) (var 24))))) R using 1

    simp [subst_lam_fresh, subst_var, substitutionBody_subst, (show R.fv = ∅ from hR)]
  have h2 : Beta (app (lam 22 (lam 23 (lam 24 (substitutionBody R (var 22) (var 23) (var 24))))) (numeral e)) (lam 23 (lam 24 (substitutionBody R (numeral e) (var 23) (var 24)))) := by
    convert Beta.contract 22 (lam 23 (lam 24 (substitutionBody R (var 22) (var 23) (var 24)))) (numeral e) using 1

    simp [subst_lam_fresh, subst_var, substitutionBody_subst, hR, subst_closed, (show ∀ n, (numeral n).fv = ∅ from numeral_closed)]
  have h3 : Beta (app (lam 23 (lam 24 (substitutionBody R (numeral e) (var 23) (var 24)))) (numeral x)) (lam 24 (substitutionBody R (numeral e) (numeral x) (var 24))) := by
    convert Beta.contract 23 (lam 24 (substitutionBody R (numeral e) (var 23) (var 24))) (numeral x) using 1

    simp [subst_lam_fresh, subst_var, substitutionBody_subst, numeral_closed, hR, subst_closed, (show ∀ n, (numeral n).fv = ∅ from numeral_closed)]
  have h4 : Beta (app (lam 24 (substitutionBody R (numeral e) (numeral x) (var 24))) (numeral d)) (substitutionBody R (numeral e) (numeral x) (numeral d)) := by
    convert Beta.contract 24 (substitutionBody R (numeral e) (numeral x) (var 24)) (numeral d) using 1

    simp [subst_var, substitutionBody_subst, numeral_closed, hR, subst_closed]
  exact (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) R) (numeral e)) (numeral x)) (numeral d)).trans ((beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) (numeral e)) (numeral x)) (numeral d)).trans ((beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h2) (numeral x)) (numeral d)).trans ((beta_steps_app_left (Relation.ReflTransGen.single h3) (numeral d)).trans ((Relation.ReflTransGen.single h4)))))

private theorem call3_steps {R E X D E' X' D' : AlphaTerm}
    (hE : Relation.ReflTransGen Beta E E') (hX : Relation.ReflTransGen Beta X X')
    (hD : Relation.ReflTransGen Beta D D') :
    Relation.ReflTransGen Beta (call3 R E X D) (call3 R E' X' D') :=
  beta_steps_app (beta_steps_app (beta_steps_app_right R hE) hX) hD

private theorem testZero_steps {T T' A B : AlphaTerm}
    (h : Relation.ReflTransGen Beta T T') :
    Relation.ReflTransGen Beta (testZero T A B) (testZero T' A B) :=
  beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm h) A) B

private theorem substitutionRename_steps (R B Y X D : AlphaTerm) {Z Z' : AlphaTerm}
    (hZ : Relation.ReflTransGen Beta Z Z') :
    Relation.ReflTransGen Beta (substitutionRename R B Y X D Z)
      (substitutionRename R B Y X D Z') := by
  simp only [substitutionRename, call3]
  repeat first | exact hZ | exact .refl | apply beta_steps_app

private theorem substitutionUnderBinder_steps (R X D : AlphaTerm) {B B' Y Y' : AlphaTerm}
    (hB : Relation.ReflTransGen Beta B B') (hY : Relation.ReflTransGen Beta Y Y') :
    Relation.ReflTransGen Beta (substitutionUnderBinder R B Y X D)
      (substitutionUnderBinder R B' Y' X D) := by
  simp only [substitutionUnderBinder, substitutionRename, testZero, call3]
  repeat first | exact hB | exact hY | exact .refl | apply beta_steps_app

private theorem substitutionVariable_code (y x : ℕ) (N : Term) :
    Relation.ReflTransGen Beta
      (substitutionVariable (numeral (Term.var y).code) (numeral x) (numeral N.code))
      (numeral (if y = x then N else Term.var y).code) := by
  unfold substitutionVariable
  have he := (beta_steps_app_left
    (beta_steps_app_right equalityTerm (syntaxPayloadTerm_var y)) (numeral x)).trans
      (equalityTerm_apply y x)
  apply (testZero_steps he).trans
  by_cases hy : y = x
  · simpa only [testZero, ite_eq_left hy] using branch_succ 0 (numeral (Term.var y).code) (numeral N.code)
  · simpa only [testZero, ite_eq_right hy] using branch_zero (numeral (Term.var y).code) (numeral N.code)
      (by rw [numeral_closed]; simp)

private theorem substitutionApplication_code {R : AlphaTerm} (k : ℕ)
    (hR : ∀ M x N, Relation.ReflTransGen Beta (call3 R (numeral M.code) (numeral x) (numeral N.code))
      (numeral (Term.substFuel k M x N).code)) (M P N : Term) (x : ℕ) :
    Relation.ReflTransGen Beta
      (substitutionApplication R (numeral (Term.app M P).code) (numeral x) (numeral N.code))
      (numeral (Term.app (Term.substFuel k M x N) (Term.substFuel k P x N)).code) := by
  have hM := (call3_steps (R := R) (syntaxFieldTerm_app true M P) .refl .refl).trans (hR M x N)
  have hP := (call3_steps (R := R) (syntaxFieldTerm_app false M P) .refl .refl).trans (hR P x N)
  exact (beta_steps_app (beta_steps_app_right applicationCodeTerm hM) hP).trans
    (applicationCodeTerm_apply _ _)

private theorem substitutionRename_code {R : AlphaTerm} (k : ℕ)
    (hR : ∀ M x N, Relation.ReflTransGen Beta (call3 R (numeral M.code) (numeral x) (numeral N.code))
      (numeral (Term.substFuel k M x N).code)) (M N : Term) (y x z : ℕ) :
    Relation.ReflTransGen Beta
      (substitutionRename R (numeral M.code) (numeral y) (numeral x) (numeral N.code) (numeral z))
      (numeral (Term.lam z (Term.substFuel k (Term.substFuel k M y (.var z)) x N)).code) := by
  have hin := (call3_steps (R := R) .refl .refl (variableCodeTerm_apply z)).trans (hR M y (.var z))
  have hout := (call3_steps (R := R) hin .refl .refl).trans (hR (Term.substFuel k M y (.var z)) x N)
  exact (beta_steps_app_right (app abstractionCodeTerm (numeral z)) hout).trans
    (abstractionCodeTerm_apply _ _)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For an abstraction whose binder is the variable being replaced, the original code is returned. If the binder is absent from the replacement's free variables, the induction hypothesis computes the substituted body and the abstraction constructor retains the binder. In the remaining case, fresh-name search returns precisely the least index required by the substitution definition. The variable constructor produces its variable code. Apply the induction hypothesis first to the body with that variable as replacement, then to the resulting named term with the intended replacement. The hypothesis covers all named terms, so this second application is valid even though the renamed body is not a literal subterm. The abstraction constructor supplies the fresh binder. These are exactly the bounded substitution clauses, and every selected computation is finite; discarded branches need not be evaluated.
-/
private theorem substitutionUnderBinder_code {R : AlphaTerm} (hc : R.Closed) (k : ℕ)
    (hR : ∀ M x N, Relation.ReflTransGen Beta (call3 R (numeral M.code) (numeral x) (numeral N.code))
      (numeral (Term.substFuel k M x N).code)) (M N : Term) (y x : ℕ) :
    Relation.ReflTransGen Beta
      (substitutionUnderBinder R (numeral M.code) (numeral y) (numeral x) (numeral N.code))
      (numeral (if y ∉ N.fv then Term.lam y (Term.substFuel k M x N)
        else let z := Term.fresh (M.fv ∪ N.fv ∪ {x})
          Term.lam z (Term.substFuel k (Term.substFuel k M y (.var z)) x N)).code) := by
  unfold substitutionUnderBinder
  apply (testZero_steps (freeVariableTerm_code N y)).trans
  by_cases hy : y ∈ N.fv
  · simp only [ite_eq_left hy, ite_eq_right (not_not_intro hy)]
    apply (branch_succ 0 _ _).trans
    apply (substitutionRename_steps R _ _ _ _ (freshVariableTerm_code M N x)).trans
    exact substitutionRename_code k hR M N y x _
  · simp only [ite_eq_right hy, ite_eq_left hy]
    have hr : 2 ∉ (app (app abstractionCodeTerm (numeral y))
        (call3 R (numeral M.code) (numeral x) (numeral N.code))).fv := by
      simp only [call3, fv_app]
      rw [abstractionCode_closed, hc, numeral_closed, numeral_closed, numeral_closed, numeral_closed]
      simp
    exact (branch_zero _ _ hr).trans
      ((beta_steps_app_right (app abstractionCodeTerm (numeral y)) (hR M x N)).trans
        (abstractionCodeTerm_apply _ _))

private theorem substitutionAbstraction_code {R : AlphaTerm} (hc : R.Closed) (k : ℕ)
    (hR : ∀ M x N, Relation.ReflTransGen Beta (call3 R (numeral M.code) (numeral x) (numeral N.code))
      (numeral (Term.substFuel k M x N).code)) (M N : Term) (y x : ℕ) :
    Relation.ReflTransGen Beta
      (substitutionAbstraction R (numeral (Term.lam y M).code) (numeral x) (numeral N.code))
      (numeral (Term.substFuel (k + 1) (.lam y M) x N).code) := by
  unfold substitutionAbstraction
  have he := (beta_steps_app_left
    (beta_steps_app_right equalityTerm (syntaxFieldTerm_lam true y M)) (numeral x)).trans
      (equalityTerm_apply y x)
  apply (testZero_steps he).trans
  by_cases hy : y = x
  · simpa only [testZero, Term.substFuel, ite_eq_left hy] using branch_succ 0 _ (numeral (Term.lam y M).code)
  · simp only [Term.substFuel, ite_eq_right hy]
    have hr : 2 ∉ (substitutionUnderBinder R
        (app (syntaxFieldTerm false) (numeral (Term.lam y M).code))
        (app (syntaxFieldTerm true) (numeral (Term.lam y M).code))
        (numeral x) (numeral N.code)).fv := by
      rw [substitutionUnderBinder_fv, hc, fv_app, fv_app, syntaxFieldTerm_closed,
        syntaxFieldTerm_closed, numeral_closed, numeral_closed, numeral_closed]
      simp
    apply (branch_zero _ _ hr).trans
    apply (substitutionUnderBinder_steps R _ _ (syntaxFieldTerm_lam false y M)
      (syntaxFieldTerm_lam true y M)).trans
    exact substitutionUnderBinder_code hc k hR M N y x

theorem substitutionBody_code {R : AlphaTerm} (hc : R.Closed) (k : ℕ)
    (hR : ∀ M x N, Relation.ReflTransGen Beta (call3 R (numeral M.code) (numeral x) (numeral N.code))
      (numeral (Term.substFuel k M x N).code)) (M N : Term) (x : ℕ) :
    Relation.ReflTransGen Beta (substitutionBody R (numeral M.code) (numeral x) (numeral N.code))
      (numeral (Term.substFuel (k + 1) M x N).code) := by
  have hv : (substitutionVariable (numeral M.code) (numeral x) (numeral N.code)).Closed := by
    unfold Closed
    rw [substitutionVariable_fv, numeral_closed, numeral_closed, numeral_closed]; simp
  have ha : (substitutionApplication R (numeral M.code) (numeral x) (numeral N.code)).Closed := by
    unfold Closed
    rw [substitutionApplication_fv, hc, numeral_closed, numeral_closed, numeral_closed]; simp
  apply (syntaxCases_code M _ _ _ hv ha).trans
  cases M with
  | var y => exact substitutionVariable_code y x N
  | app M P => exact substitutionApplication_code k hR M P N x
  | lam y M => exact substitutionAbstraction_code hc k hR M N y x

/-- The recursor's states are closed three-argument functions, not numerals. -/
def substitutionApprox : ℕ → AlphaTerm
  | 0 => substitutionBase
  | k + 1 => app (app substitutionStep (numeral k)) (substitutionApprox k)

theorem substitutionApprox_closed (k : ℕ) : (substitutionApprox k).Closed := by
  induction k with
  | zero => exact substitutionBase_closed
  | succ k ih => exact closed_app (closed_app substitutionStep_closed (numeral_closed k)) ih

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Define closed function values by $R_0:=\LambdaSubstBase$ and $R_{k+1}:=\LambdaSubstStep\,\ChurchNumeral{k}\,R_k$. The primitive-recursion theorem gives $\LambdaSubstFuel\,\ChurchNumeral{k}\to_\beta^*R_k$. We prove by induction on $k$, simultaneously for all source terms, indices and replacement terms, that $R_k$ computes the bounded procedure. At zero, three beta steps return the source code. At a successor, five beta steps expose $B(R_k,e,i,d)$, and code inspection selects the constructor branch. At a variable, equality testing chooses the replacement code or the unchanged variable code. At an application, the induction hypothesis computes the two substituted subterms, and the application constructor combines their codes.
-/
theorem substitutionApprox_code (k : ℕ) (M N : Term) (x : ℕ) :
    Relation.ReflTransGen Beta (call3 (substitutionApprox k) (numeral M.code) (numeral x) (numeral N.code))
      (numeral (Term.substFuel k M x N).code) := by
  induction k generalizing M N x with
  | zero => exact substitutionBase_apply _ _ _
  | succ k ih =>
    exact (substitutionStep_apply k (substitutionApprox_closed k) _ _ _).trans
      (substitutionBody_code (substitutionApprox_closed k) k (fun M x N => ih M N x) M N x)

/-- A single lambda program, with the depth budget as its first input. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The termination proof in §{sec:lambda-calculus} used a depth-bounded substitution procedure. Write
    $\LambdaBoundedSubst{k}{M}{x_i}{N}$ for its result at budget $k$. Budget zero returns $M$. At budget $k+1$, each
    recursive call in the substitution clauses receives budget $k$, including both calls in the renaming branch. We now
    implement that very procedure on numerical codes. The recursor's state will be a function of three inputs: the source
    code, the variable index, and the replacement code.
-/
def substitutionFuelTerm : AlphaTerm := app (app recursorTerm substitutionStep) substitutionBase

@[simp] theorem substitutionFuelTerm_closed : substitutionFuelTerm.Closed :=
  closed_app (closed_app recursorTerm_closed substitutionStep_closed) substitutionBase_closed

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Capture-avoiding substitution by a lambda term
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The termination proof in §{sec:lambda-calculus} used a depth-bounded substitution procedure. Write
    $\LambdaBoundedSubst{k}{M}{x_i}{N}$ for its result at budget $k$. Budget zero returns $M$. At budget $k+1$, each
    recursive call in the substitution clauses receives budget $k$, including both calls in the renaming branch. We now
    implement that very procedure on numerical codes. The recursor's state will be a function of three inputs: the source
    code, the variable index, and the replacement code.
-/
theorem substitutionFuelTerm_code (k : ℕ) (M N : Term) (x : ℕ) :
    Relation.ReflTransGen Beta
      (call3 (app substitutionFuelTerm (numeral k)) (numeral M.code) (numeral x) (numeral N.code))
      (numeral (Term.substFuel k M x N).code) := by
  have h := recursorTerm_apply substitutionStep_closed substitutionApprox substitutionApprox_closed
    (fun _ => .refl) k
  exact (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left h _) _) _).trans
    (substitutionApprox_code k M N x)

def substitutionTermBody (E X D : AlphaTerm) : AlphaTerm :=
  call3 (app substitutionFuelTerm (app syntaxNodesTerm E)) E X D

theorem substitutionTermBody_fv (E X D : AlphaTerm) :
    (substitutionTermBody E X D).fv = E.fv ∪ X.fv ∪ D.fv := by
  simp only [substitutionTermBody, call3, fv_app]
  rw [substitutionFuelTerm_closed, syntaxNodesTerm_closed]
  simp

theorem substitutionTermBody_subst (E X D W : AlphaTerm) (i : ℕ) :
    (substitutionTermBody E X D).subst i W =
      substitutionTermBody (E.subst i W) (X.subst i W) (D.subst i W) := by
  simp only [substitutionTermBody, call3, subst_app,
    subst_closed _ _ _ substitutionFuelTerm_closed, subst_closed _ _ _ syntaxNodesTerm_closed]

def substitutionTerm : AlphaTerm := lam 22 (lam 23 (lam 24
  (substitutionTermBody (var 22) (var 23) (var 24))))

@[simp] theorem substitutionTerm_closed : substitutionTerm.Closed := by
  unfold substitutionTerm Closed
  simp only [fv_lam, substitutionTermBody_fv, fv_var]
  decide

theorem substitutionTerm_start (e x d : ℕ) :
    Relation.ReflTransGen Beta (call3 substitutionTerm (numeral e) (numeral x) (numeral d))
      (substitutionTermBody (numeral e) (numeral x) (numeral d)) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have h₁ : Beta (app substitutionTerm (numeral e))
      (lam 23 (lam 24 (substitutionTermBody (numeral e) (var 23) (var 24)))) := by
    convert Beta.contract 22 (lam 23 (lam 24 (substitutionTermBody (var 22) (var 23) (var 24))))
      (numeral e) using 1
    · rfl
    · simp [subst_lam_fresh, subst_var, substitutionTermBody_subst, hn]
  have h₂ : Beta (app (lam 23 (lam 24 (substitutionTermBody (numeral e) (var 23) (var 24)))) (numeral x))
      (lam 24 (substitutionTermBody (numeral e) (numeral x) (var 24))) := by
    convert Beta.contract 23 (lam 24 (substitutionTermBody (numeral e) (var 23) (var 24))) (numeral x) using 1
    simp [subst_lam_fresh, subst_var, substitutionTermBody_subst, hn, subst_closed]
  have h₃ : Beta (app (lam 24 (substitutionTermBody (numeral e) (numeral x) (var 24))) (numeral d))
      (substitutionTermBody (numeral e) (numeral x) (numeral d)) := by
    convert Beta.contract 24 (substitutionTermBody (numeral e) (numeral x) (var 24)) (numeral d) using 1
    simp [substitutionTermBody_subst, subst_var, subst_closed]
  exact (beta_steps_app_left (beta_steps_app_left (.single h₁) _) _).trans
    ((beta_steps_app_left (.single h₂) _).trans (.single h₃))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For the final program, three beta steps pass the input codes and index. Node counting computes $\LambdaNodeCount{M}$. The preceding result then gives the bounded substitution at that budget, which equals $\SubstLambda{M}{x_i}{N}$ by the termination lemma. All constants used above are closed, and all displayed variables are bound, so both programs are closed. Finally, decoding and recoding any natural number gives that number back, extending the result to arbitrary numerical codes.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Capture-avoiding substitution by a lambda term
-/
theorem substitutionTerm_code (M N : Term) (x : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app substitutionTerm (numeral M.code)) (numeral x)) (numeral N.code))
      (numeral (M.subst x N).code) := by
  apply (substitutionTerm_start _ _ _).trans
  have h := beta_steps_app_right substitutionFuelTerm (syntaxNodesTerm_code M)
  exact (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left h _) _) _).trans
    (substitutionFuelTerm_code M.nodes M N x)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Capture-avoiding substitution by a lambda term
-/
theorem substitutionTerm_apply (e x d : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app substitutionTerm (numeral e)) (numeral x)) (numeral d))
      (numeral ((Term.decode e).subst x (Term.decode d)).code) := by
  simpa only [Term.code_decode] using substitutionTerm_code (Term.decode e) (Term.decode d) x

end PolishSpaceBook.NamedLambda.AlphaTerm
