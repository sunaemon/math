module

public import PolishSpaceBook.LambdaSyntaxRecursion
public import PolishSpaceBook.LambdaNumericalComparison

@[expose] public section

/-! # Free-variable membership by a closed lambda program -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

def freeUnionBody (F G X : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm (app F X)) (app G X)) (numeral 1)

theorem freeUnionBody_fv (F G X : AlphaTerm) :
    (freeUnionBody F G X).fv = F.fv ∪ G.fv ∪ X.fv := by
  simp only [freeUnionBody, fv_app]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem freeUnionBody_subst (F G X W : AlphaTerm) (x : ℕ) :
    (freeUnionBody F G X).subst x W =
      freeUnionBody (F.subst x W) (G.subst x W) (X.subst x W) := by
  simp only [freeUnionBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed,
    subst_closed _ _ _ (numeral_closed 1)]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Each recursive value will be a function of the variable index to be tested. Define closed handlers and the membership program by
    $$\begin{aligned}
    A_f&:=\lambdaab{f}{\lambdaab{g}{\lambdaab{k}{\LambdaZeroTest\,(fk)\,(gk)\,\ChurchNumeral{1}}}},\\
    L_f&:=\lambdaab{i}{\lambdaab{f}{\lambdaab{k}{\LambdaZeroTest\,(\LambdaEqual\,i\,k)\,(fk)\,\ChurchNumeral{0}}}},\\
    \LambdaFreeVarTest&:=\LambdaSyntaxFold{\LambdaEqual}{A_f}{L_f}.
    \end{aligned}$$
    The application handler takes the union of the two membership predicates. The abstraction handler removes the binder index.
-/
def freeApplicationTerm : AlphaTerm :=
  lam 14 (lam 15 (lam 16 (freeUnionBody (var 14) (var 15) (var 16))))

@[simp] theorem freeApplicationTerm_closed : freeApplicationTerm.Closed := by
  unfold freeApplicationTerm Closed
  rw [fv_lam, fv_lam, fv_lam, freeUnionBody_fv]
  simp [fv_var]
  decide

theorem freeApplicationTerm_start {F G : AlphaTerm} (hF : F.Closed) (hG : G.Closed) (x : ℕ) :
    Relation.ReflTransGen Beta (app (app (app freeApplicationTerm F) G) (numeral x))
      (freeUnionBody F G (numeral x)) := by
  have hf (i : ℕ) : i ∉ F.fv := by rw [hF]; simp
  have hg (i : ℕ) : i ∉ G.fv := by rw [hG]; simp
  have h₁ : Beta (app freeApplicationTerm F)
      (lam 15 (lam 16 (freeUnionBody F (var 15) (var 16)))) := by
    convert Beta.contract 14 (lam 15 (lam 16 (freeUnionBody (var 14) (var 15) (var 16)))) F
      using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 15 14 (by decide) (hf 15),
      subst_lam_fresh _ _ 16 14 (by decide) (hf 16), freeUnionBody_subst]
    simp [subst_var]
  have h₂ : Beta (app (lam 15 (lam 16 (freeUnionBody F (var 15) (var 16)))) G)
      (lam 16 (freeUnionBody F G (var 16))) := by
    convert Beta.contract 15 (lam 16 (freeUnionBody F (var 15) (var 16))) G using 1
    rw [subst_lam_fresh _ _ 16 15 (by decide) (hg 16), freeUnionBody_subst]
    simp [subst_var, subst_closed _ _ _ hF]
  have h₃ : Beta (app (lam 16 (freeUnionBody F G (var 16))) (numeral x))
      (freeUnionBody F G (numeral x)) := by
    convert Beta.contract 16 (freeUnionBody F G (var 16)) (numeral x) using 1
    simp [freeUnionBody_subst, subst_var, subst_closed _ _ _ hF, subst_closed _ _ _ hG]
  exact .tail (.tail (.single (.app_left _ (.app_left _ h₁))) (.app_left _ h₂)) h₃

theorem freeApplicationTerm_apply {F G : AlphaTerm} (hF : F.Closed) (hG : G.Closed)
    (x a b : ℕ) (hf : Relation.ReflTransGen Beta (app F (numeral x)) (numeral a))
    (hg : Relation.ReflTransGen Beta (app G (numeral x)) (numeral b)) :
    Relation.ReflTransGen Beta (app (app (app freeApplicationTerm F) G) (numeral x))
      (numeral (if a = 0 then b else 1)) := by
  apply (freeApplicationTerm_start hF hG x).trans
  have h := beta_steps_app_left (beta_steps_app (beta_steps_app_right zeroTestTerm hf) hg) (numeral 1)
  apply h.trans
  cases a with
  | zero => exact branch_zero _ _ (by rw [numeral_closed]; simp)
  | succ a => exact branch_succ a _ _

def freeEraseBody (I F X : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm (app (app equalityTerm I) X)) (app F X)) (numeral 0)

theorem freeEraseBody_fv (I F X : AlphaTerm) :
    (freeEraseBody I F X).fv = I.fv ∪ F.fv ∪ X.fv := by
  simp only [freeEraseBody, fv_app]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem freeEraseBody_subst (I F X W : AlphaTerm) (x : ℕ) :
    (freeEraseBody I F X).subst x W =
      freeEraseBody (I.subst x W) (F.subst x W) (X.subst x W) := by
  simp only [freeEraseBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed,
    subst_closed _ _ _ equalityTerm_closed, subst_closed _ _ _ (numeral_closed 0)]

def freeAbstractionTerm : AlphaTerm :=
  lam 14 (lam 15 (lam 16 (freeEraseBody (var 14) (var 15) (var 16))))

@[simp] theorem freeAbstractionTerm_closed : freeAbstractionTerm.Closed := by
  unfold freeAbstractionTerm Closed
  rw [fv_lam, fv_lam, fv_lam, freeEraseBody_fv]
  simp [fv_var]
  decide

theorem freeAbstractionTerm_start {F : AlphaTerm} (hF : F.Closed) (i x : ℕ) :
    Relation.ReflTransGen Beta (app (app (app freeAbstractionTerm (numeral i)) F) (numeral x))
      (freeEraseBody (numeral i) F (numeral x)) := by
  have hf (j : ℕ) : j ∉ F.fv := by rw [hF]; simp
  have h₁ : Beta (app freeAbstractionTerm (numeral i))
      (lam 15 (lam 16 (freeEraseBody (numeral i) (var 15) (var 16)))) := by
    convert Beta.contract 14 (lam 15 (lam 16 (freeEraseBody (var 14) (var 15) (var 16)))) (numeral i)
      using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 15 14 (by decide) (by rw [numeral_closed]; simp),
      subst_lam_fresh _ _ 16 14 (by decide) (by rw [numeral_closed]; simp), freeEraseBody_subst]
    simp [subst_var]
  have h₂ : Beta (app (lam 15 (lam 16 (freeEraseBody (numeral i) (var 15) (var 16)))) F)
      (lam 16 (freeEraseBody (numeral i) F (var 16))) := by
    convert Beta.contract 15 (lam 16 (freeEraseBody (numeral i) (var 15) (var 16))) F using 1
    rw [subst_lam_fresh _ _ 16 15 (by decide) (hf 16), freeEraseBody_subst]
    simp [subst_var, subst_closed _ _ _ (numeral_closed i)]
  have h₃ : Beta (app (lam 16 (freeEraseBody (numeral i) F (var 16))) (numeral x))
      (freeEraseBody (numeral i) F (numeral x)) := by
    convert Beta.contract 16 (freeEraseBody (numeral i) F (var 16)) (numeral x) using 1
    simp [freeEraseBody_subst, subst_var, subst_closed _ _ _ (numeral_closed i), subst_closed _ _ _ hF]
  exact .tail (.tail (.single (.app_left _ (.app_left _ h₁))) (.app_left _ h₂)) h₃

theorem freeAbstractionTerm_apply {F : AlphaTerm} (hF : F.Closed) (i x a : ℕ)
    (hf : Relation.ReflTransGen Beta (app F (numeral x)) (numeral a)) :
    Relation.ReflTransGen Beta (app (app (app freeAbstractionTerm (numeral i)) F) (numeral x))
      (numeral (if x = i then 0 else a)) := by
  apply (freeAbstractionTerm_start hF i x).trans
  have h := beta_steps_app_left
    (beta_steps_app (beta_steps_app_right zeroTestTerm (equalityTerm_apply i x)) hf) (numeral 0)
  apply h.trans
  by_cases he : x = i
  · subst x
    simpa using branch_succ 0 (numeral a) (numeral 0)
  · have he' : i ≠ x := Ne.symm he
    simp only [ite_eq_right he, ite_eq_right he']
    exact branch_zero _ _ (by rw [numeral_closed]; simp)

/-- A closed predicate value assembled from the syntax constructors. -/
def freeVariableValue : Term → AlphaTerm
  | .var i => app equalityTerm (numeral i)
  | .app M N => app (app freeApplicationTerm (freeVariableValue M)) (freeVariableValue N)
  | .lam i M => app (app freeAbstractionTerm (numeral i)) (freeVariableValue M)

theorem freeVariableValue_closed (M : Term) : (freeVariableValue M).Closed := by
  induction M with
  | var i => exact closed_app equalityTerm_closed (numeral_closed i)
  | app M N hM hN => exact closed_app (closed_app freeApplicationTerm_closed hM) hN
  | lam i M hM => exact closed_app (closed_app freeAbstractionTerm_closed (numeral_closed i)) hM

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Define closed predicate values recursively by
    $$W_{x_i}:=\LambdaEqual\,\ChurchNumeral{i},\qquad
    W_{MN}:=A_fW_MW_N,\qquad
    W_{\lambdaab{x_i}{M}}:=L_f\ChurchNumeral{i}W_M.$$
    The structural-recursion theorem reduces the first application of the membership program to $W_M$. It remains to prove that $W_M\ChurchNumeral{k}$ returns the required answer. Induct on $M$. At a variable, equality testing gives membership in the singleton. At an application, if the first predicate returns zero, zero testing returns the second predicate's answer; otherwise it returns one. This is precisely membership in the union. At an abstraction, equality with the binder returns zero, and inequality retains the body's answer. This is precisely removal of the binder from the free-variable set. All tests have finite reductions by the induction hypotheses. Closedness follows from the displayed binders and the closed structural recursor. The decoding identity extends the result to every numerical input.
    \end{proof}
-/
theorem freeVariableValue_apply (M : Term) (x : ℕ) :
    Relation.ReflTransGen Beta (app (freeVariableValue M) (numeral x))
      (numeral (if x ∈ M.fv then 1 else 0)) := by
  induction M with
  | var i => simpa [freeVariableValue, Term.fv, eq_comm] using equalityTerm_apply i x
  | app M N hM hN =>
    have h := freeApplicationTerm_apply (freeVariableValue_closed M) (freeVariableValue_closed N)
      x _ _ hM hN
    by_cases hm : x ∈ M.fv <;> by_cases hn : x ∈ N.fv <;>
      simpa [freeVariableValue, Term.fv, hm, hn] using h
  | lam i M hM =>
    have h := freeAbstractionTerm_apply (freeVariableValue_closed M) i x _ hM
    by_cases he : x = i <;> by_cases hm : x ∈ M.fv <;>
      simpa [freeVariableValue, Term.fv, he, hm] using h

/-- A code is consumed first; the resulting closed function tests any variable. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Capture-avoiding substitution must test free-variable membership and choose a fresh variable. The structural recursor
    and the equality test from §{sec:lambda-numerical-comparisons} supply the first operation.
-/
def freeVariableTerm : AlphaTerm :=
  syntaxFold equalityTerm freeApplicationTerm freeAbstractionTerm

@[simp] theorem freeVariableTerm_closed : freeVariableTerm.Closed :=
  syntaxFold_closed equalityTerm_closed freeApplicationTerm_closed freeAbstractionTerm_closed

theorem freeVariableTerm_value (M : Term) :
    Relation.ReflTransGen Beta (app freeVariableTerm (numeral M.code)) (freeVariableValue M) :=
  syntaxFold_apply equalityTerm_closed freeApplicationTerm_closed freeAbstractionTerm_closed
    freeVariableValue (fun _ => .refl) (fun _ _ => .refl) (fun _ _ => .refl) M

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Free-variable membership by a lambda term
-/
theorem freeVariableTerm_code (M : Term) (x : ℕ) :
    Relation.ReflTransGen Beta (app (app freeVariableTerm (numeral M.code)) (numeral x))
      (numeral (if x ∈ M.fv then 1 else 0)) :=
  (beta_steps_app_left (freeVariableTerm_value M) (numeral x)).trans (freeVariableValue_apply M x)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Free-variable membership by a lambda term
-/
theorem freeVariableTerm_apply (e x : ℕ) :
    Relation.ReflTransGen Beta (app (app freeVariableTerm (numeral e)) (numeral x))
      (numeral (if x ∈ (Term.decode e).fv then 1 else 0)) := by
  simpa only [Term.code_decode] using freeVariableTerm_code (Term.decode e) x

end PolishSpaceBook.NamedLambda.AlphaTerm
