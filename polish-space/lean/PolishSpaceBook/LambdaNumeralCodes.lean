module

public import PolishSpaceBook.LambdaSyntaxCoding

@[expose] public section

/-! # Constructing codes of Church numerals by lambda iteration -/
namespace PolishSpaceBook.NamedLambda
namespace Term

/-- The fixed named representative of a Church numeral body. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To apply the finite tests to numerical computations, we must construct the syntax codes of their inputs and outputs. Fix
    the named representative of $\ChurchNumeral{n}$ whose iterator binder is $x_1$ and whose initial-value binder is $x_2$.
    Whenever a syntax code of a numeral is used below, it refers to this representative. Its body starts at $x_2$ and
    acquires one application of $x_1$ at each step.
-/
def churchBody : ℕ → Term
  | 0 => .var 2
  | n + 1 => .app (.var 1) (churchBody n)

/-- Binder indices agree with the existing Church numerals on alpha-classes. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To apply the finite tests to numerical computations, we must construct the syntax codes of their inputs and outputs. Fix
    the named representative of $\ChurchNumeral{n}$ whose iterator binder is $x_1$ and whose initial-value binder is $x_2$.
    Whenever a syntax code of a numeral is used below, it refers to this representative. Its body starts at $x_2$ and
    acquires one application of $x_1$ at each step.
-/
def churchNumeral (n : ℕ) : Term := .lam 1 (.lam 2 (churchBody n))

theorem mk_churchBody (n : ℕ) : AlphaTerm.mk (churchBody n) = AlphaTerm.iterateBody n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change AlphaTerm.app (AlphaTerm.var 1) (AlphaTerm.mk (churchBody n)) = _
    rw [ih]
    rfl

@[simp] theorem mk_churchNumeral (n : ℕ) :
    AlphaTerm.mk (churchNumeral n) = AlphaTerm.numeral n := by
  change AlphaTerm.lam 1 (AlphaTerm.lam 2 (AlphaTerm.mk (churchBody n))) = _
  rw [mk_churchBody]
  rfl

@[simp] theorem churchNumeral_closed (n : ℕ) : (churchNumeral n).fv = ∅ := by
  have h := AlphaTerm.numeral_closed n
  rw [← mk_churchNumeral] at h
  exact h

end Term
namespace AlphaTerm

private theorem applicationCode_closed : applicationCodeTerm.Closed := taggedPairCodeTerm_closed 1
private theorem abstractionCode_closed : abstractionCodeTerm.Closed := taggedPairCodeTerm_closed 2

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Since the variable codes of $x_1,x_2$ are $3,6$, define
    $$\LambdaNumeralCodeProgram:=\lambdaab{n}{
     \LambdaTaggedCode{2}\,\ChurchNumeral{1}\,
     \bigl(\LambdaTaggedCode{2}\,\ChurchNumeral{2}\,
       (n(\LambdaTaggedCode{1}\,\ChurchNumeral{3})\ChurchNumeral{6})\bigr)}.$$
    The inner iteration builds the body code. The two abstraction constructors then bind $x_2$ and $x_1$, in that order.
-/
def numeralCodeBody (N : AlphaTerm) : AlphaTerm :=
  app (app abstractionCodeTerm (numeral 1))
    (app (app abstractionCodeTerm (numeral 2))
      (app (app N (app applicationCodeTerm (numeral 3))) (numeral 6)))

theorem numeralCodeBody_fv (N : AlphaTerm) :
    (numeralCodeBody N).fv = N.fv := by
  ext x
  simp only [numeralCodeBody, fv_app, (show abstractionCodeTerm.fv = ∅ from abstractionCode_closed), (show applicationCodeTerm.fv = ∅ from applicationCode_closed) ,(show (numeral 1).fv = ∅ from numeral_closed 1), (show (numeral 2).fv = ∅ from numeral_closed 2), (show (numeral 3).fv = ∅ from numeral_closed 3), (show (numeral 6).fv = ∅ from numeral_closed 6), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem numeralCodeBody_subst (N W : AlphaTerm) (x : ℕ) :
    (numeralCodeBody N).subst x W =
      numeralCodeBody (N.subst x W) := by
  simp only [numeralCodeBody, subst_app, subst_closed _ _ _ abstractionCode_closed, subst_closed _ _ _ applicationCode_closed ,subst_closed _ _ _ (numeral_closed 1), subst_closed _ _ _ (numeral_closed 2), subst_closed _ _ _ (numeral_closed 3), subst_closed _ _ _ (numeral_closed 6)]

def numeralCodeTerm : AlphaTerm := (lam 30 (numeralCodeBody (var 30)))

@[simp] theorem numeralCodeTerm_closed : numeralCodeTerm.Closed := by
  unfold numeralCodeTerm Closed
  simp only [fv_lam, numeralCodeBody_fv, fv_var]
  decide

theorem numeralCodeTerm_start {N : AlphaTerm}
    (hN : N.Closed) :
    Relation.ReflTransGen Beta (app numeralCodeTerm N)
      (numeralCodeBody N) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfN : N.fv = ∅ := hN
  have h0 : Beta (app (lam 30 (numeralCodeBody (var 30))) N) (numeralCodeBody N) := by
    convert Beta.contract 30 (numeralCodeBody (var 30)) N using 1

    simp [subst_var, numeralCodeBody_subst]
  exact (Relation.ReflTransGen.single h0)

theorem iterate_churchBodyCode (n : ℕ) :
    Relation.ReflTransGen Beta
      (iterateApp (app applicationCodeTerm (numeral 3)) (numeral 6) n)
      (numeral (Term.churchBody n).code) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    exact (beta_steps_app_right _ ih).trans (applicationCodeTerm_apply (.var 1) (Term.churchBody n))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Constructing numeral codes
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Apply the Church-numeral iteration formula to the closed function $\LambdaTaggedCode{1}\,\ChurchNumeral{3}$ and initial value $\ChurchNumeral{6}$. Induction on the number of iterations shows that the result reduces to the numeral for the code of the corresponding body: the base is the code of $x_2$, and the application-code program adds $x_1$ at the next step. Apply the abstraction-code equations with binder indices two and one. The result is the Church numeral for the syntax code of the fixed named representative. The constants are closed and the remaining variable is bound.
-/
theorem numeralCodeTerm_apply (n : ℕ) :
    Relation.ReflTransGen Beta (app numeralCodeTerm (numeral n))
      (numeral (Term.churchNumeral n).code) := by
  apply (numeralCodeTerm_start (numeral_closed n)).trans
  have hc := closed_app applicationCode_closed (numeral_closed 3)
  have hi := (numeral_apply n (app applicationCodeTerm (numeral 3)) (numeral 6)
    (by rw [hc]; simp)).trans (iterate_churchBodyCode n)
  apply (beta_steps_app_right _ (beta_steps_app_right _ hi)).trans
  apply (beta_steps_app_right _ (abstractionCodeTerm_apply 2 (Term.churchBody n))).trans
  exact abstractionCodeTerm_apply 1 (.lam 2 (Term.churchBody n))

end AlphaTerm
end PolishSpaceBook.NamedLambda
