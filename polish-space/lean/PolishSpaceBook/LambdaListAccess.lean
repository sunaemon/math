module

public import PolishSpaceBook.LambdaFiniteLists
public import PolishSpaceBook.LambdaNumericalFunctions

@[expose] public section

/-! # Total numerical access to finite lists

Length, tail iteration and zero-default indexing are actual closed lambda
programs, including empty lists and indices beyond the end.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

theorem listFieldTerm_zero (first : Bool) :
    Relation.ReflTransGen Beta (app (listFieldTerm first) (numeral 0)) (numeral 0) := by
  have hs : Beta (app (listFieldTerm first) (numeral 0)) (listFieldBody first (numeral 0)) := by
    simpa only [listFieldTerm,listFieldBody_subst,subst_var,ite_true] using
      Beta.contract 30 (listFieldBody first (var 30)) (numeral 0)
  apply (Relation.ReflTransGen.single hs).trans
  exact (beta_steps_app_right (numericalProjectionTerm first) (predecessorTerm_apply 0)).trans
    (by simpa using numericalProjectionTerm_apply first 0)

theorem listTail_code (xs : List ℕ) : Relation.ReflTransGen Beta
    (app (listFieldTerm false) (numeral (NatListCode.encode xs))) (numeral (NatListCode.encode xs.tail)) := by
  cases xs with
  | nil => exact listFieldTerm_zero false
  | cons a xs => exact listFieldTerm_cons false a _

theorem listHead_code (xs : List ℕ) : Relation.ReflTransGen Beta
    (app (listFieldTerm true) (numeral (NatListCode.encode xs))) (numeral (xs.getD 0 0)) := by
  cases xs with
  | nil => exact listFieldTerm_zero true
  | cons a xs => exact listFieldTerm_cons true a _

def listLengthHandler := lam 40 successorTerm

theorem listLengthHandler_closed : listLengthHandler.Closed := by
  unfold listLengthHandler Closed
  rw [fv_lam,successorTerm_closed]; simp

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To inspect a finite prefix, we need its length and its entries. Extend both list fields to the empty-list code by
    returning zero. Define
    $$\begin{aligned}
    H_0&:=\lambdaab{a}{\LambdaSucc},\\
    \LambdaListLength&:=\LambdaListRecursor\,H_0\,\ChurchNumeral{0},\\
    \LambdaListDrop&:=\lambdaab{e}{\lambdaab{n}{n\,\LambdaListField{2}\,e}},\\
    \LambdaListGet&:=\lambdaab{z}{\LambdaListField{1}\bigl(
     \LambdaListDrop\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)\bigr)}.
    \end{aligned}$$
    These formulas use the list coding and recursor of §{sec:lambda-finite-lists}. The zero extension specifies the behavior
    at the boundary explicitly; no rule for natural-number subtraction is needed here.
-/
def listLengthTerm := listFold (numeral 0) listLengthHandler

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Length and entries of finite lists
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    List recursion starts the length at zero and ignores each head, applying successor to the recursively computed length of
    the tail. Induction on the list proves the length formula. The Church numeral in the drop program iterates the tail
    operation exactly $n$ times. Induction on $n$ proves that the result is the code of the remaining suffix, including the
    empty suffix since its tail stays empty. The first list field then returns the requested entry, or zero if that suffix
    is empty. Numerical projections supply the paired arguments. The constants are closed and the abstractions bind every
    remaining variable.
-/
theorem listLength_computes : NumericalComputes listLengthTerm (fun e => (NatListCode.decode e).length) := by
  refine ⟨listFold_closed (numeral_closed 0) listLengthHandler_closed,fun e => ?_⟩
  have h := listFold_apply (numeral_closed 0) listLengthHandler_closed
    (fun xs => numeral xs.length) .refl (fun a xs => ?_) (NatListCode.decode e)
  · simpa only [listLengthTerm,NatListCode.encode_decode] using h
  · have hs : Beta (app listLengthHandler (numeral a)) successorTerm := by
      simpa only [listLengthHandler,subst_closed _ _ _ successorTerm_closed] using
        Beta.contract 40 successorTerm (numeral a)
    exact (Relation.ReflTransGen.single (.app_left _ hs)).trans (successorTerm_apply xs.length)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To inspect a finite prefix, we need its length and its entries. Extend both list fields to the empty-list code by
    returning zero. Define
    $$\begin{aligned}
    H_0&:=\lambdaab{a}{\LambdaSucc},\\
    \LambdaListLength&:=\LambdaListRecursor\,H_0\,\ChurchNumeral{0},\\
    \LambdaListDrop&:=\lambdaab{e}{\lambdaab{n}{n\,\LambdaListField{2}\,e}},\\
    \LambdaListGet&:=\lambdaab{z}{\LambdaListField{1}\bigl(
     \LambdaListDrop\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)\bigr)}.
    \end{aligned}$$
    These formulas use the list coding and recursor of §{sec:lambda-finite-lists}. The zero extension specifies the behavior
    at the boundary explicitly; no rule for natural-number subtraction is needed here.
-/
def listDropTerm := lam 40 (lam 41 (app (app (var 41) (listFieldTerm false)) (var 40)))

theorem listDropTerm_closed : listDropTerm.Closed := by
  unfold listDropTerm Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [listFieldTerm_closed]; decide

theorem iterate_listTail (xs : List ℕ) (n : ℕ) : Relation.ReflTransGen Beta
    (iterateApp (listFieldTerm false) (numeral (NatListCode.encode xs)) n)
    (numeral (NatListCode.encode (xs.drop n))) := by
  induction n with
  | zero => simp only [iterateApp,List.drop_zero]; exact .refl
  | succ n ih =>
    exact (beta_steps_app_right (listFieldTerm false) ih).trans
      (by simpa only [List.tail_drop] using listTail_code (xs.drop n))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Length and entries of finite lists
-/
theorem listDropTerm_apply (e n : ℕ) : Relation.ReflTransGen Beta
    (app (app listDropTerm (numeral e)) (numeral n))
    (numeral (NatListCode.encode ((NatListCode.decode e).drop n))) := by
  have h₁ : Beta (app listDropTerm (numeral e))
      (lam 41 (app (app (var 41) (listFieldTerm false)) (numeral e))) := by
    have he : (lam 41 (app (app (var 41) (listFieldTerm false)) (var 40))).subst 40 (numeral e) =
        lam 41 (app (app (var 41) (listFieldTerm false)) (numeral e)) := by
      rw [subst_lam_fresh _ _ 41 40 (by decide) (by rw [numeral_closed]; simp)]
      simp [subst_app,subst_var,subst_closed _ _ _ (listFieldTerm_closed false)]
    rw [← he]; exact Beta.contract 40 _ _
  have h₂ : Beta (app (lam 41 (app (app (var 41) (listFieldTerm false)) (numeral e))) (numeral n))
      (app (app (numeral n) (listFieldTerm false)) (numeral e)) := by
    simpa only [subst_app,subst_var,ite_true,subst_closed _ _ _ (listFieldTerm_closed false),
      subst_closed _ _ _ (numeral_closed e)] using
      Beta.contract 41 (app (app (var 41) (listFieldTerm false)) (numeral e)) (numeral n)
  apply (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans
  apply (numeral_apply n _ _ (by rw [listFieldTerm_closed]; simp)).trans
  simpa only [NatListCode.encode_decode] using iterate_listTail (NatListCode.decode e) n

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To inspect a finite prefix, we need its length and its entries. Extend both list fields to the empty-list code by
    returning zero. Define
    $$\begin{aligned}
    H_0&:=\lambdaab{a}{\LambdaSucc},\\
    \LambdaListLength&:=\LambdaListRecursor\,H_0\,\ChurchNumeral{0},\\
    \LambdaListDrop&:=\lambdaab{e}{\lambdaab{n}{n\,\LambdaListField{2}\,e}},\\
    \LambdaListGet&:=\lambdaab{z}{\LambdaListField{1}\bigl(
     \LambdaListDrop\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{2}z)\bigr)}.
    \end{aligned}$$
    These formulas use the list coding and recursor of §{sec:lambda-finite-lists}. The zero extension specifies the behavior
    at the boundary explicitly; no rule for natural-number subtraction is needed here.
-/
def listGetTerm := numericalCompose (listFieldTerm true) (uncurryNumerical listDropTerm)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Length and entries of finite lists
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Every natural number decodes to a finite list. The empty-list code is zero, and list access returns entry $j$ when
    $j<|s|$, and zero otherwise. List recursion may return a numeral, a pair, or a function. Indexed recursion retains its
    parameters in both the initial value and the update; only the updates actually visited must terminate.
-/
theorem listGet_computes : NumericalComputes listGetTerm
    (fun z => (NatListCode.decode z.unpair.1).getD z.unpair.2 0) := by
  have htail := uncurryNumerical_computes listDropTerm_closed
    (fun e n => NatListCode.encode ((NatListCode.decode e).drop n)) listDropTerm_apply
  have hhead : NumericalComputes (listFieldTerm true) (fun e => (NatListCode.decode e).getD 0 0) :=
    ⟨listFieldTerm_closed true,fun e => by simpa only [NatListCode.encode_decode] using listHead_code (NatListCode.decode e)⟩
  simpa [listGetTerm,List.getD] using hhead.comp htail

end PolishSpaceBook.NamedLambda.AlphaTerm
