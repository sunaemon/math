module

public import PolishSpaceBook.LambdaBetaSuccessors
public import PolishSpaceBook.LambdaInputCertificates

@[expose] public section

/-! # Enumerating finite-table query reducts by closed lambda programs -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

set_option maxRecDepth 4096

private theorem applicationCode_closed : applicationCodeTerm.Closed := taggedPairCodeTerm_closed 1
private theorem abstractionCode_closed : abstractionCodeTerm.Closed := taggedPairCodeTerm_closed 2

/-- Expose the handlers as ordinary arguments to the syntax fold. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    To supply the application handler with a table at run time, expose the three syntax-fold handlers as arguments:
    $$\LambdaSyntaxRecursor:=\lambdaab{v}{\lambdaab{a}{\lambdaab{l}{\LambdaSyntaxFold{v}{a}{l}}}}.$$
    Expand the fold inside the abstractions, choosing its internal binders distinct from the three parameters. The result is closed. For closed handlers, three beta steps supply them to precisely the fold of §{sec:lambda-syntax-recursion}.
-/
def syntaxRecursorTerm : AlphaTerm :=
  lam 30 (lam 31 (lam 32 (syntaxFold (var 30) (var 31) (var 32))))

theorem syntaxFold_fv (V A L : AlphaTerm) :
    (syntaxFold V A L).fv = (((V.fv ∪ A.fv) ∪ L.fv).erase 13).erase 12 := by
  simp only [syntaxFold, syntaxFoldKernel, fv_app, fv_lam, syntaxFoldBody_fv, fv_var]
  ext x
  simp
  tauto

theorem syntaxFold_subst (V A L W : AlphaTerm) (x : ℕ) (hx12 : 12 ≠ x) (hx13 : 13 ≠ x)
    (h12 : 12 ∉ W.fv) (h13 : 13 ∉ W.fv) :
    (syntaxFold V A L).subst x W = syntaxFold (V.subst x W) (A.subst x W) (L.subst x W) := by
  simp only [syntaxFold, syntaxFoldKernel, subst_app,
    subst_lam_fresh _ _ 12 x hx12 h12, subst_lam_fresh _ _ 13 x hx13 h13,
    syntaxFoldBody_subst, subst_var, ite_eq_right hx12, ite_eq_right hx13]

@[simp] theorem syntaxRecursorTerm_closed : syntaxRecursorTerm.Closed := by
  unfold syntaxRecursorTerm Closed
  simp only [fv_lam, syntaxFold_fv, fv_var]
  decide

theorem syntaxRecursorTerm_start {V A L : AlphaTerm}
    (hV : V.Closed) (hA : A.Closed) (hL : L.Closed) :
    Relation.ReflTransGen Beta (app (app (app syntaxRecursorTerm V) A) L) (syntaxFold V A L) := by
  have hfV (x : ℕ) : x ∉ V.fv := by rw [hV]; simp
  have hfA (x : ℕ) : x ∉ A.fv := by rw [hA]; simp
  have hfL (x : ℕ) : x ∉ L.fv := by rw [hL]; simp
  have h0 : Beta (app syntaxRecursorTerm V) (lam 31 (lam 32 (syntaxFold V (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (syntaxFold (var 30) (var 31) (var 32)))) V using 1
    · rfl
    rw [subst_lam_fresh _ _ 31 30 (by decide) (hfV 31),
      subst_lam_fresh _ _ 32 30 (by decide) (hfV 32),
      syntaxFold_subst _ _ _ _ _ (by decide) (by decide) (hfV 12) (hfV 13)]
    simp [subst_var]
  have h1 : Beta (app (lam 31 (lam 32 (syntaxFold V (var 31) (var 32)))) A)
      (lam 32 (syntaxFold V A (var 32))) := by
    convert Beta.contract 31 (lam 32 (syntaxFold V (var 31) (var 32))) A using 1
    rw [subst_lam_fresh _ _ 32 31 (by decide) (hfA 32),
      syntaxFold_subst _ _ _ _ _ (by decide) (by decide) (hfA 12) (hfA 13)]
    simp [subst_var, subst_closed _ _ _ hV]
  have h2 : Beta (app (lam 32 (syntaxFold V A (var 32))) L) (syntaxFold V A L) := by
    convert Beta.contract 32 (syntaxFold V A (var 32)) L using 1
    rw [syntaxFold_subst _ _ _ _ _ (by decide) (by decide) (hfL 12) (hfL 13)]
    simp [subst_var, subst_closed _ _ _ hV, subst_closed _ _ _ hA]
  exact (beta_steps_app_left (beta_steps_app_left (.single h0) A) L).trans
    ((beta_steps_app_left (.single h1) L).tail h2)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    For a root query, scan the table by list recursion. Define the abbreviations and closed programs
    $$\begin{aligned}
    K(b,i,v,r)&:=\LambdaZeroTest\,(\LambdaEqual\,b\,(\LambdaNumeralCodeProgram\,i))\,r\\
     &\quad(\LambdaListCons\,(\LambdaNumeralCodeProgram\,v)\,r),\\
    H_q&:=\lambdaab{b}{\lambdaab{c}{\lambdaab{r}{
     K(b,\LambdaNumericProjection{1}\,c,\LambdaNumericProjection{2}\,c,r)}}},\\
    R(t,b)&:=\LambdaListRecursor\,(H_qb)\,\ChurchNumeral{0}\,t,\\
    \LambdaRootQueryProgram&:=\lambdaab{t}{\lambdaab{a}{\lambdaab{b}{
     \LambdaZeroTest\,a\,R(t,b)\,\ChurchNumeral{0}}}}.
    \end{aligned}$$
    Expand the abbreviations before abstraction. The inputs $a,b$ are the operator and argument codes of an application. If the operator code is nonzero, the root contributes no query reduct. Otherwise, a table entry is decoded as a proposed address and answer. Equality testing compares the argument code with the fixed numeral code of that address. A match prepends the numeral code of the answer to the tail list; a failure keeps the tail list. Thus order and repeated entries are preserved.
-/
def rootQueryKeepBody (B I V R : AlphaTerm) : AlphaTerm :=
  (app (app (app zeroTestTerm (app (app equalityTerm B) (app numeralCodeTerm I))) R) (app (app listConsTerm (app numeralCodeTerm V)) R))

theorem rootQueryKeepBody_fv (B I V R : AlphaTerm) :
    (rootQueryKeepBody B I V R).fv = B.fv ∪ I.fv ∪ V.fv ∪ R.fv := by
  ext x
  simp only [rootQueryKeepBody, fv_app, (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (equalityTerm).fv = ∅ from equalityTerm_closed), (show (numeralCodeTerm).fv = ∅ from numeralCodeTerm_closed), (show (listConsTerm).fv = ∅ from listConsTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem rootQueryKeepBody_subst (B I V R W : AlphaTerm) (x : ℕ) :
    (rootQueryKeepBody B I V R).subst x W =
      rootQueryKeepBody (B.subst x W) (I.subst x W) (V.subst x W) (R.subst x W) := by
  simp only [rootQueryKeepBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ equalityTerm_closed, subst_closed _ _ _ numeralCodeTerm_closed, subst_closed _ _ _ listConsTerm_closed]

def rootQueryKeepTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (rootQueryKeepBody (var 30) (var 31) (var 32) (var 33))))))

@[simp] theorem rootQueryKeepTerm_closed : rootQueryKeepTerm.Closed := by
  unfold rootQueryKeepTerm Closed
  simp only [fv_lam, rootQueryKeepBody_fv, fv_var]
  decide

theorem rootQueryKeepTerm_start {B I V R : AlphaTerm}
    (hB : B.Closed) (hI : I.Closed) (hV : V.Closed) (hR : R.Closed) :
    Relation.ReflTransGen Beta (app (app (app (app rootQueryKeepTerm B) I) V) R)
      (rootQueryKeepBody B I V R) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfB : B.fv = ∅ := hB
  have hfI : I.fv = ∅ := hI
  have hfV : V.fv = ∅ := hV
  have hfR : R.fv = ∅ := hR
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (rootQueryKeepBody (var 30) (var 31) (var 32) (var 33)))))) B) (lam 31 (lam 32 (lam 33 (rootQueryKeepBody B (var 31) (var 32) (var 33))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (rootQueryKeepBody (var 30) (var 31) (var 32) (var 33))))) B using 1
    simp [subst_lam_fresh, subst_var, rootQueryKeepBody_subst, hfB]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (rootQueryKeepBody B (var 31) (var 32) (var 33))))) I) (lam 32 (lam 33 (rootQueryKeepBody B I (var 32) (var 33)))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (rootQueryKeepBody B (var 31) (var 32) (var 33)))) I using 1
    simp [subst_lam_fresh, subst_var, rootQueryKeepBody_subst, subst_closed, hB, hfI]
  have h2 : Beta (app (lam 32 (lam 33 (rootQueryKeepBody B I (var 32) (var 33)))) V) (lam 33 (rootQueryKeepBody B I V (var 33))) := by
    convert Beta.contract 32 (lam 33 (rootQueryKeepBody B I (var 32) (var 33))) V using 1
    simp [subst_lam_fresh, subst_var, rootQueryKeepBody_subst, subst_closed, hB, hI, hfV]
  have h3 : Beta (app (lam 33 (rootQueryKeepBody B I V (var 33))) R) (rootQueryKeepBody B I V R) := by
    convert Beta.contract 33 (rootQueryKeepBody B I V (var 33)) R using 1
    simp [subst_var, rootQueryKeepBody_subst, subst_closed, hB, hI, hV]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) I) V) R).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) V) R).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h2) R).trans
  exact (Relation.ReflTransGen.single h3)

def rootQueryEntryBody (B C R : AlphaTerm) : AlphaTerm :=
  (app (app (app (app rootQueryKeepTerm B) (app (numericalProjectionTerm true) C)) (app (numericalProjectionTerm false) C)) R)

theorem rootQueryEntryBody_fv (B C R : AlphaTerm) :
    (rootQueryEntryBody B C R).fv = B.fv ∪ C.fv ∪ R.fv := by
  ext x
  simp only [rootQueryEntryBody, fv_app, (show (rootQueryKeepTerm).fv = ∅ from rootQueryKeepTerm_closed), (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem rootQueryEntryBody_subst (B C R W : AlphaTerm) (x : ℕ) :
    (rootQueryEntryBody B C R).subst x W =
      rootQueryEntryBody (B.subst x W) (C.subst x W) (R.subst x W) := by
  simp only [rootQueryEntryBody, subst_app, subst_closed _ _ _ rootQueryKeepTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed true), subst_closed _ _ _ (numericalProjectionTerm_closed false)]

def rootQueryEntryTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (rootQueryEntryBody (var 30) (var 31) (var 32)))))

@[simp] theorem rootQueryEntryTerm_closed : rootQueryEntryTerm.Closed := by
  unfold rootQueryEntryTerm Closed
  simp only [fv_lam, rootQueryEntryBody_fv, fv_var]
  decide

theorem rootQueryEntryTerm_start {B C R : AlphaTerm}
    (hB : B.Closed) (hC : C.Closed) (hR : R.Closed) :
    Relation.ReflTransGen Beta (app (app (app rootQueryEntryTerm B) C) R)
      (rootQueryEntryBody B C R) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfB : B.fv = ∅ := hB
  have hfC : C.fv = ∅ := hC
  have hfR : R.fv = ∅ := hR
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (rootQueryEntryBody (var 30) (var 31) (var 32))))) B) (lam 31 (lam 32 (rootQueryEntryBody B (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (rootQueryEntryBody (var 30) (var 31) (var 32)))) B using 1
    simp [subst_lam_fresh, subst_var, rootQueryEntryBody_subst, hfB]
  have h1 : Beta (app (lam 31 (lam 32 (rootQueryEntryBody B (var 31) (var 32)))) C) (lam 32 (rootQueryEntryBody B C (var 32))) := by
    convert Beta.contract 31 (lam 32 (rootQueryEntryBody B (var 31) (var 32))) C using 1
    simp [subst_lam_fresh, subst_var, rootQueryEntryBody_subst, subst_closed, hB, hfC]
  have h2 : Beta (app (lam 32 (rootQueryEntryBody B C (var 32))) R) (rootQueryEntryBody B C R) := by
    convert Beta.contract 32 (rootQueryEntryBody B C (var 32)) R using 1
    simp [subst_var, rootQueryEntryBody_subst, subst_closed, hB, hC]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) C) R).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) R).trans
  exact (Relation.ReflTransGen.single h2)

def rootQueryBody (T A B : AlphaTerm) : AlphaTerm :=
  (app (app (app zeroTestTerm A) (app (app (app listRecursorTerm (app rootQueryEntryTerm B)) (numeral 0)) T)) (numeral 0))

theorem rootQueryBody_fv (T A B : AlphaTerm) :
    (rootQueryBody T A B).fv = T.fv ∪ A.fv ∪ B.fv := by
  ext x
  simp only [rootQueryBody, fv_app, (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (listRecursorTerm).fv = ∅ from listRecursorTerm_closed), (show (rootQueryEntryTerm).fv = ∅ from rootQueryEntryTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem rootQueryBody_subst (T A B W : AlphaTerm) (x : ℕ) :
    (rootQueryBody T A B).subst x W =
      rootQueryBody (T.subst x W) (A.subst x W) (B.subst x W) := by
  simp only [rootQueryBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ listRecursorTerm_closed, subst_closed _ _ _ rootQueryEntryTerm_closed ,subst_closed _ _ _ (numeral_closed 0)]

def rootQueryTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (rootQueryBody (var 30) (var 31) (var 32)))))

@[simp] theorem rootQueryTerm_closed : rootQueryTerm.Closed := by
  unfold rootQueryTerm Closed
  simp only [fv_lam, rootQueryBody_fv, fv_var]
  decide

theorem rootQueryTerm_start {T A B : AlphaTerm}
    (hT : T.Closed) (hA : A.Closed) (hB : B.Closed) :
    Relation.ReflTransGen Beta (app (app (app rootQueryTerm T) A) B)
      (rootQueryBody T A B) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfT : T.fv = ∅ := hT
  have hfA : A.fv = ∅ := hA
  have hfB : B.fv = ∅ := hB
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (rootQueryBody (var 30) (var 31) (var 32))))) T) (lam 31 (lam 32 (rootQueryBody T (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (rootQueryBody (var 30) (var 31) (var 32)))) T using 1
    simp [subst_lam_fresh, subst_var, rootQueryBody_subst, hfT]
  have h1 : Beta (app (lam 31 (lam 32 (rootQueryBody T (var 31) (var 32)))) A) (lam 32 (rootQueryBody T A (var 32))) := by
    convert Beta.contract 31 (lam 32 (rootQueryBody T (var 31) (var 32))) A using 1
    simp [subst_lam_fresh, subst_var, rootQueryBody_subst, subst_closed, hT, hfA]
  have h2 : Beta (app (lam 32 (rootQueryBody T A (var 32))) B) (rootQueryBody T A B) := by
    convert Beta.contract 32 (rootQueryBody T A (var 32)) B using 1
    simp [subst_var, rootQueryBody_subst, subst_closed, hT, hA]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) A) B).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) B).trans
  exact (Relation.ReflTransGen.single h2)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Put
    $$\LambdaQueryReductListCode{t}{M}:=
    \LambdaListCode{\ListMap{\LambdaSyntaxCode{\cdot}}{\LambdaQuerySuccessors{t}{M}}}.$$
    Keep the variable handler $V$ and left-context map $E$ from §{sec:lambda-one-step-programs}. For applications and abstractions define
    $$\begin{aligned}
    J(t,a,b,l,r)&:=\LambdaListAppend\\
     &\quad\bigl(\LambdaListAppend\,(\LambdaRootQueryProgram\,t\,a\,b)
           (\LambdaListMap\,(Eb)\,l)\bigr)\\
     &\quad\bigl(\LambdaListMap\,(\LambdaTaggedCode{1}\,a)\,r\bigr),\\
    A_0&:=\lambdaab{t}{\lambdaab{a}{\lambdaab{b}{\lambdaab{l}{\lambdaab{r}{
     \LambdaNumericPair\,(\LambdaTaggedCode{1}\,a\,b)\,J(t,a,b,l,r)}}}}},\\
    L_0&:=\lambdaab{i}{\lambdaab{a}{\lambdaab{l}{
     \LambdaNumericPair\,(\LambdaTaggedCode{2}\,i\,a)
     (\LambdaZeroTest\,i\,\ChurchNumeral{0}
     (\LambdaListMap\,(\LambdaTaggedCode{2}\,i)\,l))}}}.
    \end{aligned}$$
    The state keeps the original syntax code together with the query-reduct list code. The application handler concatenates the root, left and right lists in that order. The abstraction handler returns an empty query list when its binder is $x_0$; otherwise it restores the binder around every body query reduct.
-/
def queryApplicationBody (T A B L R : AlphaTerm) : AlphaTerm :=
  (app (app numericalPairTerm (app (app applicationCodeTerm A) B)) (app (app listAppendTerm (app (app listAppendTerm (app (app (app rootQueryTerm T) A) B)) (app (app listMapTerm (app leftReductMapTerm B)) L))) (app (app listMapTerm (app applicationCodeTerm A)) R)))

theorem queryApplicationBody_fv (T A B L R : AlphaTerm) :
    (queryApplicationBody T A B L R).fv = T.fv ∪ A.fv ∪ B.fv ∪ L.fv ∪ R.fv := by
  ext x
  simp only [queryApplicationBody, fv_app, (show (numericalPairTerm).fv = ∅ from numericalPairTerm_closed), (show (applicationCodeTerm).fv = ∅ from applicationCode_closed), (show (listAppendTerm).fv = ∅ from listAppendTerm_closed), (show (rootQueryTerm).fv = ∅ from rootQueryTerm_closed), (show (listMapTerm).fv = ∅ from listMapTerm_closed), (show (leftReductMapTerm).fv = ∅ from leftReductMapTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem queryApplicationBody_subst (T A B L R W : AlphaTerm) (x : ℕ) :
    (queryApplicationBody T A B L R).subst x W =
      queryApplicationBody (T.subst x W) (A.subst x W) (B.subst x W) (L.subst x W) (R.subst x W) := by
  simp only [queryApplicationBody, subst_app, subst_closed _ _ _ numericalPairTerm_closed, subst_closed _ _ _ applicationCode_closed, subst_closed _ _ _ listAppendTerm_closed, subst_closed _ _ _ rootQueryTerm_closed, subst_closed _ _ _ listMapTerm_closed, subst_closed _ _ _ leftReductMapTerm_closed]

def queryApplicationTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (lam 34 (queryApplicationBody (var 30) (var 31) (var 32) (var 33) (var 34)))))))

@[simp] theorem queryApplicationTerm_closed : queryApplicationTerm.Closed := by
  unfold queryApplicationTerm Closed
  simp only [fv_lam, queryApplicationBody_fv, fv_var]
  decide

theorem queryApplicationTerm_start {T A B L R : AlphaTerm}
    (hT : T.Closed) (hA : A.Closed) (hB : B.Closed) (hL : L.Closed) (hR : R.Closed) :
    Relation.ReflTransGen Beta (app (app (app (app (app queryApplicationTerm T) A) B) L) R)
      (queryApplicationBody T A B L R) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfT : T.fv = ∅ := hT
  have hfA : A.fv = ∅ := hA
  have hfB : B.fv = ∅ := hB
  have hfL : L.fv = ∅ := hL
  have hfR : R.fv = ∅ := hR
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (lam 34 (queryApplicationBody (var 30) (var 31) (var 32) (var 33) (var 34))))))) T) (lam 31 (lam 32 (lam 33 (lam 34 (queryApplicationBody T (var 31) (var 32) (var 33) (var 34)))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (lam 34 (queryApplicationBody (var 30) (var 31) (var 32) (var 33) (var 34)))))) T using 1
    simp [subst_lam_fresh, subst_var, queryApplicationBody_subst, hfT]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (lam 34 (queryApplicationBody T (var 31) (var 32) (var 33) (var 34)))))) A) (lam 32 (lam 33 (lam 34 (queryApplicationBody T A (var 32) (var 33) (var 34))))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (lam 34 (queryApplicationBody T (var 31) (var 32) (var 33) (var 34))))) A using 1
    simp [subst_lam_fresh, subst_var, queryApplicationBody_subst, subst_closed, hT, hfA]
  have h2 : Beta (app (lam 32 (lam 33 (lam 34 (queryApplicationBody T A (var 32) (var 33) (var 34))))) B) (lam 33 (lam 34 (queryApplicationBody T A B (var 33) (var 34)))) := by
    convert Beta.contract 32 (lam 33 (lam 34 (queryApplicationBody T A (var 32) (var 33) (var 34)))) B using 1
    simp [subst_lam_fresh, subst_var, queryApplicationBody_subst, subst_closed, hT, hA, hfB]
  have h3 : Beta (app (lam 33 (lam 34 (queryApplicationBody T A B (var 33) (var 34)))) L) (lam 34 (queryApplicationBody T A B L (var 34))) := by
    convert Beta.contract 33 (lam 34 (queryApplicationBody T A B (var 33) (var 34))) L using 1
    simp [subst_lam_fresh, subst_var, queryApplicationBody_subst, subst_closed, hT, hA, hB, hfL]
  have h4 : Beta (app (lam 34 (queryApplicationBody T A B L (var 34))) R) (queryApplicationBody T A B L R) := by
    convert Beta.contract 34 (queryApplicationBody T A B L (var 34)) R using 1
    simp [subst_var, queryApplicationBody_subst, subst_closed, hT, hA, hB, hL]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) A) B) L) R).trans
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) B) L) R).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h2) L) R).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h3) R).trans
  exact (Relation.ReflTransGen.single h4)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: prose
  excerpt: |
    Extract the state fields and assemble the programs:
    $$\begin{aligned}
    A&:=\lambdaab{t}{\lambdaab{s}{\lambdaab{u}{
     A_0t(\LambdaNumericProjection{1}\,s)(\LambdaNumericProjection{1}\,u)
     (\LambdaNumericProjection{2}\,s)(\LambdaNumericProjection{2}\,u)}}},\\
    L&:=\lambdaab{i}{\lambdaab{s}{
     L_0i(\LambdaNumericProjection{1}\,s)(\LambdaNumericProjection{2}\,s)}},\\
    \LambdaQueryReductProgram&:=\lambdaab{t}{\lambdaab{e}{
     \LambdaNumericProjection{2}(\LambdaSyntaxRecursor\,V\,(At)\,L\,e)}},\\
    \LambdaInputReductProgram&:=\lambdaab{t}{\lambdaab{e}{
     \LambdaListAppend\,(\LambdaReductProgram\,e)(\LambdaQueryReductProgram\,t\,e)}},\\
    \LambdaInputStepTest&:=\lambdaab{t}{\lambdaab{e}{\lambdaab{d}{
     \LambdaListMember\,d\,(\LambdaInputReductProgram\,t\,e)}}}.
    \end{aligned}$$
    All abbreviations are expanded within the indicated abstractions. Every displayed program is closed. The full reduct list concatenates the beta list with the query list, and the last program tests membership of the target code.
-/
def queryApplicationHandlerBody (T S U : AlphaTerm) : AlphaTerm :=
  (app (app (app (app (app queryApplicationTerm T) (app (numericalProjectionTerm true) S)) (app (numericalProjectionTerm true) U)) (app (numericalProjectionTerm false) S)) (app (numericalProjectionTerm false) U))

theorem queryApplicationHandlerBody_fv (T S U : AlphaTerm) :
    (queryApplicationHandlerBody T S U).fv = T.fv ∪ S.fv ∪ U.fv := by
  ext x
  simp only [queryApplicationHandlerBody, fv_app, (show (queryApplicationTerm).fv = ∅ from queryApplicationTerm_closed), (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem queryApplicationHandlerBody_subst (T S U W : AlphaTerm) (x : ℕ) :
    (queryApplicationHandlerBody T S U).subst x W =
      queryApplicationHandlerBody (T.subst x W) (S.subst x W) (U.subst x W) := by
  simp only [queryApplicationHandlerBody, subst_app, subst_closed _ _ _ queryApplicationTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed true), subst_closed _ _ _ (numericalProjectionTerm_closed false)]

def queryApplicationHandlerTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (queryApplicationHandlerBody (var 30) (var 31) (var 32)))))

@[simp] theorem queryApplicationHandlerTerm_closed : queryApplicationHandlerTerm.Closed := by
  unfold queryApplicationHandlerTerm Closed
  simp only [fv_lam, queryApplicationHandlerBody_fv, fv_var]
  decide

theorem queryApplicationHandlerTerm_start {T S U : AlphaTerm}
    (hT : T.Closed) (hS : S.Closed) (hU : U.Closed) :
    Relation.ReflTransGen Beta (app (app (app queryApplicationHandlerTerm T) S) U)
      (queryApplicationHandlerBody T S U) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfT : T.fv = ∅ := hT
  have hfS : S.fv = ∅ := hS
  have hfU : U.fv = ∅ := hU
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (queryApplicationHandlerBody (var 30) (var 31) (var 32))))) T) (lam 31 (lam 32 (queryApplicationHandlerBody T (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (queryApplicationHandlerBody (var 30) (var 31) (var 32)))) T using 1
    simp [subst_lam_fresh, subst_var, queryApplicationHandlerBody_subst, hfT]
  have h1 : Beta (app (lam 31 (lam 32 (queryApplicationHandlerBody T (var 31) (var 32)))) S) (lam 32 (queryApplicationHandlerBody T S (var 32))) := by
    convert Beta.contract 31 (lam 32 (queryApplicationHandlerBody T (var 31) (var 32))) S using 1
    simp [subst_lam_fresh, subst_var, queryApplicationHandlerBody_subst, subst_closed, hT, hfS]
  have h2 : Beta (app (lam 32 (queryApplicationHandlerBody T S (var 32))) U) (queryApplicationHandlerBody T S U) := by
    convert Beta.contract 32 (queryApplicationHandlerBody T S (var 32)) U using 1
    simp [subst_var, queryApplicationHandlerBody_subst, subst_closed, hT, hS]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) S) U).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) U).trans
  exact (Relation.ReflTransGen.single h2)

def queryAbstractionBody (I A L : AlphaTerm) : AlphaTerm :=
  (app (app numericalPairTerm (app (app abstractionCodeTerm I) A)) (app (app (app zeroTestTerm I) (numeral 0)) (app (app listMapTerm (app abstractionCodeTerm I)) L)))

theorem queryAbstractionBody_fv (I A L : AlphaTerm) :
    (queryAbstractionBody I A L).fv = I.fv ∪ A.fv ∪ L.fv := by
  ext x
  simp only [queryAbstractionBody, fv_app, (show (numericalPairTerm).fv = ∅ from numericalPairTerm_closed), (show (abstractionCodeTerm).fv = ∅ from abstractionCode_closed), (show (zeroTestTerm).fv = ∅ from zeroTestTerm_closed), (show (listMapTerm).fv = ∅ from listMapTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem queryAbstractionBody_subst (I A L W : AlphaTerm) (x : ℕ) :
    (queryAbstractionBody I A L).subst x W =
      queryAbstractionBody (I.subst x W) (A.subst x W) (L.subst x W) := by
  simp only [queryAbstractionBody, subst_app, subst_closed _ _ _ numericalPairTerm_closed, subst_closed _ _ _ abstractionCode_closed, subst_closed _ _ _ zeroTestTerm_closed, subst_closed _ _ _ listMapTerm_closed ,subst_closed _ _ _ (numeral_closed 0)]

def queryAbstractionTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (queryAbstractionBody (var 30) (var 31) (var 32)))))

@[simp] theorem queryAbstractionTerm_closed : queryAbstractionTerm.Closed := by
  unfold queryAbstractionTerm Closed
  simp only [fv_lam, queryAbstractionBody_fv, fv_var]
  decide

theorem queryAbstractionTerm_start {I A L : AlphaTerm}
    (hI : I.Closed) (hA : A.Closed) (hL : L.Closed) :
    Relation.ReflTransGen Beta (app (app (app queryAbstractionTerm I) A) L)
      (queryAbstractionBody I A L) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfI : I.fv = ∅ := hI
  have hfA : A.fv = ∅ := hA
  have hfL : L.fv = ∅ := hL
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (queryAbstractionBody (var 30) (var 31) (var 32))))) I) (lam 31 (lam 32 (queryAbstractionBody I (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (queryAbstractionBody (var 30) (var 31) (var 32)))) I using 1
    simp [subst_lam_fresh, subst_var, queryAbstractionBody_subst, hfI]
  have h1 : Beta (app (lam 31 (lam 32 (queryAbstractionBody I (var 31) (var 32)))) A) (lam 32 (queryAbstractionBody I A (var 32))) := by
    convert Beta.contract 31 (lam 32 (queryAbstractionBody I (var 31) (var 32))) A using 1
    simp [subst_lam_fresh, subst_var, queryAbstractionBody_subst, subst_closed, hI, hfA]
  have h2 : Beta (app (lam 32 (queryAbstractionBody I A (var 32))) L) (queryAbstractionBody I A L) := by
    convert Beta.contract 32 (queryAbstractionBody I A (var 32)) L using 1
    simp [subst_var, queryAbstractionBody_subst, subst_closed, hI, hA]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) A) L).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) L).trans
  exact (Relation.ReflTransGen.single h2)

def queryAbstractionHandlerBody (I S : AlphaTerm) : AlphaTerm :=
  (app (app (app queryAbstractionTerm I) (app (numericalProjectionTerm true) S)) (app (numericalProjectionTerm false) S))

theorem queryAbstractionHandlerBody_fv (I S : AlphaTerm) :
    (queryAbstractionHandlerBody I S).fv = I.fv ∪ S.fv := by
  ext x
  simp only [queryAbstractionHandlerBody, fv_app, (show (queryAbstractionTerm).fv = ∅ from queryAbstractionTerm_closed), (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem queryAbstractionHandlerBody_subst (I S W : AlphaTerm) (x : ℕ) :
    (queryAbstractionHandlerBody I S).subst x W =
      queryAbstractionHandlerBody (I.subst x W) (S.subst x W) := by
  simp only [queryAbstractionHandlerBody, subst_app, subst_closed _ _ _ queryAbstractionTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed true), subst_closed _ _ _ (numericalProjectionTerm_closed false)]

def queryAbstractionHandlerTerm : AlphaTerm := (lam 30 (lam 31 (queryAbstractionHandlerBody (var 30) (var 31))))

@[simp] theorem queryAbstractionHandlerTerm_closed : queryAbstractionHandlerTerm.Closed := by
  unfold queryAbstractionHandlerTerm Closed
  simp only [fv_lam, queryAbstractionHandlerBody_fv, fv_var]
  decide

theorem queryAbstractionHandlerTerm_start {I S : AlphaTerm}
    (hI : I.Closed) (hS : S.Closed) :
    Relation.ReflTransGen Beta (app (app queryAbstractionHandlerTerm I) S)
      (queryAbstractionHandlerBody I S) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfI : I.fv = ∅ := hI
  have hfS : S.fv = ∅ := hS
  have h0 : Beta (app (lam 30 (lam 31 (queryAbstractionHandlerBody (var 30) (var 31)))) I) (lam 31 (queryAbstractionHandlerBody I (var 31))) := by
    convert Beta.contract 30 (lam 31 (queryAbstractionHandlerBody (var 30) (var 31))) I using 1
    simp [subst_lam_fresh, subst_var, queryAbstractionHandlerBody_subst, hfI]
  have h1 : Beta (app (lam 31 (queryAbstractionHandlerBody I (var 31))) S) (queryAbstractionHandlerBody I S) := by
    convert Beta.contract 31 (queryAbstractionHandlerBody I (var 31)) S using 1
    simp [subst_var, queryAbstractionHandlerBody_subst, subst_closed, hI]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) S).trans
  exact (Relation.ReflTransGen.single h1)

def querySuccessorsBody (T E : AlphaTerm) : AlphaTerm :=
  (app (numericalProjectionTerm false) (app (app (app (app syntaxRecursorTerm reductVariableTerm) (app queryApplicationHandlerTerm T)) queryAbstractionHandlerTerm) E))

theorem querySuccessorsBody_fv (T E : AlphaTerm) :
    (querySuccessorsBody T E).fv = T.fv ∪ E.fv := by
  ext x
  simp only [querySuccessorsBody, fv_app, (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)), (show (syntaxRecursorTerm).fv = ∅ from syntaxRecursorTerm_closed), (show (reductVariableTerm).fv = ∅ from reductVariableTerm_closed), (show (queryApplicationHandlerTerm).fv = ∅ from queryApplicationHandlerTerm_closed), (show (queryAbstractionHandlerTerm).fv = ∅ from queryAbstractionHandlerTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem querySuccessorsBody_subst (T E W : AlphaTerm) (x : ℕ) :
    (querySuccessorsBody T E).subst x W =
      querySuccessorsBody (T.subst x W) (E.subst x W) := by
  simp only [querySuccessorsBody, subst_app, subst_closed _ _ _ (numericalProjectionTerm_closed false), subst_closed _ _ _ syntaxRecursorTerm_closed, subst_closed _ _ _ reductVariableTerm_closed, subst_closed _ _ _ queryApplicationHandlerTerm_closed, subst_closed _ _ _ queryAbstractionHandlerTerm_closed]

def querySuccessorsTerm : AlphaTerm := (lam 30 (lam 31 (querySuccessorsBody (var 30) (var 31))))

@[simp] theorem querySuccessorsTerm_closed : querySuccessorsTerm.Closed := by
  unfold querySuccessorsTerm Closed
  simp only [fv_lam, querySuccessorsBody_fv, fv_var]
  decide

theorem querySuccessorsTerm_start {T E : AlphaTerm}
    (hT : T.Closed) (hE : E.Closed) :
    Relation.ReflTransGen Beta (app (app querySuccessorsTerm T) E)
      (querySuccessorsBody T E) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfT : T.fv = ∅ := hT
  have hfE : E.fv = ∅ := hE
  have h0 : Beta (app (lam 30 (lam 31 (querySuccessorsBody (var 30) (var 31)))) T) (lam 31 (querySuccessorsBody T (var 31))) := by
    convert Beta.contract 30 (lam 31 (querySuccessorsBody (var 30) (var 31))) T using 1
    simp [subst_lam_fresh, subst_var, querySuccessorsBody_subst, hfT]
  have h1 : Beta (app (lam 31 (querySuccessorsBody T (var 31))) E) (querySuccessorsBody T E) := by
    convert Beta.contract 31 (querySuccessorsBody T (var 31)) E using 1
    simp [subst_var, querySuccessorsBody_subst, subst_closed, hT]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) E).trans
  exact (Relation.ReflTransGen.single h1)

def inputSuccessorsBody (T E : AlphaTerm) : AlphaTerm :=
  (app (app listAppendTerm (app betaSuccessorsTerm E)) (app (app querySuccessorsTerm T) E))

theorem inputSuccessorsBody_fv (T E : AlphaTerm) :
    (inputSuccessorsBody T E).fv = T.fv ∪ E.fv := by
  ext x
  simp only [inputSuccessorsBody, fv_app, (show (listAppendTerm).fv = ∅ from listAppendTerm_closed), (show (betaSuccessorsTerm).fv = ∅ from betaSuccessorsTerm_closed), (show (querySuccessorsTerm).fv = ∅ from querySuccessorsTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem inputSuccessorsBody_subst (T E W : AlphaTerm) (x : ℕ) :
    (inputSuccessorsBody T E).subst x W =
      inputSuccessorsBody (T.subst x W) (E.subst x W) := by
  simp only [inputSuccessorsBody, subst_app, subst_closed _ _ _ listAppendTerm_closed, subst_closed _ _ _ betaSuccessorsTerm_closed, subst_closed _ _ _ querySuccessorsTerm_closed]

def inputSuccessorsTerm : AlphaTerm := (lam 30 (lam 31 (inputSuccessorsBody (var 30) (var 31))))

@[simp] theorem inputSuccessorsTerm_closed : inputSuccessorsTerm.Closed := by
  unfold inputSuccessorsTerm Closed
  simp only [fv_lam, inputSuccessorsBody_fv, fv_var]
  decide

theorem inputSuccessorsTerm_start {T E : AlphaTerm}
    (hT : T.Closed) (hE : E.Closed) :
    Relation.ReflTransGen Beta (app (app inputSuccessorsTerm T) E)
      (inputSuccessorsBody T E) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfT : T.fv = ∅ := hT
  have hfE : E.fv = ∅ := hE
  have h0 : Beta (app (lam 30 (lam 31 (inputSuccessorsBody (var 30) (var 31)))) T) (lam 31 (inputSuccessorsBody T (var 31))) := by
    convert Beta.contract 30 (lam 31 (inputSuccessorsBody (var 30) (var 31))) T using 1
    simp [subst_lam_fresh, subst_var, inputSuccessorsBody_subst, hfT]
  have h1 : Beta (app (lam 31 (inputSuccessorsBody T (var 31))) E) (inputSuccessorsBody T E) := by
    convert Beta.contract 31 (inputSuccessorsBody T (var 31)) E using 1
    simp [subst_var, inputSuccessorsBody_subst, subst_closed, hT]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) E).trans
  exact (Relation.ReflTransGen.single h1)

def inputStepTestBody (T E D : AlphaTerm) : AlphaTerm :=
  (app (app listMemberTerm D) (app (app inputSuccessorsTerm T) E))

theorem inputStepTestBody_fv (T E D : AlphaTerm) :
    (inputStepTestBody T E D).fv = T.fv ∪ E.fv ∪ D.fv := by
  ext x
  simp only [inputStepTestBody, fv_app, (show (listMemberTerm).fv = ∅ from listMemberTerm_closed), (show (inputSuccessorsTerm).fv = ∅ from inputSuccessorsTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem inputStepTestBody_subst (T E D W : AlphaTerm) (x : ℕ) :
    (inputStepTestBody T E D).subst x W =
      inputStepTestBody (T.subst x W) (E.subst x W) (D.subst x W) := by
  simp only [inputStepTestBody, subst_app, subst_closed _ _ _ listMemberTerm_closed, subst_closed _ _ _ inputSuccessorsTerm_closed]

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We implement the finite-table reduction tests by closed lambda terms. At this stage the answer table is numerical data:
    the programs inspect the stored pairs without querying any input name. Agreement of these stored answers with the actual
    name is the separate finite check in §{sec:lambda-input-certificates}. Choose the distinguished input variable to be
    $o=x_0$, whose syntax code is zero. All other syntax codes are positive.
-/
def inputStepTestTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (inputStepTestBody (var 30) (var 31) (var 32)))))

@[simp] theorem inputStepTestTerm_closed : inputStepTestTerm.Closed := by
  unfold inputStepTestTerm Closed
  simp only [fv_lam, inputStepTestBody_fv, fv_var]
  decide

theorem inputStepTestTerm_start {T E D : AlphaTerm}
    (hT : T.Closed) (hE : E.Closed) (hD : D.Closed) :
    Relation.ReflTransGen Beta (app (app (app inputStepTestTerm T) E) D)
      (inputStepTestBody T E D) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfT : T.fv = ∅ := hT
  have hfE : E.fv = ∅ := hE
  have hfD : D.fv = ∅ := hD
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (inputStepTestBody (var 30) (var 31) (var 32))))) T) (lam 31 (lam 32 (inputStepTestBody T (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (inputStepTestBody (var 30) (var 31) (var 32)))) T using 1
    simp [subst_lam_fresh, subst_var, inputStepTestBody_subst, hfT]
  have h1 : Beta (app (lam 31 (lam 32 (inputStepTestBody T (var 31) (var 32)))) E) (lam 32 (inputStepTestBody T E (var 32))) := by
    convert Beta.contract 31 (lam 32 (inputStepTestBody T (var 31) (var 32))) E using 1
    simp [subst_lam_fresh, subst_var, inputStepTestBody_subst, subst_closed, hT, hfE]
  have h2 : Beta (app (lam 32 (inputStepTestBody T E (var 32))) D) (inputStepTestBody T E D) := by
    convert Beta.contract 32 (inputStepTestBody T E (var 32)) D using 1
    simp [subst_var, inputStepTestBody_subst, subst_closed, hT, hE]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) E) D).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) D).trans
  exact (Relation.ReflTransGen.single h2)


def queryRootCodes (t : Term.AnswerTable) (M N : Term) : List ℕ :=
  (t.filterMap (fun a => if M = .var 0 ∧ N = Term.churchNumeral a.1 then
    some (Term.churchNumeral a.2) else none)).map Term.code

def queryCodes (t : Term.AnswerTable) (M : Term) : List ℕ :=
  (Term.querySuccessors t M).map Term.code

def queryStateCode (t : Term.AnswerTable) (M : Term) : ℕ :=
  Nat.pair M.code (NatListCode.encode (queryCodes t M))

theorem rootQueryKeepTerm_apply (N : Term) (i v r : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app (app rootQueryKeepTerm (numeral N.code)) (numeral i)) (numeral v)) (numeral r))
      (numeral (if N = Term.churchNumeral i then Nat.pair (Term.churchNumeral v).code r + 1 else r)) := by
  apply (rootQueryKeepTerm_start (numeral_closed _) (numeral_closed _)
    (numeral_closed _) (numeral_closed _)).trans
  unfold rootQueryKeepBody
  have he := (beta_steps_app_right (app equalityTerm (numeral N.code)) (numeralCodeTerm_apply i)).trans
    (equalityTerm_apply N.code (Term.churchNumeral i).code)
  have heq : N.code = (Term.churchNumeral i).code ↔ N = Term.churchNumeral i :=
    Term.code_injective.eq_iff
  simp only [heq] at he
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm he) _) _).trans
  by_cases hn : N = Term.churchNumeral i
  · simp only [hn, ite_true]
    apply (branch_succ 0 _ _).trans
    exact (beta_steps_app_left (beta_steps_app_right listConsTerm (numeralCodeTerm_apply v)) _).trans
      (listConsTerm_apply _ r)
  · simp only [hn, ite_false]
    exact branch_zero _ _ (by rw [numeral_closed]; simp)

theorem rootQueryEntryTerm_apply (N : Term) (a r : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app rootQueryEntryTerm (numeral N.code)) (numeral a)) (numeral r))
      (numeral (if N = Term.churchNumeral (Nat.unpair a).1 then
        Nat.pair (Term.churchNumeral (Nat.unpair a).2).code r + 1 else r)) := by
  apply (rootQueryEntryTerm_start (numeral_closed _) (numeral_closed _) (numeral_closed _)).trans
  exact (beta_steps_app_left (beta_steps_app
    (beta_steps_app_right (app rootQueryKeepTerm (numeral N.code)) (numericalProjectionTerm_apply true a))
    (numericalProjectionTerm_apply false a)) (numeral r)).trans
    (rootQueryKeepTerm_apply N _ _ r)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For the root list, induct on the table. The empty table gives the empty-list code. At a table entry, numerical projections recover the proposed address and answer. The numeral-code program and injectivity of syntax coding make numerical equality exactly the required syntactic equality. Depending on this test, the list handler either retains the tail or prepends the answer's numeral code. Zero testing of the operator code restricts this scan to the input variable. This proves the root-list formula with its original order and duplicates.
-/
theorem rootQueryTerm_code (t : Term.AnswerTable) (M N : Term) :
    Relation.ReflTransGen Beta
      (app (app (app rootQueryTerm (numeral (Term.answerTableCode t))) (numeral M.code)) (numeral N.code))
      (numeral (NatListCode.encode (queryRootCodes t M N))) := by
  apply (rootQueryTerm_start (numeral_closed _) (numeral_closed _) (numeral_closed _)).trans
  unfold rootQueryBody
  by_cases hM : M = .var 0
  · subst M
    have hclosed := closed_app
      (closed_app (closed_app listRecursorTerm_closed
        (closed_app rootQueryEntryTerm_closed (numeral_closed N.code))) (numeral_closed 0))
      (numeral_closed (Term.answerTableCode t))
    apply (branch_zero _ _ (by rw [hclosed]; simp)).trans
    have h := listRecursorTerm_apply
      (closed_app rootQueryEntryTerm_closed (numeral_closed N.code)) (numeral_closed 0)
      (fun xs => numeral (NatListCode.encode (queryRootCodes (xs.map Nat.unpair) (.var 0) N)))
      (by rfl) ?_ (t.map (fun a => Nat.pair a.1 a.2))
    · simpa [Term.answerTableCode, List.map_map, Function.comp_def] using h
    · intro a xs
      have h := rootQueryEntryTerm_apply N a
        (NatListCode.encode (queryRootCodes (xs.map Nat.unpair) (.var 0) N))
      by_cases hn : N = Term.churchNumeral (Nat.unpair a).1
      · simpa [queryRootCodes, List.filterMap_cons, hn, NatListCode.encode] using h
      · simpa [queryRootCodes, List.filterMap_cons, hn] using h
  · have hc : M.code ≠ 0 := by
      intro he
      exact hM (Term.code_injective (show M.code = (Term.var 0).code from he))
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hc
    rw [hk]
    simpa [queryRootCodes, hM, NatListCode.encode] using
      (branch_succ k
        (app (app (app listRecursorTerm (app rootQueryEntryTerm (numeral N.code))) (numeral 0))
          (numeral (Term.answerTableCode t))) (numeral 0))

private theorem map_left_reducts (N : Term) (xs : List Term) :
    Relation.ReflTransGen Beta
      (app (app listMapTerm (app leftReductMapTerm (numeral N.code)))
        (numeral (NatListCode.encode (xs.map Term.code))))
      (numeral (NatListCode.encode ((xs.map (fun M => Term.app M N)).map Term.code))) := by
  have h := listMapTerm_code (closed_app leftReductMapTerm_closed (numeral_closed N.code))
    (fun c => 3 * Nat.pair c N.code + 1) (leftReductMapTerm_apply N.code) (xs.map Term.code)
  simpa only [List.map_map, Function.comp_def, Term.code] using h

private theorem map_right_reducts (M : Term) (xs : List Term) :
    Relation.ReflTransGen Beta
      (app (app listMapTerm (app applicationCodeTerm (numeral M.code)))
        (numeral (NatListCode.encode (xs.map Term.code))))
      (numeral (NatListCode.encode ((xs.map (Term.app M)).map Term.code))) := by
  have h := listMapTerm_code (closed_app applicationCode_closed (numeral_closed M.code))
    (fun c => 3 * Nat.pair M.code c + 1) (taggedPairCodeTerm_apply 1 M.code) (xs.map Term.code)
  simpa only [List.map_map, Function.comp_def, Term.code] using h

private theorem map_abstraction_reducts (x : ℕ) (xs : List Term) :
    Relation.ReflTransGen Beta
      (app (app listMapTerm (app abstractionCodeTerm (numeral x)))
        (numeral (NatListCode.encode (xs.map Term.code))))
      (numeral (NatListCode.encode ((xs.map (Term.lam x)).map Term.code))) := by
  have h := listMapTerm_code (closed_app abstractionCode_closed (numeral_closed x))
    (fun c => 3 * Nat.pair x c + 2) (taggedPairCodeTerm_apply 2 x) (xs.map Term.code)
  simpa only [List.map_map, Function.comp_def, Term.code] using h

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: proof
  excerpt: |
    Now use structural recursion with state
    $$\ChurchNumeral{\NatPair{\LambdaSyntaxCode{M}}{\LambdaQueryReductListCode{t}{M}}}.$$
    The variable case uses the unchanged variable handler. In the application case, projections recover both child codes and both query lists. The root calculation and the two context maps give exactly the defining three lists. The abstraction case splits at binder index zero: zero discards the body query list, and a positive index restores the binder around each body query reduct. Thus the fold gives the required state, and its second projection gives the query list. Concatenation with the beta list gives the full list. Membership testing is exact because syntax coding is injective. Finally, every table and term code decodes, so the inverse coding identities give the arbitrary-code statements. Uniqueness of numeral outputs excludes an incorrect Boolean answer.
    \end{proof}
-/
theorem queryApplicationTerm_code (t : Term.AnswerTable) (M N : Term) :
    Relation.ReflTransGen Beta
      (app (app (app (app (app queryApplicationTerm (numeral (Term.answerTableCode t)))
        (numeral M.code)) (numeral N.code)) (numeral (NatListCode.encode (queryCodes t M))))
        (numeral (NatListCode.encode (queryCodes t N))))
      (numeral (queryStateCode t (.app M N))) := by
  apply (queryApplicationTerm_start (numeral_closed _) (numeral_closed _) (numeral_closed _)
    (numeral_closed _) (numeral_closed _)).trans
  have hleft := (beta_steps_app (beta_steps_app_right listAppendTerm (rootQueryTerm_code t M N))
    (map_left_reducts N (Term.querySuccessors t M))).trans
      (listAppendTerm_code (queryRootCodes t M N)
        (((Term.querySuccessors t M).map (fun M' => Term.app M' N)).map Term.code))
  have hall := (beta_steps_app (beta_steps_app_right listAppendTerm hleft)
    (map_right_reducts M (Term.querySuccessors t N))).trans (listAppendTerm_code _ _)
  have h := (beta_steps_app (beta_steps_app_right numericalPairTerm (applicationCodeTerm_apply M N)) hall).trans
    (numericalPairTerm_apply _ _)
  have he : queryCodes t (.app M N) =
      (queryRootCodes t M N ++ ((Term.querySuccessors t M).map (fun M' => Term.app M' N)).map Term.code) ++
        ((Term.querySuccessors t N).map (Term.app M)).map Term.code := by
    simp only [queryCodes, Term.querySuccessors, queryRootCodes, List.map_append]
  change Relation.ReflTransGen Beta _
    (numeral (Nat.pair (Term.app M N).code (NatListCode.encode (queryCodes t (.app M N)))))
  rw [he]
  simpa only [queryApplicationBody, queryCodes] using h

theorem queryApplicationHandlerTerm_code (t : Term.AnswerTable) (M N : Term) :
    Relation.ReflTransGen Beta
      (app (app (app queryApplicationHandlerTerm (numeral (Term.answerTableCode t)))
        (numeral (queryStateCode t M))) (numeral (queryStateCode t N)))
      (numeral (queryStateCode t (.app M N))) := by
  apply (queryApplicationHandlerTerm_start (numeral_closed _) (numeral_closed _) (numeral_closed _)).trans
  have h := beta_steps_app
    (beta_steps_app
      (beta_steps_app
        (beta_steps_app_right (app queryApplicationTerm (numeral (Term.answerTableCode t)))
          (numericalProjectionTerm_pair true M.code (NatListCode.encode (queryCodes t M))))
        (numericalProjectionTerm_pair true N.code (NatListCode.encode (queryCodes t N))))
      (numericalProjectionTerm_pair false M.code (NatListCode.encode (queryCodes t M))))
    (numericalProjectionTerm_pair false N.code (NatListCode.encode (queryCodes t N)))
  exact h.trans (queryApplicationTerm_code t M N)

theorem queryAbstractionTerm_code (t : Term.AnswerTable) (x : ℕ) (M : Term) :
    Relation.ReflTransGen Beta
      (app (app (app queryAbstractionTerm (numeral x)) (numeral M.code))
        (numeral (NatListCode.encode (queryCodes t M))))
      (numeral (queryStateCode t (.lam x M))) := by
  apply (queryAbstractionTerm_start (numeral_closed _) (numeral_closed _) (numeral_closed _)).trans
  unfold queryAbstractionBody
  have hlist : Relation.ReflTransGen Beta
      (app (app (app zeroTestTerm (numeral x)) (numeral 0))
        (app (app listMapTerm (app abstractionCodeTerm (numeral x)))
          (numeral (NatListCode.encode (queryCodes t M)))))
      (numeral (NatListCode.encode (queryCodes t (.lam x M)))) := by
    cases x with
    | zero =>
      simpa [queryCodes, Term.querySuccessors, NatListCode.encode] using
        branch_zero (numeral 0)
          (app (app listMapTerm (app abstractionCodeTerm (numeral 0)))
            (numeral (NatListCode.encode (queryCodes t M)))) (by rw [numeral_closed]; simp)
    | succ x =>
      apply (branch_succ x _ _).trans
      simpa only [queryCodes, Term.querySuccessors, Nat.succ_ne_zero, ite_false]
        using map_abstraction_reducts (x + 1) (Term.querySuccessors t M)
  exact (beta_steps_app (beta_steps_app_right numericalPairTerm (abstractionCodeTerm_apply x M)) hlist).trans
    (numericalPairTerm_apply _ _)

theorem queryAbstractionHandlerTerm_code (t : Term.AnswerTable) (x : ℕ) (M : Term) :
    Relation.ReflTransGen Beta
      (app (app queryAbstractionHandlerTerm (numeral x)) (numeral (queryStateCode t M)))
      (numeral (queryStateCode t (.lam x M))) := by
  apply (queryAbstractionHandlerTerm_start (numeral_closed _) (numeral_closed _)).trans
  exact (beta_steps_app
    (beta_steps_app_right (app queryAbstractionTerm (numeral x))
      (numericalProjectionTerm_pair true M.code (NatListCode.encode (queryCodes t M))))
    (numericalProjectionTerm_pair false M.code (NatListCode.encode (queryCodes t M)))).trans
    (queryAbstractionTerm_code t x M)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Finite-table step programs
-/
theorem querySuccessorsTerm_code (t : Term.AnswerTable) (M : Term) :
    Relation.ReflTransGen Beta
      (app (app querySuccessorsTerm (numeral (Term.answerTableCode t))) (numeral M.code))
      (numeral (NatListCode.encode ((Term.querySuccessors t M).map Term.code))) := by
  apply (querySuccessorsTerm_start (numeral_closed _) (numeral_closed _)).trans
  have ha := closed_app queryApplicationHandlerTerm_closed (numeral_closed (Term.answerTableCode t))
  have hf := syntaxFold_apply reductVariableTerm_closed ha queryAbstractionHandlerTerm_closed
    (fun M => numeral (queryStateCode t M))
    (fun x => reductVariableTerm_apply x) (queryApplicationHandlerTerm_code t)
    (queryAbstractionHandlerTerm_code t) M
  have hs := (beta_steps_app_left
    (syntaxRecursorTerm_start reductVariableTerm_closed ha queryAbstractionHandlerTerm_closed)
    (numeral M.code)).trans hf
  exact (beta_steps_app_right (numericalProjectionTerm false) hs).trans
    (numericalProjectionTerm_pair false M.code (NatListCode.encode (queryCodes t M)))

theorem querySuccessorsTerm_apply (t e : ℕ) :
    Relation.ReflTransGen Beta (app (app querySuccessorsTerm (numeral t)) (numeral e))
      (numeral (NatListCode.encode
        ((Term.querySuccessors (Term.decodeAnswerTable t) (Term.decode e)).map Term.code))) := by
  simpa only [Term.answerTableCode_decode, Term.code_decode] using
    querySuccessorsTerm_code (Term.decodeAnswerTable t) (Term.decode e)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Finite-table step programs
-/
theorem inputSuccessorsTerm_code (t : Term.AnswerTable) (M : Term) :
    Relation.ReflTransGen Beta
      (app (app inputSuccessorsTerm (numeral (Term.answerTableCode t))) (numeral M.code))
      (numeral (NatListCode.encode ((Term.inputSuccessors t M).map Term.code))) := by
  apply (inputSuccessorsTerm_start (numeral_closed _) (numeral_closed _)).trans
  have h := (beta_steps_app (beta_steps_app_right listAppendTerm (betaSuccessorsTerm_code M))
    (querySuccessorsTerm_code t M)).trans (listAppendTerm_code _ _)
  simpa only [inputSuccessorsBody, Term.inputSuccessors, List.map_append] using h

theorem inputSuccessorsTerm_apply (t e : ℕ) :
    Relation.ReflTransGen Beta (app (app inputSuccessorsTerm (numeral t)) (numeral e))
      (numeral (NatListCode.encode
        ((Term.inputSuccessors (Term.decodeAnswerTable t) (Term.decode e)).map Term.code))) := by
  simpa only [Term.answerTableCode_decode, Term.code_decode] using
    inputSuccessorsTerm_code (Term.decodeAnswerTable t) (Term.decode e)

instance namedInputStepDecidable (t : Term.AnswerTable) (M N : Term) :
    Decidable (Term.InputStep t M N) :=
  decidable_of_iff (N ∈ Term.inputSuccessors t M) (Term.mem_inputSuccessors_iff t M N)

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Finite-table step programs
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We implement the finite-table reduction tests by closed lambda terms. At this stage the answer table is numerical data:
    the programs inspect the stored pairs without querying any input name. Agreement of these stored answers with the actual
    name is the separate finite check in §{sec:lambda-input-certificates}. Choose the distinguished input variable to be
    $o=x_0$, whose syntax code is zero. All other syntax codes are positive.
-/
theorem inputStepTestTerm_code (t : Term.AnswerTable) (M N : Term) :
    Relation.ReflTransGen Beta
      (app (app (app inputStepTestTerm (numeral (Term.answerTableCode t))) (numeral M.code)) (numeral N.code))
      (numeral (if Term.InputStep t M N then 1 else 0)) := by
  apply (inputStepTestTerm_start (numeral_closed _) (numeral_closed _) (numeral_closed _)).trans
  have h := (beta_steps_app_right (app listMemberTerm (numeral N.code)) (inputSuccessorsTerm_code t M)).trans
    (listMemberTerm_code N.code ((Term.inputSuccessors t M).map Term.code))
  have hm : N.code ∈ (Term.inputSuccessors t M).map Term.code ↔ Term.InputStep t M N := by
    rw [← Term.mem_inputSuccessors_iff]
    constructor
    · intro hn
      obtain ⟨P,hp,he⟩ := List.mem_map.mp hn
      exact Term.code_injective he ▸ hp
    · intro hn
      exact List.mem_map.mpr ⟨N,hn,rfl⟩
  simpa only [inputStepTestBody, hm] using h

/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  target: statement
  kind: theorem
  title: Finite-table step programs
-/
theorem inputStepTestTerm_apply (t e d : ℕ) :
    Relation.ReflTransGen Beta
      (app (app (app inputStepTestTerm (numeral t)) (numeral e)) (numeral d))
      (numeral (if Term.InputStep (Term.decodeAnswerTable t) (Term.decode e) (Term.decode d) then 1 else 0)) := by
  simpa only [Term.answerTableCode_decode, Term.code_decode] using
    inputStepTestTerm_code (Term.decodeAnswerTable t) (Term.decode e) (Term.decode d)

end PolishSpaceBook.NamedLambda.AlphaTerm
