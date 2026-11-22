module

public import PolishSpaceBook.LambdaCodeSubstitution
public import PolishSpaceBook.LambdaReductionCertificates

@[expose] public section

/-! # Enumerating all one-step beta reducts by a lambda program

The fold carries the original syntax code together with the numerical list of
reduct codes. The application handler lists root contraction first, then left
and right reductions, in the exact order of `Term.betaSuccessors`.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

private theorem applicationCode_closed : applicationCodeTerm.Closed := taggedPairCodeTerm_closed 1
private theorem abstractionCode_closed : abstractionCodeTerm.Closed := taggedPairCodeTerm_closed 2

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    First define the list contributed by a contraction at the root of an application. Use the abbreviations
    $$\begin{aligned}
    C(a,b)&:=\LambdaListCons\,
     \bigl(\LambdaSubstCode\,(\LambdaSyntaxField{2}\,a)\,(\LambdaSyntaxField{1}\,a)\,b\bigr)
     \,\ChurchNumeral{0},\\
    \LambdaRootReduct&:=\lambdaab{a}{\lambdaab{b}{
     \LambdaSyntaxCase{a}{\ChurchNumeral{0}}{\ChurchNumeral{0}}{C(a,b)}}}.
    \end{aligned}$$
    Expand $C$ inside the abstractions. If the left term is an abstraction, its body and binder are extracted, substitution computes the contracted term, and cons puts its code into a singleton list. A variable or application on the left gives the empty list. In particular, the substitution branch is not evaluated when there is no root redex.
-/
def rootReductBody (A B : AlphaTerm) : AlphaTerm :=
  syntaxCases A (numeral 0) (numeral 0)
    (app (app listConsTerm
      (app (app (app substitutionTerm (app (syntaxFieldTerm false) A))
        (app (syntaxFieldTerm true) A)) B)) (numeral 0))

theorem rootReductBody_fv (A B : AlphaTerm) :
    (rootReductBody A B).fv = A.fv ∪ B.fv := by
  ext x
  simp only [rootReductBody, syntaxCases_fv, fv_app, (show (listConsTerm).fv = ∅ from listConsTerm_closed), (show (substitutionTerm).fv = ∅ from substitutionTerm_closed), (show (syntaxFieldTerm true).fv = ∅ from (syntaxFieldTerm_closed true)), (show (syntaxFieldTerm false).fv = ∅ from (syntaxFieldTerm_closed false)) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem rootReductBody_subst (A B W : AlphaTerm) (x : ℕ) :
    (rootReductBody A B).subst x W =
      rootReductBody (A.subst x W) (B.subst x W) := by
  simp only [rootReductBody, syntaxCases_subst, subst_app, subst_closed _ _ _ listConsTerm_closed, subst_closed _ _ _ substitutionTerm_closed, subst_closed _ _ _ (syntaxFieldTerm_closed true), subst_closed _ _ _ (syntaxFieldTerm_closed false) ,subst_closed _ _ _ (numeral_closed 0)]

def rootReductTerm : AlphaTerm := (lam 30 (lam 31 (rootReductBody (var 30) (var 31))))

@[simp] theorem rootReductTerm_closed : rootReductTerm.Closed := by
  unfold rootReductTerm Closed
  simp only [fv_lam, rootReductBody_fv, fv_var]
  decide

theorem rootReductTerm_start {A B : AlphaTerm}
    (hA : A.Closed) (hB : B.Closed) :
    Relation.ReflTransGen Beta (app (app rootReductTerm A) B)
      (rootReductBody A B) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfA : A.fv = ∅ := hA
  have hfB : B.fv = ∅ := hB
  have h0 : Beta (app (lam 30 (lam 31 (rootReductBody (var 30) (var 31)))) A) (lam 31 (rootReductBody A (var 31))) := by
    convert Beta.contract 30 (lam 31 (rootReductBody (var 30) (var 31))) A using 1

    simp [subst_lam_fresh, subst_var, rootReductBody_subst, hfA]
  have h1 : Beta (app (lam 31 (rootReductBody A (var 31))) B) (rootReductBody A B) := by
    convert Beta.contract 31 (rootReductBody A (var 31)) B using 1

    simp [subst_var, rootReductBody_subst, subst_closed, hA]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) B).trans
  exact (Relation.ReflTransGen.single h1)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    For the internal reductions, define a left-context program and an abbreviation for the combined list:
    $$\begin{aligned}
    E&:=\lambdaab{b}{\lambdaab{c}{\LambdaTaggedCode{1}\,c\,b}},\\
    J(a,b,l,r)&:=\LambdaListAppend\\
     &\quad\bigl(\LambdaListAppend\,(\LambdaRootReduct\,a\,b)
           (\LambdaListMap\,(Eb)\,l)\bigr)\\
     &\quad\bigl(\LambdaListMap\,(\LambdaTaggedCode{1}\,a)\,r\bigr).
    \end{aligned}$$
    The first map restores the unchanged right term around each left reduct; the second restores the unchanged left term around each right reduct. Form the state-building programs
    $$\begin{aligned}
    V&:=\lambdaab{i}{\LambdaNumericPair\,(\LambdaVarCode\,i)\,\ChurchNumeral{0}},\\
    A_0&:=\lambdaab{a}{\lambdaab{b}{\lambdaab{l}{\lambdaab{r}{
     \LambdaNumericPair\,(\LambdaTaggedCode{1}\,a\,b)\,J(a,b,l,r)}}}},\\
    L_0&:=\lambdaab{i}{\lambdaab{a}{\lambdaab{l}{
     \LambdaNumericPair\,(\LambdaTaggedCode{2}\,i\,a)
     (\LambdaListMap\,(\LambdaTaggedCode{2}\,i)\,l)}}}.
    \end{aligned}$$
    Expand $J$ in $A_0$. The variable state records its original code and an empty list. The abstraction state restores its binder around every body reduct.
-/
def leftReductMapBody (B C : AlphaTerm) : AlphaTerm :=
  app (app applicationCodeTerm C) B

theorem leftReductMapBody_fv (B C : AlphaTerm) :
    (leftReductMapBody B C).fv = B.fv ∪ C.fv := by
  ext x
  simp only [leftReductMapBody, fv_app, (show (applicationCodeTerm).fv = ∅ from applicationCode_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem leftReductMapBody_subst (B C W : AlphaTerm) (x : ℕ) :
    (leftReductMapBody B C).subst x W =
      leftReductMapBody (B.subst x W) (C.subst x W) := by
  simp only [leftReductMapBody, subst_app, subst_closed _ _ _ applicationCode_closed]

def leftReductMapTerm : AlphaTerm := (lam 30 (lam 31 (leftReductMapBody (var 30) (var 31))))

@[simp] theorem leftReductMapTerm_closed : leftReductMapTerm.Closed := by
  unfold leftReductMapTerm Closed
  simp only [fv_lam, leftReductMapBody_fv, fv_var]
  decide

theorem leftReductMapTerm_start {B C : AlphaTerm}
    (hB : B.Closed) (hC : C.Closed) :
    Relation.ReflTransGen Beta (app (app leftReductMapTerm B) C)
      (leftReductMapBody B C) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfB : B.fv = ∅ := hB
  have hfC : C.fv = ∅ := hC
  have h0 : Beta (app (lam 30 (lam 31 (leftReductMapBody (var 30) (var 31)))) B) (lam 31 (leftReductMapBody B (var 31))) := by
    convert Beta.contract 30 (lam 31 (leftReductMapBody (var 30) (var 31))) B using 1

    simp [subst_lam_fresh, subst_var, leftReductMapBody_subst, hfB]
  have h1 : Beta (app (lam 31 (leftReductMapBody B (var 31))) C) (leftReductMapBody B C) := by
    convert Beta.contract 31 (leftReductMapBody B (var 31)) C using 1

    simp [subst_var, leftReductMapBody_subst, subst_closed, hB]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) C).trans
  exact (Relation.ReflTransGen.single h1)

def reductVariableBody (I : AlphaTerm) : AlphaTerm :=
  app (app numericalPairTerm (app variableCodeTerm I)) (numeral 0)

theorem reductVariableBody_fv (I : AlphaTerm) :
    (reductVariableBody I).fv = I.fv := by
  ext x
  simp only [reductVariableBody, fv_app, (show (numericalPairTerm).fv = ∅ from numericalPairTerm_closed), (show (variableCodeTerm).fv = ∅ from variableCodeTerm_closed) ,(show (numeral 0).fv = ∅ from numeral_closed 0), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem reductVariableBody_subst (I W : AlphaTerm) (x : ℕ) :
    (reductVariableBody I).subst x W =
      reductVariableBody (I.subst x W) := by
  simp only [reductVariableBody, subst_app, subst_closed _ _ _ numericalPairTerm_closed, subst_closed _ _ _ variableCodeTerm_closed ,subst_closed _ _ _ (numeral_closed 0)]

def reductVariableTerm : AlphaTerm := (lam 30 (reductVariableBody (var 30)))

@[simp] theorem reductVariableTerm_closed : reductVariableTerm.Closed := by
  unfold reductVariableTerm Closed
  simp only [fv_lam, reductVariableBody_fv, fv_var]
  decide

theorem reductVariableTerm_start {I : AlphaTerm}
    (hI : I.Closed) :
    Relation.ReflTransGen Beta (app reductVariableTerm I)
      (reductVariableBody I) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfI : I.fv = ∅ := hI
  have h0 : Beta (app (lam 30 (reductVariableBody (var 30))) I) (reductVariableBody I) := by
    convert Beta.contract 30 (reductVariableBody (var 30)) I using 1

    simp [subst_var, reductVariableBody_subst]
  exact (Relation.ReflTransGen.single h0)

def reductApplicationBody (A B L R : AlphaTerm) : AlphaTerm :=
  app (app numericalPairTerm (app (app applicationCodeTerm A) B))
    (app (app listAppendTerm
      (app (app listAppendTerm (app (app rootReductTerm A) B))
        (app (app listMapTerm (app leftReductMapTerm B)) L)))
      (app (app listMapTerm (app applicationCodeTerm A)) R))

theorem reductApplicationBody_fv (A B L R : AlphaTerm) :
    (reductApplicationBody A B L R).fv = A.fv ∪ B.fv ∪ L.fv ∪ R.fv := by
  ext x
  simp only [reductApplicationBody, fv_app, (show (numericalPairTerm).fv = ∅ from numericalPairTerm_closed), (show (applicationCodeTerm).fv = ∅ from applicationCode_closed), (show (listAppendTerm).fv = ∅ from listAppendTerm_closed), (show (rootReductTerm).fv = ∅ from rootReductTerm_closed), (show (listMapTerm).fv = ∅ from listMapTerm_closed), (show (leftReductMapTerm).fv = ∅ from leftReductMapTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem reductApplicationBody_subst (A B L R W : AlphaTerm) (x : ℕ) :
    (reductApplicationBody A B L R).subst x W =
      reductApplicationBody (A.subst x W) (B.subst x W) (L.subst x W) (R.subst x W) := by
  simp only [reductApplicationBody, subst_app, subst_closed _ _ _ numericalPairTerm_closed, subst_closed _ _ _ applicationCode_closed, subst_closed _ _ _ listAppendTerm_closed, subst_closed _ _ _ rootReductTerm_closed, subst_closed _ _ _ listMapTerm_closed, subst_closed _ _ _ leftReductMapTerm_closed]

def reductApplicationTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (lam 33 (reductApplicationBody (var 30) (var 31) (var 32) (var 33))))))

@[simp] theorem reductApplicationTerm_closed : reductApplicationTerm.Closed := by
  unfold reductApplicationTerm Closed
  simp only [fv_lam, reductApplicationBody_fv, fv_var]
  decide

theorem reductApplicationTerm_start {A B L R : AlphaTerm}
    (hA : A.Closed) (hB : B.Closed) (hL : L.Closed) (hR : R.Closed) :
    Relation.ReflTransGen Beta (app (app (app (app reductApplicationTerm A) B) L) R)
      (reductApplicationBody A B L R) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfA : A.fv = ∅ := hA
  have hfB : B.fv = ∅ := hB
  have hfL : L.fv = ∅ := hL
  have hfR : R.fv = ∅ := hR
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (lam 33 (reductApplicationBody (var 30) (var 31) (var 32) (var 33)))))) A) (lam 31 (lam 32 (lam 33 (reductApplicationBody A (var 31) (var 32) (var 33))))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (lam 33 (reductApplicationBody (var 30) (var 31) (var 32) (var 33))))) A using 1

    simp [subst_lam_fresh, subst_var, reductApplicationBody_subst, hfA]
  have h1 : Beta (app (lam 31 (lam 32 (lam 33 (reductApplicationBody A (var 31) (var 32) (var 33))))) B) (lam 32 (lam 33 (reductApplicationBody A B (var 32) (var 33)))) := by
    convert Beta.contract 31 (lam 32 (lam 33 (reductApplicationBody A (var 31) (var 32) (var 33)))) B using 1

    simp [subst_lam_fresh, subst_var, reductApplicationBody_subst, subst_closed, hA, hfB]
  have h2 : Beta (app (lam 32 (lam 33 (reductApplicationBody A B (var 32) (var 33)))) L) (lam 33 (reductApplicationBody A B L (var 33))) := by
    convert Beta.contract 32 (lam 33 (reductApplicationBody A B (var 32) (var 33))) L using 1

    simp [subst_lam_fresh, subst_var, reductApplicationBody_subst, subst_closed, hA, hB, hfL]
  have h3 : Beta (app (lam 33 (reductApplicationBody A B L (var 33))) R) (reductApplicationBody A B L R) := by
    convert Beta.contract 33 (reductApplicationBody A B L (var 33)) R using 1

    simp [subst_var, reductApplicationBody_subst, subst_closed, hA, hB, hL]
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) B) L) R).trans
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h1) L) R).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h2) R).trans
  exact (Relation.ReflTransGen.single h3)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Extract the two fields of each recursive state and assemble the fold:
    $$\begin{aligned}
    A&:=\lambdaab{s}{\lambdaab{t}{
     A_0(\LambdaNumericProjection{1}\,s)(\LambdaNumericProjection{1}\,t)
     (\LambdaNumericProjection{2}\,s)(\LambdaNumericProjection{2}\,t)}},\\
    L&:=\lambdaab{i}{\lambdaab{s}{
     L_0\,i\,(\LambdaNumericProjection{1}\,s)(\LambdaNumericProjection{2}\,s)}},\\
    \LambdaReductState&:=\LambdaSyntaxFold{V}{A}{L},\\
    \LambdaReductProgram&:=\lambdaab{e}{\LambdaNumericProjection{2}(\LambdaReductState\,e)},\\
    \LambdaBetaStepTest&:=\lambdaab{e}{\lambdaab{d}{
     \LambdaListMember\,d\,(\LambdaReductProgram\,e)}}.
    \end{aligned}$$
    The last program checks membership of the target code in the computed list. All displayed programs are closed.
-/
def reductApplicationHandlerBody (S T : AlphaTerm) : AlphaTerm :=
  app (app (app (app reductApplicationTerm
    (app (numericalProjectionTerm true) S)) (app (numericalProjectionTerm true) T))
      (app (numericalProjectionTerm false) S)) (app (numericalProjectionTerm false) T)

theorem reductApplicationHandlerBody_fv (S T : AlphaTerm) :
    (reductApplicationHandlerBody S T).fv = S.fv ∪ T.fv := by
  ext x
  simp only [reductApplicationHandlerBody, fv_app, (show (reductApplicationTerm).fv = ∅ from reductApplicationTerm_closed), (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem reductApplicationHandlerBody_subst (S T W : AlphaTerm) (x : ℕ) :
    (reductApplicationHandlerBody S T).subst x W =
      reductApplicationHandlerBody (S.subst x W) (T.subst x W) := by
  simp only [reductApplicationHandlerBody, subst_app, subst_closed _ _ _ reductApplicationTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed true), subst_closed _ _ _ (numericalProjectionTerm_closed false)]

def reductApplicationHandlerTerm : AlphaTerm := (lam 30 (lam 31 (reductApplicationHandlerBody (var 30) (var 31))))

@[simp] theorem reductApplicationHandlerTerm_closed : reductApplicationHandlerTerm.Closed := by
  unfold reductApplicationHandlerTerm Closed
  simp only [fv_lam, reductApplicationHandlerBody_fv, fv_var]
  decide

theorem reductApplicationHandlerTerm_start {S T : AlphaTerm}
    (hS : S.Closed) (hT : T.Closed) :
    Relation.ReflTransGen Beta (app (app reductApplicationHandlerTerm S) T)
      (reductApplicationHandlerBody S T) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfS : S.fv = ∅ := hS
  have hfT : T.fv = ∅ := hT
  have h0 : Beta (app (lam 30 (lam 31 (reductApplicationHandlerBody (var 30) (var 31)))) S) (lam 31 (reductApplicationHandlerBody S (var 31))) := by
    convert Beta.contract 30 (lam 31 (reductApplicationHandlerBody (var 30) (var 31))) S using 1

    simp [subst_lam_fresh, subst_var, reductApplicationHandlerBody_subst, hfS]
  have h1 : Beta (app (lam 31 (reductApplicationHandlerBody S (var 31))) T) (reductApplicationHandlerBody S T) := by
    convert Beta.contract 31 (reductApplicationHandlerBody S (var 31)) T using 1

    simp [subst_var, reductApplicationHandlerBody_subst, subst_closed, hS]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) T).trans
  exact (Relation.ReflTransGen.single h1)

def reductAbstractionBody (I A L : AlphaTerm) : AlphaTerm :=
  app (app numericalPairTerm (app (app abstractionCodeTerm I) A))
    (app (app listMapTerm (app abstractionCodeTerm I)) L)

theorem reductAbstractionBody_fv (I A L : AlphaTerm) :
    (reductAbstractionBody I A L).fv = I.fv ∪ A.fv ∪ L.fv := by
  ext x
  simp only [reductAbstractionBody, fv_app, (show (numericalPairTerm).fv = ∅ from numericalPairTerm_closed), (show (abstractionCodeTerm).fv = ∅ from abstractionCode_closed), (show (listMapTerm).fv = ∅ from listMapTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem reductAbstractionBody_subst (I A L W : AlphaTerm) (x : ℕ) :
    (reductAbstractionBody I A L).subst x W =
      reductAbstractionBody (I.subst x W) (A.subst x W) (L.subst x W) := by
  simp only [reductAbstractionBody, subst_app, subst_closed _ _ _ numericalPairTerm_closed, subst_closed _ _ _ abstractionCode_closed, subst_closed _ _ _ listMapTerm_closed]

def reductAbstractionTerm : AlphaTerm := (lam 30 (lam 31 (lam 32 (reductAbstractionBody (var 30) (var 31) (var 32)))))

@[simp] theorem reductAbstractionTerm_closed : reductAbstractionTerm.Closed := by
  unfold reductAbstractionTerm Closed
  simp only [fv_lam, reductAbstractionBody_fv, fv_var]
  decide

theorem reductAbstractionTerm_start {I A L : AlphaTerm}
    (hI : I.Closed) (hA : A.Closed) (hL : L.Closed) :
    Relation.ReflTransGen Beta (app (app (app reductAbstractionTerm I) A) L)
      (reductAbstractionBody I A L) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfI : I.fv = ∅ := hI
  have hfA : A.fv = ∅ := hA
  have hfL : L.fv = ∅ := hL
  have h0 : Beta (app (lam 30 (lam 31 (lam 32 (reductAbstractionBody (var 30) (var 31) (var 32))))) I) (lam 31 (lam 32 (reductAbstractionBody I (var 31) (var 32)))) := by
    convert Beta.contract 30 (lam 31 (lam 32 (reductAbstractionBody (var 30) (var 31) (var 32)))) I using 1

    simp [subst_lam_fresh, subst_var, reductAbstractionBody_subst, hfI]
  have h1 : Beta (app (lam 31 (lam 32 (reductAbstractionBody I (var 31) (var 32)))) A) (lam 32 (reductAbstractionBody I A (var 32))) := by
    convert Beta.contract 31 (lam 32 (reductAbstractionBody I (var 31) (var 32))) A using 1

    simp [subst_lam_fresh, subst_var, reductAbstractionBody_subst, subst_closed, hI, hfA]
  have h2 : Beta (app (lam 32 (reductAbstractionBody I A (var 32))) L) (reductAbstractionBody I A L) := by
    convert Beta.contract 32 (reductAbstractionBody I A (var 32)) L using 1

    simp [subst_var, reductAbstractionBody_subst, subst_closed, hI, hA]
  apply (beta_steps_app_left (beta_steps_app_left (Relation.ReflTransGen.single h0) A) L).trans
  apply (beta_steps_app_left (Relation.ReflTransGen.single h1) L).trans
  exact (Relation.ReflTransGen.single h2)

def reductAbstractionHandlerBody (I S : AlphaTerm) : AlphaTerm :=
  app (app (app reductAbstractionTerm I)
    (app (numericalProjectionTerm true) S)) (app (numericalProjectionTerm false) S)

theorem reductAbstractionHandlerBody_fv (I S : AlphaTerm) :
    (reductAbstractionHandlerBody I S).fv = I.fv ∪ S.fv := by
  ext x
  simp only [reductAbstractionHandlerBody, fv_app, (show (reductAbstractionTerm).fv = ∅ from reductAbstractionTerm_closed), (show (numericalProjectionTerm true).fv = ∅ from (numericalProjectionTerm_closed true)), (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem reductAbstractionHandlerBody_subst (I S W : AlphaTerm) (x : ℕ) :
    (reductAbstractionHandlerBody I S).subst x W =
      reductAbstractionHandlerBody (I.subst x W) (S.subst x W) := by
  simp only [reductAbstractionHandlerBody, subst_app, subst_closed _ _ _ reductAbstractionTerm_closed, subst_closed _ _ _ (numericalProjectionTerm_closed true), subst_closed _ _ _ (numericalProjectionTerm_closed false)]

def reductAbstractionHandlerTerm : AlphaTerm := (lam 30 (lam 31 (reductAbstractionHandlerBody (var 30) (var 31))))

@[simp] theorem reductAbstractionHandlerTerm_closed : reductAbstractionHandlerTerm.Closed := by
  unfold reductAbstractionHandlerTerm Closed
  simp only [fv_lam, reductAbstractionHandlerBody_fv, fv_var]
  decide

theorem reductAbstractionHandlerTerm_start {I S : AlphaTerm}
    (hI : I.Closed) (hS : S.Closed) :
    Relation.ReflTransGen Beta (app (app reductAbstractionHandlerTerm I) S)
      (reductAbstractionHandlerBody I S) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfI : I.fv = ∅ := hI
  have hfS : S.fv = ∅ := hS
  have h0 : Beta (app (lam 30 (lam 31 (reductAbstractionHandlerBody (var 30) (var 31)))) I) (lam 31 (reductAbstractionHandlerBody I (var 31))) := by
    convert Beta.contract 30 (lam 31 (reductAbstractionHandlerBody (var 30) (var 31))) I using 1

    simp [subst_lam_fresh, subst_var, reductAbstractionHandlerBody_subst, hfI]
  have h1 : Beta (app (lam 31 (reductAbstractionHandlerBody I (var 31))) S) (reductAbstractionHandlerBody I S) := by
    convert Beta.contract 31 (reductAbstractionHandlerBody I (var 31)) S using 1

    simp [subst_var, reductAbstractionHandlerBody_subst, subst_closed, hI]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) S).trans
  exact (Relation.ReflTransGen.single h1)

def reductStateFold : AlphaTerm :=
  syntaxFold reductVariableTerm reductApplicationHandlerTerm reductAbstractionHandlerTerm

@[simp] theorem reductStateFold_closed : reductStateFold.Closed :=
  syntaxFold_closed reductVariableTerm_closed reductApplicationHandlerTerm_closed reductAbstractionHandlerTerm_closed

def betaSuccessorsBody (E : AlphaTerm) : AlphaTerm :=
  app (numericalProjectionTerm false) (app reductStateFold E)

theorem betaSuccessorsBody_fv (E : AlphaTerm) :
    (betaSuccessorsBody E).fv = E.fv := by
  ext x
  simp only [betaSuccessorsBody, fv_app, (show (numericalProjectionTerm false).fv = ∅ from (numericalProjectionTerm_closed false)), (show (reductStateFold).fv = ∅ from reductStateFold_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem betaSuccessorsBody_subst (E W : AlphaTerm) (x : ℕ) :
    (betaSuccessorsBody E).subst x W =
      betaSuccessorsBody (E.subst x W) := by
  simp only [betaSuccessorsBody, subst_app, subst_closed _ _ _ (numericalProjectionTerm_closed false), subst_closed _ _ _ reductStateFold_closed]

def betaSuccessorsTerm : AlphaTerm := (lam 30 (betaSuccessorsBody (var 30)))

@[simp] theorem betaSuccessorsTerm_closed : betaSuccessorsTerm.Closed := by
  unfold betaSuccessorsTerm Closed
  simp only [fv_lam, betaSuccessorsBody_fv, fv_var]
  decide

theorem betaSuccessorsTerm_start {E : AlphaTerm}
    (hE : E.Closed) :
    Relation.ReflTransGen Beta (app betaSuccessorsTerm E)
      (betaSuccessorsBody E) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have h0 : Beta (app (lam 30 (betaSuccessorsBody (var 30))) E) (betaSuccessorsBody E) := by
    convert Beta.contract 30 (betaSuccessorsBody (var 30)) E using 1

    simp [subst_var, betaSuccessorsBody_subst]
  exact (Relation.ReflTransGen.single h0)

def rootReductCodes (M N : Term) : List ℕ :=
  match M with | .lam x A => [(A.subst x N).code] | _ => []

def reductCodes (M : Term) : List ℕ := M.betaSuccessors.map Term.code

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Let $\LambdaReductListCode{M}$ be the numerical code of the list of codes of the named reducts:
    $$\LambdaReductListCode{M}:=
    \LambdaListCode{\ListMap{\LambdaSyntaxCode{\cdot}}{\LambdaBetaSuccessors{M}}}.$$
    The list keeps the indicated order, including repeated entries if distinct redex positions yield the same term. A structural fold will carry the pair consisting of the original term code and this list code. Keeping the original code makes the body and binder of a potential root redex available to the application handler.
-/
def reductStateCode (M : Term) : ℕ := Nat.pair M.code (NatListCode.encode (reductCodes M))

theorem rootReductTerm_code (M N : Term) :
    Relation.ReflTransGen Beta (app (app rootReductTerm (numeral M.code)) (numeral N.code))
      (numeral (NatListCode.encode (rootReductCodes M N))) := by
  apply (rootReductTerm_start (numeral_closed _) (numeral_closed _)).trans
  apply (syntaxCases_code M _ _ _ (numeral_closed 0) (numeral_closed 0)).trans
  cases M with
  | var x => exact .refl
  | app A B => exact .refl
  | lam x A =>
    have hs := (beta_steps_app_left
      (beta_steps_app (beta_steps_app_right substitutionTerm (syntaxFieldTerm_lam false x A))
        (syntaxFieldTerm_lam true x A)) (numeral N.code)).trans (substitutionTerm_code A N x)
    exact (beta_steps_app_left (beta_steps_app_right listConsTerm hs) (numeral 0)).trans
      (listConsTerm_apply _ 0)

theorem leftReductMapTerm_apply (b c : ℕ) :
    Relation.ReflTransGen Beta (app (app leftReductMapTerm (numeral b)) (numeral c))
      (numeral (3 * Nat.pair c b + 1)) :=
  (leftReductMapTerm_start (numeral_closed b) (numeral_closed c)).trans
    (taggedPairCodeTerm_apply 1 c b)

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

theorem reductVariableTerm_apply (x : ℕ) :
    Relation.ReflTransGen Beta (app reductVariableTerm (numeral x))
      (numeral (reductStateCode (.var x))) :=
  (reductVariableTerm_start (numeral_closed x)).trans
    ((beta_steps_app_left (beta_steps_app_right numericalPairTerm (variableCodeTerm_apply x))
      (numeral 0)).trans (numericalPairTerm_apply _ 0))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use structural recursion with the state at $M$ equal to
    $$\ChurchNumeral{\NatPair{\LambdaSyntaxCode{M}}{\LambdaReductListCode{M}}}.$$
    At a variable, the variable constructor recovers its code and the empty list gives all reducts. At an application, numerical projections recover both original child codes and both child reduct lists. Constructor inspection computes the root list: it is empty unless the left child is an abstraction, in which case the substitution program produces exactly the prescribed contraction. Mapping restores the unchanged context around the left and right reducts. Two concatenations place the root result first, then the left results, then the right results. The syntax constructor also recovers the original application code. This is exactly the defining application clause for the reduct list.
-/
theorem reductApplicationTerm_code (M N : Term) :
    Relation.ReflTransGen Beta
      (app (app (app (app reductApplicationTerm (numeral M.code)) (numeral N.code))
        (numeral (NatListCode.encode (reductCodes M)))) (numeral (NatListCode.encode (reductCodes N))))
      (numeral (reductStateCode (.app M N))) := by
  apply (reductApplicationTerm_start (numeral_closed _) (numeral_closed _)
    (numeral_closed _) (numeral_closed _)).trans
  have hleft := (beta_steps_app (beta_steps_app_right listAppendTerm (rootReductTerm_code M N))
    (map_left_reducts N M.betaSuccessors)).trans
      (listAppendTerm_code (rootReductCodes M N) ((M.betaSuccessors.map (fun M' => Term.app M' N)).map Term.code))
  have hall := (beta_steps_app (beta_steps_app_right listAppendTerm hleft)
    (map_right_reducts M N.betaSuccessors)).trans (listAppendTerm_code _ _)
  have h := (beta_steps_app (beta_steps_app_right numericalPairTerm (applicationCodeTerm_apply M N)) hall).trans
    (numericalPairTerm_apply _ _)
  have he : reductCodes (.app M N) =
      (rootReductCodes M N ++ (M.betaSuccessors.map (fun M' => Term.app M' N)).map Term.code) ++
        (N.betaSuccessors.map (Term.app M)).map Term.code := by
    cases M <;> simp [reductCodes, Term.betaSuccessors, rootReductCodes, List.map_append]
  change Relation.ReflTransGen Beta _
    (numeral (Nat.pair (Term.app M N).code (NatListCode.encode (reductCodes (.app M N)))))
  rw [he]
  simpa only [reductApplicationBody, reductCodes] using h

theorem reductApplicationHandlerTerm_code (M N : Term) :
    Relation.ReflTransGen Beta
      (app (app reductApplicationHandlerTerm (numeral (reductStateCode M))) (numeral (reductStateCode N)))
      (numeral (reductStateCode (.app M N))) := by
  apply (reductApplicationHandlerTerm_start (numeral_closed _) (numeral_closed _)).trans
  have h := beta_steps_app
    (beta_steps_app
      (beta_steps_app
        (beta_steps_app_right reductApplicationTerm (numericalProjectionTerm_pair true M.code (NatListCode.encode (reductCodes M))))
        (numericalProjectionTerm_pair true N.code (NatListCode.encode (reductCodes N))))
      (numericalProjectionTerm_pair false M.code (NatListCode.encode (reductCodes M))))
    (numericalProjectionTerm_pair false N.code (NatListCode.encode (reductCodes N)))
  exact h.trans (reductApplicationTerm_code M N)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    At an abstraction, mapping restores the same binder around every body reduct, and the abstraction constructor reconstructs the original term code. The induction hypotheses and the proved numerical, list and substitution operations therefore establish the state invariant with finite reductions. Projecting the second state component proves the first displayed conclusion.
-/
theorem reductAbstractionTerm_code (x : ℕ) (M : Term) :
    Relation.ReflTransGen Beta
      (app (app (app reductAbstractionTerm (numeral x)) (numeral M.code))
        (numeral (NatListCode.encode (reductCodes M))))
      (numeral (reductStateCode (.lam x M))) := by
  apply (reductAbstractionTerm_start (numeral_closed _) (numeral_closed _) (numeral_closed _)).trans
  exact (beta_steps_app (beta_steps_app_right numericalPairTerm (abstractionCodeTerm_apply x M))
    (map_abstraction_reducts x M.betaSuccessors)).trans (numericalPairTerm_apply _ _)

theorem reductAbstractionHandlerTerm_code (x : ℕ) (M : Term) :
    Relation.ReflTransGen Beta
      (app (app reductAbstractionHandlerTerm (numeral x)) (numeral (reductStateCode M)))
      (numeral (reductStateCode (.lam x M))) := by
  apply (reductAbstractionHandlerTerm_start (numeral_closed _) (numeral_closed _)).trans
  exact (beta_steps_app
    (beta_steps_app_right (app reductAbstractionTerm (numeral x)) (numericalProjectionTerm_pair true M.code (NatListCode.encode (reductCodes M))))
    (numericalProjectionTerm_pair false M.code (NatListCode.encode (reductCodes M)))).trans (reductAbstractionTerm_code x M)

theorem reductStateFold_code (M : Term) :
    Relation.ReflTransGen Beta (app reductStateFold (numeral M.code)) (numeral (reductStateCode M)) :=
  syntaxFold_apply reductVariableTerm_closed reductApplicationHandlerTerm_closed reductAbstractionHandlerTerm_closed
    (fun M => numeral (reductStateCode M)) reductVariableTerm_apply reductApplicationHandlerTerm_code
    reductAbstractionHandlerTerm_code M

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: One-step reduction programs
-/
theorem betaSuccessorsTerm_code (M : Term) :
    Relation.ReflTransGen Beta (app betaSuccessorsTerm (numeral M.code))
      (numeral (NatListCode.encode (M.betaSuccessors.map Term.code))) :=
  (betaSuccessorsTerm_start (numeral_closed M.code)).trans
    ((beta_steps_app_right (numericalProjectionTerm false) (reductStateFold_code M)).trans
      (numericalProjectionTerm_pair false M.code (NatListCode.encode (reductCodes M))))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: One-step reduction programs
-/
theorem betaSuccessorsTerm_apply (e : ℕ) :
    Relation.ReflTransGen Beta (app betaSuccessorsTerm (numeral e))
      (numeral (NatListCode.encode ((Term.decode e).betaSuccessors.map Term.code))) := by
  simpa only [Term.code_decode] using betaSuccessorsTerm_code (Term.decode e)

def betaStepTestBody (E D : AlphaTerm) : AlphaTerm :=
  app (app listMemberTerm D) (app betaSuccessorsTerm E)

theorem betaStepTestBody_fv (E D : AlphaTerm) :
    (betaStepTestBody E D).fv = E.fv ∪ D.fv := by
  ext x
  simp only [betaStepTestBody, fv_app, (show listMemberTerm.fv = ∅ from listMemberTerm_closed), (show betaSuccessorsTerm.fv = ∅ from betaSuccessorsTerm_closed), Finset.mem_union, Finset.notMem_empty]
  tauto

theorem betaStepTestBody_subst (E D W : AlphaTerm) (x : ℕ) :
    (betaStepTestBody E D).subst x W =
      betaStepTestBody (E.subst x W) (D.subst x W) := by
  simp only [betaStepTestBody, subst_app, subst_closed _ _ _ listMemberTerm_closed, subst_closed _ _ _ betaSuccessorsTerm_closed]

def betaStepTestTerm : AlphaTerm := (lam 30 (lam 31 (betaStepTestBody (var 30) (var 31))))

@[simp] theorem betaStepTestTerm_closed : betaStepTestTerm.Closed := by
  unfold betaStepTestTerm Closed
  simp only [fv_lam, betaStepTestBody_fv, fv_var]
  decide

theorem betaStepTestTerm_start {E D : AlphaTerm}
    (hE : E.Closed) (hD : D.Closed) :
    Relation.ReflTransGen Beta (app (app betaStepTestTerm E) D)
      (betaStepTestBody E D) := by
  have hn : ∀ n, (numeral n).fv = ∅ := numeral_closed
  have hfE : E.fv = ∅ := hE
  have hfD : D.fv = ∅ := hD
  have h0 : Beta (app (lam 30 (lam 31 (betaStepTestBody (var 30) (var 31)))) E) (lam 31 (betaStepTestBody E (var 31))) := by
    convert Beta.contract 30 (lam 31 (betaStepTestBody (var 30) (var 31))) E using 1

    simp [subst_lam_fresh, subst_var, betaStepTestBody_subst, hfE]
  have h1 : Beta (app (lam 31 (betaStepTestBody E (var 31))) D) (betaStepTestBody E D) := by
    convert Beta.contract 31 (betaStepTestBody E (var 31)) D using 1

    simp [subst_var, betaStepTestBody_subst, subst_closed, hE]
  apply (beta_steps_app_left (Relation.ReflTransGen.single h0) D).trans
  exact (Relation.ReflTransGen.single h1)

instance namedBetaDecidable (M N : Term) : Decidable (Term.Beta M N) :=
  decidable_of_iff (N ∈ M.betaSuccessors) (Term.mem_betaSuccessors_iff M N)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For the final test, apply numerical list membership to the target code and the computed list. Injectivity of syntax coding identifies membership of the target code with membership of the named target term. Soundness and completeness of the reduct list then identify this with a named one-step reduction. All inserted constants and handlers are closed. Finally, the syntax code-decoding identities extend both results to arbitrary natural-number inputs.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: One-step reduction programs
-/
theorem betaStepTestTerm_code (M N : Term) :
    Relation.ReflTransGen Beta (app (app betaStepTestTerm (numeral M.code)) (numeral N.code))
      (numeral (if Term.Beta M N then 1 else 0)) := by
  apply (betaStepTestTerm_start (numeral_closed _) (numeral_closed _)).trans
  have h := (beta_steps_app_right (app listMemberTerm (numeral N.code)) (betaSuccessorsTerm_code M)).trans
    (listMemberTerm_code N.code (M.betaSuccessors.map Term.code))
  have hm : N.code ∈ M.betaSuccessors.map Term.code ↔ Term.Beta M N := by
    rw [← Term.mem_betaSuccessors_iff]
    constructor
    · intro hn
      obtain ⟨P, hp, he⟩ := List.mem_map.mp hn
      exact Term.code_injective he ▸ hp
    · intro hn
      exact List.mem_map.mpr ⟨N, hn, rfl⟩
  simpa only [betaStepTestBody, hm] using h

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: One-step reduction programs
-/
theorem betaStepTestTerm_apply (e d : ℕ) :
    Relation.ReflTransGen Beta (app (app betaStepTestTerm (numeral e)) (numeral d))
      (numeral (if Term.Beta (Term.decode e) (Term.decode d) then 1 else 0)) := by
  simpa only [Term.code_decode] using betaStepTestTerm_code (Term.decode e) (Term.decode d)


end PolishSpaceBook.NamedLambda.AlphaTerm
