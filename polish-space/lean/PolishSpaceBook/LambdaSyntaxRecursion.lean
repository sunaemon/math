module

public import PolishSpaceBook.LambdaSyntaxInspection

@[expose] public section

/-! # Structural recursion on syntax codes by a closed lambda program -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Code inspection lets a lambda program follow the structure of a decoded term. For a code term $e$ and three branch terms $X,Y,Z$, abbreviate
    $$\begin{aligned}
    \LambdaSyntaxCase{e}{X}{Y}{Z}&:=\LambdaZeroTest\,(\LambdaSyntaxTag\,e)\,X\\
    &\qquad\bigl(\LambdaZeroTest\,(\LambdaPred(\LambdaSyntaxTag\,e))\,Y\,Z\bigr).
    \end{aligned}$$
    On the code of a variable, application or abstraction, this selects the first, second or third branch, respectively. The unselected branches need not be reduced.
-/
def syntaxCases (E V A L : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm (app syntaxTagTerm E)) V)
    (app (app (app zeroTestTerm (app predecessorTerm (app syntaxTagTerm E))) A) L)

theorem syntaxCases_fv (E V A L : AlphaTerm) :
    (syntaxCases E V A L).fv = E.fv ∪ V.fv ∪ A.fv ∪ L.fv := by
  simp only [syntaxCases, fv_app]
  rw [zeroTestTerm_closed, syntaxTagTerm_closed, predecessorTerm_closed]
  ext x
  simp only [Finset.mem_union, Finset.notMem_empty, false_or]
  tauto

theorem syntaxCases_subst (E V A L W : AlphaTerm) (x : ℕ) :
    (syntaxCases E V A L).subst x W =
      syntaxCases (E.subst x W) (V.subst x W) (A.subst x W) (L.subst x W) := by
  simp only [syntaxCases, subst_app, subst_closed _ _ _ zeroTestTerm_closed,
    subst_closed _ _ _ syntaxTagTerm_closed, subst_closed _ _ _ predecessorTerm_closed]

theorem syntaxCases_code (M : Term) (V A L : AlphaTerm) (hV : V.Closed) (hA : A.Closed) :
    Relation.ReflTransGen Beta (syntaxCases (numeral M.code) V A L)
      (match M with | .var _ => V | .app _ _ => A | .lam _ _ => L) := by
  have ht := syntaxTagTerm_code M
  unfold syntaxCases
  have h := beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm ht) V)
    (app (app (app zeroTestTerm (app predecessorTerm (app syntaxTagTerm (numeral M.code)))) A) L)
  apply h.trans
  cases M with
  | var x => exact branch_zero _ _ (by rw [hV]; simp)
  | app M N =>
    apply (branch_succ 0 _ _).trans
    have hp := (beta_steps_app_right predecessorTerm ht).trans (predecessorTerm_apply 1)
    exact (beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm hp) A) L).trans
      (branch_zero _ _ (by rw [hA]; simp))
  | lam x M =>
    apply (branch_succ 1 _ _).trans
    have hp := (beta_steps_app_right predecessorTerm ht).trans (predecessorTerm_apply 2)
    exact (beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm hp) A) L).trans
      (branch_succ 0 _ _)

def syntaxFoldBody (V A L R E : AlphaTerm) : AlphaTerm :=
  syntaxCases E (app V (app syntaxPayloadTerm E))
    (app (app A (app R (app (syntaxFieldTerm true) E)))
      (app R (app (syntaxFieldTerm false) E)))
    (app (app L (app (syntaxFieldTerm true) E)) (app R (app (syntaxFieldTerm false) E)))

theorem syntaxFoldBody_fv (V A L R E : AlphaTerm) :
    (syntaxFoldBody V A L R E).fv = V.fv ∪ A.fv ∪ L.fv ∪ R.fv ∪ E.fv := by
  simp only [syntaxFoldBody, syntaxCases_fv, fv_app]
  rw [syntaxPayloadTerm_closed, syntaxFieldTerm_closed, syntaxFieldTerm_closed]
  ext x
  simp only [Finset.mem_union, Finset.notMem_empty, false_or]
  tauto

theorem syntaxFoldBody_subst (V A L R E W : AlphaTerm) (x : ℕ) :
    (syntaxFoldBody V A L R E).subst x W =
      syntaxFoldBody (V.subst x W) (A.subst x W) (L.subst x W)
        (R.subst x W) (E.subst x W) := by
  simp only [syntaxFoldBody, syntaxCases_subst, subst_app,
    subst_closed _ _ _ syntaxPayloadTerm_closed,
    subst_closed _ _ _ (syntaxFieldTerm_closed true),
    subst_closed _ _ _ (syntaxFieldTerm_closed false)]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Fix closed handler terms $V,A,L$ for variables, applications and abstractions. With fresh distinct variables $s,z$, define the following abbreviations, expanding them inside the abstractions:
    $$\begin{aligned}
    X(z)&:=V(\LambdaSyntaxPayload\,z),\\
    Y(R,z)&:=A\bigl(R(\LambdaSyntaxField{1}\,z)\bigr)\bigl(R(\LambdaSyntaxField{2}\,z)\bigr),\\
    Z(R,z)&:=L(\LambdaSyntaxField{1}\,z)\bigl(R(\LambdaSyntaxField{2}\,z)\bigr),\\
    B(R,z)&:=\LambdaSyntaxCase{z}{X(z)}{Y(R,z)}{Z(R,z)},\\
    K&:=\lambdaab{s}{\lambdaab{z}{B(ss,z)}},\\
    \LambdaSyntaxFold{V}{A}{L}&:=KK.
    \end{aligned}$$
    Thus the recursive call is the same self-application, with a subterm code as its input. The three handlers are fixed parts of this finite term; they do not vary with the input code.
-/
def syntaxFoldKernel (V A L : AlphaTerm) : AlphaTerm :=
  lam 12 (lam 13 (syntaxFoldBody V A L (app (var 12) (var 12)) (var 13)))

def syntaxFold (V A L : AlphaTerm) : AlphaTerm :=
  app (syntaxFoldKernel V A L) (syntaxFoldKernel V A L)

theorem syntaxFoldKernel_closed {V A L : AlphaTerm}
    (hV : V.Closed) (hA : A.Closed) (hL : L.Closed) : (syntaxFoldKernel V A L).Closed := by
  unfold syntaxFoldKernel Closed
  rw [fv_lam, fv_lam, syntaxFoldBody_fv, hV, hA, hL, fv_app]
  simp [fv_var]
  decide

theorem syntaxFold_closed {V A L : AlphaTerm}
    (hV : V.Closed) (hA : A.Closed) (hL : L.Closed) : (syntaxFold V A L).Closed :=
  closed_app (syntaxFoldKernel_closed hV hA hL) (syntaxFoldKernel_closed hV hA hL)

theorem syntaxFold_unfold {V A L : AlphaTerm}
    (hV : V.Closed) (hA : A.Closed) (hL : L.Closed) (e : ℕ) :
    Relation.ReflTransGen Beta (app (syntaxFold V A L) (numeral e))
      (syntaxFoldBody V A L (syntaxFold V A L) (numeral e)) := by
  let K := syntaxFoldKernel V A L
  have hK : K.Closed := syntaxFoldKernel_closed hV hA hL
  have hR := syntaxFold_closed hV hA hL
  have h₁ : Beta (app K K) (lam 13 (syntaxFoldBody V A L (app K K) (var 13))) := by
    convert Beta.contract 12 (lam 13 (syntaxFoldBody V A L (app (var 12) (var 12)) (var 13))) K
      using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 13 12 (by decide) (by rw [hK]; simp), syntaxFoldBody_subst]
    simp [subst_app, subst_var, subst_closed _ _ _ hV, subst_closed _ _ _ hA,
      subst_closed _ _ _ hL]
  have h₂ : Beta (app (lam 13 (syntaxFoldBody V A L (syntaxFold V A L) (var 13))) (numeral e))
      (syntaxFoldBody V A L (syntaxFold V A L) (numeral e)) := by
    convert Beta.contract 13 (syntaxFoldBody V A L (syntaxFold V A L) (var 13)) (numeral e)
      using 1
    simp [syntaxFoldBody_subst, subst_var, subst_closed _ _ _ hV,
      subst_closed _ _ _ hA, subst_closed _ _ _ hL, subst_closed _ _ _ hR]
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Put $F:=\LambdaSyntaxFold{V}{A}{L}$. Two beta steps give $F\ChurchNumeral{e}\to_\beta^*B(F,\ChurchNumeral{e})$. All
    inserted constants and handlers are closed, so the fresh binders prevent capture. Reduce the constructor tag and select
    the appropriate branch. The payload and field equations then give
    $$\begin{aligned}
    F\ChurchNumeral{\LambdaSyntaxCode{x_i}}&\to_\beta^*V\ChurchNumeral{i},\\
    F\ChurchNumeral{\LambdaSyntaxCode{MN}}&\to_\beta^*A\bigl(F\ChurchNumeral{\LambdaSyntaxCode{M}}
    \bigr)\bigl(F\ChurchNumeral{\LambdaSyntaxCode{N}}\bigr),\\
    F\ChurchNumeral{\LambdaSyntaxCode{\lambdaab{x_i}{M}}}&\to_\beta^*L\ChurchNumeral{i}
    \bigl(F\ChurchNumeral{\LambdaSyntaxCode{M}}\bigr).
    \end{aligned}$$
    These reductions expose the required recursive calls without reducing discarded branches.
-/
theorem syntaxFold_step {V A L : AlphaTerm}
    (hV : V.Closed) (hA : A.Closed) (hL : L.Closed) (M : Term) :
    Relation.ReflTransGen Beta (app (syntaxFold V A L) (numeral M.code))
      (match M with
      | .var x => app V (numeral x)
      | .app M N => app (app A (app (syntaxFold V A L) (numeral M.code)))
          (app (syntaxFold V A L) (numeral N.code))
      | .lam x M => app (app L (numeral x)) (app (syntaxFold V A L) (numeral M.code))) := by
  apply (syntaxFold_unfold hV hA hL M.code).trans
  have hR := syntaxFold_closed hV hA hL
  have he := numeral_closed M.code
  have hv := closed_app hV (closed_app syntaxPayloadTerm_closed he)
  have ha := closed_app (closed_app hA
    (closed_app hR (closed_app (syntaxFieldTerm_closed true) he)))
    (closed_app hR (closed_app (syntaxFieldTerm_closed false) he))
  apply (syntaxCases_code M _ _ _ hv ha).trans
  cases M with
  | var x => exact beta_steps_app_right V (syntaxPayloadTerm_var x)
  | app M N =>
    exact beta_steps_app
      (beta_steps_app_right A (beta_steps_app_right _ (syntaxFieldTerm_app true M N)))
      (beta_steps_app_right _ (syntaxFieldTerm_app false M N))
  | lam x M =>
    exact beta_steps_app (beta_steps_app_right L (syntaxFieldTerm_lam true x M))
      (beta_steps_app_right _ (syntaxFieldTerm_lam false x M))

/-- A single finite program realizes structural recursion on every named term. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: theorem
  title: Structural recursion by a lambda term
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Induct on the structure of $M$. At a variable, apply the variable-handler assumption. At an application, the induction hypotheses give finite reductions for both subterms; lift them through the application contexts, then apply the application-handler assumption. At an abstraction, use the induction hypothesis for its body and then the abstraction-handler assumption. Every case concatenates finitely many finite reductions. Finally, the kernel binds its two remaining free variables, so both the kernel and its self-application are closed.
    \end{proof}
-/
theorem syntaxFold_apply {V A L : AlphaTerm}
    (hV : V.Closed) (hA : A.Closed) (hL : L.Closed)
    (f : Term → AlphaTerm)
    (hv : ∀ x, Relation.ReflTransGen Beta (app V (numeral x)) (f (.var x)))
    (ha : ∀ M N, Relation.ReflTransGen Beta (app (app A (f M)) (f N)) (f (.app M N)))
    (hl : ∀ x M, Relation.ReflTransGen Beta (app (app L (numeral x)) (f M)) (f (.lam x M)))
    (M : Term) :
    Relation.ReflTransGen Beta (app (syntaxFold V A L) (numeral M.code)) (f M) := by
  induction M with
  | var x => exact (syntaxFold_step hV hA hL _).trans (hv x)
  | app M N hM hN =>
    exact (syntaxFold_step hV hA hL _).trans
      ((beta_steps_app (beta_steps_app_right A hM) hN).trans (ha M N))
  | lam x M hM =>
    exact (syntaxFold_step hV hA hL _).trans
      ((beta_steps_app_right (app L (numeral x)) hM).trans (hl x M))


/-- A fold whose handlers rebuild each constructor recovers the input code. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: example
  title: Reconstructing a code
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Take $W_M=\ChurchNumeral{\LambdaSyntaxCode{M}}$. The constructor-program equations verify the three hypotheses. Every natural number is the code of its decoded term, so the conclusion covers every numeral input.
    \end{proof}
-/
theorem syntaxFold_rebuild (M : Term) :
    Relation.ReflTransGen Beta
      (app (syntaxFold variableCodeTerm applicationCodeTerm abstractionCodeTerm) (numeral M.code))
      (numeral M.code) :=
  syntaxFold_apply variableCodeTerm_closed (taggedPairCodeTerm_closed 1) (taggedPairCodeTerm_closed 2)
    (fun M => numeral M.code) variableCodeTerm_apply applicationCodeTerm_apply abstractionCodeTerm_apply M

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Let $\LambdaNodeCount{M}$ count the variable, application and abstraction nodes of $M$. Thus
    $$\begin{aligned}
    \LambdaNodeCount{x_i}&=1,\\
    \LambdaNodeCount{MN}&=\LambdaNodeCount{M}+\LambdaNodeCount{N}+1,\\
    \LambdaNodeCount{\lambdaab{x_i}{M}}&=\LambdaNodeCount{M}+1.
    \end{aligned}$$
    Define
    $$\begin{aligned}
    V_\#&:=\lambdaab{i}{\ChurchNumeral{1}},\\
    A_\#&:=\lambdaab{m}{\lambdaab{n}{\LambdaSucc(\LambdaAdd\,m\,n)}},\\
    L_\#&:=\lambdaab{i}{\LambdaSucc},\\
    \LambdaSyntaxNodes&:=\LambdaSyntaxFold{V_\#}{A_\#}{L_\#}.
    \end{aligned}$$
-/
def nodeVariableTerm : AlphaTerm := lam 3 (numeral 1)
def nodeApplicationTerm : AlphaTerm := lam 3 (lam 4
  (app successorTerm (app (app additionTerm (var 3)) (var 4))))
def nodeAbstractionTerm : AlphaTerm := lam 3 successorTerm

@[simp] theorem nodeVariableTerm_closed : nodeVariableTerm.Closed := by
  unfold nodeVariableTerm Closed
  rw [fv_lam, numeral_closed]
  simp

@[simp] theorem nodeApplicationTerm_closed : nodeApplicationTerm.Closed := by
  unfold nodeApplicationTerm Closed
  simp only [fv_lam, fv_app]
  rw [successorTerm_closed, additionTerm_closed]
  simp [fv_var]
  decide

@[simp] theorem nodeAbstractionTerm_closed : nodeAbstractionTerm.Closed := by
  unfold nodeAbstractionTerm Closed
  rw [fv_lam, successorTerm_closed]
  simp

theorem nodeVariableTerm_apply (x : ℕ) :
    Beta (app nodeVariableTerm (numeral x)) (numeral 1) := by
  simpa only [nodeVariableTerm, subst_closed _ _ _ (numeral_closed 1)] using
    Beta.contract 3 (numeral 1) (numeral x)

theorem nodeApplicationTerm_apply (m n : ℕ) :
    Relation.ReflTransGen Beta (app (app nodeApplicationTerm (numeral m)) (numeral n))
      (numeral (m + n + 1)) := by
  have h₁ : Beta (app nodeApplicationTerm (numeral m))
      (lam 4 (app successorTerm (app (app additionTerm (numeral m)) (var 4)))) := by
    convert Beta.contract 3 (lam 4 (app successorTerm (app (app additionTerm (var 3)) (var 4))))
      (numeral m) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 4 3 (by decide) (by rw [numeral_closed]; simp)]
    simp [subst_app, subst_var, subst_closed _ _ _ successorTerm_closed,
      subst_closed _ _ _ additionTerm_closed]
  have h₂ : Beta
      (app (lam 4 (app successorTerm (app (app additionTerm (numeral m)) (var 4)))) (numeral n))
      (app successorTerm (app (app additionTerm (numeral m)) (numeral n))) := by
    convert Beta.contract 4 (app successorTerm (app (app additionTerm (numeral m)) (var 4)))
      (numeral n) using 1
    simp [subst_app, subst_var, subst_closed _ _ _ successorTerm_closed,
      subst_closed _ _ _ additionTerm_closed, subst_closed _ _ _ (numeral_closed m)]
  exact (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans
    ((beta_steps_app_right successorTerm (additionTerm_apply m n)).trans (successorTerm_apply (m + n)))

theorem nodeAbstractionTerm_apply (x n : ℕ) :
    Relation.ReflTransGen Beta (app (app nodeAbstractionTerm (numeral x)) (numeral n))
      (numeral (n + 1)) := by
  have h : Beta (app nodeAbstractionTerm (numeral x)) successorTerm := by
    simpa only [nodeAbstractionTerm, subst_closed _ _ _ successorTerm_closed] using
      Beta.contract 3 successorTerm (numeral x)
  exact (Relation.ReflTransGen.single (.app_left _ h)).trans (successorTerm_apply n)

/-- A computable bound for the capture-avoiding substitution procedure. -/
def syntaxNodesTerm : AlphaTerm :=
  syntaxFold nodeVariableTerm nodeApplicationTerm nodeAbstractionTerm

@[simp] theorem syntaxNodesTerm_closed : syntaxNodesTerm.Closed :=
  syntaxFold_closed nodeVariableTerm_closed nodeApplicationTerm_closed nodeAbstractionTerm_closed

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Counting syntax nodes by a lambda term
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The variable handler discards its input and returns one. Two beta steps, addition and successor make the application handler return the sum of its two inputs plus one. The abstraction handler discards the binder index and returns the successor of the body count. Apply structural recursion with $W_M=\ChurchNumeral{\LambdaNodeCount{M}}$, and then use the coding identity for $\LambdaSyntaxDecode{e}$.
    \end{proof}
-/
theorem syntaxNodesTerm_code (M : Term) :
    Relation.ReflTransGen Beta (app syntaxNodesTerm (numeral M.code)) (numeral M.nodes) :=
  syntaxFold_apply nodeVariableTerm_closed nodeApplicationTerm_closed nodeAbstractionTerm_closed
    (fun M => numeral M.nodes) (fun x => .single (nodeVariableTerm_apply x))
    (fun M N => nodeApplicationTerm_apply M.nodes N.nodes)
    (fun x M => nodeAbstractionTerm_apply x M.nodes) M

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Counting syntax nodes by a lambda term
-/
theorem syntaxNodesTerm_apply (e : ℕ) :
    Relation.ReflTransGen Beta (app syntaxNodesTerm (numeral e)) (numeral (Term.decode e).nodes) := by
  simpa only [Term.code_decode] using syntaxNodesTerm_code (Term.decode e)

end PolishSpaceBook.NamedLambda.AlphaTerm
