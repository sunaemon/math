module

public import PolishSpaceBook.LambdaNumerals

@[expose] public section

/-!
# Iteration and arithmetic by Church numerals

These are finite terms of the same named lambda calculus. The proofs expose
ordinary beta reductions, rather than assuming a numerical computability API.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

@[simp] theorem fv_var (x : ℕ) : (var x).fv = {x} := rfl

theorem subst_closed (M N : AlphaTerm) (x : ℕ) (h : M.Closed) : M.subst x N = M :=
  subst_not_free M N x (by rw [h]; simp)

/-- Repeated application, a meta-level description of the resulting lambda term. -/
def iterateApp (F X : AlphaTerm) : ℕ → AlphaTerm
  | 0 => X
  | n + 1 => app F (iterateApp F X n)

theorem iterateBody_eq (n : ℕ) : iterateBody n = iterateApp (var 1) (var 2) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterateBody, iterateApp, ih]

theorem iterateApp_subst (F X R : AlphaTerm) (n x : ℕ) :
    (iterateApp F X n).subst x R = iterateApp (F.subst x R) (X.subst x R) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterateApp, subst_app, ih]

theorem iterateApp_add (F X : AlphaTerm) (m n : ℕ) :
    iterateApp F (iterateApp F X n) m = iterateApp F X (m + n) := by
  induction m with
  | zero => simp [iterateApp]
  | succ m ih => simp only [iterateApp, ih, Nat.succ_add]

/-- Applying a numeral to a function and an argument yields actual iteration.
The sole freshness condition prevents capture in the numeral's second binder. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    For lambda terms $F,X$, define the finite expression $\LambdaIter{F}{X}{n}$ by
    $$\LambdaIter{F}{X}{0}=X,\qquad
    \LambdaIter{F}{X}{n+1}=F(\LambdaIter{F}{X}{n}).$$
    This notation describes repeated application in the existing syntax; it adds no reduction rule. Choose the numeral's second binder $x$ outside $\FreeVarsLambda{F}$. Two beta steps then give
    $$\ChurchNumeral{n}\,F\,X\to_\beta^*\LambdaIter{F}{X}{n}.$$
    Indeed, the first substitution replaces each occurrence of the iterator variable by $F$ without capture by $x$, and the second replaces the initial-value variable by $X$. Induction on $n$ verifies both substitution formulas. The same induction gives
    $$\LambdaIter{F}{\LambdaIter{F}{X}{n}}{m}=\LambdaIter{F}{X}{m+n}.$$
-/
theorem numeral_apply (n : ℕ) (F X : AlphaTerm) (hF : 2 ∉ F.fv) :
    Relation.ReflTransGen Beta (app (app (numeral n) F) X) (iterateApp F X n) := by
  have h₁ : Beta (app (numeral n) F) (lam 2 (iterateApp F (var 2) n)) := by
    convert Beta.contract 1 (lam 2 (iterateBody n)) F using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 2 1 (by decide) hF, iterateBody_eq, iterateApp_subst]
    simp [subst_var]
  have h₂ : Beta (app (lam 2 (iterateApp F (var 2) n)) X) (iterateApp F X n) := by
    convert Beta.contract 2 (iterateApp F (var 2) n) X using 1
    simp [iterateApp_subst, subst_not_free F X 2 hF, subst_var]
  exact .tail (.single (.app_left X h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Define the following closed terms, choosing the displayed bound variables distinct:
    $$\begin{aligned}
    \LambdaSucc&:=\lambdaab{n}{\lambdaab{f}{\lambdaab{x}{f(nfx)}}},\\
    \LambdaAdd&:=\lambdaab{m}{\lambdaab{n}{\lambdaab{f}{\lambdaab{x}{mf(nfx)}}}},\\
    \LambdaMul&:=\lambdaab{m}{\lambdaab{n}{\lambdaab{f}{\lambdaab{x}{m(nf)x}}}}.
    \end{aligned}$$
-/
def successorTerm : AlphaTerm :=
  lam 3 (lam 1 (lam 2 (app (var 1) (app (app (var 3) (var 1)) (var 2)))))

@[simp] theorem successorTerm_closed : successorTerm.Closed := by
  unfold successorTerm Closed
  simp [fv_lam, fv_app, fv_var] ; decide

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Arithmetic on Church numerals
-/
theorem successorTerm_apply (n : ℕ) :
    Relation.ReflTransGen Beta (app successorTerm (numeral n)) (numeral (n + 1)) := by
  have hf (x : ℕ) : x ∉ (numeral n).fv := by rw [numeral_closed]; simp
  have h : Beta (app successorTerm (numeral n))
      (lam 1 (lam 2 (app (var 1) (app (app (numeral n) (var 1)) (var 2))))) := by
    convert Beta.contract 3 (lam 1 (lam 2 (app (var 1) (app (app (var 3) (var 1)) (var 2)))))
      (numeral n) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 1 3 (by decide) (hf 1),
      subst_lam_fresh _ _ 2 3 (by decide) (hf 2)]
    simp [subst_app, subst_var]
  apply (Relation.ReflTransGen.single h).trans
  apply beta_steps_lam 1
  apply beta_steps_lam 2
  simpa only [numeral, iterateBody, iterateBody_eq] using
    beta_steps_app_right (var 1) (numeral_apply n (var 1) (var 2) (by simp))

def additionTerm : AlphaTerm :=
  lam 3 (lam 4 (lam 1 (lam 2
    (app (app (var 3) (var 1)) (app (app (var 4) (var 1)) (var 2))))))

@[simp] theorem additionTerm_closed : additionTerm.Closed := by
  unfold additionTerm Closed
  simp [fv_lam, fv_app, fv_var] ; decide

theorem additionTerm_start (m n : ℕ) :
    Relation.ReflTransGen Beta (app (app additionTerm (numeral m)) (numeral n))
      (lam 1 (lam 2 (app (app (numeral m) (var 1)) (app (app (numeral n) (var 1)) (var 2))))) := by
  have hf (k x : ℕ) : x ∉ (numeral k).fv := by rw [numeral_closed]; simp
  have h₁ : Beta (app additionTerm (numeral m))
      (lam 4 (lam 1 (lam 2
        (app (app (numeral m) (var 1)) (app (app (var 4) (var 1)) (var 2)))))) := by
    convert Beta.contract 3 (lam 4 (lam 1 (lam 2
      (app (app (var 3) (var 1)) (app (app (var 4) (var 1)) (var 2)))))) (numeral m) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 4 3 (by decide) (hf m 4),
      subst_lam_fresh _ _ 1 3 (by decide) (hf m 1),
      subst_lam_fresh _ _ 2 3 (by decide) (hf m 2)]
    simp [subst_app, subst_var]
  have h₂ : Beta (app (lam 4 (lam 1 (lam 2
      (app (app (numeral m) (var 1)) (app (app (var 4) (var 1)) (var 2)))))) (numeral n))
      (lam 1 (lam 2 (app (app (numeral m) (var 1)) (app (app (numeral n) (var 1)) (var 2))))) := by
    convert Beta.contract 4 (lam 1 (lam 2
      (app (app (numeral m) (var 1)) (app (app (var 4) (var 1)) (var 2))))) (numeral n) using 1
    rw [subst_lam_fresh _ _ 1 4 (by decide) (hf n 1),
      subst_lam_fresh _ _ 2 4 (by decide) (hf n 2)]
    simp [subst_app, subst_var, subst_closed _ _ _ (numeral_closed m)]
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Arithmetic on Church numerals
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    First substitute the closed input numerals for the outer variables. In the successor term, reduce $\ChurchNumeral{n}fx$ to $\LambdaIter{f}{x}{n}$; the additional outer application of $f$ gives the numeral for $n+1$. In the addition term, first reduce the inner iteration of length $n$, then the outer iteration of length $m$. The iteration identity gives the numeral for $m+n$. All these reductions lift under the two remaining binders.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Natural numbers are supplied as Church numerals. Numerical predicates return the numeral one for true and zero for
    false; the selectors $\LambdaTrue,\LambdaFalse$ instead select the first and second branch. An unselected branch need
    not terminate. Functional pairs store terms; numerical pairs encode two natural numbers as a single numerical input.
    The arithmetic operations and numerical projections terminate on every numerical input.
-/
theorem additionTerm_apply (m n : ℕ) :
    Relation.ReflTransGen Beta (app (app additionTerm (numeral m)) (numeral n)) (numeral (m + n)) := by
  apply (additionTerm_start m n).trans
  apply beta_steps_lam 1
  apply beta_steps_lam 2
  have h := (beta_steps_app_right (app (numeral m) (var 1))
    (numeral_apply n (var 1) (var 2) (by simp))).trans
    (numeral_apply m (var 1) (iterateApp (var 1) (var 2) n) (by simp))
  simpa only [numeral, iterateBody_eq, iterateApp_add] using h

def multiplicationTerm : AlphaTerm :=
  lam 3 (lam 4 (lam 1 (lam 2
    (app (app (var 3) (app (var 4) (var 1))) (var 2)))))

@[simp] theorem multiplicationTerm_closed : multiplicationTerm.Closed := by
  unfold multiplicationTerm Closed
  simp [fv_lam, fv_app, fv_var] ; decide

theorem multiplicationTerm_start (m n : ℕ) :
    Relation.ReflTransGen Beta (app (app multiplicationTerm (numeral m)) (numeral n))
      (lam 1 (lam 2 (app (app (numeral m) (app (numeral n) (var 1))) (var 2)))) := by
  have hf (k x : ℕ) : x ∉ (numeral k).fv := by rw [numeral_closed]; simp
  have h₁ : Beta (app multiplicationTerm (numeral m))
      (lam 4 (lam 1 (lam 2 (app (app (numeral m) (app (var 4) (var 1))) (var 2))))) := by
    convert Beta.contract 3 (lam 4 (lam 1 (lam 2
      (app (app (var 3) (app (var 4) (var 1))) (var 2))))) (numeral m) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 4 3 (by decide) (hf m 4),
      subst_lam_fresh _ _ 1 3 (by decide) (hf m 1),
      subst_lam_fresh _ _ 2 3 (by decide) (hf m 2)]
    simp [subst_app, subst_var]
  have h₂ : Beta (app (lam 4 (lam 1 (lam 2
      (app (app (numeral m) (app (var 4) (var 1))) (var 2))))) (numeral n))
      (lam 1 (lam 2 (app (app (numeral m) (app (numeral n) (var 1))) (var 2)))) := by
    convert Beta.contract 4 (lam 1 (lam 2
      (app (app (numeral m) (app (var 4) (var 1))) (var 2)))) (numeral n) using 1
    rw [subst_lam_fresh _ _ 1 4 (by decide) (hf n 1),
      subst_lam_fresh _ _ 2 4 (by decide) (hf n 2)]
    simp [subst_app, subst_var, subst_closed _ _ _ (numeral_closed m)]
  exact .tail (.single (.app_left _ h₁)) h₂

theorem iterate_numeral_function (m n : ℕ) :
    Relation.ReflTransGen Beta (iterateApp (app (numeral n) (var 1)) (var 2) m)
      (iterateApp (var 1) (var 2) (m * n)) := by
  induction m with
  | zero => simpa [iterateApp] using (Relation.ReflTransGen.refl (r := Beta) (a := var 2))
  | succ m ih =>
    have h := (beta_steps_app_right (app (numeral n) (var 1)) ih).trans
      (numeral_apply n (var 1) (iterateApp (var 1) (var 2) (m * n)) (by simp))
    simpa only [iterateApp, iterateApp_add, Nat.succ_mul, Nat.add_comm n] using h

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Arithmetic on Church numerals
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For multiplication, apply the iteration formula to $\ChurchNumeral{m}(\ChurchNumeral{n}f)x$. Induction on $m$ shows that the result reduces to $\LambdaIter{f}{x}{mn}$. At the next step, first reduce the preceding iterate, then apply $\ChurchNumeral{n}f$ to it. This adds $n$ further applications of $f$, giving $(m+1)n=mn+n$. Lifting under the binders gives the claimed numeral. Counting free variables in the displayed terms proves their closedness.
-/
theorem multiplicationTerm_apply (m n : ℕ) :
    Relation.ReflTransGen Beta (app (app multiplicationTerm (numeral m)) (numeral n))
      (numeral (m * n)) := by
  apply (multiplicationTerm_start m n).trans
  apply beta_steps_lam 1
  apply beta_steps_lam 2
  have hf : 2 ∉ (app (numeral n) (var 1)).fv := by rw [fv_app, numeral_closed]; simp
  have h := (numeral_apply m (app (numeral n) (var 1)) (var 2) hf).trans
    (iterate_numeral_function m n)
  simpa only [numeral, iterateBody_eq] using h

/-- Church booleans select one of two unevaluated arguments. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    For branching, use the closed \termdefineas{Church boolean}{Church booleans}
    $$\LambdaTrue:=\lambdaab{a}{\lambdaab{b}{a}},\qquad
    \LambdaFalse:=\lambdaab{a}{\lambdaab{b}{b}},$$
    and put
    $$\LambdaZeroTest:=\lambdaab{n}{n(\lambdaab{u}{\LambdaFalse})\LambdaTrue}.$$
    For closed $A$ and arbitrary $B$, two beta steps give $\LambdaTrue\,A\,B\to_\beta^*A$; for arbitrary $A,B$, two give $\LambdaFalse\,A\,B\to_\beta^*B$. The first calculation also works for open $A$ when the second binder $b$ is chosen outside $\FreeVarsLambda{A}$. Neither calculation reduces the discarded argument.
-/
def trueTerm : AlphaTerm := lam 1 (lam 2 (var 1))
def falseTerm : AlphaTerm := lam 1 (lam 2 (var 2))

@[simp] theorem trueTerm_closed : trueTerm.Closed := by
  unfold trueTerm Closed
  simp [fv_lam, fv_var]

@[simp] theorem falseTerm_closed : falseTerm.Closed := by
  unfold falseTerm Closed
  simp [fv_lam, fv_var]

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Natural numbers are supplied as Church numerals. Numerical predicates return the numeral one for true and zero for
    false; the selectors $\LambdaTrue,\LambdaFalse$ instead select the first and second branch. An unselected branch need
    not terminate. Functional pairs store terms; numerical pairs encode two natural numbers as a single numerical input.
    The arithmetic operations and numerical projections terminate on every numerical input.
-/
theorem trueTerm_apply (A B : AlphaTerm) (hA : 2 ∉ A.fv) :
    Relation.ReflTransGen Beta (app (app trueTerm A) B) A := by
  have h₁ : Beta (app trueTerm A) (lam 2 A) := by
    convert Beta.contract 1 (lam 2 (var 1)) A using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 2 1 (by decide) hA]
    simp [subst_var]
  have h₂ : Beta (app (lam 2 A) B) A := by
    simpa only [subst_not_free _ _ _ hA] using Beta.contract 2 A B
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Natural numbers are supplied as Church numerals. Numerical predicates return the numeral one for true and zero for
    false; the selectors $\LambdaTrue,\LambdaFalse$ instead select the first and second branch. An unselected branch need
    not terminate. Functional pairs store terms; numerical pairs encode two natural numbers as a single numerical input.
    The arithmetic operations and numerical projections terminate on every numerical input.
-/
theorem falseTerm_apply (A B : AlphaTerm) :
    Relation.ReflTransGen Beta (app (app falseTerm A) B) B := by
  have hf : 1 ∉ (lam 2 (var 2)).fv := by simp [fv_lam, fv_var]
  have h₁ : Beta (app falseTerm A) (lam 2 (var 2)) := by
    simpa only [falseTerm, subst_not_free _ _ _ hf] using Beta.contract 1 (lam 2 (var 2)) A
  have h₂ : Beta (app (lam 2 (var 2)) B) B := by
    simpa [subst_var] using Beta.contract 2 (var 2) B
  exact .tail (.single (.app_left _ h₁)) h₂

def eraseToFalse : AlphaTerm := lam 3 falseTerm

def zeroTestTerm : AlphaTerm := lam 3 (app (app (var 3) eraseToFalse) trueTerm)

@[simp] theorem eraseToFalse_closed : eraseToFalse.Closed := by
  unfold Closed eraseToFalse
  rw [fv_lam, falseTerm_closed]
  simp

@[simp] theorem zeroTestTerm_closed : zeroTestTerm.Closed := by
  unfold zeroTestTerm Closed
  rw [fv_lam, fv_app, fv_app, eraseToFalse_closed, trueTerm_closed]
  simp [fv_var]

theorem zeroTestTerm_start (n : ℕ) :
    Relation.ReflTransGen Beta (app zeroTestTerm (numeral n))
      (iterateApp eraseToFalse trueTerm n) := by
  have h : Beta (app zeroTestTerm (numeral n)) (app (app (numeral n) eraseToFalse) trueTerm) := by
    convert Beta.contract 3 (app (app (var 3) eraseToFalse) trueTerm) (numeral n) using 1 <;> try rfl
    simp [subst_app, subst_var, subst_closed _ _ _ eraseToFalse_closed,
      subst_closed _ _ _ trueTerm_closed]
  exact (Relation.ReflTransGen.single h).trans
    (numeral_apply n eraseToFalse trueTerm (by rw [eraseToFalse_closed]; simp))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Zero test and branching
-/
theorem zeroTestTerm_zero : Relation.ReflTransGen Beta (app zeroTestTerm (numeral 0)) trueTerm :=
  zeroTestTerm_start 0

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Zero test and branching
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    The iteration formula reduces the zero test to iteration of the constant function $\lambdaab{u}{\LambdaFalse}$ starting from $\LambdaTrue$. Zero iterations leave $\LambdaTrue$. At every positive iteration count, the outermost application of the constant function reduces to $\LambdaFalse$, discarding the preceding iterate. Lift these reductions through application to the two branch terms and use the selection calculations above. Closedness follows directly from the displayed definitions.
-/
theorem zeroTestTerm_succ (n : ℕ) :
    Relation.ReflTransGen Beta (app zeroTestTerm (numeral (n + 1))) falseTerm := by
  apply (zeroTestTerm_start (n + 1)).tail
  simpa only [iterateApp, eraseToFalse, subst_closed _ _ _ falseTerm_closed]
    using Beta.contract 3 falseTerm (iterateApp eraseToFalse trueTerm n)

theorem branch_zero (A B : AlphaTerm) (hA : 2 ∉ A.fv) :
    Relation.ReflTransGen Beta (app (app (app zeroTestTerm (numeral 0)) A) B) A :=
  (beta_steps_app_left (beta_steps_app_left zeroTestTerm_zero A) B).trans (trueTerm_apply A B hA)

theorem branch_succ (n : ℕ) (A B : AlphaTerm) :
    Relation.ReflTransGen Beta (app (app (app zeroTestTerm (numeral (n + 1))) A) B) B :=
  (beta_steps_app_left (beta_steps_app_left (zeroTestTerm_succ n) A) B).trans (falseTerm_apply A B)

/-- A functional pair, used as finite state; it is not a numerical pairing code. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    To store two closed terms $A,B$ as one state, define
    $$\LambdaPairValue{A}{B}:=\lambdaab{s}{sAB},\qquad
    \LambdaPair:=\lambdaab{a}{\lambdaab{b}{\lambdaab{s}{sab}}}.$$
    The state $\LambdaPairValue{A}{B}$ is a functional pair. It is not itself a Church numeral and is distinct from a bijective numerical pairing function on $\NN^2$.
-/
def pairValue (A B : AlphaTerm) : AlphaTerm := lam 5 (app (app (var 5) A) B)

def pairTerm : AlphaTerm := lam 3 (lam 4 (lam 5 (app (app (var 5) (var 3)) (var 4))))

@[simp] theorem pairTerm_closed : pairTerm.Closed := by
  unfold pairTerm Closed
  simp [fv_lam, fv_app, fv_var] ; decide

theorem pairValue_closed {A B : AlphaTerm} (hA : A.Closed) (hB : B.Closed) :
    (pairValue A B).Closed := by
  unfold Closed pairValue
  rw [fv_lam, fv_app, fv_app, hA, hB]
  simp [fv_var]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Functional pairs and selection
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Two beta steps substitute $A,B$ into the constructor. Applying the resulting pair to any selector $S$ gives $SAB$ in one beta step, since substitution leaves the closed components unchanged. Use the true and false selection calculations. The same closedness of the components shows that the pair has no free variable.
-/
theorem pairTerm_apply {A B : AlphaTerm} (hA : A.Closed) (hB : B.Closed) :
    Relation.ReflTransGen Beta (app (app pairTerm A) B) (pairValue A B) := by
  have hAf (x : ℕ) : x ∉ A.fv := by rw [hA]; simp
  have hBf (x : ℕ) : x ∉ B.fv := by rw [hB]; simp
  have h₁ : Beta (app pairTerm A) (lam 4 (lam 5 (app (app (var 5) A) (var 4)))) := by
    convert Beta.contract 3 (lam 4 (lam 5 (app (app (var 5) (var 3)) (var 4)))) A using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 4 3 (by decide) (hAf 4), subst_lam_fresh _ _ 5 3 (by decide) (hAf 5)]
    simp [subst_app, subst_var]
  have h₂ : Beta (app (lam 4 (lam 5 (app (app (var 5) A) (var 4)))) B) (pairValue A B) := by
    convert Beta.contract 4 (lam 5 (app (app (var 5) A) (var 4))) B using 1
    rw [subst_lam_fresh _ _ 5 4 (by decide) (hBf 5)]
    simp [pairValue, subst_app, subst_var, subst_closed _ _ _ hA]
  exact .tail (.single (.app_left _ h₁)) h₂

theorem pairValue_apply {A B : AlphaTerm} (hA : A.Closed) (hB : B.Closed) (S : AlphaTerm) :
    Beta (app (pairValue A B) S) (app (app S A) B) := by
  convert Beta.contract 5 (app (app (var 5) A) B) S using 1 <;> try rfl
  simp [subst_app, subst_var, subst_closed _ _ _ hA, subst_closed _ _ _ hB]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Functional pairs and selection
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Natural numbers are supplied as Church numerals. Numerical predicates return the numeral one for true and zero for
    false; the selectors $\LambdaTrue,\LambdaFalse$ instead select the first and second branch. An unselected branch need
    not terminate. Functional pairs store terms; numerical pairs encode two natural numbers as a single numerical input.
    The arithmetic operations and numerical projections terminate on every numerical input.
-/
theorem pairValue_first {A B : AlphaTerm} (hA : A.Closed) (hB : B.Closed) :
    Relation.ReflTransGen Beta (app (pairValue A B) trueTerm) A :=
  (Relation.ReflTransGen.single (pairValue_apply hA hB trueTerm)).trans
    (trueTerm_apply A B (by rw [hA]; simp))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Functional pairs and selection
-/
theorem pairValue_second {A B : AlphaTerm} (hA : A.Closed) (hB : B.Closed) :
    Relation.ReflTransGen Beta (app (pairValue A B) falseTerm) B :=
  (Relation.ReflTransGen.single (pairValue_apply hA hB falseTerm)).trans (falseTerm_apply A B)

/-- Advance the pair of previous and current numerals. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Use a pair to retain the previous and current counter values. Define
    $$\begin{aligned}
    \LambdaPairNext&:=\lambdaab{s}{\LambdaPair\,(s\LambdaFalse)\,(\LambdaSucc(s\LambdaFalse))},\\
    \LambdaPred&:=\lambdaab{n}{\bigl(n\LambdaPairNext\,\LambdaPairValue{\ChurchNumeral{0}}{\ChurchNumeral{0}}
    \bigr)\LambdaTrue},\\
    \LambdaSub&:=\lambdaab{m}{\lambdaab{n}{n\LambdaPred\,m}}.
    \end{aligned}$$
-/
def pairNextTerm : AlphaTerm := lam 6
  (app (app pairTerm (app (var 6) falseTerm))
    (app successorTerm (app (var 6) falseTerm)))

@[simp] theorem pairNextTerm_closed : pairNextTerm.Closed := by
  unfold pairNextTerm Closed
  simp only [fv_lam, fv_app]
  rw [pairTerm_closed, falseTerm_closed, successorTerm_closed]
  simp [fv_var]

theorem pairNextTerm_apply (a b : ℕ) :
    Relation.ReflTransGen Beta (app pairNextTerm (pairValue (numeral a) (numeral b)))
      (pairValue (numeral b) (numeral (b + 1))) := by
  let S := pairValue (numeral a) (numeral b)
  have h₁ : Beta (app pairNextTerm S)
      (app (app pairTerm (app S falseTerm)) (app successorTerm (app S falseTerm))) := by
    convert Beta.contract 6 (app (app pairTerm (app (var 6) falseTerm))
      (app successorTerm (app (var 6) falseTerm))) S using 1 <;> try rfl
    simp [subst_app, subst_var, subst_closed _ _ _ pairTerm_closed,
      subst_closed _ _ _ falseTerm_closed, subst_closed _ _ _ successorTerm_closed]
  have hs : Relation.ReflTransGen Beta (app S falseTerm) (numeral b) :=
    pairValue_second (numeral_closed a) (numeral_closed b)
  exact (Relation.ReflTransGen.single h₁).trans
    ((beta_steps_app (beta_steps_app_right pairTerm hs)
      ((beta_steps_app_right successorTerm hs).trans (successorTerm_apply b))).trans
      (pairTerm_apply (numeral_closed b) (numeral_closed (b + 1))))

theorem iterate_pairNext (n : ℕ) :
    Relation.ReflTransGen Beta (iterateApp pairNextTerm (pairValue (numeral 0) (numeral 0)) n)
      (pairValue (numeral (n - 1)) (numeral n)) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    simpa only [iterateApp, Nat.add_sub_cancel] using
      (beta_steps_app_right pairNextTerm ih).trans (pairNextTerm_apply (n - 1) n)

def predecessorTerm : AlphaTerm := lam 3
  (app (app (app (var 3) pairNextTerm) (pairValue (numeral 0) (numeral 0))) trueTerm)

@[simp] theorem predecessorTerm_closed : predecessorTerm.Closed := by
  unfold predecessorTerm Closed
  simp only [fv_lam, fv_app]
  rw [pairNextTerm_closed, pairValue_closed (numeral_closed 0) (numeral_closed 0), trueTerm_closed]
  simp [fv_var]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Predecessor and subtraction
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    The pair selection and successor calculations give
    $$\LambdaPairNext\,\LambdaPairValue{\ChurchNumeral{a}}{\ChurchNumeral{b}}
    \to_\beta^*\LambdaPairValue{\ChurchNumeral{b}}{\ChurchNumeral{b+1}}.$$
    Reduce each occurrence of the second component, apply successor to one copy, and then construct the new pair. Start the iteration of $\LambdaPairNext$ at $\LambdaPairValue{\ChurchNumeral{0}}{\ChurchNumeral{0}}$. With no iterations, the state is this initial pair. For $n\ge1$, induction shows that the state after $n$ iterations is $\LambdaPairValue{\ChurchNumeral{n-1}}{\ChurchNumeral{n}}$: the first step gives the pair of zero and one, and each subsequent step replaces the first component by the current counter and increments the second. The iteration formula for numerals followed by true selection proves the two cases of the predecessor assertion.
-/
theorem predecessorTerm_apply (n : ℕ) :
    Relation.ReflTransGen Beta (app predecessorTerm (numeral n)) (numeral (n - 1)) := by
  let S := pairValue (numeral 0) (numeral 0)
  have hc : S.Closed := pairValue_closed (numeral_closed 0) (numeral_closed 0)
  have h₁ : Beta (app predecessorTerm (numeral n))
      (app (app (app (numeral n) pairNextTerm) S) trueTerm) := by
    convert Beta.contract 3 (app (app (app (var 3) pairNextTerm) S) trueTerm) (numeral n)
      using 1 <;> try rfl
    simp [subst_app, subst_var, subst_closed _ _ _ pairNextTerm_closed,
      subst_closed _ _ _ hc, subst_closed _ _ _ trueTerm_closed]
  have hf : 2 ∉ pairNextTerm.fv := by rw [pairNextTerm_closed]; simp
  exact (Relation.ReflTransGen.single h₁).trans
    ((beta_steps_app_left ((numeral_apply n pairNextTerm S hf).trans (iterate_pairNext n)) trueTerm).trans
      (pairValue_first (numeral_closed (n - 1)) (numeral_closed n)))

def subtractionTerm : AlphaTerm := lam 3 (lam 4 (app (app (var 4) predecessorTerm) (var 3)))

@[simp] theorem subtractionTerm_closed : subtractionTerm.Closed := by
  unfold subtractionTerm Closed
  simp only [fv_lam, fv_app]
  rw [predecessorTerm_closed]
  simp [fv_var]

theorem iterate_predecessor (m n : ℕ) :
    Relation.ReflTransGen Beta (iterateApp predecessorTerm (numeral m) n) (numeral (m - n)) := by
  induction n with
  | zero => simpa [iterateApp] using (Relation.ReflTransGen.refl (r := Beta) (a := numeral m))
  | succ n ih =>
    simpa only [iterateApp, Nat.sub_sub] using
      (beta_steps_app_right predecessorTerm ih).trans (predecessorTerm_apply (m - n))

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Predecessor and subtraction
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For subtraction, the two outer beta steps leave iteration of $\LambdaPred$ starting at $\ChurchNumeral{m}$. Each application decreases a positive numeral by one and leaves the zero numeral unchanged. Thus, for $n<m$, induction gives $\ChurchNumeral{m-n}$ after $n$ iterations. After $m$ iterations the result is $\ChurchNumeral{0}$, and every further iteration leaves it unchanged. This proves the case $m\le n$ as well, including $m=0$. The definitions contain only closed constants and bound variables, which proves their closedness. Together with uniqueness of numeral outputs, these reductions verify the asserted numerical functions directly in lambda calculus.
-/
theorem subtractionTerm_apply (m n : ℕ) :
    Relation.ReflTransGen Beta (app (app subtractionTerm (numeral m)) (numeral n))
      (numeral (m - n)) := by
  have hf : 4 ∉ (numeral m).fv := by rw [numeral_closed]; simp
  have h₁ : Beta (app subtractionTerm (numeral m))
      (lam 4 (app (app (var 4) predecessorTerm) (numeral m))) := by
    convert Beta.contract 3 (lam 4 (app (app (var 4) predecessorTerm) (var 3)))
      (numeral m) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 4 3 (by decide) hf]
    simp [subst_app, subst_var, subst_closed _ _ _ predecessorTerm_closed]
  have h₂ : Beta (app (lam 4 (app (app (var 4) predecessorTerm) (numeral m))) (numeral n))
      (app (app (numeral n) predecessorTerm) (numeral m)) := by
    convert Beta.contract 4 (app (app (var 4) predecessorTerm) (numeral m)) (numeral n)
      using 1
    simp [subst_app, subst_var, subst_closed _ _ _ predecessorTerm_closed,
      subst_closed _ _ _ (numeral_closed m)]
  have hf' : 2 ∉ predecessorTerm.fv := by rw [predecessorTerm_closed]; simp
  exact (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans
    ((numeral_apply n predecessorTerm (numeral m) hf').trans (iterate_predecessor m n))

end PolishSpaceBook.NamedLambda.AlphaTerm
