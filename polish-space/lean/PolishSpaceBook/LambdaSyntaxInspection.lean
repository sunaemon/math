module

public import PolishSpaceBook.LambdaSyntaxCoding
public import PolishSpaceBook.LambdaNumericalProjections

@[expose] public section

/-! # Closed lambda programs inspecting numerical syntax codes

These programs read the constructor tag, payload, and unpaired fields.
They operate on Church numerals in the existing lambda calculus.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

def quotientThreeStepBody (K R : AlphaTerm) : AlphaTerm :=
  chooseLeBody (app (app multiplicationTerm (numeral 3)) (app successorTerm R))
    (app successorTerm K) (app successorTerm R) R

theorem quotientThreeStepBody_fv (K R : AlphaTerm) :
    (quotientThreeStepBody K R).fv = K.fv ∪ R.fv := by
  simp only [quotientThreeStepBody, chooseLeBody_fv, fv_app]
  rw [multiplicationTerm_closed, numeral_closed, successorTerm_closed]
  ext x
  simp only [Finset.mem_union, Finset.notMem_empty, false_or]
  tauto

theorem quotientThreeStepBody_subst (K R V : AlphaTerm) (x : ℕ) :
    (quotientThreeStepBody K R).subst x V =
      quotientThreeStepBody (K.subst x V) (R.subst x V) := by
  simp only [quotientThreeStepBody, chooseLeBody_subst, subst_app,
    subst_closed _ _ _ multiplicationTerm_closed, subst_closed _ _ _ successorTerm_closed,
    subst_closed _ _ _ (numeral_closed 3)]

theorem quotientThreeStepBody_apply (k r : ℕ) :
    Relation.ReflTransGen Beta (quotientThreeStepBody (numeral k) (numeral r))
      (numeral (if 3 * (r + 1) ≤ k + 1 then r + 1 else r)) := by
  have hr := successorTerm_apply r
  have ht := (beta_steps_app_right (app multiplicationTerm (numeral 3)) hr).trans
    (multiplicationTerm_apply 3 (r + 1))
  exact (chooseLeBody_steps ht (successorTerm_apply k) hr .refl).trans
    (chooseLeBody_apply _ _ _ _)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Define the closed step term and payload program by
    $$\begin{aligned}
    G&:=\lambdaab{k}{\lambdaab{r}{
    \LambdaLeCase{\LambdaMul\,\ChurchNumeral{3}\,(\LambdaSucc\,r)}{\LambdaSucc\,k}{\LambdaSucc\,r}{r}}},\\
    \LambdaSyntaxPayload&:=\LambdaRecursor\,G\,\ChurchNumeral{0}.
    \end{aligned}$$
    The step compares the next multiple of three with the next iteration count. Define the tag and field programs by
    $$\begin{aligned}
    \LambdaSyntaxTag&:=\lambdaab{z}{\LambdaSub\,z\,(\LambdaMul\,\ChurchNumeral{3}\,(\LambdaSyntaxPayload\,z))},\\
    \LambdaSyntaxField{j}&:=\lambdaab{z}{\LambdaNumericProjection{j}(\LambdaSyntaxPayload\,z)}\qquad(j=1,2).
    \end{aligned}$$
-/
def quotientThreeStepTerm : AlphaTerm :=
  lam 3 (lam 4 (quotientThreeStepBody (var 3) (var 4)))

@[simp] theorem quotientThreeStepTerm_closed : quotientThreeStepTerm.Closed := by
  unfold quotientThreeStepTerm Closed
  rw [fv_lam, fv_lam, quotientThreeStepBody_fv]
  simp [fv_var]
  decide

theorem quotientThreeStepTerm_apply (k r : ℕ) :
    Relation.ReflTransGen Beta
      (app (app quotientThreeStepTerm (numeral k)) (numeral r))
      (numeral (if 3 * (r + 1) ≤ k + 1 then r + 1 else r)) := by
  have h₁ : Beta (app quotientThreeStepTerm (numeral k))
      (lam 4 (quotientThreeStepBody (numeral k) (var 4))) := by
    convert Beta.contract 3 (lam 4 (quotientThreeStepBody (var 3) (var 4))) (numeral k)
      using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 4 3 (by decide) (by rw [numeral_closed]; simp),
      quotientThreeStepBody_subst]
    simp [subst_var]
  have h₂ : Beta (app (lam 4 (quotientThreeStepBody (numeral k) (var 4))) (numeral r))
      (quotientThreeStepBody (numeral k) (numeral r)) := by
    convert Beta.contract 4 (quotientThreeStepBody (numeral k) (var 4)) (numeral r) using 1
    simp [quotientThreeStepBody_subst, subst_var, subst_closed _ _ _ (numeral_closed k)]
  exact (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans
    (quotientThreeStepBody_apply k r)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Successor, multiplication and comparison show that $G$ computes the recurrence
    $$r_0=0,\qquad r_{k+1}=\begin{cases}r_k+1,&3(r_k+1)\le k+1,\\r_k,&3(r_k+1)>k+1.\end{cases}$$
    We prove $r_k=\lfloor k/3\rfloor$ by induction. It holds at zero. At stage $k$, the induction hypothesis gives $3r_k\le k<3r_k+3$. If the next comparison succeeds, $k+1=3(r_k+1)$ and the quotient increases by one. Otherwise $3r_k\le k+1<3(r_k+1)$ and the quotient is unchanged. The recursor theorem therefore gives the claimed payload reduction after $e$ iterations.
-/
theorem quotientThree_invariant (n : ℕ) :
    primitiveRec 0 (fun k r => if 3 * (r + 1) ≤ k + 1 then r + 1 else r) n = n / 3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [primitiveRec, ih]
    split_ifs <;> omega

/-- The input is the iteration count; the state is its quotient by three. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The decoder uses division by three and numerical projections. We now implement these operations by closed lambda terms,
    so subsequent programs can inspect codes within the same calculus. The payload of a code $e$ is $\lfloor e/3\rfloor$,
    and its constructor tag is $e\bmod3$.
-/
def syntaxPayloadTerm : AlphaTerm :=
  app (app recursorTerm quotientThreeStepTerm) (numeral 0)

@[simp] theorem syntaxPayloadTerm_closed : syntaxPayloadTerm.Closed :=
  closed_app (closed_app recursorTerm_closed quotientThreeStepTerm_closed) (numeral_closed 0)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Lambda terms inspecting syntax codes
-/
theorem syntaxPayloadTerm_apply (e : ℕ) :
    Relation.ReflTransGen Beta (app syntaxPayloadTerm (numeral e)) (numeral (e / 3)) := by
  have h := recursorTerm_numeral quotientThreeStepTerm_closed 0 _ quotientThreeStepTerm_apply e
  simpa only [syntaxPayloadTerm, quotientThree_invariant] using h

def syntaxTagBody (Z : AlphaTerm) : AlphaTerm :=
  app (app subtractionTerm Z)
    (app (app multiplicationTerm (numeral 3)) (app syntaxPayloadTerm Z))

theorem syntaxTagBody_fv (Z : AlphaTerm) : (syntaxTagBody Z).fv = Z.fv := by
  simp only [syntaxTagBody, fv_app]
  rw [subtractionTerm_closed, multiplicationTerm_closed, numeral_closed, syntaxPayloadTerm_closed]
  simp

theorem syntaxTagBody_subst (Z V : AlphaTerm) (x : ℕ) :
    (syntaxTagBody Z).subst x V = syntaxTagBody (Z.subst x V) := by
  simp only [syntaxTagBody, subst_app, subst_closed _ _ _ subtractionTerm_closed,
    subst_closed _ _ _ multiplicationTerm_closed, subst_closed _ _ _ (numeral_closed 3),
    subst_closed _ _ _ syntaxPayloadTerm_closed]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The decoder uses division by three and numerical projections. We now implement these operations by closed lambda terms,
    so subsequent programs can inspect codes within the same calculus. The payload of a code $e$ is $\lfloor e/3\rfloor$,
    and its constructor tag is $e\bmod3$.
-/
def syntaxTagTerm : AlphaTerm := lam 11 (syntaxTagBody (var 11))

@[simp] theorem syntaxTagTerm_closed : syntaxTagTerm.Closed := by
  unfold syntaxTagTerm Closed
  rw [fv_lam, syntaxTagBody_fv, fv_var]
  simp

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Lambda terms inspecting syntax codes
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    For the tag, substitute the input numeral, compute the payload, multiply by three, and subtract. Since $3q\le e$, the
    difference $e-3q$ is an ordinary nonnegative difference and equals $e\bmod3$. For each field, compute the payload and
    apply the corresponding numerical projection. These are finite beta-reductions in application contexts. The constants
    are closed and the displayed abstractions bind every remaining variable.
    \end{proof}
-/
theorem syntaxTagTerm_apply (e : ℕ) :
    Relation.ReflTransGen Beta (app syntaxTagTerm (numeral e)) (numeral (e % 3)) := by
  have h₁ : Beta (app syntaxTagTerm (numeral e)) (syntaxTagBody (numeral e)) := by
    convert Beta.contract 11 (syntaxTagBody (var 11)) (numeral e) using 1 <;> try rfl
    simp [syntaxTagBody_subst, subst_var]
  have hp := (beta_steps_app_right (app multiplicationTerm (numeral 3))
    (syntaxPayloadTerm_apply e)).trans (multiplicationTerm_apply 3 (e / 3))
  have h := (beta_steps_app_right (app subtractionTerm (numeral e)) hp).trans
    (subtractionTerm_apply e (3 * (e / 3)))
  have he : e - 3 * (e / 3) = e % 3 := by omega
  rw [he] at h
  exact (Relation.ReflTransGen.single h₁).trans h

/-- The Boolean chooses a fixed projection when constructing the program. -/
def syntaxFieldTerm (first : Bool) : AlphaTerm := lam 11
  (app (numericalProjectionTerm first) (app syntaxPayloadTerm (var 11)))

@[simp] theorem syntaxFieldTerm_closed (first : Bool) : (syntaxFieldTerm first).Closed := by
  unfold syntaxFieldTerm Closed
  rw [fv_lam, fv_app, fv_app, numericalProjectionTerm_closed, syntaxPayloadTerm_closed, fv_var]
  simp

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Lambda terms inspecting syntax codes
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Reading the three syntax constructors
-/
theorem syntaxFieldTerm_apply (first : Bool) (e : ℕ) :
    Relation.ReflTransGen Beta (app (syntaxFieldTerm first) (numeral e))
      (numeral (if first then (Nat.unpair (e / 3)).1 else (Nat.unpair (e / 3)).2)) := by
  have h₁ : Beta (app (syntaxFieldTerm first) (numeral e))
      (app (numericalProjectionTerm first) (app syntaxPayloadTerm (numeral e))) := by
    simpa only [syntaxFieldTerm, subst_app, subst_var, ite_true,
      subst_closed _ _ _ (numericalProjectionTerm_closed first),
      subst_closed _ _ _ syntaxPayloadTerm_closed] using
      Beta.contract 11 (app (numericalProjectionTerm first) (app syntaxPayloadTerm (var 11)))
        (numeral e)
  exact (Relation.ReflTransGen.single h₁).trans
    ((beta_steps_app_right (numericalProjectionTerm first) (syntaxPayloadTerm_apply e)).trans
      (numericalProjectionTerm_apply first (e / 3)))

/-- Tags distinguish the three constructors on every term code. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Reading the three syntax constructors
-/
theorem syntaxTagTerm_code (M : Term) :
    Relation.ReflTransGen Beta (app syntaxTagTerm (numeral M.code))
      (numeral (match M with | .var _ => 0 | .app _ _ => 1 | .lam _ _ => 2)) := by
  have h := syntaxTagTerm_apply M.code
  cases M <;> simpa [Term.code] using h

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Reading the three syntax constructors
-/
theorem syntaxPayloadTerm_var (x : ℕ) :
    Relation.ReflTransGen Beta (app syntaxPayloadTerm (numeral (Term.var x).code))
      (numeral x) := by
  simpa [Term.code] using syntaxPayloadTerm_apply (Term.var x).code

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Reading the three syntax constructors
-/
theorem syntaxFieldTerm_app (first : Bool) (M N : Term) :
    Relation.ReflTransGen Beta (app (syntaxFieldTerm first) (numeral (Term.app M N).code))
      (numeral (if first then M.code else N.code)) := by
  simpa [Term.code, Nat.add_div, Nat.unpair_pair] using
    syntaxFieldTerm_apply first (Term.app M N).code

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: corollary
  title: Reading the three syntax constructors
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Insert the three constructor-code formulas into the proposition. Division and remainder recover the payload and tag, and the inverse identities for numerical pairing recover the two fields. For a variable code only the payload is needed; the field programs are used after checking that the tag is one or two.
    \end{proof}
-/
theorem syntaxFieldTerm_lam (first : Bool) (x : ℕ) (M : Term) :
    Relation.ReflTransGen Beta (app (syntaxFieldTerm first) (numeral (Term.lam x M).code))
      (numeral (if first then x else M.code)) := by
  simpa [Term.code, Nat.add_div, Nat.unpair_pair] using
    syntaxFieldTerm_apply first (Term.lam x M).code

end PolishSpaceBook.NamedLambda.AlphaTerm
