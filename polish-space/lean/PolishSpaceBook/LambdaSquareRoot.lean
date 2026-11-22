module

public import PolishSpaceBook.LambdaNumericalPairing
public import PolishSpaceBook.LambdaNumericalComparison

@[expose] public section

/-! # Integer square root by bounded lambda recursion -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

def sqrtStepBody (Z K R : AlphaTerm) : AlphaTerm :=
  chooseLeBody (app (app multiplicationTerm (app successorTerm K)) (app successorTerm K))
    Z (app successorTerm K) R

theorem sqrtStepBody_fv (Z K R : AlphaTerm) : (sqrtStepBody Z K R).fv = Z.fv ∪ K.fv ∪ R.fv := by
  simp only [sqrtStepBody, chooseLeBody_fv, fv_app]
  rw [multiplicationTerm_closed, successorTerm_closed]
  ext x
  simp only [Finset.mem_union, Finset.notMem_empty, false_or]
  tauto

theorem sqrtStepBody_subst (Z K R V : AlphaTerm) (x : ℕ) :
    (sqrtStepBody Z K R).subst x V = sqrtStepBody (Z.subst x V) (K.subst x V) (R.subst x V) := by
  simp only [sqrtStepBody, chooseLeBody_subst, subst_app,
    subst_closed _ _ _ multiplicationTerm_closed, subst_closed _ _ _ successorTerm_closed]

theorem sqrtStepBody_apply (z k r : ℕ) :
    Relation.ReflTransGen Beta (sqrtStepBody (numeral z) (numeral k) (numeral r))
      (numeral (if (k + 1) * (k + 1) ≤ z then k + 1 else r)) := by
  have hk := successorTerm_apply k
  have hs := (beta_steps_app (beta_steps_app_right multiplicationTerm hk) hk).trans
    (multiplicationTerm_apply (k + 1) (k + 1))
  exact (chooseLeBody_steps hs .refl hk .refl).trans (chooseLeBody_apply _ _ _ _)

/-- The bounded step receives z, the stage k, and the last successful candidate. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    Define closed terms
    $$\begin{aligned}
    B&:=\lambdaab{z}{\ChurchNumeral{0}},\\
    H&:=\lambdaab{z}{\lambdaab{k}{\lambdaab{r}{
    \LambdaLeCase{\LambdaMul\,(\LambdaSucc\,k)\,(\LambdaSucc\,k)}{z}{\LambdaSucc\,k}{r}}}},\\
    \LambdaSqrt&:=\lambdaab{z}{\LambdaParamRec{B}{H}\,z\,z}.
    \end{aligned}$$
    Thus the input is supplied both as the fixed parameter and as the number of iterations. All abbreviations are expanded before binding variables.
-/
def sqrtStepTerm : AlphaTerm := lam 11 (lam 3 (lam 4 (sqrtStepBody (var 11) (var 3) (var 4))))

@[simp] theorem sqrtStepTerm_closed : sqrtStepTerm.Closed := by
  unfold sqrtStepTerm Closed
  rw [fv_lam, fv_lam, fv_lam, sqrtStepBody_fv]
  simp [fv_var]
  decide

theorem sqrtStepTerm_apply (z k r : ℕ) :
    Relation.ReflTransGen Beta (app (app (app sqrtStepTerm (numeral z)) (numeral k)) (numeral r))
      (numeral (if (k + 1) * (k + 1) ≤ z then k + 1 else r)) := by
  have hf (n x : ℕ) : x ∉ (numeral n).fv := by rw [numeral_closed]; simp
  have h₁ : Beta (app sqrtStepTerm (numeral z))
      (lam 3 (lam 4 (sqrtStepBody (numeral z) (var 3) (var 4)))) := by
    convert Beta.contract 11 (lam 3 (lam 4 (sqrtStepBody (var 11) (var 3) (var 4))))
      (numeral z) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 3 11 (by decide) (hf z 3),
      subst_lam_fresh _ _ 4 11 (by decide) (hf z 4), sqrtStepBody_subst]
    simp [subst_var]
  have h₂ : Beta (app (lam 3 (lam 4 (sqrtStepBody (numeral z) (var 3) (var 4)))) (numeral k))
      (lam 4 (sqrtStepBody (numeral z) (numeral k) (var 4))) := by
    convert Beta.contract 3 (lam 4 (sqrtStepBody (numeral z) (var 3) (var 4))) (numeral k)
      using 1
    rw [subst_lam_fresh _ _ 4 3 (by decide) (hf k 4), sqrtStepBody_subst]
    simp [subst_var, subst_closed _ _ _ (numeral_closed z)]
  have h₃ : Beta (app (lam 4 (sqrtStepBody (numeral z) (numeral k) (var 4))) (numeral r))
      (sqrtStepBody (numeral z) (numeral k) (numeral r)) := by
    convert Beta.contract 4 (sqrtStepBody (numeral z) (numeral k) (var 4)) (numeral r)
      using 1
    simp [sqrtStepBody_subst, subst_var, subst_closed _ _ _ (numeral_closed z),
      subst_closed _ _ _ (numeral_closed k)]
  exact (Relation.ReflTransGen.tail (.tail (.single (.app_left _ (.app_left _ h₁))) (.app_left _ h₂)) h₃).trans
    (sqrtStepBody_apply z k r)

def zeroBaseTerm : AlphaTerm := lam 11 (numeral 0)

@[simp] theorem zeroBaseTerm_closed : zeroBaseTerm.Closed := by
  unfold zeroBaseTerm Closed
  rw [fv_lam, numeral_closed]
  simp

theorem zeroBaseTerm_apply (X : AlphaTerm) : Beta (app zeroBaseTerm X) (numeral 0) := by
  simpa only [zeroBaseTerm, subst_closed _ _ _ (numeral_closed 0)] using Beta.contract 11 (numeral 0) X

/-- Scanning k stages stores exactly min(k, floor(sqrt(z))). -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Fix $z$ and put $s=\lfloor\sqrt z\rfloor$. The step term computes the recurrence
    $$r_0=0,\qquad r_{k+1}=\begin{cases}k+1,&(k+1)^2\le z,\\r_k,&(k+1)^2>z.\end{cases}$$
    We claim that $r_k=\min(k,s)$. The claim holds at zero. If $k+1\le s$, then $(k+1)^2\le z$ and the next value is $k+1$.
    Otherwise $s\le k$, the test fails, and the induction hypothesis gives the retained value $s$. This proves the claim by
    induction. The parameterized recursor therefore returns the numeral for $\min(z,s)$ after $z$ iterations. Since $s\le
    z$, this is the numeral for $s$, including when $z=0$. Each arithmetic operation and branch has a finite beta-reduction,
    so the recursor theorem supplies a finite reduction of the whole term.
-/
theorem boundedSqrt_invariant (z k : ℕ) :
    primitiveRec 0 (fun k r => if (k + 1) * (k + 1) ≤ z then k + 1 else r) k = min k (Nat.sqrt z) := by
  induction k with
  | zero => simp [primitiveRec]
  | succ k ih =>
    rw [primitiveRec, ih]
    simp only [← Nat.le_sqrt]
    by_cases h : k + 1 ≤ Nat.sqrt z
    · simp [h]
    · have h' : Nat.sqrt z ≤ k := by omega
      simp [h, Nat.min_eq_right h', Nat.min_eq_right (Nat.le_succ_of_le h')]

def squareRootTerm : AlphaTerm := lam 11
  (app (app (parameterRecursor zeroBaseTerm sqrtStepTerm) (var 11)) (var 11))

@[simp] theorem squareRootTerm_closed : squareRootTerm.Closed := by
  unfold squareRootTerm Closed
  simp only [fv_lam, fv_app]
  rw [parameterRecursor_closed zeroBaseTerm_closed sqrtStepTerm_closed]
  simp [fv_var]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Integer square root by a lambda term
-/
theorem squareRootTerm_apply (z : ℕ) :
    Relation.ReflTransGen Beta (app squareRootTerm (numeral z)) (numeral (Nat.sqrt z)) := by
  have h₁ : Beta (app squareRootTerm (numeral z))
      (app (app (parameterRecursor zeroBaseTerm sqrtStepTerm) (numeral z)) (numeral z)) := by
    convert Beta.contract 11
      (app (app (parameterRecursor zeroBaseTerm sqrtStepTerm) (var 11)) (var 11)) (numeral z)
      using 1 <;> try rfl
    simp [subst_app, subst_var,
      subst_closed _ _ _ (parameterRecursor_closed zeroBaseTerm_closed sqrtStepTerm_closed)]
  have h := parameterRecursor_apply zeroBaseTerm_closed sqrtStepTerm_closed (numeral_closed z) 0
    (fun k r => if (k + 1) * (k + 1) ≤ z then k + 1 else r)
    (.single (zeroBaseTerm_apply _)) (sqrtStepTerm_apply z) z
  rw [boundedSqrt_invariant, Nat.min_eq_right (Nat.sqrt_le_self z)] at h
  exact (Relation.ReflTransGen.single h₁).trans h

end PolishSpaceBook.NamedLambda.AlphaTerm
