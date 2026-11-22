module

public import PolishSpaceBook.LambdaPrimitiveRecursion
public import Mathlib.Data.Nat.Pairing

@[expose] public section

/-! # The book's numerical pairing function computed by a closed lambda term -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- The arithmetic body of the square-shell pairing function. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    The forward numerical pairing has a direct lambda implementation using the arithmetic terms already constructed. In variables $m,n$, abbreviate the following open terms by $T,L,U$:
    $$\begin{aligned}
    T&:=\LambdaZeroTest\,(\LambdaSub\,(\LambdaSucc\,m)\,n),\\
    L&:=\LambdaAdd\,(\LambdaMul\,n\,n)\,m,\\
    U&:=\LambdaAdd\,(\LambdaAdd\,(\LambdaMul\,m\,m)\,m)\,n.
    \end{aligned}$$
    Expand these abbreviations before abstraction and put
    $$\LambdaNumericPair:=\lambdaab{m}{\lambdaab{n}{TLU}}.$$
-/
def numericalPairBody (M N : AlphaTerm) : AlphaTerm :=
  let test := app zeroTestTerm (app (app subtractionTerm (app successorTerm M)) N)
  let lo := app (app additionTerm (app (app multiplicationTerm N) N)) M
  let hi := app (app additionTerm (app (app additionTerm (app (app multiplicationTerm M) M)) M)) N
  app (app test lo) hi

theorem numericalPairBody_fv (M N : AlphaTerm) :
    (numericalPairBody M N).fv = M.fv ∪ N.fv := by
  unfold numericalPairBody
  simp only [fv_app]
  rw [zeroTestTerm_closed, subtractionTerm_closed, successorTerm_closed,
    additionTerm_closed, multiplicationTerm_closed]
  ext x
  simp only [Finset.mem_union, Finset.notMem_empty, false_or]
  tauto

theorem numericalPairBody_subst (M N R : AlphaTerm) (x : ℕ) :
    (numericalPairBody M N).subst x R = numericalPairBody (M.subst x R) (N.subst x R) := by
  simp only [numericalPairBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed,
    subst_closed _ _ _ subtractionTerm_closed, subst_closed _ _ _ successorTerm_closed,
    subst_closed _ _ _ additionTerm_closed, subst_closed _ _ _ multiplicationTerm_closed]

def numericalPairTerm : AlphaTerm := lam 3 (lam 4 (numericalPairBody (var 3) (var 4)))

@[simp] theorem numericalPairTerm_closed : numericalPairTerm.Closed := by
  unfold numericalPairTerm Closed
  rw [fv_lam, fv_lam, numericalPairBody_fv]
  simp [fv_var]
  decide

theorem numericalPairTerm_start (m n : ℕ) :
    Relation.ReflTransGen Beta (app (app numericalPairTerm (numeral m)) (numeral n))
      (numericalPairBody (numeral m) (numeral n)) := by
  have hf : 4 ∉ (numeral m).fv := by rw [numeral_closed]; simp
  have h₁ : Beta (app numericalPairTerm (numeral m)) (lam 4 (numericalPairBody (numeral m) (var 4))) := by
    convert Beta.contract 3 (lam 4 (numericalPairBody (var 3) (var 4))) (numeral m) using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 4 3 (by decide) hf, numericalPairBody_subst]
    simp [subst_var]
  have h₂ : Beta (app (lam 4 (numericalPairBody (numeral m) (var 4))) (numeral n))
      (numericalPairBody (numeral m) (numeral n)) := by
    convert Beta.contract 4 (numericalPairBody (numeral m) (var 4)) (numeral n) using 1
    simp [numericalPairBody_subst, subst_var, subst_closed _ _ _ (numeral_closed m)]
  exact .tail (.single (.app_left _ h₁)) h₂

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    Two beta steps substitute the closed numerals into the body. The arithmetic reductions turn the branch arguments into the numerals for $b^2+a$ and $a^2+a+b$. If $a<b$, then $a+1\le b$, so the subtraction term in the test reduces to $\ChurchNumeral{0}$ and the zero test selects the first branch. If $b\le a$, that subtraction term reduces to $\ChurchNumeral{a+1-b}$, whose value is positive, so the second branch is selected. These are precisely the two clauses of the pairing definition. All constants are closed and both input variables are bound, proving closedness.
-/
theorem numericalPairBody_apply (m n : ℕ) :
    Relation.ReflTransGen Beta (numericalPairBody (numeral m) (numeral n)) (numeral (Nat.pair m n)) := by
  have htest := beta_steps_app_right zeroTestTerm
    ((beta_steps_app_left (beta_steps_app_right subtractionTerm (successorTerm_apply m)) (numeral n)).trans
      (subtractionTerm_apply (m + 1) n))
  have hlo := (beta_steps_app_left (beta_steps_app_right additionTerm (multiplicationTerm_apply n n))
    (numeral m)).trans (additionTerm_apply (n * n) m)
  have hhi := (beta_steps_app_left (beta_steps_app_right additionTerm
    ((beta_steps_app_left (beta_steps_app_right additionTerm (multiplicationTerm_apply m m))
      (numeral m)).trans (additionTerm_apply (m * m) m))) (numeral n)).trans
        (additionTerm_apply (m * m + m) n)
  have hs := beta_steps_app (beta_steps_app htest hlo) hhi
  change Relation.ReflTransGen Beta (numericalPairBody (numeral m) (numeral n))
    (app (app (app zeroTestTerm (numeral ((m + 1) - n))) (numeral (n * n + m)))
      (numeral (m * m + m + n))) at hs
  apply hs.trans
  by_cases h : m < n
  · have hz : m + 1 - n = 0 := Nat.sub_eq_zero_of_le (Nat.succ_le_of_lt h)
    rw [hz, Nat.pair, ite_eq_left h]
    exact branch_zero _ _ (by rw [numeral_closed]; simp)
  · have hz : m + 1 - n ≠ 0 := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
    rw [hk, Nat.pair, ite_eq_right h]
    exact branch_succ k _ _

/-- A direct lambda implementation of the canonical bijection on natural numbers. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Numerical pairing by a lambda term
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    For numerical data use the \termdefine{square-shell pairing}
    $$\NatPair{a}{b}:=
    \begin{cases}
    b^2+a,&a<b,\\
    a^2+a+b,&b\le a.
    \end{cases}$$
    Pairs with $\max(a,b)=s$ occupy the consecutive integers from $s^2$ through $(s+1)^2-1$.
-/
theorem numericalPairTerm_apply (m n : ℕ) :
    Relation.ReflTransGen Beta (app (app numericalPairTerm (numeral m)) (numeral n))
      (numeral (Nat.pair m n)) :=
  (numericalPairTerm_start m n).trans (numericalPairBody_apply m n)

/-- Decoding follows the two pieces of each square shell. This is a numerical
identity, not yet a lambda implementation of the inverse projections. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Inverse of square-shell pairing
-/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    The square-root bounds give $s^2\le z<(s+1)^2$, hence $0\le d\le 2s$. If $d<s$, pairing $(d,s)$ gives $s^2+d=z$. If $s\le d$, then $d-s\le s$, and pairing $(s,d-s)$ gives $s^2+s+(d-s)=z$. Conversely, if $a<b$, the number $b^2+a$ has integer square root $b$ and remainder $a<b$, so decoding returns $(a,b)$. If $b\le a$, the number $a^2+a+b$ has integer square root $a$ and remainder $a+b$; the second inverse clause again returns $(a,b)$. Both round trips hold, including zero.
-/
theorem squarePair_decode_encode (a b : ℕ) : Nat.unpair (Nat.pair a b) = (a, b) := by
  dsimp only [Nat.pair]
  split_ifs with h
  · have hs : Nat.sqrt (b * b + a) = b :=
      Nat.sqrt_add_eq _ (le_trans (le_of_lt h) (Nat.le_add_left _ _))
    simp [Nat.unpair, hs, h]
  · have hs : Nat.sqrt (a * a + (a + b)) = a := by
      rw [Nat.sqrt_add_eq]
      exact Nat.add_le_add_left (le_of_not_gt h) _
    simp [Nat.unpair, hs, Nat.add_assoc]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Inverse of square-shell pairing
-/
theorem squarePair_encode_decode (n : ℕ) : Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 = n := by
  dsimp only [Nat.unpair]
  let s := Nat.sqrt n
  have hs : s * s + (n - s * s) = n := Nat.add_sub_cancel' (Nat.sqrt_le _)
  split_ifs with h
  · simp [s, Nat.pair, h, hs]
  · have hd : n - s * s - s ≤ s := Nat.sub_le_iff_le_add.2
      (Nat.sub_le_iff_le_add'.2 (by rw [← Nat.add_assoc]; apply Nat.sqrt_le_add))
    simp [s, Nat.pair, hd.not_gt, Nat.add_assoc, Nat.add_sub_cancel' (le_of_not_gt h), hs]

end PolishSpaceBook.NamedLambda.AlphaTerm
