module

public import PolishSpaceBook.LambdaSquareRoot

@[expose] public section

/-! # Lambda programs for the two numerical pairing projections -/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- The Boolean selects which closed program to construct, not a runtime language. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    For an input variable $z$, form the open terms
    $$S:=\LambdaSqrt\,z,\qquad D:=\LambdaSub\,z\,(\LambdaMul\,S\,S).$$
    Define the two closed numerical projections by
    $$\begin{aligned}
    \LambdaNumericProjection{1}&:=\lambdaab{z}{\LambdaLeCase{\LambdaSucc\,D}{S}{D}{S}},\\
    \LambdaNumericProjection{2}&:=\lambdaab{z}{\LambdaLeCase{\LambdaSucc\,D}{S}{S}{\LambdaSub\,D\,S}}.
    \end{aligned}$$
    Here $S$ and $D$ are expanded inside each abstraction.
-/
def numericalProjectionBody (first : Bool) (Z : AlphaTerm) : AlphaTerm :=
  let S := app squareRootTerm Z
  let D := app (app subtractionTerm Z) (app (app multiplicationTerm S) S)
  chooseLeBody (app successorTerm D) S
    (if first then D else S)
    (if first then S else app (app subtractionTerm D) S)

theorem numericalProjectionBody_fv (first : Bool) (Z : AlphaTerm) :
    (numericalProjectionBody first Z).fv = Z.fv := by
  cases first <;> simp only [numericalProjectionBody, Bool.false_eq_true, ↓reduceIte,
    chooseLeBody_fv, fv_app]
  all_goals
    rw [squareRootTerm_closed, subtractionTerm_closed, multiplicationTerm_closed, successorTerm_closed]
    simp

theorem numericalProjectionBody_subst (first : Bool) (Z V : AlphaTerm) (x : ℕ) :
    (numericalProjectionBody first Z).subst x V = numericalProjectionBody first (Z.subst x V) := by
  cases first <;> simp only [numericalProjectionBody, Bool.false_eq_true, ↓reduceIte,
    chooseLeBody_subst, subst_app, subst_closed _ _ _ squareRootTerm_closed,
    subst_closed _ _ _ subtractionTerm_closed, subst_closed _ _ _ multiplicationTerm_closed,
    subst_closed _ _ _ successorTerm_closed]

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: proof
  excerpt: |
    After substituting the input numeral, reduce each copy of $S$ to the numeral for $s=\lfloor\sqrt z\rfloor$ and each copy of $D$ to the numeral for $d=z-s^2$. The comparison tests $d+1\le s$, equivalently $d<s$. In that case the two branches return $d$ and $s$; otherwise they return $s$ and $d-s$. These are the two clauses of the inverse already proved in §{sec:lambda-numerical-pairing}. The encode/decode identity gives the last assertion. The only free variable of each projection body is $z$, which is bound in the displayed terms.
-/
theorem numericalProjectionBody_apply (first : Bool) (z : ℕ) :
    Relation.ReflTransGen Beta (numericalProjectionBody first (numeral z))
      (numeral (if first then (Nat.unpair z).1 else (Nat.unpair z).2)) := by
  let s := Nat.sqrt z
  let d := z - s * s
  have hs := squareRootTerm_apply z
  have hm := (beta_steps_app (beta_steps_app_right multiplicationTerm hs) hs).trans
    (multiplicationTerm_apply s s)
  have hd := (beta_steps_app_right (app subtractionTerm (numeral z)) hm).trans
    (subtractionTerm_apply z (s * s))
  have ht := (beta_steps_app_right successorTerm hd).trans (successorTerm_apply d)
  have hr := (beta_steps_app (beta_steps_app_right subtractionTerm hd) hs).trans
    (subtractionTerm_apply d s)
  cases first
  · have h := (chooseLeBody_steps ht hs hs hr).trans (chooseLeBody_apply (d + 1) s s (d - s))
    simpa only [numericalProjectionBody, Bool.false_eq_true, ↓reduceIte, Nat.unpair,
      Nat.add_one_le_iff, s, d, apply_ite Prod.snd, Prod.snd] using h
  · have h := (chooseLeBody_steps ht hs hd hs).trans (chooseLeBody_apply (d + 1) s d s)
    simpa only [numericalProjectionBody, ↓reduceIte, Nat.unpair,
      Nat.add_one_le_iff, s, d, apply_ite Prod.fst, Prod.fst] using h

def numericalProjectionTerm (first : Bool) : AlphaTerm :=
  lam 11 (numericalProjectionBody first (var 11))

@[simp] theorem numericalProjectionTerm_closed (first : Bool) :
    (numericalProjectionTerm first).Closed := by
  unfold numericalProjectionTerm Closed
  rw [fv_lam, numericalProjectionBody_fv, fv_var]
  simp

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Numerical projections by lambda terms
-/
theorem numericalProjectionTerm_apply (first : Bool) (z : ℕ) :
    Relation.ReflTransGen Beta (app (numericalProjectionTerm first) (numeral z))
      (numeral (if first then (Nat.unpair z).1 else (Nat.unpair z).2)) := by
  have h : Beta (app (numericalProjectionTerm first) (numeral z))
      (numericalProjectionBody first (numeral z)) := by
    convert Beta.contract 11 (numericalProjectionBody first (var 11)) (numeral z) using 1 <;> try rfl
    simp [numericalProjectionBody_subst, subst_var]
  exact (Relation.ReflTransGen.single h).trans (numericalProjectionBody_apply first z)

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: statement
  kind: proposition
  title: Numerical projections by lambda terms
-/
theorem numericalProjectionTerm_pair (first : Bool) (a b : ℕ) :
    Relation.ReflTransGen Beta (app (numericalProjectionTerm first) (numeral (Nat.pair a b)))
      (numeral (if first then a else b)) := by
  simpa only [squarePair_decode_encode] using numericalProjectionTerm_apply first (Nat.pair a b)

end PolishSpaceBook.NamedLambda.AlphaTerm
