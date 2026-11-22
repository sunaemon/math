module

public import PolishSpaceBook.LambdaNumeralOperations

@[expose] public section

/-! # Numerical comparisons by closed lambda terms

These elementary procedures depend only on numeral arithmetic, booleans and
pairs. Syntax coding and free-variable analysis use them later.
-/
namespace PolishSpaceBook.NamedLambda.AlphaTerm

/-- Select X when A is at most B, using truncated subtraction and zero testing. -/
/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    For lambda terms $A,B,X,Y$, abbreviate
    $$\LambdaLeCase{A}{B}{X}{Y}:=\LambdaZeroTest\,(\LambdaSub\,A\,B)\,X\,Y.$$
    On numeral arguments, this term selects $X$ when the number represented by $A$ is at most that represented by $B$, and selects $Y$ otherwise. Indeed, the two cases of the subtraction formula show that the test argument reduces to the zero numeral in the first case and to a positive numeral otherwise. The zero-test reductions therefore select the required branch. This is an abbreviation for the displayed lambda term.
-/
def chooseLeBody (A B X Y : AlphaTerm) : AlphaTerm :=
  app (app (app zeroTestTerm (app (app subtractionTerm A) B)) X) Y

theorem chooseLeBody_fv (A B X Y : AlphaTerm) :
    (chooseLeBody A B X Y).fv = A.fv ∪ B.fv ∪ X.fv ∪ Y.fv := by
  simp only [chooseLeBody, fv_app]
  rw [zeroTestTerm_closed, subtractionTerm_closed]
  simp

theorem chooseLeBody_subst (A B X Y R : AlphaTerm) (x : ℕ) :
    (chooseLeBody A B X Y).subst x R =
      chooseLeBody (A.subst x R) (B.subst x R) (X.subst x R) (Y.subst x R) := by
  simp only [chooseLeBody, subst_app, subst_closed _ _ _ zeroTestTerm_closed,
    subst_closed _ _ _ subtractionTerm_closed]

theorem chooseLeBody_steps {A A' B B' X X' Y Y' : AlphaTerm}
    (hA : Relation.ReflTransGen Beta A A') (hB : Relation.ReflTransGen Beta B B')
    (hX : Relation.ReflTransGen Beta X X') (hY : Relation.ReflTransGen Beta Y Y') :
    Relation.ReflTransGen Beta (chooseLeBody A B X Y) (chooseLeBody A' B' X' Y') :=
  beta_steps_app (beta_steps_app (beta_steps_app_right zeroTestTerm
    (beta_steps_app (beta_steps_app_right subtractionTerm hA) hB)) hX) hY

theorem chooseLeBody_apply (a b x y : ℕ) :
    Relation.ReflTransGen Beta (chooseLeBody (numeral a) (numeral b) (numeral x) (numeral y))
      (numeral (if a ≤ b then x else y)) := by
  apply (beta_steps_app_left (beta_steps_app_left (beta_steps_app_right zeroTestTerm
    (subtractionTerm_apply a b)) (numeral x)) (numeral y)).trans
  by_cases h : a ≤ b
  · rw [ite_eq_left h, Nat.sub_eq_zero_of_le h]
    exact branch_zero _ _ (by rw [numeral_closed]; simp)
  · have hz : a - b ≠ 0 := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
    rw [ite_eq_right h, hk]
    exact branch_succ k _ _

/-@ booklink:
  source: polish-space-book/appendix-lambda-calculus-computability.md
  target: prose
  excerpt: |
    We use one and zero as the numerical answers to a predicate. Define equality testing by
    $$\begin{aligned}
    E(u,v)&:=\LambdaLeCase{v}{u}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
    \LambdaEqual&:=\lambdaab{u}{\lambdaab{v}{\LambdaLeCase{u}{v}{E(u,v)}{\ChurchNumeral{0}}}}.
    \end{aligned}$$
    Expand $E$ inside the abstractions. The two comparisons give
    $$\LambdaEqual\,\ChurchNumeral{i}\,\ChurchNumeral{j}\to_\beta^*
    \begin{cases}\ChurchNumeral{1},&i=j,\\\ChurchNumeral{0},&i\ne j.\end{cases}$$
-/
def equalityBody (X Y : AlphaTerm) : AlphaTerm :=
  chooseLeBody X Y (chooseLeBody Y X (numeral 1) (numeral 0)) (numeral 0)

theorem equalityBody_fv (X Y : AlphaTerm) : (equalityBody X Y).fv = X.fv ∪ Y.fv := by
  simp only [equalityBody, chooseLeBody_fv]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem equalityBody_subst (X Y W : AlphaTerm) (x : ℕ) :
    (equalityBody X Y).subst x W = equalityBody (X.subst x W) (Y.subst x W) := by
  simp only [equalityBody, chooseLeBody_subst, subst_closed _ _ _ (numeral_closed 1),
    subst_closed _ _ _ (numeral_closed 0)]

theorem equalityBody_apply (x y : ℕ) :
    Relation.ReflTransGen Beta (equalityBody (numeral x) (numeral y))
      (numeral (if x = y then 1 else 0)) := by
  have h := (chooseLeBody_steps .refl .refl (chooseLeBody_apply y x 1 0) .refl).trans
    (chooseLeBody_apply x y (if y ≤ x then 1 else 0) 0)
  have he : (if x ≤ y then if y ≤ x then 1 else 0 else 0) = (if x = y then 1 else 0) := by
    split_ifs <;> omega
  simpa only [equalityBody, he] using h

def equalityTerm : AlphaTerm := lam 14 (lam 16 (equalityBody (var 14) (var 16)))

@[simp] theorem equalityTerm_closed : equalityTerm.Closed := by
  unfold equalityTerm Closed
  rw [fv_lam, fv_lam, equalityBody_fv]
  simp [fv_var]
  decide

theorem equalityTerm_apply (x y : ℕ) :
    Relation.ReflTransGen Beta (app (app equalityTerm (numeral x)) (numeral y))
      (numeral (if x = y then 1 else 0)) := by
  have h₁ : Beta (app equalityTerm (numeral x)) (lam 16 (equalityBody (numeral x) (var 16))) := by
    convert Beta.contract 14 (lam 16 (equalityBody (var 14) (var 16))) (numeral x)
      using 1 <;> try rfl
    rw [subst_lam_fresh _ _ 16 14 (by decide) (by rw [numeral_closed]; simp), equalityBody_subst]
    simp [subst_var]
  have h₂ : Beta (app (lam 16 (equalityBody (numeral x) (var 16))) (numeral y))
      (equalityBody (numeral x) (numeral y)) := by
    convert Beta.contract 16 (equalityBody (numeral x) (var 16)) (numeral y) using 1
    simp [equalityBody_subst, subst_var, subst_closed _ _ _ (numeral_closed x)]
  exact (Relation.ReflTransGen.tail (.single (.app_left _ h₁)) h₂).trans (equalityBody_apply x y)

end PolishSpaceBook.NamedLambda.AlphaTerm
