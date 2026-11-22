module

public import PolishSpaceBook.FirstOrderClosedEquality

@[expose] public section

/-!
# Replacing equal arguments one coordinate at a time

A one-variable hole expresses a single argument replacement by the primitive
equality rule. Induction on the finite set of coordinates combines replacements
into congruence of functions and invariance of relations.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v w
variable {L : Language.{u,v}}

/-- A finite tuple with one named-variable hole and otherwise closed entries. -/
def closedTupleHole {n : ℕ} (ts : Fin n → L.Term Empty) (i : Fin n) : Fin n → L.Term ℕ :=
  fun j => if j = i then .var 0 else namedClosedTerm (ts j)

@[simp] theorem subst_closedTupleHole {n : ℕ} (ts : Fin n → L.Term Empty) (i : Fin n)
    (r : L.Term Empty) (j : Fin n) :
    termSubst (closedTupleHole ts i j) 0 (namedClosedTerm r) =
      namedClosedTerm (Function.update ts i r j) := by
  by_cases hj : j = i <;> simp [closedTupleHole, hj]

@[simp] theorem termSubst_func {n : ℕ} (f : L.Functions n) (ts : Fin n → L.Term ℕ) (x : ℕ) (r : L.Term ℕ) :
    termSubst (.func f ts) x r = .func f (fun i => termSubst (ts i) x r) := rfl

/-- A property stable under one related-coordinate replacement is stable under finitely many. -/
theorem replace_finite_tuple {A : Type w} {n : ℕ} (E : A → A → Prop) (P : (Fin n → A) → Prop)
    (ts rs : Fin n → A) (hP : P ts) (hE : ∀ i, E (ts i) (rs i))
    (hstep : ∀ i us r, E (us i) r → P us → P (Function.update us i r)) : P rs := by
  classical
  let mixed (F : Finset (Fin n)) := fun i => if i ∈ F then rs i else ts i
  have hF (F : Finset (Fin n)) : P (mixed F) := by
    induction F using Finset.induction_on with
    | empty => simpa [mixed] using hP
    | @insert i F hi ih =>
      have he : E (mixed F i) (rs i) := by simpa [mixed, hi] using hE i
      have hs := hstep i (mixed F) (rs i) he ih
      have hu : Function.update (mixed F) i (rs i) = mixed (insert i F) := by
        funext j
        by_cases hj : j = i <;> simp [mixed, hj]
      rwa [hu] at hs
  simpa [mixed] using hF Finset.univ

namespace ProvesFrom

theorem closedFunction_update {T : Set (AlphaFormula L)} {n : ℕ} (f : L.Functions n)
    (ts : Fin n → L.Term Empty) (i : Fin n) (r : L.Term Empty)
    (he : ProvesFrom T (closedEq (ts i) r)) :
    ProvesFrom T (closedEq (.func f ts) (.func f (Function.update ts i r))) := by
  let φ := equal (namedClosedTerm (.func f ts)) (.func f (closedTupleHole ts i))
  have hi : φ.subst 0 (namedClosedTerm (ts i)) = closedEq (.func f ts) (.func f ts) := by
    simp [φ, closedEq]
  have hr : φ.subst 0 (namedClosedTerm r) = closedEq (.func f ts) (.func f (Function.update ts i r)) := by
    simp [φ, closedEq]
  rw [← hr]
  exact eqElim φ 0 _ _ (hi.symm ▸ closedEq_refl T (.func f ts)) he

theorem closedRelation_update {T : Set (AlphaFormula L)} {n : ℕ} (R : L.Relations n)
    (ts : Fin n → L.Term Empty) (i : Fin n) (r : L.Term Empty)
    (he : ProvesFrom T (closedEq (ts i) r)) (hR : ProvesFrom T (closedRel R ts)) :
    ProvesFrom T (closedRel R (Function.update ts i r)) := by
  have hs := eqElim (rel R (closedTupleHole ts i)) 0 (namedClosedTerm (ts i)) (namedClosedTerm r)
    (by simpa [closedRel] using hR) he
  simpa [closedRel] using hs

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    To replace one argument of a function, start with the reflexive equality
    $f(t_1,\ldots,t_n)=f(t_1,\ldots,t_n)$ and put a variable in the chosen argument on the right.
    Equality elimination replaces that argument by any provably equal closed term.
    Replace the finitely many arguments one at a time and use transitivity to compose the resulting equalities.
    Consequently the class of the function value does not depend on the representatives.
-/
theorem closedFunction_congr {T : Set (AlphaFormula L)} {n : ℕ} (f : L.Functions n)
    (ts rs : Fin n → L.Term Empty) (h : ∀ i, ProvesFrom T (closedEq (ts i) (rs i))) :
    ProvesFrom T (closedEq (.func f ts) (.func f rs)) := by
  apply replace_finite_tuple (fun t r => ProvesFrom T (closedEq t r))
    (fun us => ProvesFrom T (closedEq (.func f ts) (.func f us))) ts rs (closedEq_refl T _) h
  intro i us r he hu
  exact hu.closedEq_trans (closedFunction_update f us i r he)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For a relation, place a variable in one argument of the atomic formula and apply equality elimination.
    This transfers provability to the replaced tuple; symmetry gives the converse.
    Again replace the finitely many arguments in succession. Since these atomic formulas are sentences,
    deductive closure identifies their provability with membership in the theory.
    This proves that the relation interpretation also does not depend on the representatives.
-/
theorem closedRelation_congr {T : Set (AlphaFormula L)} {n : ℕ} (R : L.Relations n)
    (ts rs : Fin n → L.Term Empty) (h : ∀ i, ProvesFrom T (closedEq (ts i) (rs i))) :
    ProvesFrom T (closedRel R ts) ↔ ProvesFrom T (closedRel R rs) := by
  constructor
  · intro hR
    exact replace_finite_tuple (fun t r => ProvesFrom T (closedEq t r))
      (fun us => ProvesFrom T (closedRel R us)) ts rs hR h (fun i us r => closedRelation_update R us i r)
  · intro hR
    exact replace_finite_tuple (fun t r => ProvesFrom T (closedEq t r))
      (fun us => ProvesFrom T (closedRel R us)) rs ts hR (fun i => (h i).closedEq_symm)
      (fun i us r => closedRelation_update R us i r)

end ProvesFrom
end PolishSpaceBook.NamedFirstOrder
