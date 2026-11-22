module

public import PolishSpaceBook.FirstOrderSimultaneousComposition

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Relation elimination commutes with substitution

Choose a representative whose binders avoid the substitution target and term.
Induct on that representative; instantiated relation definitions use the
simultaneous-substitution composition lemma.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}

namespace AlphaFormula

theorem subst_quant_fresh (q : Quantifier) (y : ℕ) (φ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ)
    (hyx : y ≠ x) (hy : y ∉ t.varFinset) :
    (quant q y φ).subst x t = quant q y (φ.subst x t) := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact congrArg mk (by dsimp only; rw [Formula.subst_quant, ite_eq_right hyx, ite_eq_left hy])

end AlphaFormula
namespace RelationDefinitions

theorem eraseTerm_subst (r : (L.sum (relationSymbols ι)).Term ℕ) (x : ℕ)
    (t : (L.sum (relationSymbols ι)).Term ℕ) :
    eraseTerm (termSubst r x t) = termSubst (eraseTerm r) x (eraseTerm t) := by
  induction r with
  | var y => by_cases h : y = x <;> simp [termSubst, Term.subst, h, eraseTerm]
  | func f ts ih =>
    rcases f with f | f
    · simp only [termSubst_func, eraseTerm, ih]
    · exact nomatch f

variable (D : RelationDefinitions L ι)

theorem eraseFormula_subst_fresh (φ : Formula (L.sum (relationSymbols ι))) (x : ℕ)
    (t : (L.sum (relationSymbols ι)).Term ℕ) (hb : Disjoint φ.boundNames (insert x t.varFinset)) :
    D.eraseFormula (φ.subst x t) = (D.eraseFormula φ).subst x (eraseTerm t) := by
  induction φ with
  | falsum => rfl
  | equal a b => simp only [Formula.subst_equal, eraseFormula, eraseTerm_subst]; rfl
  | rel P ts =>
    rw [Formula.subst_rel]
    rcases P with P | r
    · simp only [eraseFormula, eraseTerm_subst]; rfl
    · simp only [eraseFormula, eraseTerm_subst]
      exact (simultaneous_subst (D.formula r) _ x (eraseTerm t) (D.freeVars r)).symm
  | binary c φ ψ ihφ ihψ =>
    have hd := Finset.disjoint_union_left.mp hb
    simp only [Formula.subst_binary, eraseFormula, subst_binary, ihφ hd.1, ihψ hd.2]
  | quant q y φ ih =>
    have hd : y ∉ insert x t.varFinset ∧ Disjoint φ.boundNames (insert x t.varFinset) :=
      Finset.disjoint_insert_left.mp hb
    have hy : y ≠ x ∧ y ∉ t.varFinset := by simpa using hd.1
    rw [Formula.subst_quant, ite_eq_right hy.1, ite_eq_left hy.2, eraseFormula, eraseFormula,
      subst_quant_fresh q y _ x _ hy.1 (by simpa using hy.2), ih hd.2]

/-- Translation commutes with capture-avoiding substitution on alpha-classes. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For a general formula, first choose its bound names to avoid the substitution variable and the variables of the
    inserted term. Induct on the formula. Old atoms use ordinary term substitution, and new relation atoms use the
    identity just proved. Connectives commute with both operations. At a quantifier, the bound name is neither the
    substitution target nor a variable of the inserted term, so substitution passes into the body on both sides.
    The induction hypothesis completes this case. Independence of representatives gives the assertion on
    $\alpha$-classes.
-/
theorem eliminate_subst (φ : AlphaFormula (L.sum (relationSymbols ι))) (x : ℕ)
    (t : (L.sum (relationSymbols ι)).Term ℕ) :
    D.eliminate (φ.subst x t) = (D.eliminate φ).subst x (eraseTerm t) := by
  obtain ⟨ψ, he, hψ⟩ := φ.exists_fresh_rep (insert x t.varFinset)
  rw [← he, subst_mk, eliminate_mk, eliminate_mk]
  exact D.eraseFormula_subst_fresh ψ x t hψ

end RelationDefinitions
end PolishSpaceBook.NamedFirstOrder
