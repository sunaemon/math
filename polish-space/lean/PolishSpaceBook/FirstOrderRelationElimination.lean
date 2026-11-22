module

public import PolishSpaceBook.FirstOrderSimultaneousSubstitution

@[expose] public section

/-!
# Recursive elimination of defined relation symbols

There are no new function symbols, so terms retain their constructors.
At a fresh relation atom, insert its old-language definition by simultaneous
substitution. Connectives and quantifiers are traversed recursively. The
translation is first defined on named representatives; compatibility with
alpha-classes is proved in FirstOrderRelationClasses. Compatibility with
natural-deduction derivations is proved in FirstOrderRelationDerivations.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z w
variable {L : Language.{u,v}} {ι : ℕ → Type z}

namespace RelationDefinitions
variable (D : RelationDefinitions L ι)

/-- Forget the empty extra function signature in a relation-only expansion. -/
def eraseTerm : (L.sum (relationSymbols ι)).Term ℕ → L.Term ℕ
  | .var x => .var x
  | .func (Sum.inl f) ts => .func f (fun i => eraseTerm (ts i))
  | .func (Sum.inr f) _ => nomatch f

@[simp] theorem fv_eraseTerm (t : (L.sum (relationSymbols ι)).Term ℕ) :
    (eraseTerm t).varFinset = t.varFinset := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    rcases f with f | f
    · simp only [eraseTerm, Term.varFinset, ih]
    · exact nomatch f

/-- Insert defining formulas at fresh atoms, then preserve every connective and binder. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    There are no new function symbols, so leave terms, equalities, and old relation atoms unchanged.
    Replace each atom $R(\vec{t})$ for a new relation by $\varphi\subst{\vec{x}}{\vec{t}}$, using its defining formula.
    Recursively translate the subformulas of each connective and quantified formula, preserving the connective,
    the quantifier, and its bound variable.
-/
def eraseFormula : Formula (L.sum (relationSymbols ι)) → AlphaFormula L
  | .falsum => falsum
  | .equal t r => equal (eraseTerm t) (eraseTerm r)
  | .rel (Sum.inl R) ts => rel R (fun i => eraseTerm (ts i))
  | .rel (Sum.inr r) ts => (D.formula r).simultaneous (fun i => eraseTerm (ts i))
  | .binary c φ ψ => binary c (eraseFormula φ) (eraseFormula ψ)
  | .quant q x φ => quant q x (eraseFormula φ)

/-- No new free variable escapes from an inserted definition. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The free-variable assertion follows by the same
    induction: an inserted definition has only the argument terms' free variables, connectives take unions, and
    quantification removes the bound variable. Temporary names introduced inside an atom therefore cannot be
    captured by an outer quantifier or escape from the translated formula.
-/
theorem fv_eraseFormula_subset (φ : Formula (L.sum (relationSymbols ι))) :
    (D.eraseFormula φ).fv ⊆ φ.fv := by
  induction φ with
  | falsum => exact Finset.Subset.refl _
  | equal t r =>
    change (eraseTerm t).varFinset ∪ (eraseTerm r).varFinset ⊆ t.varFinset ∪ r.varFinset
    simp
  | rel R ts =>
    rcases R with R | r
    · change Finset.univ.biUnion (fun i => (eraseTerm (ts i)).varFinset) ⊆ _
      simp only [fv_eraseTerm]
      exact Finset.Subset.refl _
    · have h := fv_simultaneous_subset (D.formula r) (fun i => eraseTerm (ts i))
      have hf : (D.formula r).fv \ Finset.range _ = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr (D.freeVars r)
      simpa only [eraseFormula, hf, Finset.empty_union, argumentVars, fv_eraseTerm, Formula.fv] using h
  | binary c φ ψ ihφ ihψ =>
    simpa only [eraseFormula, fv_binary, Formula.fv] using Finset.union_subset_union ihφ ihψ
  | quant q x φ ih =>
    simpa only [eraseFormula, fv_quant, Formula.fv] using Finset.erase_subset_erase x ih

section Semantics
variable {M : Type w} [L.Structure M] [(L.sum (relationSymbols ι)).Structure M]
    [(inclusion (L := L) (ι := ι)).IsExpansionOn M]

theorem realize_eraseTerm (t : (L.sum (relationSymbols ι)).Term ℕ) (s : ℕ → M) :
    (eraseTerm t).realize s = t.realize s := by
  induction t with
  | var x => rfl
  | func f ts ih =>
    rcases f with f | f
    · simp only [eraseTerm, Term.realize_func, ih]
      exact ((inclusion (L := L) (ι := ι)).map_onFunction f _).symm
    · exact nomatch f

/-- A defined relation at arbitrary old-language terms has the prescribed truth value. -/
theorem realize_instance {n : ℕ} (r : ι n) (ts : Fin n → L.Term ℕ)
    (haxiom : ∀ s : ℕ → M, (D.definingAxiom r).Realize s) (s : ℕ → M) :
    ((D.formula r).simultaneous ts).Realize s ↔
      Structure.RelMap (L := L.sum (relationSymbols ι)) (Sum.inr r) (fun i => (ts i).realize s) := by
  rw [realize_simultaneous]
  have h := (D.realize_axiom_iff r).mp haxiom
    (fun x => if h : x < n then (ts ⟨x,h⟩).realize s else s x)
  simpa only [dite_eq_left (Fin.isLt _)] using h.symm

/-- Structural recursion proves truth preservation for every named formula. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: theorem
  title: Elimination of defined relations
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Prove truth preservation by structural induction. Old atoms have unchanged interpretations.
    For a new relation atom, the defining axiom identifies the relation at the argument values with the defining
    formula at those values. The simultaneous-substitution lemma gives exactly that assignment, even when an
    argument term contains another input variable. Connectives follow from their truth clauses.
    At a quantifier, apply the induction hypothesis under every assignment obtained by changing its bound variable;
    the universal and existential clauses then give the result.
-/
theorem realize_eraseFormula (φ : Formula (L.sum (relationSymbols ι)))
    (haxioms : ∀ n (r : ι n) (s : ℕ → M), (D.definingAxiom r).Realize s) (s : ℕ → M) :
    (D.eraseFormula φ).Realize s ↔ φ.Realize s := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t r =>
    simp only [eraseFormula, realize_equal, realize_eraseTerm, Formula.Realize]
  | rel R ts =>
    rcases R with R | r
    · change Structure.RelMap (L := L) R (fun i => (eraseTerm (ts i)).realize s) ↔
        Structure.RelMap (L := L.sum (relationSymbols ι)) (Sum.inl R) (fun i => (ts i).realize s)
      simp only [realize_eraseTerm]
      exact (iff_of_eq ((inclusion (L := L) (ι := ι)).map_onRelation R _)).symm
    · exact (D.realize_instance r (fun i => eraseTerm (ts i)) (haxioms _ r) s).trans
        (by simp only [realize_eraseTerm]; rfl)
  | binary c φ ψ ihφ ihψ =>
    rw [eraseFormula, realize_binary]
    exact c.eval_congr (ihφ s) (ihψ s)
  | quant q x φ ih =>
    rw [eraseFormula, realize_quant]
    exact q.eval_congr (fun a => ih (Function.update s x a))

end Semantics
end RelationDefinitions
end PolishSpaceBook.NamedFirstOrder
