module

public import PolishSpaceBook.FirstOrderSubstitutionCorrespondence

@[expose] public section

/-!
# Relation elimination on alpha-classes

Compare bound names syntactically, including inside instantiated definitions.
This proves independence of representatives without identifying logically
equivalent formulas. FirstOrderRelationSubstitution and FirstOrderRelationDerivations
extend this translation to substitution and derivations.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z w
variable {L : Language.{u,v}} {ι : ℕ → Type z}

namespace RelationDefinitions

theorem eraseTerm_corresponds {R : ℕ → ℕ → Prop}
    {t r : (L.sum (relationSymbols ι)).Term ℕ} (h : TermRel R t r) :
    TermRel R (eraseTerm t) (eraseTerm r) := by
  induction h with
  | var h => exact .var h
  | func f h ih =>
    rcases f with f | f
    · exact .func f ih
    · exact nomatch f

variable (D : RelationDefinitions L ι)

/-- Elimination respects matching free names and corresponding bound positions. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Now induct on a comparison of two formulas in the expanded language, allowing its relation on names to vary.
    Old atoms preserve the comparison. At a new relation atom, apply the preceding instance comparison to its defining
    formula. Connectives preserve the induction hypotheses; under a quantifier, apply the hypothesis with the updated
    bound-name relation. Taking equality as the initial relation proves the assertion by the comparison lemma.
    Hence the recursive translation descends to $\alpha$-classes. Its truth and free-variable assertions follow from
    those already proved for representatives.
-/
theorem eraseFormula_corresponds {R : ℕ → ℕ → Prop}
    {φ ψ : Formula (L.sum (relationSymbols ι))} (h : Formula.NameRel R φ ψ) :
    Corresponds R (D.eraseFormula φ) (D.eraseFormula ψ) := by
  induction h with
  | falsum R => exact Corresponds.falsum R
  | equal h h' => exact Corresponds.equal (eraseTerm_corresponds h) (eraseTerm_corresponds h')
  | rel P h =>
    rcases P with P | r
    · exact Corresponds.rel P (fun i => eraseTerm_corresponds (h i))
    · exact simultaneous_corresponds (D.formula r) _ _ _ (D.freeVars r)
        (fun i => eraseTerm_corresponds (h i))
  | binary c h h' ih ih' => exact Corresponds.binary c ih ih'
  | quant q h ih => exact Corresponds.quant q ih

/-- The recursive translation is independent of the named representative. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Bound names in relation elimination
-/
theorem eraseFormula_alpha {φ ψ : Formula (L.sum (relationSymbols ι))}
    (h : Formula.Alpha φ ψ) : D.eraseFormula φ = D.eraseFormula ψ :=
  (D.eraseFormula_corresponds h.nameRel).eq

/-- Eliminate defined relations directly on alpha-equivalence classes. -/
def eliminate : AlphaFormula (L.sum (relationSymbols ι)) → AlphaFormula L :=
  Quotient.lift D.eraseFormula (fun _ _ h => D.eraseFormula_alpha h)

@[simp] theorem eliminate_mk (φ : Formula (L.sum (relationSymbols ι))) :
    D.eliminate (AlphaFormula.mk φ) = D.eraseFormula φ := rfl

@[simp] theorem eliminate_binary (c : Connective)
    (φ ψ : AlphaFormula (L.sum (relationSymbols ι))) :
    D.eliminate (binary c φ ψ) = binary c (D.eliminate φ) (D.eliminate ψ) := by
  induction φ using Quotient.inductionOn with | _ φ =>
    induction ψ using Quotient.inductionOn with | _ ψ => rfl

@[simp] theorem eliminate_quant (q : Quantifier) (x : ℕ)
    (φ : AlphaFormula (L.sum (relationSymbols ι))) :
    D.eliminate (quant q x φ) = quant q x (D.eliminate φ) := by
  induction φ using Quotient.inductionOn with | _ φ => rfl

theorem fv_eliminate_subset (φ : AlphaFormula (L.sum (relationSymbols ι))) :
    (D.eliminate φ).fv ⊆ φ.fv := by
  induction φ using Quotient.inductionOn with | _ φ => exact D.fv_eraseFormula_subset φ

section Semantics
variable {M : Type w} [L.Structure M] [(L.sum (relationSymbols ι)).Structure M]
    [(inclusion (L := L) (ι := ι)).IsExpansionOn M]

theorem realize_eliminate (φ : AlphaFormula (L.sum (relationSymbols ι)))
    (haxioms : ∀ n (r : ι n) (s : ℕ → M), (D.definingAxiom r).Realize s) (s : ℕ → M) :
    (D.eliminate φ).Realize s ↔ φ.Realize s := by
  induction φ using Quotient.inductionOn with | _ φ => exact D.realize_eraseFormula φ haxioms s

end Semantics
end RelationDefinitions
end PolishSpaceBook.NamedFirstOrder
