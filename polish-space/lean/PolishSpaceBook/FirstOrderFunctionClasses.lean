module

public import PolishSpaceBook.FirstOrderTermGraphCorrespondence

@[expose] public section

/-!
# Function elimination on alpha-classes

Witness blocks match position by position. Correspondence of terms therefore
lifts to correspondence of atomic translations, then of all formulas. Equality
of alpha-classes follows syntactically, without using semantic completeness.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z w
variable {L : Language.{u,v}} {ι : ℕ → Type z}
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- Choosing a different fresh block does not change the term graph's alpha-class. -/
theorem termGraph_bound_independent (t : (L.sum (functionSymbols ι)).Term ℕ) (x B C : ℕ)
    (hxB : x < B) (hxC : x < C)
    (htB : ∀ a ∈ t.varFinset, a < B) (htC : ∀ a ∈ t.varFinset, a < C) :
    D.termGraph t x B = D.termGraph t x C :=
  (D.termGraph_corresponds t t Eq x x B C (TermRel.refl t) rfl hxB hxC htB htC).eq

/-- Formula comparison is preserved through every recursively introduced witness. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The same argument compares translations of atoms: pair their argument witnesses, compare the recursive term
    graphs, and compare the final relation or equality at those witnesses. Now induct on formula comparison.
    Connectives preserve comparison, and at a quantifier the induction hypothesis uses the updated relation on
    bound names. Taking equality as the initial relation and applying the comparison lemma proves that elimination
    respects $\alpha$-equivalence. The translation consequently descends to $\alpha$-classes, and its truth and
    free-variable properties follow from those already proved for representatives.
-/
theorem eraseFormula_corresponds {R : ℕ → ℕ → Prop}
    {φ ψ : Formula (L.sum (functionSymbols ι))} (h : Formula.NameRel R φ ψ) :
    Corresponds R (D.eraseFormula φ) (D.eraseFormula ψ) := by
  induction h with
  | falsum R => exact Corresponds.falsum R
  | @equal R t t' r r' ht hr =>
    refine D.withValues_corresponds ![t,r] ![t',r'] R _ _ _ _ ?_ (valueBound_spec _) (valueBound_spec _) ?_
    · intro i; fin_cases i
      · exact ht
      · exact hr
    · apply Corresponds.equal
      · exact .var (bindBlock_position R 2 _ _ 0)
      · exact .var (bindBlock_position R 2 _ _ 1)
  | @rel R n P ts us h =>
    rcases P with P | P
    · apply D.withValues_corresponds ts us R _ _ _ _ h (valueBound_spec _) (valueBound_spec _)
      exact Corresponds.rel P (fun i => .var (bindBlock_position R n _ _ i))
    · exact nomatch P
  | binary c h h' ih ih' => exact Corresponds.binary c ih ih'
  | quant q h ih => exact Corresponds.quant q ih

/-- Bound-variable renaming preserves the alpha-class of the translated formula. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Bound names in function elimination
-/
theorem eraseFormula_alpha {φ ψ : Formula (L.sum (functionSymbols ι))}
    (h : Formula.Alpha φ ψ) : D.eraseFormula φ = D.eraseFormula ψ :=
  (D.eraseFormula_corresponds h.nameRel).eq

/-- Eliminate defined functions directly on alpha-equivalence classes. -/
def eliminate : AlphaFormula (L.sum (functionSymbols ι)) → AlphaFormula L :=
  Quotient.lift D.eraseFormula (fun _ _ h => D.eraseFormula_alpha h)

@[simp] theorem eliminate_mk (φ : Formula (L.sum (functionSymbols ι))) :
    D.eliminate (AlphaFormula.mk φ) = D.eraseFormula φ := rfl

@[simp] theorem eliminate_binary (c : Connective)
    (φ ψ : AlphaFormula (L.sum (functionSymbols ι))) :
    D.eliminate (binary c φ ψ) = binary c (D.eliminate φ) (D.eliminate ψ) := by
  induction φ, ψ using Quotient.inductionOn₂ with | _ φ ψ => rfl

@[simp] theorem eliminate_quant (q : Quantifier) (x : ℕ)
    (φ : AlphaFormula (L.sum (functionSymbols ι))) :
    D.eliminate (quant q x φ) = quant q x (D.eliminate φ) := by
  induction φ using Quotient.inductionOn with | _ φ => rfl

theorem fv_eliminate_subset (φ : AlphaFormula (L.sum (functionSymbols ι))) :
    (D.eliminate φ).fv ⊆ φ.fv := by
  induction φ using Quotient.inductionOn with | _ φ => exact D.fv_eraseFormula_subset φ

section Semantics
variable {M : Type w} [L.Structure M] [(L.sum (functionSymbols ι)).Structure M]
    [(inclusion (L := L) (ι := ι)).IsExpansionOn M]

theorem realize_eliminate (φ : AlphaFormula (L.sum (functionSymbols ι))) (s : ℕ → M)
    (hu : ∀ k (g : ι k) (s : ℕ → M), ∃! b, (D.graph g).Realize (Function.update s k b))
    (ha : ∀ k (g : ι k) (s : ℕ → M), (D.definingAxiom g).Realize s) :
    (D.eliminate φ).Realize s ↔ φ.Realize s := by
  induction φ using Quotient.inductionOn with | _ φ => exact D.realize_eraseFormula φ s hu ha

end Semantics
end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
