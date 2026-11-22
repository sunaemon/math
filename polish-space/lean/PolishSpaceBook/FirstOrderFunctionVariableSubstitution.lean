module

public import PolishSpaceBook.FirstOrderVariableCorrespondence

@[expose] public section

/-!
# Function elimination commutes with variable substitution

Both routes correspond to the original formula under the same functional name
relation. Left uniqueness gives equality of alpha-classes, including when the
replacement name already occurs freely in the source.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- The comparison theorem descends to formulas represented by alpha-classes. -/
theorem eliminate_corresponds {R : ℕ → ℕ → Prop}
    {φ ψ : AlphaFormula (L.sum (functionSymbols ι))} (h : Corresponds R φ ψ) :
    Corresponds R (D.eliminate φ) (D.eliminate ψ) := by
  rcases h with ⟨a,b,rfl,rfl,h⟩
  exact D.eraseFormula_corresponds h

/-- No freshness or injectivity assumption on the replacement name is required. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Variable substitution and elimination
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Let $r$ send $x$ to $y$ and fix every other name, and put $R(a,b)$ if and only if $a=r(b)$.
    The substitution comparison lemma compares the substituted formula with the original under $R$.
    Function elimination preserves this comparison, by the proof of bound-name invariance above.
    Independently, substitution in the translated formula compares with that same original translation under $R$.
    Compose the first comparison with the reverse of the second. A right-hand name determines its left-hand name
    uniquely, so the resulting comparison is equality of names and gives $\alpha$-equivalence.
    This does not require the replacement map to be injective.
-/
theorem eliminate_subst_var (φ : AlphaFormula (L.sum (functionSymbols ι))) (x y : ℕ) :
    D.eliminate (φ.subst x (.var y)) = (D.eliminate φ).subst x (.var y) :=
  (D.eliminate_corresponds (subst_var_corresponds φ x y)).left_unique
    (subst_var_corresponds (D.eliminate φ) x y) (fun _ _ _ h h' => h.trans h'.symm)

/-- Entire finite variable instances commute with elimination, even with repeated names. -/
theorem eliminate_simultaneous_vars {n : ℕ} (φ : AlphaFormula (L.sum (functionSymbols ι)))
    (a : Fin n → ℕ) (hf : φ.fv ⊆ Finset.range n) :
    D.eliminate (φ.simultaneous (fun i => .var (a i))) =
      (D.eliminate φ).simultaneous (fun i => .var (a i)) :=
  (D.eliminate_corresponds (simultaneous_vars_corresponds φ a hf)).left_unique
    (simultaneous_vars_corresponds (D.eliminate φ) a (Finset.Subset.trans (D.fv_eliminate_subset φ) hf))
    (fun _ _ _ h h' => h.trans h'.symm)

/-- Parameter substitution in a term graph agrees with substitution in its term and output. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For simultaneous variable replacement, use the finite replacement map and the comparison lemma for simultaneous
    instances. The free-variable inclusion for elimination ensures that the translated formula has no extra input
    positions. The same comparison argument applies to term graphs, including the output in the name relation
    and choosing admissible internal starting indices independently on the two sides.
-/
theorem termGraph_subst_var (t : (L.sum (functionSymbols ι)).Term ℕ) (w x y B C : ℕ)
    (hw : w < B) (ht : ∀ a ∈ t.varFinset, a < B)
    (hw' : (if w = x then y else w) < C)
    (ht' : ∀ a ∈ (termSubst t x (.var y)).varFinset, a < C) :
    (D.termGraph t w B).subst x (.var y) =
      D.termGraph (termSubst t x (.var y)) (if w = x then y else w) C := by
  have h := D.termGraph_corresponds (termSubst t x (.var y)) t
    (fun a b => a = if b = x then y else b) (if w = x then y else w) w C B
    (termSubst_var_corresponds t x y) rfl hw' hw ht' ht
  exact (subst_var_corresponds (D.termGraph t w B) x y).left_unique h
    (fun _ _ _ h h' => h.trans h'.symm)

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
