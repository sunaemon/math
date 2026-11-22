module

public import PolishSpaceBook.FirstOrderTermGraphSubstitution
public import PolishSpaceBook.FirstOrderValueBinding

@[expose] public section

/-!
# Composition of recursive term graphs

Bind one value of the replacement term. Forward substitution and the converse
obtained from uniqueness identify this composite with the substituted graph.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance termGraphCompositionDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- Recursive term graphs compose by existentially binding the value of the substituted term. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Substitution in term graphs
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Finally, existence supplies a value of the replacement term. Under that value's graph, the converse just proved
    turns the left side of the displayed equivalence into the outer graph, and existential introduction gives
    the right side. Conversely, open the value on the right and use the first direction. The bound value's name
    is not free in the left side or in the sentence assumptions, so both existential eliminations are valid.
-/
theorem proves_termGraph_composition {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (t r : (L.sum (functionSymbols ι)).Term ℕ) (x y w B : ℕ)
    (hy : y < B) (hw : w < B) (hyw : y ≠ w)
    (hyt : y ∉ t.varFinset) (hyr : y ∉ r.varFinset)
    (hwt : w ∉ t.varFinset) (hwr : w ∉ r.varFinset)
    (ht : ∀ a ∈ t.varFinset, a < B) (hr : ∀ a ∈ r.varFinset, a < B) :
    ProvesFrom T (binary .conj
      (binary .imp (D.termGraph (termSubst t x r) w B)
        (quant .ex y (binary .conj (D.termGraph r y B)
          (D.termGraph (termSubst t x (.var y)) w B))))
      (binary .imp (quant .ex y (binary .conj (D.termGraph r y B)
          (D.termGraph (termSubst t x (.var y)) w B)))
        (D.termGraph (termSubst t x r) w B))) := by
  let ρ := D.termGraph r y B
  let σ := D.termGraph (termSubst t x (.var y)) w B
  let χ := D.termGraph (termSubst t x r) w B
  have hf := D.proves_termGraph_substitution (T := T) t r x y w B hy hw hyr ht hr
  have hb := D.proves_termGraph_substitution_reverse hT hu t r x y w B hy hw hyr hwt hwr ht hr
  have he := D.proves_termGraph_exists hT hu r y B hy hyr hr
  have hyχ : y ∉ χ.fv := by
    intro hm
    rcases Finset.mem_insert.mp (D.fv_termGraph_subset (termSubst t x r) w B hm) with hm | hm
    · exact hyw hm
    · rcases (mem_varFinset_termSubst t x r y).mp hm with hm | hm
      · exact hyt hm.1
      · exact hyr hm.2
  exact ProvesFrom.bind_value_equivalence hT ρ σ χ y hyχ he hf hb

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
