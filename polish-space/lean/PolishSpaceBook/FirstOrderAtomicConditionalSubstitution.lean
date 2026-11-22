module

public import PolishSpaceBook.FirstOrderAtomicFunctionSubstitution

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Atomic substitution under a fixed value assumption

Keep the value graph as an assumption rather than binding its value yet.
This form extends through connectives and quantifiers by proof congruence.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- Conditional equivalence for a relation atom, with canonical witness choices. -/
theorem proves_eliminate_rel_conditional {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f)) {n : ℕ} (R : L.Relations n)
    (ts : Fin n → (L.sum (functionSymbols ι)).Term ℕ)
    (r : (L.sum (functionSymbols ι)).Term ℕ) (x y B : ℕ)
    (hy : y < B) (hyr : y ∉ r.varFinset)
    (ht : ∀ i a, a ∈ (ts i).varFinset → a < B) (hr : ∀ a ∈ r.varFinset, a < B) :
    ProvesFrom T (binary .imp (D.termGraph r y B)
      (biimp (D.eliminate ((rel (Sum.inl R) ts).subst x r))
        (D.eliminate ((rel (Sum.inl R) ts).subst x (.var y))))) := by
  rw [subst_rel,subst_rel]
  rw [D.eliminate_rel_at R _ B (fun i => termSubst_vars_below (ts i) r x B (ht i) hr),
    D.eliminate_rel_at R _ B
      (fun i => termSubst_vars_below (ts i) (.var y) x B (ht i) (by simpa using hy))]
  exact D.proves_withValues_substitution_conditional hT hu ts r x y B (relationValues R B)
    hy hyr ht hr (fv_relationValues_subset R B)

/-- Conditional equivalence for an equality, using the same two value slots. -/
theorem proves_eliminate_equal_conditional {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (t u r : (L.sum (functionSymbols ι)).Term ℕ) (x y B : ℕ)
    (hy : y < B) (hyr : y ∉ r.varFinset)
    (ht : ∀ a ∈ t.varFinset, a < B) (hu' : ∀ a ∈ u.varFinset, a < B)
    (hr : ∀ a ∈ r.varFinset, a < B) :
    ProvesFrom T (binary .imp (D.termGraph r y B)
      (biimp (D.eliminate ((equal t u).subst x r)) (D.eliminate ((equal t u).subst x (.var y))))) := by
  rw [subst_equal,subst_equal]
  rw [D.eliminate_equal_at _ _ B (termSubst_vars_below t r x B ht hr)
      (termSubst_vars_below u r x B hu' hr),
    D.eliminate_equal_at _ _ B (termSubst_vars_below t (.var y) x B ht (by simpa using hy))
      (termSubst_vars_below u (.var y) x B hu' (by simpa using hy))]
  have hv (a : (L.sum (functionSymbols ι)).Term ℕ) :
      (fun i : Fin 2 => termSubst (![t,u] i) x a) = ![termSubst t x a,termSubst u x a] := by
    funext i; fin_cases i <;> rfl
  have hh := D.proves_withValues_substitution_conditional hT hu ![t,u] r x y B (equalValues B) hy hyr
    (by intro i; fin_cases i; exact ht; exact hu') hr (fv_equalValues_subset B)
  simpa only [hv] using hh

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
