module

public import PolishSpaceBook.ForcingRelabelClosure

@[expose] public section

/-! # A defining formula for the actual recursive name translation -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingNames
universe u

/-- The table's defining formula, followed by lookup at the input name. -/
def relabelNameFormula : ForcingFormulas.Formula 5 :=
  (reindex (recursiveValueFormula relabelTableStepFormula) ![(0 : Fin 6), 1, 2, 3, 5] ⊓
    pairMemberFormula 5 3 4).ex

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
  (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hinf hpair hunion hpower hsep hrep in
 theorem relabelName_definable (P Q E a b : M) :
    relabelNameFormula.Realize Empty.elim ![P, Q, E, a, b] ↔ b.val = relabelName P.val Q.val E.val a.val := by
  have hv (t : M) :
      (recursiveValueFormula relabelTableStepFormula).Realize Empty.elim ![P, Q, E, a, t] ↔
        t.val = hereditaryTable (relabelName P.val Q.val E.val) a.val := by
    have he : ![P, Q, E, a, t] = Fin.snoc (Fin.snoc ![P, Q, E] a) t := by
      funext i; fin_cases i <;> rfl
    rw [he]
    exact realize_recursiveValueFormula_external hM hinf hpair hunion hpower hsep hrep
      relabelTableStepFormula ![P, Q, E] (relabelTableStep P.val Q.val E.val)
      (fun a g b => realize_relabelTableStepFormula hM hpair hunion hpower hsep P Q E a g b)
      (fun a g => relabelTableStep_mem hM hpair hunion hpower hsep P Q E a g)
      (hereditaryTable (relabelName P.val Q.val E.val)) (relabelTable_step_equation P.val Q.val E.val) a t
  have hp {n : ℕ} (r x y : Fin n) (xs : Fin n → M) :
      (pairMemberFormula r x y).Realize Empty.elim xs ↔ pair (xs x).val (xs y).val ∈ (xs r).val :=
    realize_pairMemberFormula (M : ZFClass) (fun _ ha _ hb => hM.mem_trans hb ha) r x y xs
  rw [relabelNameFormula, BoundedFormula.realize_ex]
  have he (t : M) : Fin.snoc ![P, Q, E, a, b] t ∘ ![(0 : Fin 6), 1, 2, 3, 5] = ![P, Q, E, a, t] := by
    funext i; fin_cases i <;> rfl
  simp only [BoundedFormula.realize_inf, realize_reindex, he, hv, hp]
  change (∃ t : M, t.val = hereditaryTable (relabelName P.val Q.val E.val) a.val ∧
    pair a.val b.val ∈ t.val) ↔ _
  constructor
  · rintro ⟨t, ht, hab⟩
    rw [ht] at hab
    exact hereditaryTable_correct _ _ hab
  · intro hb
    have ht := external_recursive_value_mem hM hinf hpair hunion hpower hsep hrep relabelTableStepFormula ![P, Q, E]
      (relabelTableStep P.val Q.val E.val)
      (fun a g b => realize_relabelTableStepFormula hM hpair hunion hpower hsep P Q E a g b)
      (fun a g => relabelTableStep_mem hM hpair hunion hpower hsep P Q E a g)
      (hereditaryTable (relabelName P.val Q.val E.val)) (relabelTable_step_equation P.val Q.val E.val) a
    exact ⟨⟨_, ht⟩, rfl, hb ▸ hereditaryTable_self _ _⟩

end PolishSpaceBook.SetTheoryModels
