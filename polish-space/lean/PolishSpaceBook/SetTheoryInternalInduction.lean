module

public import PolishSpaceBook.SetTheoryDefinitionalExtensions
public import PolishSpaceBook.SetTheoryLevyEquivalences

@[expose] public section

/-! # Definable membership induction inside arbitrary ZFC models

External well-foundedness is not assumed. Foundation is applied to the set of
counterexamples obtained by the actual Separation schema. The ambient bound
is an internally transitive set, not a transitive model.
-/

namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

/-- A definable nonempty subclass of an internal transitive set has an
internal membership-minimal member. -/
theorem definable_minimum_in_transitive {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (hsep : M ⊨ separationSentence φ) (hfoundation : M ⊨ foundationSentence)
    (ps : Fin n → M) (A : M)
    (hA : ∀ a : M, member a A → ∀ b : M, member b a → member b A)
    (hex : ∃ a : M, member a A ∧ φ.Realize Empty.elim (Fin.snoc ps a)) :
    ∃ a : M, member a A ∧ φ.Realize Empty.elim (Fin.snoc ps a) ∧
      ∀ b : M, member b a → ¬φ.Realize Empty.elim (Fin.snoc ps b) := by
  obtain ⟨D, hD⟩ := (realize_separation M φ).mp hsep ps A
  obtain ⟨a, haA, haφ⟩ := hex
  obtain ⟨b, hbD, hbmin⟩ := (models_foundation_iff M).mp hfoundation D
    ⟨a, (hD a).mpr ⟨haA, haφ⟩⟩
  obtain ⟨hbA, hbφ⟩ := (hD b).mp hbD
  exact ⟨b, hbA, hbφ, fun c hcb hcφ => hbmin c hcb
    ((hD c).mpr ⟨hA b hbA c hcb, hcφ⟩)⟩

/-- Induction for an actual formula with any finite tuple of parameters.
It remains valid in externally ill-founded membership structures. -/
theorem definable_induction_on_transitive {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (hsep : M ⊨ separationSentence φ.not) (hfoundation : M ⊨ foundationSentence)
    (ps : Fin n → M) (A : M)
    (hA : ∀ a : M, member a A → ∀ b : M, member b a → member b A)
    (hstep : ∀ a : M, member a A →
      (∀ b : M, member b a → φ.Realize Empty.elim (Fin.snoc ps b)) →
      φ.Realize Empty.elim (Fin.snoc ps a)) :
    ∀ a : M, member a A → φ.Realize Empty.elim (Fin.snoc ps a) := by
  classical
  intro a haA
  by_contra hbad
  obtain ⟨b, hbA, hbφ, hbmin⟩ := definable_minimum_in_transitive φ.not hsep hfoundation
    ps A hA ⟨a, haA, (BoundedFormula.realize_not).mpr hbad⟩
  exact (BoundedFormula.realize_not.mp hbφ) (hstep b hbA (fun c hcb => by
    by_contra hc
    exact hbmin c hcb (BoundedFormula.realize_not.mpr hc)))

/-- Every literal ZFC model satisfies the preceding definable induction
principle; no new induction axiom is added to the theory. -/
theorem fullZFC_definable_induction {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (hM : M ⊨ fullZFCTheory) (ps : Fin n → M) (A : M)
    (hA : ∀ a : M, member a A → ∀ b : M, member b a → member b A)
    (hstep : ∀ a : M, member a A →
      (∀ b : M, member b a → φ.Realize Empty.elim (Fin.snoc ps b)) →
      φ.Realize Empty.elim (Fin.snoc ps a)) :
    ∀ a : M, member a A → φ.Realize Empty.elim (Fin.snoc ps a) :=
  definable_induction_on_transitive φ (fullZFC_model_separation hM _)
    (hM.realize_of_mem _ ZFCAxiom.foundation) ps A hA hstep

end PolishSpaceBook.SetTheoryModels.AbstractMembership
