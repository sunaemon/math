module

public import PolishSpaceBook.SetTheoryLevyRenaming

@[expose] public section

/-! # Duality and unbounded prefixes at all finite Lévy levels -/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas

def LevyPolarity.dual : LevyPolarity → LevyPolarity
  | .sigma => .pi
  | .pi => .sigma

theorem LevySigma.ex {k n : ℕ} {φ : ForcingFormulas.Formula (n + 1)}
    (h : LevySigma (k + 1) φ) : LevySigma (k + 1) φ.ex := by
  obtain ⟨ψ, hp, he⟩ := h
  exact ⟨ψ.ex, .ex hp, he.ex⟩

theorem LevyPi.all {k n : ℕ} {φ : ForcingFormulas.Formula (n + 1)}
    (h : LevyPi (k + 1) φ) : LevyPi (k + 1) φ.all := by
  obtain ⟨ψ, hp, he⟩ := h
  exact ⟨ψ.all, .all hp, he.all⟩

theorem zfc_neg_ex {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) :
    ZFCFormulaEquivalent φ.ex.not φ.not.all := by
  apply ZFCFormulaEquivalent.of_models
  intro M inst _ _ xs
  simp only [BoundedFormula.realize_not, BoundedFormula.realize_ex,
    BoundedFormula.realize_all, not_exists]

theorem zfc_neg_all {n : ℕ} (φ : ForcingFormulas.Formula (n + 1)) :
    ZFCFormulaEquivalent φ.all.not φ.not.ex := by
  classical
  apply ZFCFormulaEquivalent.of_models
  intro M inst _ _ xs
  simp only [BoundedFormula.realize_not, BoundedFormula.realize_ex,
    BoundedFormula.realize_all, not_forall]

theorem zfc_double_neg {n : ℕ} (φ : ForcingFormulas.Formula n) :
    ZFCFormulaEquivalent φ.not.not φ := by
  classical
  apply ZFCFormulaEquivalent.of_models
  intro M inst _ _ xs
  simp only [BoundedFormula.realize_not, not_not]

/-- Negation interchanges the two polarities without changing the stage. -/
theorem LevyClass.not (k : ℕ) {p : LevyPolarity} {n : ℕ}
    {φ : ForcingFormulas.Formula n} (h : LevyClass p k φ) :
    LevyClass p.dual k φ.not := by
  induction k generalizing p n with
  | zero => exact IsDeltaZero.not h
  | succ k ih =>
    cases p with
    | sigma =>
      obtain ⟨ψ, hp, he⟩ := h
      apply LevyClass.of_equivalent (φ := ψ.not) _ he.not
      clear he φ
      induction hp with
      | base h => exact LevyPi.of_prefix (.base (ih h))
      | @ex n ψ _ ihp =>
        exact (LevyPi.all ihp).of_equivalent (zfc_neg_ex ψ)
    | pi =>
      obtain ⟨ψ, hp, he⟩ := h
      apply LevyClass.of_equivalent (φ := ψ.not) _ he.not
      clear he φ
      induction hp with
      | base h => exact LevySigma.of_prefix (.base (ih h))
      | @all n ψ _ ihp =>
        exact (LevySigma.ex ihp).of_equivalent (zfc_neg_all ψ)

theorem LevySigma.not {k n : ℕ} {φ : ForcingFormulas.Formula n}
    (h : LevySigma k φ) : LevyPi k φ.not := LevyClass.not k h

theorem LevyPi.not {k n : ℕ} {φ : ForcingFormulas.Formula n}
    (h : LevyPi k φ) : LevySigma k φ.not := LevyClass.not k h

theorem LevyDelta.not {k n : ℕ} {φ : ForcingFormulas.Formula n}
    (h : LevyDelta k φ) : LevyDelta k φ.not := by
  cases k with
  | zero => exact IsDeltaZero.not h
  | succ k => exact ⟨LevyPi.not h.2, LevySigma.not h.1⟩

end PolishSpaceBook.SetTheoryModels
