module

public import PolishSpaceBook.SetTheoryLevyDuality

@[expose] public section

/-! # Explicit finite-context prenex moves for bounded quantifiers -/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas AbstractMembership

/-- Insert a new bounding set immediately before the last old parameter. -/
def levyInsertBound (n : ℕ) : Fin (n + 1) → Fin (n + 2) :=
  Fin.snoc (fun i : Fin n => i.castSucc.castSucc) (Fin.last (n + 1))

/-- Exchange the two last parameters, retaining the entire earlier context. -/
def levySwapLast (n : ℕ) : Fin (n + 2) → Fin (n + 2) :=
  Fin.snoc (Fin.snoc (fun i : Fin n => i.castSucc.castSucc) (Fin.last (n + 1))) (Fin.last n).castSucc

lemma levy_insert_assignment {M : Type*} {n : ℕ} (xs : Fin n → M) (B x y : M) :
    Fin.snoc (Fin.snoc (Fin.snoc xs B) x) y ∘ liftParameterMap (levyInsertBound n) =
      Fin.snoc (Fin.snoc xs x) y := by
  rw [snoc_comp_liftParameterMap]
  congr 1
  funext i
  cases i using Fin.lastCases <;> simp [levyInsertBound]

lemma levy_swap_assignment {M : Type*} {n : ℕ} (xs : Fin n → M) (x y : M) :
    Fin.snoc (Fin.snoc xs y) x ∘ levySwapLast n = Fin.snoc (Fin.snoc xs x) y := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [levySwapLast]
  | cast i => cases i using Fin.lastCases <;> simp [levySwapLast]

/-- Pairing packages two successive existential witnesses into one bounding
set; both witnesses remain explicitly bounded inside the matrix. -/
def levyPairMatrix {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) : ForcingFormulas.Formula (n + 1) :=
  boundedExists (Fin.last n) (boundedExists (Fin.last n).castSucc
    (renameParameters φ (liftParameterMap (levyInsertBound n))))

def levyCollectionMatrix {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 2)) :
    ForcingFormulas.Formula (n + 1) :=
  boundedAll i.castSucc (boundedExists (Fin.last n).castSucc
    (renameParameters φ (liftParameterMap (levyInsertBound n))))

lemma realize_levyPairMatrix {M : Type*} [membershipLanguage.Structure M] {n : ℕ}
    (φ : ForcingFormulas.Formula (n + 2)) (xs : Fin n → M) (B : M) :
    (levyPairMatrix φ).Realize Empty.elim (Fin.snoc xs B) ↔
      ∃ x, member x B ∧ ∃ y, member y B ∧ φ.Realize Empty.elim (Fin.snoc (Fin.snoc xs x) y) := by
  simp only [levyPairMatrix, AbstractMembership.realize_boundedExists, realize_renameParameters,
    levy_insert_assignment, Fin.snoc_last, Fin.snoc_castSucc]

lemma realize_levyCollectionMatrix {M : Type*} [membershipLanguage.Structure M] {n : ℕ}
    (i : Fin n) (φ : ForcingFormulas.Formula (n + 2)) (xs : Fin n → M) (B : M) :
    (levyCollectionMatrix i φ).Realize Empty.elim (Fin.snoc xs B) ↔
      ∀ x, member x (xs i) → ∃ y, member y B ∧ φ.Realize Empty.elim (Fin.snoc (Fin.snoc xs x) y) := by
  simp only [levyCollectionMatrix, AbstractMembership.realize_boundedAll, AbstractMembership.realize_boundedExists, realize_renameParameters,
    levy_insert_assignment, Fin.snoc_last, Fin.snoc_castSucc]

theorem zfc_pair_existentials {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) :
    ZFCFormulaEquivalent φ.ex.ex (levyPairMatrix φ).ex := by
  apply ZFCFormulaEquivalent.of_models
  intro M inst _ hM xs
  simp only [BoundedFormula.realize_ex, realize_levyPairMatrix]
  constructor
  · rintro ⟨x, y, hxy⟩
    obtain ⟨B, hB⟩ := (AbstractMembership.models_pairing_iff M).mp (hM.realize_of_mem _ ZFCAxiom.pairing) x y
    exact ⟨B, x, (hB x).mpr (Or.inl rfl), y, (hB y).mpr (Or.inr rfl), hxy⟩
  · rintro ⟨B, x, _, y, _, hxy⟩
    exact ⟨x, y, hxy⟩

theorem zfc_dummy_existential {n : ℕ} (φ : ForcingFormulas.Formula n) :
    ZFCFormulaEquivalent φ (renameParameters φ Fin.castSucc).ex := by
  apply ZFCFormulaEquivalent.of_models
  intro M inst hne _ xs
  simp only [BoundedFormula.realize_ex, realize_renameParameters]
  have he (a : M) : Fin.snoc xs a ∘ Fin.castSucc = xs := by funext i; simp
  simp only [he]
  exact ⟨fun h => ⟨Classical.choice hne, h⟩, fun ⟨_, h⟩ => h⟩

theorem zfc_boundedExists_ex {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 2)) :
    ZFCFormulaEquivalent (boundedExists i φ.ex)
      (boundedExists i.castSucc (renameParameters φ (levySwapLast n))).ex := by
  apply ZFCFormulaEquivalent.of_models
  intro M inst _ _ xs
  simp only [AbstractMembership.realize_boundedExists, BoundedFormula.realize_ex, realize_renameParameters,
    levy_swap_assignment, Fin.snoc_castSucc]
  exact ⟨fun ⟨x, hx, y, h⟩ => ⟨y, x, hx, h⟩, fun ⟨y, x, hx, h⟩ => ⟨x, hx, y, h⟩⟩

/-- The literal Collection schema in every model of the actual ZFC theory.
This intermediate hypothesis is discharged by the arbitrary-model Collection theorem. -/
def FullZFCCollectionSchema : Prop :=
  ∀ (M : Type) [membershipLanguage.Structure M], M ⊨ fullZFCTheory →
    ∀ {n : ℕ} (φ : ForcingFormulas.Formula (n + 2)) (ps : Fin n → M) (A : M),
      (∀ x, member x A → ∃ y, φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps x) y)) →
      ∃ B, ∀ x, member x A → ∃ y, member y B ∧ φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps x) y)

theorem zfc_boundedAll_ex_of_collection (hc : FullZFCCollectionSchema) {n : ℕ}
    (i : Fin n) (φ : ForcingFormulas.Formula (n + 2)) :
    ZFCFormulaEquivalent (boundedAll i φ.ex) (levyCollectionMatrix i φ).ex := by
  apply ZFCFormulaEquivalent.of_models
  intro M inst _ hM xs
  simp only [AbstractMembership.realize_boundedAll, BoundedFormula.realize_ex, realize_levyCollectionMatrix]
  exact ⟨hc M hM φ xs (xs i), fun ⟨B, hB⟩ x hx => by obtain ⟨y, _, hy⟩ := hB x hx; exact ⟨y, hy⟩⟩

theorem zfc_boundedAll_dual {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 1)) :
    ZFCFormulaEquivalent (boundedAll i φ) (boundedExists i φ.not).not := by
  classical
  apply ZFCFormulaEquivalent.of_models
  intro M inst _ _ xs
  simp only [AbstractMembership.realize_boundedAll, AbstractMembership.realize_boundedExists, BoundedFormula.realize_not,
    not_exists, not_and, not_not]

theorem zfc_boundedExists_dual {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 1)) :
    ZFCFormulaEquivalent (boundedExists i φ) (boundedAll i φ.not).not :=
  ZFCFormulaEquivalent.refl _

end PolishSpaceBook.SetTheoryModels
