module

public import PolishSpaceBook.SetTheoryLevyEquivalences

@[expose] public section

/-! # Finite-context renaming for every Lévy level

The structural renaming below lifts the parameter map under each binder. Its
semantic agreement with `reindex` produces an actual ZFC proof when used at a
positive level; at level zero it preserves bounded syntax directly.
-/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas NamedFirstOrder

def liftParameterMap {m n : ℕ} (ρ : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  Fin.snoc (fun i => (ρ i).castSucc) (Fin.last n)

def renameParameters : {m : ℕ} → ForcingFormulas.Formula m →
    {n : ℕ} → (Fin m → Fin n) → ForcingFormulas.Formula n
  | _, .falsum, _, _ => .falsum
  | _, .equal t r, _, ρ => .equal (t.relabel (Sum.map id ρ)) (r.relabel (Sum.map id ρ))
  | _, .rel R ts, _, ρ => .rel R (fun i => (ts i).relabel (Sum.map id ρ))
  | _, .imp φ ψ, _, ρ => (renameParameters φ ρ).imp (renameParameters ψ ρ)
  | _, .all φ, _, ρ => (renameParameters φ (liftParameterMap ρ)).all

theorem snoc_comp_liftParameterMap {M : Type*} {m n : ℕ}
    (xs : Fin n → M) (a : M) (ρ : Fin m → Fin n) :
    Fin.snoc xs a ∘ liftParameterMap ρ = Fin.snoc (xs ∘ ρ) a := by
  funext i
  cases i using Fin.lastCases <;> simp [liftParameterMap]

theorem realize_renameParameters {M : Type*} [membershipLanguage.Structure M]
    {m n : ℕ} (φ : ForcingFormulas.Formula m) (ρ : Fin m → Fin n) (xs : Fin n → M) :
    (renameParameters φ ρ).Realize Empty.elim xs ↔ φ.Realize Empty.elim (xs ∘ ρ) := by
  have ht {m n : ℕ} (t : membershipLanguage.Term (Empty ⊕ Fin m))
      (ρ : Fin m → Fin n) (xs : Fin n → M) :
      (t.relabel (Sum.map id ρ)).realize (Sum.elim Empty.elim xs) =
        t.realize (Sum.elim Empty.elim (xs ∘ ρ)) := by
    rw [Term.realize_relabel]
    congr 1
    funext i
    cases i with
    | inl e => exact e.elim
    | inr i => rfl
  induction φ generalizing n with
  | falsum => rfl
  | equal t r => simp only [renameParameters, BoundedFormula.Realize, ht]
  | rel R ts => simp only [renameParameters, BoundedFormula.Realize, ht]
  | imp φ ψ ihφ ihψ => simp only [renameParameters, BoundedFormula.realize_imp, ihφ, ihψ]
  | all φ ih =>
    simp only [renameParameters, BoundedFormula.realize_all, ih, snoc_comp_liftParameterMap]

@[simp] theorem renameParameters_not {m n : ℕ} (φ : ForcingFormulas.Formula m)
    (ρ : Fin m → Fin n) : renameParameters φ.not ρ = (renameParameters φ ρ).not := rfl

@[simp] theorem renameParameters_ex {m n : ℕ} (φ : ForcingFormulas.Formula (m + 1))
    (ρ : Fin m → Fin n) :
    renameParameters φ.ex ρ = (renameParameters φ (liftParameterMap ρ)).ex := rfl

@[simp] theorem renameParameters_memberAt {m n : ℕ} (i j : Fin m) (ρ : Fin m → Fin n) :
    renameParameters (memberAt i j) ρ = memberAt (ρ i) (ρ j) := by
  unfold memberAt renameParameters
  congr 1
  funext k
  fin_cases k <;> rfl

@[simp] theorem renameParameters_boundedAll {m n : ℕ} (i : Fin m)
    (φ : ForcingFormulas.Formula (m + 1)) (ρ : Fin m → Fin n) :
    renameParameters (boundedAll i φ) ρ =
      boundedAll (ρ i) (renameParameters φ (liftParameterMap ρ)) := by
  simp [boundedAll, renameParameters, renameParameters_memberAt, liftParameterMap]

theorem IsDeltaZero.renameParameters {m n : ℕ} {φ : ForcingFormulas.Formula m}
    (h : IsDeltaZero φ) (ρ : Fin m → Fin n) : IsDeltaZero (renameParameters φ ρ) := by
  induction h generalizing n with
  | falsum => exact .falsum
  | equal => exact .equal _ _
  | member => exact .member _
  | imp _ _ ihφ ihψ => exact .imp (ihφ ρ) (ihψ ρ)
  | all i _ ih =>
    rw [renameParameters_boundedAll]
    exact .all (ρ i) (ih (liftParameterMap ρ))

theorem ZFCFormulaEquivalent.renameParameters {m n : ℕ} {φ ψ : ForcingFormulas.Formula m}
    (h : ZFCFormulaEquivalent φ ψ) (ρ : Fin m → Fin n) :
    ZFCFormulaEquivalent (renameParameters φ ρ) (renameParameters ψ ρ) := by
  apply ZFCFormulaEquivalent.of_models
  intro M inst hne hM xs
  rw [realize_renameParameters, realize_renameParameters]
  exact h.sound_fin hM (Classical.choice hne) _

theorem renameParameters_equivalent_reindex {m n : ℕ} (φ : ForcingFormulas.Formula m)
    (ρ : Fin m → Fin n) : ZFCFormulaEquivalent (renameParameters φ ρ) (reindex φ ρ) := by
  apply ZFCFormulaEquivalent.of_models
  intro M inst _ _ xs
  rw [realize_renameParameters, AbstractMembership.realize_reindex]

/-- Arbitrary finite parameter maps preserve each syntactic/derivable level. -/
theorem LevyClass.renameParameters (k : ℕ) {p : LevyPolarity} {m n : ℕ}
    {φ : ForcingFormulas.Formula m} (h : LevyClass p k φ) (ρ : Fin m → Fin n) :
    LevyClass p k (renameParameters φ ρ) := by
  induction k generalizing p m n with
  | zero => exact IsDeltaZero.renameParameters h ρ
  | succ k ih =>
    cases p with
    | sigma =>
      obtain ⟨ψ, hp, he⟩ := h
      refine ⟨SetTheoryModels.renameParameters ψ ρ, ?_, he.renameParameters ρ⟩
      clear he φ
      induction hp generalizing n with
      | base h => exact .base (ih h ρ)
      | ex _ ihp => exact .ex (ihp (liftParameterMap ρ))
    | pi =>
      obtain ⟨ψ, hp, he⟩ := h
      refine ⟨SetTheoryModels.renameParameters ψ ρ, ?_, he.renameParameters ρ⟩
      clear he φ
      induction hp generalizing n with
      | base h => exact .base (ih h ρ)
      | all _ ihp => exact .all (ihp (liftParameterMap ρ))

theorem LevyClass.reindex {p : LevyPolarity} {k m n : ℕ}
    {φ : ForcingFormulas.Formula m} (h : LevyClass p (k + 1) φ) (ρ : Fin m → Fin n) :
    LevyClass p (k + 1) (reindex φ ρ) :=
  (h.renameParameters (k + 1) ρ).of_equivalent (renameParameters_equivalent_reindex φ ρ).symm

end PolishSpaceBook.SetTheoryModels
