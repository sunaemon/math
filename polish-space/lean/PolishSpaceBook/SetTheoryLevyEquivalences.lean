module

public import PolishSpaceBook.SetTheoryLevyHierarchy
public import PolishSpaceBook.FirstOrderOpenCompleteness

@[expose] public section

/-! # Parameter-preserving ZFC equivalences

Open completeness converts truths proved in arbitrary models of the literal
axioms into the natural-deduction biconditionals used by the Lévy hierarchy.
-/

namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ForcingFormulas NamedFirstOrder

/-- The open-formula completeness bridge uses arbitrary membership structures,
not transitive set models. All finite parameter contexts are retained. -/
theorem ZFCFormulaEquivalent.of_models {n : ℕ} {φ ψ : ForcingFormulas.Formula n}
    (h : ∀ (M : Type) [membershipLanguage.Structure M], Nonempty M →
      M ⊨ fullZFCTheory → ∀ xs : Fin n → M,
        φ.Realize Empty.elim xs ↔ ψ.Realize Empty.elim xs) :
    ZFCFormulaEquivalent φ ψ := by
  apply (proves_iff_small_model_consequence_open
    (fun _ hθ => namedFullZFCTheory_sentences hθ) _).mpr
  intro M inst hne s hs
  let := inst
  have hM : M ⊨ fullZFCTheory := by
    constructor
    intro θ hθ
    exact (realize_boundedToNamed_sentence θ s).mp (hs _ ⟨θ, hθ, rfl⟩)
  have hh := h M hne hM (fun i => s i.val)
  simp only [AlphaFormula.biimp, AlphaFormula.realize_binary, Connective.eval,
    AlphaFormula.realize_mk, realize_boundedToNamed]
  exact ⟨hh.mp, hh.mpr⟩

theorem ZFCFormulaEquivalent.symm {n : ℕ} {φ ψ : ForcingFormulas.Formula n}
    (h : ZFCFormulaEquivalent φ ψ) : ZFCFormulaEquivalent ψ φ :=
  h.map (fun hp => .andIntro (.andRight hp) (.andLeft hp))

theorem ZFCFormulaEquivalent.trans {n : ℕ} {φ ψ χ : ForcingFormulas.Formula n}
    (h : ZFCFormulaEquivalent φ ψ) (h' : ZFCFormulaEquivalent ψ χ) :
    ZFCFormulaEquivalent φ χ := by
  classical
  apply h.map₂ h'
  intro Γ h₁ h₂
  apply Derives.andIntro
  · apply Derives.impIntro
    exact .impElim ((Derives.andLeft h₂).weaken (Finset.subset_insert _ _))
      (.impElim ((Derives.andLeft h₁).weaken (Finset.subset_insert _ _)) (.hyp Γ _))
  · apply Derives.impIntro
    exact .impElim ((Derives.andRight h₁).weaken (Finset.subset_insert _ _))
      (.impElim ((Derives.andRight h₂).weaken (Finset.subset_insert _ _)) (.hyp Γ _))

/-- Repeated, omitted, and permuted parameters all preserve derivable equivalence. -/
theorem ZFCFormulaEquivalent.reindex {m n : ℕ} {φ ψ : ForcingFormulas.Formula m}
    (h : ZFCFormulaEquivalent φ ψ) (ρ : Fin m → Fin n) :
    ZFCFormulaEquivalent (reindex φ ρ) (reindex ψ ρ) := by
  apply ZFCFormulaEquivalent.of_models
  intro M inst hne hM xs
  rw [AbstractMembership.realize_reindex, AbstractMembership.realize_reindex]
  exact h.sound_fin hM (Classical.choice hne) _

theorem ZFCFormulaEquivalent.not {n : ℕ} {φ ψ : ForcingFormulas.Formula n}
    (h : ZFCFormulaEquivalent φ ψ) : ZFCFormulaEquivalent φ.not ψ.not := by
  apply ZFCFormulaEquivalent.of_models
  intro M inst hne hM xs
  simp only [BoundedFormula.realize_not]
  exact not_congr (h.sound_fin hM (Classical.choice hne) xs)

theorem ZFCFormulaEquivalent.all {n : ℕ} {φ ψ : ForcingFormulas.Formula (n + 1)}
    (h : ZFCFormulaEquivalent φ ψ) : ZFCFormulaEquivalent φ.all ψ.all := by
  apply ZFCFormulaEquivalent.of_models
  intro M inst hne hM xs
  simp only [BoundedFormula.realize_all]
  exact forall_congr' (fun a => h.sound_fin hM a (Fin.snoc xs a))

theorem ZFCFormulaEquivalent.ex {n : ℕ} {φ ψ : ForcingFormulas.Formula (n + 1)}
    (h : ZFCFormulaEquivalent φ ψ) : ZFCFormulaEquivalent φ.ex ψ.ex := by
  apply ZFCFormulaEquivalent.of_models
  intro M inst hne hM xs
  simp only [BoundedFormula.realize_ex]
  exact exists_congr (fun a => h.sound_fin hM a (Fin.snoc xs a))

namespace AbstractMembership

theorem realize_boundedAll {M : Type*} [membershipLanguage.Structure M]
    {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → M) :
    (boundedAll i φ).Realize Empty.elim xs ↔
      ∀ a : M, member a (xs i) → φ.Realize Empty.elim (Fin.snoc xs a) := by
  simp only [boundedAll, BoundedFormula.realize_all, BoundedFormula.realize_imp,
    realize_memberAt, Fin.snoc_last, Fin.snoc_castSucc]

theorem realize_boundedExists {M : Type*} [membershipLanguage.Structure M]
    {n : ℕ} (i : Fin n) (φ : ForcingFormulas.Formula (n + 1)) (xs : Fin n → M) :
    (boundedExists i φ).Realize Empty.elim xs ↔
      ∃ a : M, member a (xs i) ∧ φ.Realize Empty.elim (Fin.snoc xs a) := by
  classical
  simp only [boundedExists, BoundedFormula.realize_not, realize_boundedAll,
    not_forall, not_not, exists_prop]

end AbstractMembership

theorem ZFCFormulaEquivalent.boundedAll {n : ℕ} {φ ψ : ForcingFormulas.Formula (n + 1)}
    (h : ZFCFormulaEquivalent φ ψ) (i : Fin n) :
    ZFCFormulaEquivalent (boundedAll i φ) (boundedAll i ψ) := by
  apply ZFCFormulaEquivalent.of_models
  intro M inst hne hM xs
  simp only [AbstractMembership.realize_boundedAll]
  exact forall_congr' (fun a => imp_congr_right (fun _ => h.sound_fin hM a (Fin.snoc xs a)))

theorem ZFCFormulaEquivalent.boundedExists {n : ℕ} {φ ψ : ForcingFormulas.Formula (n + 1)}
    (h : ZFCFormulaEquivalent φ ψ) (i : Fin n) :
    ZFCFormulaEquivalent (boundedExists i φ) (boundedExists i ψ) := by
  exact (h.not.boundedAll i).not

/-- At every positive stage the classification is invariant under actual
ZFC-provable equivalence. This does not add closure constructors. -/
theorem LevyClass.of_equivalent {p : LevyPolarity} {k n : ℕ}
    {φ ψ : ForcingFormulas.Formula n} (hφ : LevyClass p (k + 1) φ)
    (h : ZFCFormulaEquivalent ψ φ) : LevyClass p (k + 1) ψ := by
  cases p <;> obtain ⟨χ, hχ, he⟩ := hφ <;> exact ⟨χ, hχ, h.trans he⟩

end PolishSpaceBook.SetTheoryModels
