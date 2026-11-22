module

public import PolishSpaceBook.FirstOrderLambdaContextTests

@[expose] public section

/-! # Finite eigenvariable bounds for unannotated quantifier rules

Nonvacuous eigenvariables occur freely in the observed premise data. In the
vacuous case a fresh name above the observed numerical codes suffices. These
bounds preserve the exact finite-set contexts and the printed side conditions.
-/
namespace PolishSpaceBook.FirstOrderLambdaEncoding
open NamedLambda NamedFirstOrder FirstOrder Language
open ContextPrograms
noncomputable local instance eigenvariableFormulaDecidableEq : DecidableEq (AlphaFormula ForcingFormulas.membershipLanguage) := Classical.decEq _

 theorem freeName_le_formulaCode (φ : FOL) {x : ℕ} (hx : x ∈ φ.fv) : x ≤ (encode φ).code :=
  EqualityMatcher.syntaxName_le_code _ (EqualityMatcher.names_subset_syntaxNames φ (fv_subset_names φ hx))

theorem quant_absent_alpha (q : Quantifier) (φ : FOL) (x y : ℕ)
    (hx : x ∉ φ.fv) (hy : y ∉ φ.fv) :
    (Formula.quant q x φ).Alpha (.quant q y φ) := by
  apply (encode_alpha_iff _ _).mp
  apply (Term.alpha_iff_bindingTree _ _).mpr
  simp only [encode, node, Term.bindingTree]
  rw [BindingTree.close_eq_self _ x 0 (by simpa using hx),
    BindingTree.close_eq_self _ y 0 (by simpa using hy)]

def allIntroWitness (Γ : List FOL) (φ ψ : FOL) (x : ℕ) : Prop :=
  x ∉ (context Γ).fv ∧ (Formula.quant .all x φ).Alpha ψ

def allIntroBound (Γ : List FOL) (φ : FOL) : ℕ := listCode Γ + (encode φ).code + 2

theorem allIntro_witness_bounded (Γ : List FOL) (φ ψ : FOL) :
    (∃ x, allIntroWitness Γ φ ψ x) ↔ ∃ x < allIntroBound Γ φ, allIntroWitness Γ φ ψ x := by
  constructor
  · rintro ⟨x, hxΓ, hxψ⟩
    by_cases hx : x ∈ φ.fv
    · have hb := freeName_le_formulaCode φ hx
      exact ⟨x, by simp only [allIntroBound]; omega, hxΓ, hxψ⟩
    · let z := listCode Γ + (encode φ).code + 1
      have hzΓ : z ∉ (context Γ).fv := by
        intro h
        have := context_name_bound Γ h
        dsimp [z] at this
        omega
      have hzφ : z ∉ φ.fv := by
        intro h
        have := freeName_le_formulaCode φ h
        dsimp [z] at this
        omega
      exact ⟨z, by simp only [allIntroBound, z]; omega, hzΓ,
        (quant_absent_alpha .all φ z x hzφ hx).trans hxψ⟩
  · rintro ⟨x, _, hx⟩; exact ⟨x, hx⟩

def exElimWitness (Γ Δ : List FOL) (φ χ : FOL) (x y : ℕ) : Prop :=
  context Δ = insert (AlphaFormula.mk (φ.subst x (.var y))) (context Γ) ∧
    y ∉ (context Γ).fv ∪ χ.fv ∪ (Formula.quant .ex x φ).fv

def exElimBound (Γ Δ : List FOL) (φ χ : FOL) (x : ℕ) : ℕ :=
  listCode Γ + listCode Δ + (encode χ).code + (encode (.quant .ex x φ)).code + 2

/-- The condition permits `y = x`; the finite bound adds no distinctness assumption. -/
theorem exElim_witness_bounded (Γ Δ : List FOL) (φ χ : FOL) (x : ℕ) :
    (∃ y, exElimWitness Γ Δ φ χ x y) ↔
      ∃ y < exElimBound Γ Δ φ χ x, exElimWitness Γ Δ φ χ x y := by
  constructor
  · rintro ⟨y, hΔ, hy⟩
    by_cases hx : x ∈ φ.fv
    · have hfv : y ∈ (context Δ).fv := by
        apply Finset.mem_biUnion.mpr
        refine ⟨AlphaFormula.mk (φ.subst x (.var y)), ?_, ?_⟩
        · rw [hΔ]; simp
        · change y ∈ (φ.subst x (.var y)).fv
          rw [Formula.mem_fv_subst]
          exact Or.inr ⟨hx, by simp⟩
      have hb := context_name_bound Δ hfv
      exact ⟨y, by simp only [exElimBound]; omega, hΔ, hy⟩
    · let z := listCode Γ + (encode χ).code + (encode (.quant .ex x φ)).code + 1
      have hzΓ : z ∉ (context Γ).fv := by
        intro h
        have := context_name_bound Γ h
        dsimp [z] at this
        omega
      have hzχ : z ∉ χ.fv := by
        intro h
        have := freeName_le_formulaCode χ h
        dsimp [z] at this
        omega
      have hzφ : z ∉ (Formula.quant .ex x φ).fv := by
        intro h
        have := freeName_le_formulaCode (.quant .ex x φ) h
        dsimp [z] at this
        omega
      have he : AlphaFormula.mk (φ.subst x (.var y)) = AlphaFormula.mk (φ.subst x (.var z)) :=
        (AlphaFormula.mk_eq_iff _ _).mpr
          ((absent_instance_alpha φ x y hx).trans (absent_instance_alpha φ x z hx).symm)
      refine ⟨z, by simp only [exElimBound, z]; omega, ?_, ?_⟩
      · exact hΔ.trans (congrArg (fun a => insert a (context Γ)) he)
      · simp only [Finset.mem_union, not_or]
        exact ⟨⟨hzΓ, hzχ⟩, hzφ⟩
  · rintro ⟨y, _, hy⟩; exact ⟨y, hy⟩

end PolishSpaceBook.FirstOrderLambdaEncoding
