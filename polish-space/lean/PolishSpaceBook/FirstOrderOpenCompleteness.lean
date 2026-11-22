module

public import PolishSpaceBook.FirstOrderCompleteness
public import PolishSpaceBook.FirstOrderGraphTotality

@[expose] public section

/-! # Completeness with free parameters

Universal closure is introduced and eliminated by the actual natural-deduction
rules. Sentence completeness then applies to formulas with any finite support.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}

namespace Derives

/-- Close any finite initial segment of names under sentence assumptions. -/
theorem closeAll_of_closed_context {Γ : Context L} (hΓ : Γ.fv = ∅)
    {φ : AlphaFormula L} (h : Derives Γ φ) (n : ℕ) :
    Derives Γ (closeAll n φ) := by
  induction n with
  | zero => exact h
  | succ n ih => exact .allIntro n ih (by simp [hΓ])

end Derives

namespace ProvesFrom

/-- Free parameters may be universally closed without changing provability. -/
theorem closeAll_iff {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (n : ℕ) (φ : AlphaFormula L) :
    ProvesFrom T (closeAll n φ) ↔ ProvesFrom T φ := by
  constructor
  · exact fun h => h.map (Derives.open_closeAll n φ)
  · rintro ⟨Γ, hΓ, h⟩
    exact ⟨Γ, hΓ, h.closeAll_of_closed_context (Context.fv_eq_empty_of_sentences hT Γ hΓ) n⟩

end ProvesFrom

/-- Small-model consequence retains every free parameter, with no sentence
restriction on the conclusion. The resulting proof is a `ProvesFrom` proof. -/
theorem proves_iff_small_model_consequence_open {T : Set (AlphaFormula L)}
    (hT : T ⊆ Sentences L) (φ : AlphaFormula L) :
    ProvesFrom T φ ↔ ∀ (M : Type (max u v)) (inst : L.Structure M), Nonempty M →
      ∀ s : ℕ → M, (∀ ψ ∈ T, @AlphaFormula.Realize L M inst ψ s) →
        @AlphaFormula.Realize L M inst φ s := by
  classical
  constructor
  · intro hp M inst _ s hs
    let := inst
    exact hp.sound s hs
  · intro h
    let n := φ.fv.sup id + 1
    have hf : φ.fv ⊆ Finset.range n := by
      intro x hx
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hx))
    apply (ProvesFrom.closeAll_iff hT n φ).mp
    apply (proves_iff_small_model_consequence hT (by
      change (closeAll n φ).fv = ∅
      rw [fv_closeAll, Finset.sdiff_eq_empty_iff_subset]
      exact hf)).mpr
    intro M inst hne s hs
    let := inst
    apply (forall_realize_closeAll n φ).mpr ?_ s
    intro t
    apply h M inst hne t
    intro ψ hψ
    apply (AlphaFormula.realize_congr ψ s t ?_).mp (hs ψ hψ)
    intro x hx
    have hc : ψ.fv = ∅ := hT hψ
    simp only [hc, Finset.notMem_empty] at hx

end PolishSpaceBook.NamedFirstOrder
