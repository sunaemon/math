module

public import PolishSpaceBook.SetTheoryAbsoluteness

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Bounded absoluteness without an inclusion assumption

Compare each transitive class with the same ambient membership structure.
The inclusion theorem needs no set-theoretic axioms in the larger structure.
-/
namespace PolishSpaceBook.SetTheoryModels
noncomputable section
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    This completes the induction and proves $\Delta_0$ absoluteness. For the non-nested formulation, compare each
    transitive model with the common ambient membership structure. The inclusion argument needs no set-theoretic axioms
    in the larger domain: transitivity of the smaller model already keeps every bounded witness in that smaller model.
    With parameters in both models, their interpretations therefore agree with the same external interpretation.\termref{absoluteness}
-/
/-- Shared parameters give the same bounded truth value in two transitive
classes, even when neither class is contained in the other. -/
theorem delta_zero_absolute_common_parameters (M N : ZFClass.{u})
    (hM : ∀ a, M a → ∀ b ∈ a, M b)
    (hN : ∀ a, N a → ∀ b ∈ a, N b)
    {n : ℕ} {φ : ForcingFormulas.Formula n} (hφ : IsDeltaZero φ)
    (p : Fin n → ZFSet.{u}) (hpM : ∀ i, M (p i)) (hpN : ∀ i, N (p i)) :
    φ.Realize Empty.elim (fun i => (⟨p i, hpM i⟩ : ClassDomain M)) ↔
      φ.Realize Empty.elim (fun i => (⟨p i, hpN i⟩ : ClassDomain N)) := by
  let V : ZFClass.{u} := fun _ => True
  have hMV : M ⊆ V := fun _ _ => trivial
  have hNV : N ⊆ V := fun _ _ => trivial
  have hm := delta_zero_absolute M V hMV hM hφ
    (fun i => (⟨p i, hpM i⟩ : ClassDomain M))
  have hn := delta_zero_absolute N V hNV hN hφ
    (fun i => (⟨p i, hpN i⟩ : ClassDomain N))
  have hparams :
      inclusion hMV ∘ (fun i => (⟨p i, hpM i⟩ : ClassDomain M)) =
        inclusion hNV ∘ (fun i => (⟨p i, hpN i⟩ : ClassDomain N)) := by
    funext i
    exact Subtype.ext rfl
  rw [hparams] at hm
  exact hm.trans hn.symm

end
end PolishSpaceBook.SetTheoryModels
