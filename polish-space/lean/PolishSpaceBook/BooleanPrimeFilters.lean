module

public import Mathlib.Order.PFilter
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.Atoms

@[expose] public section

namespace PolishSpaceBook
open Set Order

/-- A proper order filter is completely prime when membership in an arbitrary
join is witnessed by a member of the joined family. -/
def IsCompletelyPrimePFilter {B : Type*} [CompleteBooleanAlgebra B] (F : PFilter B) : Prop :=
  (⊥ : B) ∉ F ∧ ∀ S : Set B, sSup S ∈ F → ∃ b ∈ S, b ∈ F

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    This is not an assertion that the ground-model locale has a point: an atomless complete Boolean algebra
    has no completely prime filter in the ground model.
-/
theorem completelyPrimePFilter_exists_atom {B : Type*} [CompleteBooleanAlgebra B]
    (F : PFilter B) (hF : IsCompletelyPrimePFilter F) : ∃ a : B, IsAtom a := by
  classical
  let a : B := sSup {b : B | b ∉ F}
  have ha : a ∉ F := by
    intro ha
    obtain ⟨b, hb, hbf⟩ := hF.2 _ ha
    exact hb hbf
  have choose_compl (b : B) : b ∈ F ∨ bᶜ ∈ F := by
    obtain ⟨c, hc, hcf⟩ := hF.2 {b, bᶜ} (by simp)
    rcases Set.mem_insert_iff.mp hc with rfl | hc
    · exact Or.inl hcf
    · exact Or.inr (Set.mem_singleton_iff.mp hc ▸ hcf)
  have hac : aᶜ ∈ F := (choose_compl a).resolve_left ha
  refine ⟨aᶜ, ?_, ?_⟩
  · intro h
    exact hF.1 (h ▸ hac)
  · intro b hb
    by_cases hbf : b ∈ F
    · have hn : bᶜ ∉ F := by
        intro hc
        have hi := PFilter.inf_mem hbf hc
        exact hF.1 (by simpa using hi)
      have hba : bᶜ ≤ a := le_sSup hn
      have hab : aᶜ ≤ b := by simpa using compl_le_compl hba
      exact False.elim (not_le_of_gt hb hab)
    · have hba : b ≤ a := le_sSup hbf
      have hbot : b ≤ (⊥ : B) := by
        have hi := le_inf hba hb.le
        simpa using hi
      exact le_bot_iff.mp hbot

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    This is not an assertion that the ground-model locale has a point: an atomless complete Boolean algebra
    has no completely prime filter in the ground model.
-/
theorem no_completelyPrimePFilter_of_no_atoms {B : Type*} [CompleteBooleanAlgebra B]
    (h : ∀ a : B, ¬ IsAtom a) (F : PFilter B) : ¬ IsCompletelyPrimePFilter F := by
  intro hF
  obtain ⟨a, ha⟩ := completelyPrimePFilter_exists_atom F hF
  exact h a ha

end PolishSpaceBook
