module

public import PolishSpaceBook.SetTheoryAbstractRecursion

@[expose] public section

/-! # The defining equation of internal membership recursion -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.AbstractMembership
open FirstOrder Language ForcingFormulas
universe u
variable {M : Type u} [membershipLanguage.Structure M]

theorem recursiveSolution_value (hM : M ⊨ fullZFCTheory) {p : ℕ}
    (φ : ForcingFormulas.Formula (p + 3)) (ps : Fin p → M)
    (hφ : ∀ a g : M, ∃! b : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b))
    {D f a b : M}
    (hf : IsRecursiveSolution
      (fun a g b => φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b)) D f)
    (hab : GraphApplication f a b) :
    (recursiveValueBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) := by
  obtain ⟨c, hc, _⟩ := recursiveValue_existsUnique hM φ ps hφ a
  obtain ⟨E, g, _, hg, hac⟩ := (realize_recursiveValueBody φ ps a c).mp hc
  have hR : ∀ a g b c : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b) →
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) c) → b = c := by
    intro a g b c hb hc
    obtain ⟨d, _, hd⟩ := hφ a g
    exact (hd b hb).trans (hd c hc).symm
  exact (recursiveSolutions_agree hM hR hf hg a b c hab hac).symm ▸ hc

def recursiveFunction (hM : M ⊨ fullZFCTheory) {p : ℕ}
    (φ : ForcingFormulas.Formula (p + 3)) (ps : Fin p → M)
    (hφ : ∀ a g : M, ∃! b : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b)) (a : M) : M :=
  Classical.choose (recursiveValue_existsUnique hM φ ps hφ a)

theorem recursiveFunction_spec (hM : M ⊨ fullZFCTheory) {p : ℕ}
    (φ : ForcingFormulas.Formula (p + 3)) (ps : Fin p → M)
    (hφ : ∀ a g : M, ∃! b : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b)) (a : M) :
    (recursiveValueBody φ).Realize Empty.elim
      (Fin.snoc (Fin.snoc ps a) (recursiveFunction hM φ ps hφ a)) :=
  (Classical.choose_spec (recursiveValue_existsUnique hM φ ps hφ a)).1

theorem realize_recursiveValue_iff (hM : M ⊨ fullZFCTheory) {p : ℕ}
    (φ : ForcingFormulas.Formula (p + 3)) (ps : Fin p → M)
    (hφ : ∀ a g : M, ∃! b : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b)) (a b : M) :
    (recursiveValueBody φ).Realize Empty.elim (Fin.snoc (Fin.snoc ps a) b) ↔
      b = recursiveFunction hM φ ps hφ a := by
  constructor
  · exact (Classical.choose_spec (recursiveValue_existsUnique hM φ ps hφ a)).2 b
  · intro h
    exact h ▸ recursiveFunction_spec hM φ ps hφ a

/-- The recursive function has an internal graph on every predecessor set,
and that graph satisfies the original step formula at the next point. -/
theorem recursiveFunction_equation (hM : M ⊨ fullZFCTheory) {p : ℕ}
    (φ : ForcingFormulas.Formula (p + 3)) (ps : Fin p → M)
    (hφ : ∀ a g : M, ∃! b : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g) b)) (a : M) :
    ∃ g : M, IsGraphOn g a ∧
      (∀ x y : M, GraphApplication g x y ↔ member x a ∧ y = recursiveFunction hM φ ps hφ x) ∧
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc (Fin.snoc ps a) g)
        (recursiveFunction hM φ ps hφ a)) := by
  obtain ⟨D, f, hD, hf, hab⟩ := (realize_recursiveValueBody φ ps a _).mp
    (recursiveFunction_spec hM φ ps hφ a)
  obtain ⟨g, b, hg, hfab, hb⟩ := hf.2.2 a hD.1
  have hbval := hf.2.1.1.2 a b _ hfab hab
  subst b
  refine ⟨g, hg.1, ?_, hb⟩
  intro x y
  rw [hg.2 x y]
  constructor
  · rintro ⟨hx, hxy⟩
    exact ⟨hx, (realize_recursiveValue_iff hM φ ps hφ x y).mp
      (recursiveSolution_value hM φ ps hφ hf hxy)⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨z, hxz⟩ := (hf.2.1.2 x).mpr (hD.2.1 a hD.1 x hx)
    have hz := (realize_recursiveValue_iff hM φ ps hφ x z).mp
      (recursiveSolution_value hM φ ps hφ hf hxz)
    exact ⟨hx, (hz.trans hy.symm) ▸ hxz⟩

end PolishSpaceBook.SetTheoryModels.AbstractMembership
