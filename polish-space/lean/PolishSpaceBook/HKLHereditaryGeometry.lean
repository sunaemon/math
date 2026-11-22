module

public import PolishSpaceBook.HKLKernel
public import PolishSpaceBook.EquivalenceRelationSeparation

@[expose] public section

/-! # Pure saturation algebra for hereditary HKL kernels

Agreement on a set propagates to its saturation. The gap image is the
complementary part of the larger saturation under this agreement.
-/

namespace PolishSpaceBook
open Set

variable {X : Type*}

/-- The part of the F-saturation witnessed by an E-inequivalent source point. -/
def relationGapImage (E F : Setoid X) (A : Set X) : Set X :=
  {z | ∃ a ∈ A, F.r a z ∧ ¬ E.r a z}

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    They also agree on $Y$: given two points of $Y$, move each back into $A$ along $E$ and use transitivity.
-/
theorem relation_agreement_on_saturation (E F : Setoid X)
    (hEF : ∀ ⦃x y⦄, E.r x y → F.r x y) {A : Set X}
    (hA : ∀ x ∈ A, ∀ y ∈ A, F.r x y → E.r x y) :
    ∀ x ∈ erSaturation E A, ∀ y ∈ erSaturation E A, F.r x y → E.r x y := by
  rintro x ⟨a, ha, hax⟩ y ⟨b, hb, hby⟩ hxy
  have hab : F.r a b := F.trans (hEF hax) (F.trans hxy (F.symm (hEF hby)))
  exact E.trans (E.symm hax) (E.trans (hA a ha b hb hab) hby)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    Under this assumption the set
    $$Y'=\{z:\exists a\in A\ (a\mathrel{\EffectiveClosureER{E}}z\ \land\ a\mathrel{\not E}z)\}$$
    is exactly $\SetDifference{Z}{Y}$
-/
theorem relationGapImage_eq_diff (E F : Setoid X)
    (hEF : ∀ ⦃x y⦄, E.r x y → F.r x y) {A : Set X}
    (hA : ∀ x ∈ A, ∀ y ∈ A, F.r x y → E.r x y) :
    relationGapImage E F A = erSaturation F A \ erSaturation E A := by
  ext z
  constructor
  · rintro ⟨a, ha, haz, hne⟩
    refine ⟨⟨a, ha, haz⟩, ?_⟩
    rintro ⟨b, hb, hbz⟩
    exact hne (E.trans (hA a ha b hb (F.trans haz (F.symm (hEF hbz)))) hbz)
  · rintro ⟨⟨a, ha, haz⟩, hn⟩
    exact ⟨a, ha, haz, fun he => hn ⟨a, ha, he⟩⟩

theorem relationGapImage_invariant (E F : Setoid X)
    (hEF : ∀ ⦃x y⦄, E.r x y → F.r x y) {A : Set X}
    (hA : ∀ x ∈ A, ∀ y ∈ A, F.r x y → E.r x y) :
    ERInvariant E (relationGapImage E F A) := by
  rw [relationGapImage_eq_diff E F hEF hA]
  intro x y hxy
  exact and_congr (erSaturation_invariant F A (hEF hxy))
    (not_congr (erSaturation_invariant E A hxy))

theorem relationGapImage_disjoint_saturation (E F : Setoid X)
    (hEF : ∀ ⦃x y⦄, E.r x y → F.r x y) {A : Set X}
    (hA : ∀ x ∈ A, ∀ y ∈ A, F.r x y → E.r x y) :
    Disjoint (erSaturation E A) (relationGapImage E F A) := by
  rw [relationGapImage_eq_diff E F hEF hA]
  exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)

/-- Each point in the gap kernel supplies a witness in the gap image. -/
theorem relationGapImage_nonempty (E F : Setoid X) {A : Set X}
    (hne : A.Nonempty) (hAH : A ⊆ equivalenceGapKernel E F) :
    (relationGapImage E F A).Nonempty := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨z, haz, hne⟩ := hAH ha
  exact ⟨z, a, ha, haz, hne⟩

end PolishSpaceBook
