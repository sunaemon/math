module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Basic.Denumerable

@[expose] public section

/-! # Patching a measurable equivalence across countable leftovers

A measurable equivalence on a large piece is retained away from a reserved
countable set. A bijection of the countable leftovers supplies the other
branch, with the same two branches for the inverse.
-/
namespace PolishSpaceBook.CountableBorelPatch
open Set
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {S : Set X} (h : S ≃ᵐ Y) (R : Set Y)

def reserved : Set X := (fun y => (h.symm y).val) '' R

def leftover : Set X := Sᶜ ∪ reserved h R

theorem reserved_subset : reserved h R ⊆ S := by
  rintro _ ⟨y, _, rfl⟩
  exact (h.symm y).property

theorem leftover_countable (hSc : Sᶜ.Countable) (hRc : R.Countable) :
    (leftover h R).Countable := hSc.union (hRc.image _)

theorem leftover_infinite (hRi : R.Infinite) : (leftover h R).Infinite := by
  have hinj : Function.Injective (fun y => (h.symm y).val) :=
    Subtype.val_injective.comp h.symm.injective
  exact (hRi.image hinj.injOn).mono subset_union_right

theorem outside {x : X} (hx : x ∉ leftover h R) :
    ∃ hxS : x ∈ S, h ⟨x, hxS⟩ ∉ R := by
  classical
  have hxS : x ∈ S := by
    by_contra hnot
    exact hx (Or.inl hnot)
  refine ⟨hxS, ?_⟩
  intro hmem
  apply hx
  exact Or.inr ⟨h ⟨x, hxS⟩, hmem, by simp⟩

theorem inverse_outside {y : Y} (hy : y ∉ R) : (h.symm y).val ∉ leftover h R := by
  rintro (hnot | ⟨z, hz, hzy⟩)
  · exact hnot (h.symm y).property
  · exact hy (h.symm.injective (Subtype.ext hzy) ▸ hz)

/-- The large branches are the original map and its inverse, restricted. -/
noncomputable def largeEquiv : ((leftover h R)ᶜ : Set X) ≃ᵐ (Rᶜ : Set Y) where
  toFun x := ⟨h ⟨x.val, (outside h R x.property).choose⟩, (outside h R x.property).choose_spec⟩
  invFun y := ⟨(h.symm y.val).val, inverse_outside h R y.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by apply Subtype.ext; simp
  measurable_toFun := (h.measurable.comp (measurable_subtype_coe.subtype_mk)).subtype_mk
  measurable_invFun := (measurable_subtype_coe.comp
    (h.symm.measurable.comp measurable_subtype_coe)).subtype_mk

variable [MeasurableSingletonClass X] [MeasurableSingletonClass Y]

/-- Any bijection of countable leftovers is automatically measurable in both directions. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Any such map is Borel, since every subset of a countable subset of a Polish space is Borel.
-/
noncomputable def smallEquiv (hSc : Sᶜ.Countable) (hRc : R.Countable)
    (e : leftover h R ≃ R) : leftover h R ≃ᵐ R := by
  letI := (leftover_countable h R hSc hRc).to_subtype
  letI := hRc.to_subtype
  exact ⟨e, measurable_of_countable _, measurable_of_countable _⟩

/-- Countable infinitude suffices to choose the leftover bijection. -/
noncomputable def leftoverEquiv (hSc : Sᶜ.Countable) (hRc : R.Countable) (hRi : R.Infinite) :
    leftover h R ≃ R := by
  letI := (leftover_countable h R hSc hRc).to_subtype
  letI := hRc.to_subtype
  letI := (leftover_infinite h R hRi).to_subtype
  letI := hRi.to_subtype
  exact Classical.choice nonempty_equiv_of_countable

/-- The sum decomposition implements the book's piecewise map and inverse. -/
noncomputable def patch (hSc : Sᶜ.Countable) (hRc : R.Countable)
    (e : leftover h R ≃ R) : X ≃ᵐ Y := by
  classical
  exact (MeasurableEquiv.sumCompl (leftover_countable h R hSc hRc).measurableSet).symm.trans
    ((MeasurableEquiv.sumCongr (smallEquiv h R hSc hRc e) (largeEquiv h R)).trans
      (MeasurableEquiv.sumCompl hRc.measurableSet))

theorem patch_small (hSc : Sᶜ.Countable) (hRc : R.Countable)
    (e : leftover h R ≃ R) {x : X} (hx : x ∈ leftover h R) :
    patch h R hSc hRc e x = (e ⟨x, hx⟩).val := by
  classical
  change (Equiv.sumCompl (fun y => y ∈ R))
    ((e.sumCongr (largeEquiv h R).toEquiv)
      ((Equiv.sumCompl (fun x => x ∈ leftover h R)).symm x)) = _
  rw [Equiv.sumCompl_symm_apply_of_pos hx]
  rfl

theorem patch_large (hSc : Sᶜ.Countable) (hRc : R.Countable)
    (e : leftover h R ≃ R) {x : X} (hx : x ∉ leftover h R) :
    patch h R hSc hRc e x = h ⟨x, (outside h R hx).choose⟩ := by
  classical
  change (Equiv.sumCompl (fun y => y ∈ R))
    ((e.sumCongr (largeEquiv h R).toEquiv)
      ((Equiv.sumCompl (fun x => x ∈ leftover h R)).symm x)) = _
  rw [Equiv.sumCompl_symm_apply_of_neg hx]
  rfl

theorem patch_symm_small (hSc : Sᶜ.Countable) (hRc : R.Countable)
    (e : leftover h R ≃ R) {y : Y} (hy : y ∈ R) :
    (patch h R hSc hRc e).symm y = (e.symm ⟨y, hy⟩).val := by
  classical
  change (Equiv.sumCompl (fun x => x ∈ leftover h R))
    ((e.symm.sumCongr (largeEquiv h R).symm.toEquiv)
      ((Equiv.sumCompl (fun y => y ∈ R)).symm y)) = _
  rw [Equiv.sumCompl_symm_apply_of_pos hy]
  rfl

theorem patch_symm_large (hSc : Sᶜ.Countable) (hRc : R.Countable)
    (e : leftover h R ≃ R) {y : Y} (hy : y ∉ R) :
    (patch h R hSc hRc e).symm y = (h.symm y).val := by
  classical
  change (Equiv.sumCompl (fun x => x ∈ leftover h R))
    ((e.symm.sumCongr (largeEquiv h R).symm.toEquiv)
      ((Equiv.sumCompl (fun y => y ∈ R)).symm y)) = _
  rw [Equiv.sumCompl_symm_apply_of_neg hy]
  rfl

/-- Preimages split into the countable branch and the inverse large-piece map. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    For the displayed implication, if $B$ is Borel in $\BaireSpace$, then
    $$
    \Phi^{-1}(B)
    =
    e^{-1}(B\cap R)
    \;\cup\;
    \mathrm{gap}^{-1}(\SetDifference{B}{R}).
    $$
-/
theorem patch_preimage (hSc : Sᶜ.Countable) (hRc : R.Countable)
    (e : leftover h R ≃ R) (B : Set Y) :
    patch h R hSc hRc e ⁻¹' B =
      Subtype.val '' {x : leftover h R | (e x).val ∈ B} ∪
      (fun y => (h.symm y).val) '' (B \ R) := by
  classical
  ext x
  constructor
  · intro hxB
    by_cases hxL : x ∈ leftover h R
    · refine Or.inl ⟨⟨x, hxL⟩, ?_, rfl⟩
      change (e ⟨x, hxL⟩).val ∈ B
      rwa [← patch_small h R hSc hRc e hxL]
    · refine Or.inr ⟨patch h R hSc hRc e x, ⟨hxB, ?_⟩, ?_⟩
      · rw [patch_large h R hSc hRc e hxL]
        exact (outside h R hxL).choose_spec
      · rw [patch_large h R hSc hRc e hxL]
        simp
  · rintro (⟨z, hz, rfl⟩ | ⟨y, ⟨hyB, hyR⟩, rfl⟩)
    · change patch h R hSc hRc e z.val ∈ B
      rwa [patch_small h R hSc hRc e z.property]
    · change patch h R hSc hRc e (h.symm y).val ∈ B
      rw [← patch_symm_large h R hSc hRc e hyR, MeasurableEquiv.apply_symm_apply]
      exact hyB

/-- Images have the same two-piece description, using the forward map. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Conversely, if $A\IncludedIn\CantorSpace$ is Borel, then
    $$
    \Phi(A)
    =
    e(A\cap(\mathrm{Fin}\internalDisjointUnion E))
    \;\cup\;
    \mathrm{gap}(A\cap(\SetDifference{\infiniteSubsets{\omega}}{E})).
    $$
-/
theorem patch_image (hSc : Sᶜ.Countable) (hRc : R.Countable)
    (e : leftover h R ≃ R) (A : Set X) :
    patch h R hSc hRc e '' A =
      (fun x : leftover h R => (e x).val) '' (Subtype.val ⁻¹' A) ∪
      h '' {x : S | x.val ∈ A ∧ x.val ∉ leftover h R} := by
  classical
  apply Subset.antisymm
  · rintro y ⟨x, hxA, rfl⟩
    by_cases hxL : x ∈ leftover h R
    · exact Or.inl ⟨⟨x, hxL⟩, hxA, (patch_small h R hSc hRc e hxL).symm⟩
    · exact Or.inr ⟨⟨x, (outside h R hxL).choose⟩, ⟨hxA, hxL⟩,
        (patch_large h R hSc hRc e hxL).symm⟩
  · rintro y (⟨x, hx, rfl⟩ | ⟨x, ⟨hxA, hxL⟩, rfl⟩)
    · exact ⟨x.val, hx, patch_small h R hSc hRc e x.property⟩
    · exact ⟨x.val, hxA, patch_large h R hSc hRc e hxL⟩

end PolishSpaceBook.CountableBorelPatch
