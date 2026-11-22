module

public import PolishSpaceBook.HilbertDimensionIsometry
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

@[expose] public section

/-!
# Spectral gluing for compact self-adjoint operators

The compact spectral theorem decomposes the Hilbert space as the orthogonal
Hilbert sum of all eigenspaces, including the kernel. Isometries on matching
eigenspaces therefore glue to an intertwining unitary. This is the spectral
classification step; encoding the eigenspace multiplicities by ordered
min–max lists is a separate step.
-/

noncomputable section

open Set TopologicalSpace
open scoped ENNReal

namespace PolishSpaceBook.CompactSpectralUnitary

open HilbertProjectionTrace HilbertDimensionIsometry

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Eigenspaces of bounded operators, including the zero eigenspace. -/
abbrev Eigen (A : H →L[𝕜] H) (μ : 𝕜) : Submodule 𝕜 H :=
  Module.End.eigenspace A.toLinearMap μ

instance (A : H →L[𝕜] H) (μ : 𝕜) : CompleteSpace (Eigen A μ) :=
  (ContinuousLinearMap.isClosed_eigenspace A μ).completeSpace_coe

/-- The spectral Hilbert-sum decomposition includes every eigenspace. -/
theorem eigen_isHilbertSum (A : H →L[𝕜] H)
    (hc : IsCompactOperator A) (hs : IsSelfAdjoint A) :
    IsHilbertSum 𝕜 (fun μ => Eigen A μ) (fun μ => (Eigen A μ).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal
  · exact hs.isSymmetric.orthogonalFamily_eigenspaces
  · rw [← eq_top_iff, Submodule.topologicalClosure_eq_top_iff]
    exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs.isSymmetric

/-- Every nonzero eigenspace of a compact operator is finite dimensional. -/
theorem finiteDimensional_eigen (A : H →L[𝕜] H)
    (hc : IsCompactOperator A) (μ : 𝕜) (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (Eigen A μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace hc μ hμ

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    The compact spectral theorem gives an orthogonal
    decomposition into the corresponding finite-dimensional eigenspaces and the kernel.
-/
/-- The spectral decomposition includes the kernel and finite-dimensional nonzero blocks. -/
theorem compact_spectral_decomposition (A : H →L[𝕜] H)
    (hc : IsCompactOperator A) (hs : IsSelfAdjoint A) :
    IsHilbertSum 𝕜 (fun μ => Eigen A μ) (fun μ => (Eigen A μ).subtypeₗᵢ) ∧
      ∀ μ ≠ 0, FiniteDimensional 𝕜 (Eigen A μ) :=
  ⟨eigen_isHilbertSum A hc hs, finiteDimensional_eigen A hc⟩

/-- Unitary equivalence expressed by an intertwining linear isometry. -/
def UnitarilyEquivalent (A B : H →L[𝕜] H) : Prop :=
  ∃ U : H ≃ₗᵢ[𝕜] H, ∀ x, U (A x) = B (U x)

/-- Isometries on all eigenspaces glue to an intertwining unitary. -/
theorem unitarilyEquivalent_of_eigenspace_isometries
    (A B : H →L[𝕜] H) (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hBc : IsCompactOperator B) (hBs : IsSelfAdjoint B)
    (e : ∀ μ, Eigen A μ ≃ₗᵢ[𝕜] Eigen B μ) : UnitarilyEquivalent A B := by
  classical
  let sA := eigen_isHilbertSum A hAc hAs
  let V : ∀ μ, Eigen A μ →ₗᵢ[𝕜] H := fun μ =>
    (Eigen B μ).subtypeₗᵢ.comp (e μ).toLinearIsometry
  have hV : IsHilbertSum 𝕜 (fun μ => Eigen A μ) V := by
    apply IsHilbertSum.mk
    · intro μ ν hμν x y
      exact hBs.isSymmetric.orthogonalFamily_eigenspaces hμν (e μ x) (e ν y)
    · have hr (μ : 𝕜) : LinearMap.range (V μ).toLinearMap = Eigen B μ := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact (e μ y).2
        · intro hx
          exact ⟨(e μ).symm ⟨x, hx⟩, by simp [V]⟩
      simp_rw [hr]
      rw [← eq_top_iff, Submodule.topologicalClosure_eq_top_iff]
      exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hBc hBs.isSymmetric
  let U := sA.linearIsometryEquiv.trans hV.linearIsometryEquiv.symm
  have hU (μ : 𝕜) (x : Eigen A μ) : U (x : H) = (e μ x : H) := by
    have hx := sA.linearIsometryEquiv_symm_apply_single x
    change sA.linearIsometryEquiv.symm (lp.single 2 μ x) = (x : H) at hx
    have hrepr : sA.linearIsometryEquiv (x : H) = lp.single 2 μ x := by
      rw [← hx]
      exact sA.linearIsometryEquiv.apply_symm_apply _
    change hV.linearIsometryEquiv.symm (sA.linearIsometryEquiv (x : H)) = _
    rw [hrepr, hV.linearIsometryEquiv_symm_apply_single]
    rfl
  refine ⟨U, ?_⟩
  let f := U.toContinuousLinearEquiv.toContinuousLinearMap.comp A
  let g := B.comp U.toContinuousLinearEquiv.toContinuousLinearMap
  have heq : f.comp sA.linearIsometryEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      g.comp sA.linearIsometryEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro μ
    ext x
    change U (A (sA.linearIsometryEquiv.symm (lp.single 2 μ x))) =
      B (U (sA.linearIsometryEquiv.symm (lp.single 2 μ x)))
    rw [sA.linearIsometryEquiv_symm_apply_single]
    have hAx : A (x : H) = μ • (x : H) := Module.End.mem_eigenspace_iff.mp x.2
    have hBx : B (e μ x : H) = μ • (e μ x : H) :=
      Module.End.mem_eigenspace_iff.mp (e μ x).2
    change U (A (x : H)) = B (U (x : H))
    rw [hAx, map_smul, hU, hBx]
  intro x
  have h := congrArg (fun T : _ →L[𝕜] H => T (sA.linearIsometryEquiv x)) heq
  simpa [f, g] using h

omit [CompleteSpace H] in
/-- An intertwining unitary restricts to a linear equivalence on every eigenspace. -/
theorem eigenspace_dimensions_eq_of_unitarilyEquivalent
    (A B : H →L[𝕜] H) (h : UnitarilyEquivalent A B) (μ : 𝕜) :
    hilbertDimension 𝕜 (Eigen A μ) = hilbertDimension 𝕜 (Eigen B μ) := by
  obtain ⟨U, hU⟩ := h
  let e : Eigen A μ ≃ₗ[𝕜] Eigen B μ :=
    { toFun := fun x => ⟨U x, by
        apply Module.End.mem_eigenspace_iff.mpr
        change B (U (x : H)) = μ • U (x : H)
        have hx : A (x : H) = μ • (x : H) := Module.End.mem_eigenspace_iff.mp x.2
        rw [← hU, hx, map_smul]⟩
      invFun := fun y => ⟨U.symm y, by
        apply Module.End.mem_eigenspace_iff.mpr
        apply U.injective
        change U (A (U.symm (y : H))) = U (μ • U.symm (y : H))
        rw [hU, U.apply_symm_apply, map_smul, U.apply_symm_apply]
        exact Module.End.mem_eigenspace_iff.mp y.2⟩
      left_inv := by intro x; apply Subtype.ext; exact U.symm_apply_apply (x : H)
      right_inv := by intro y; apply Subtype.ext; exact U.apply_symm_apply (y : H)
      map_add' := by intro x y; apply Subtype.ext; exact U.map_add (x : H) (y : H)
      map_smul' := by intro a x; apply Subtype.ext; exact U.map_smul a (x : H) }
  exact hilbertDimension_eq_of_linearEquiv e

variable [SeparableSpace H]

/-- Equality of actual eigenspace dimensions suffices for unitary equivalence;
the eigenspace isometries are constructed from dimension equality. -/
theorem unitarilyEquivalent_of_eigenspace_dimensions
    (A B : H →L[𝕜] H) (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hBc : IsCompactOperator B) (hBs : IsSelfAdjoint B)
    (h : ∀ μ, hilbertDimension 𝕜 (Eigen A μ) = hilbertDimension 𝕜 (Eigen B μ)) :
    UnitarilyEquivalent A B := by
  classical
  exact unitarilyEquivalent_of_eigenspace_isometries A B hAc hAs hBc hBs
    (fun μ => Classical.choice (nonempty_linearIsometryEquiv_of_dimension_eq (h μ)))

/-- Compact self-adjoint operators are unitarily equivalent exactly when every
eigenspace has the same Hilbert dimension, including the zero eigenspace. -/
theorem unitarilyEquivalent_iff_eigenspace_dimensions
    (A B : H →L[𝕜] H) (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hBc : IsCompactOperator B) (hBs : IsSelfAdjoint B) :
    UnitarilyEquivalent A B ↔
      ∀ μ, hilbertDimension 𝕜 (Eigen A μ) = hilbertDimension 𝕜 (Eigen B μ) :=
  ⟨fun h μ => eigenspace_dimensions_eq_of_unitarilyEquivalent A B h μ,
    unitarilyEquivalent_of_eigenspace_dimensions A B hAc hAs hBc hBs⟩

end PolishSpaceBook.CompactSpectralUnitary
