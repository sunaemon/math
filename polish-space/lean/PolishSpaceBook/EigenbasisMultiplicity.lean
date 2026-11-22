module

public import PolishSpaceBook.DiagonalMinMax

@[expose] public section

/-! # Eigenspace dimensions from fibers of an actual eigenbasis -/

noncomputable section

open Set Filter
open scoped ENNReal

namespace PolishSpaceBook.EigenbasisMultiplicity

open DiagonalMinMax CompactSpectralUnitary HilbertProjectionTrace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {ι : Type*}

theorem coefficient_eq_zero_of_distinct_eigenvalues
    (A : H →L[𝕜] H) (hs : IsSelfAdjoint A)
    (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i)
    {μ : ℝ} {x : H} (hx : x ∈ Eigen A (μ : 𝕜)) {i : ι} (hi : ev i ≠ μ) :
    inner 𝕜 (b i) x = 0 := by
  have hAx : A x = (μ : 𝕜) • x := Module.End.mem_eigenspace_iff.mp hx
  have hprod : (ev i : 𝕜) * inner 𝕜 (b i) x = (μ : 𝕜) * inner 𝕜 (b i) x := by
    calc
      _ = inner 𝕜 (A (b i)) x := by rw [he, inner_smul_left, RCLike.conj_ofReal]
      _ = inner 𝕜 (b i) (A x) := hs.isSymmetric.apply_clm _ _
      _ = _ := by rw [hAx, inner_smul_right]
  by_contra hne
  exact hi (RCLike.ofReal_injective (mul_right_cancel₀ hne hprod))

/-- A finite eigenvalue fiber spans precisely its eigenspace. -/
theorem eigen_eq_basisSpan_fiber (A : H →L[𝕜] H) (hs : IsSelfAdjoint A)
    (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i) (μ : ℝ)
    (hfin : {i | ev i = μ}.Finite) :
    Eigen A (μ : 𝕜) = basisSpan b {i | ev i = μ} := by
  classical
  let s := {i | ev i = μ}
  let : Fintype s := hfin.fintype
  have : FiniteDimensional 𝕜 (basisSpan b s) :=
    FiniteDimensional.span_of_finite 𝕜 (finite_range _)
  apply le_antisymm
  · intro x hx
    apply (basisSpan b s).closed_of_finiteDimensional.mem_of_tendsto (b.hasSum_repr x)
    filter_upwards [] with t
    apply Submodule.sum_mem
    intro i _
    by_cases hi : ev i = μ
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [b.repr_apply_apply, coefficient_eq_zero_of_distinct_eigenvalues A hs b ev he hx hi,
        zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change A (b i) = (μ : 𝕜) • b i
    rw [he, i.2]

/-- Finite eigenspace multiplicity is the cardinality of its eigenbasis fiber. -/
theorem dimension_eigen_eq_ncard_fiber (A : H →L[𝕜] H) (hs : IsSelfAdjoint A)
    (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i) (μ : ℝ)
    (hfin : {i | ev i = μ}.Finite) :
    hilbertDimension 𝕜 (Eigen A (μ : 𝕜)) = ({i | ev i = μ}.ncard : ℝ≥0∞) := by
  classical
  let s := {i | ev i = μ}
  let : Fintype s := hfin.fintype
  have : FiniteDimensional 𝕜 (basisSpan b s) :=
    FiniteDimensional.span_of_finite 𝕜 (finite_range _)
  rw [eigen_eq_basisSpan_fiber A hs b ev he μ hfin]
  rw [hilbertDimension_of_finiteDimensional]
  have hdim : Module.finrank 𝕜 (basisSpan b s) = Fintype.card s :=
    finrank_span_eq_card (b.orthonormal.linearIndependent.comp _ Subtype.val_injective)
  rw [hdim]
  simp only [Set.fintypeCard_eq_ncard, s]

/-- A self-adjoint operator has no nonreal eigenspaces. -/
theorem eigen_eq_bot_of_nonreal (A : H →L[𝕜] H) (hs : IsSelfAdjoint A)
    {μ : 𝕜} (hμ : (RCLike.re μ : 𝕜) ≠ μ) : Eigen A μ = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  by_cases hz : x = 0
  · simp [hz]
  · exact False.elim (hμ (RCLike.conj_eq_iff_re.mp
      (hs.isSymmetric.conj_eigenvalue_eq_self
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx, hz⟩))))

end PolishSpaceBook.EigenbasisMultiplicity
