module

public import PolishSpaceBook.HilbertMinMaxBounds
public import PolishSpaceBook.CompactEigenbasis

@[expose] public section

/-! # Rayleigh estimates in a genuine eigenbasis -/

noncomputable section

open Set
open scoped ENNReal

namespace PolishSpaceBook.DiagonalMinMax

open HilbertMinMax HilbertMinMaxBounds

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι : Type*}

theorem hasSum_weights (b : HilbertBasis ι 𝕜 H) (x : H) :
    HasSum (fun i => ‖inner 𝕜 (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    HilbertBasis.repr_apply_apply, LinearIsometryEquiv.norm_map] using
    lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (b.repr x)

variable [CompleteSpace H]

/-- The quadratic form is the convergent weighted sum of eigenvalues. -/
theorem hasSum_quadratic (A : H →L[𝕜] H) (hs : IsSelfAdjoint A)
    (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i) (x : H) :
    HasSum (fun i => ev i * ‖inner 𝕜 (b i) x‖ ^ 2)
      (RCLike.re (inner 𝕜 x (A x))) := by
  have h := RCLike.reCLM.hasSum (b.hasSum_inner_mul_inner x (A x))
  convert h using 1
  · ext i
    change _ = RCLike.re (inner 𝕜 x (b i) * inner 𝕜 (b i) (A x))
    rw [← hs.isSymmetric.apply_clm, he, inner_smul_left, RCLike.conj_ofReal]
    rw [← inner_conj_symm (b i) x]
    rw [mul_left_comm, RCLike.mul_conj]
    rw [← RCLike.ofReal_pow]
    simp [norm_inner_symm]
  · rfl

/-- The algebraic span of the chosen part of a Hilbert basis. -/
def basisSpan (b : HilbertBasis ι 𝕜 H) (s : Set ι) : Submodule 𝕜 H :=
  Submodule.span 𝕜 (range (fun i : s => b i))

omit [CompleteSpace H] in
theorem inner_eq_zero_of_mem_basisSpan (b : HilbertBasis ι 𝕜 H) (s : Set ι)
    {x : H} (hx : x ∈ basisSpan b s) {i : ι} (hi : i ∉ s) :
    inner 𝕜 (b i) x = 0 := by
  have hle : basisSpan b s ≤ (innerSL 𝕜 (b i)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact b.orthonormal.inner_eq_zero (fun h => hi (h ▸ j.2))
  exact hle hx

theorem quadratic_lower_on_basisSpan (A : H →L[𝕜] H) (hs : IsSelfAdjoint A)
    (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i)
    (s : Set ι) {r : ℝ} (hr : ∀ i ∈ s, r ≤ ev i)
    {x : H} (hx : x ∈ basisSpan b s) :
    r * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 x (A x)) := by
  apply hasSum_le _ ((hasSum_weights b x).mul_left r) (hasSum_quadratic A hs b ev he x)
  intro i
  by_cases hi : i ∈ s
  · exact mul_le_mul_of_nonneg_right (hr i hi) (sq_nonneg _)
  · rw [inner_eq_zero_of_mem_basisSpan b s hx hi]
    simp

theorem quadratic_upper_on_orthogonal (A : H →L[𝕜] H) (hs : IsSelfAdjoint A)
    (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i)
    (s : Set ι) {r : ℝ} (hr : ∀ i ∉ s, ev i ≤ r)
    {x : H} (hx : x ∈ (basisSpan b s)ᗮ) :
    RCLike.re (inner 𝕜 x (A x)) ≤ r * ‖x‖ ^ 2 := by
  apply hasSum_le _ (hasSum_quadratic A hs b ev he x) ((hasSum_weights b x).mul_left r)
  intro i
  by_cases hi : i ∈ s
  · have hz : inner 𝕜 (b i) x = 0 :=
      ((basisSpan b s).mem_orthogonal x).mp hx _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    rw [hz]
    simp
  · exact mul_le_mul_of_nonneg_right (hr i hi) (sq_nonneg _)

theorem minMax_upper_of_finite_cutoff (A : H →L[𝕜] H) (hs : IsSelfAdjoint A)
    (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i)
    (s : Set ι) [Fintype s] {n : ℕ} {r : ℝ}
    (hn : Fintype.card s ≤ n) (hr0 : 0 ≤ r) (hr : ∀ i ∉ s, ev i ≤ r) :
    minMax A n ≤ r := by
  have : FiniteDimensional 𝕜 (basisSpan b s) :=
    FiniteDimensional.span_of_finite 𝕜 (finite_range _)
  have hdim : Module.finrank 𝕜 (basisSpan b s) = Fintype.card s :=
    finrank_span_eq_card (b.orthonormal.linearIndependent.comp _ Subtype.val_injective)
  apply (minMax_le_rayleighSup A n ⟨basisSpan b s, inferInstance, hdim ▸ hn⟩).trans
  apply ciSup_le
  intro x
  have hq := quadratic_upper_on_orthogonal A hs b ev he s hr x.1.2
  apply hq.trans
  have hnorm : ‖(x.1 : H)‖ ≤ 1 := x.2
  have hsq : ‖(x.1 : H)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (x.1 : H)]
  simpa using mul_le_mul_of_nonneg_left hsq hr0

theorem minMax_lower_of_finite_basisSpan (A : H →L[𝕜] H) (hs : IsSelfAdjoint A)
    (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i)
    (s : Set ι) [Fintype s] {n : ℕ} {r : ℝ}
    (hn : n < Fintype.card s) (hr : ∀ i ∈ s, r ≤ ev i) :
    r ≤ minMax A n := by
  have : FiniteDimensional 𝕜 (basisSpan b s) :=
    FiniteDimensional.span_of_finite 𝕜 (finite_range _)
  have hdim : Module.finrank 𝕜 (basisSpan b s) = Fintype.card s :=
    finrank_span_eq_card (b.orthonormal.linearIndependent.comp _ Subtype.val_injective)
  exact le_minMax_of_subspace A (basisSpan b s) (hdim ▸ hn)
    (fun _ hx => quadratic_lower_on_basisSpan A hs b ev he s hr hx)

end PolishSpaceBook.DiagonalMinMax
