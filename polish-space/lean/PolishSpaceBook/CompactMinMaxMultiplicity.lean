module

public import PolishSpaceBook.CompactMinMaxCounting
public import PolishSpaceBook.SpectralCountRecovery
public import PolishSpaceBook.EigenbasisMultiplicity
public import Mathlib.Order.Interval.Set.Nat

@[expose] public section

/-! # Min–max lists record the actual positive eigenvalues with multiplicity -/

noncomputable section

open Set
open scoped ENNReal

namespace PolishSpaceBook.CompactMinMaxMultiplicity

open HilbertMinMax HilbertProjectionTrace CompactSpectralUnitary CompactEigenbasis
  CompactMinMaxCounting SpectralCountRecovery EigenbasisMultiplicity

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Every positive superlevel set of the min–max list is finite. -/
theorem finite_minMax_ge (A : H →L[𝕜] H) (hc : IsCompactOperator A)
    (hs : IsSelfAdjoint A) {r : ℝ} (hr : 0 < r) :
    {n | r ≤ minMax A n}.Finite := by
  obtain ⟨ι, b, ev, he⟩ := exists_eigenbasis A hc hs
  have h := minMax_threshold_set A hc hs b ev he (half_pos hr)
  apply (Set.finite_Iio {i | r / 2 < ev i}.ncard).subset
  intro n hn
  rw [← h]
  exact (half_lt_self hr).trans_le hn

/-- The multiplicity of each strictly positive eigenvalue equals the number
of occurrences of that value in the min–max list. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    These threshold counts identify the decreasing sequence $\MinMaxValue{A}{n}$ with the positive eigenvalues,
    counted with multiplicity and padded by zeros. Hence $\lambda^+_n(A)=\MinMaxValue{A}{n}$.
-/
theorem dimension_eigen_eq_minMax_fiber (A : H →L[𝕜] H)
    (hc : IsCompactOperator A) (hs : IsSelfAdjoint A) {μ : ℝ} (hμ : 0 < μ) :
    hilbertDimension 𝕜 (Eigen A (μ : 𝕜)) =
      ({n | minMax A n = μ}.ncard : ℝ≥0∞) := by
  classical
  obtain ⟨ι, b, ev, he⟩ := exists_eigenbasis A hc hs
  have hcounts (r : ℝ) (hr : 0 < r) :
      {i | r < ev i}.ncard = {n | r < minMax A n}.ncard := by
    rw [minMax_threshold_set A hc hs b ev he hr, Set.ncard_Iio_nat]
  have hcard := positive_fiber_ncard_eq ev (minMax A)
    (fun r hr => finite_eigenvalue_ge A hc hs b ev he hr)
    (fun r hr => finite_minMax_ge A hc hs hr) hcounts hμ
  have hfin : {i | ev i = μ}.Finite :=
    (finite_eigenvalue_ge A hc hs b ev he hμ).subset (by intro i hi; exact hi.ge)
  rw [dimension_eigen_eq_ncard_fiber A hs b ev he μ hfin, hcard]

/-- If there are only finitely many positive eigenvalues, the list is zero
from their total multiplicity onward. -/
theorem minMax_eq_zero_of_finite_positive (A : H →L[𝕜] H)
    (hs : IsSelfAdjoint A) {ι : Type*} (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i) (hf : {i | 0 < ev i}.Finite)
    {n : ℕ} (hn : {i | 0 < ev i}.ncard ≤ n) : minMax A n = 0 := by
  classical
  let s := {i | 0 < ev i}
  let : Fintype s := hf.fintype
  apply le_antisymm _ (minMax_nonneg A n)
  exact DiagonalMinMax.minMax_upper_of_finite_cutoff A hs b ev he s
    (by simpa only [Set.fintypeCard_eq_ncard] using hn) le_rfl
    (fun i hi => le_of_not_gt hi)

end PolishSpaceBook.CompactMinMaxMultiplicity
