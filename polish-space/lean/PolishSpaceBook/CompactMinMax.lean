module

public import PolishSpaceBook.HilbertMinMax
public import PolishSpaceBook.CompactOperatorStandardBorel

@[expose] public section

/-!
# Vanishing at infinity of compact min–max coordinates

Finite rank-one sums have eventually zero min–max coordinates: discard the
span of their input vectors. Norm approximation and the 1-Lipschitz estimate
then imply that the min–max coordinates of a compact operator tend to zero.
This statement applies to arbitrary compact operators; self-adjointness is
needed for the separate identification with eigenvalues.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace PolishSpaceBook.CompactMinMax

open HilbertMinMax CompactOperatorStandardBorel

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Discarding a finite subspace on whose orthogonal complement the operator
vanishes forces all later min–max coordinates to be zero. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    For a finite-rank operator they eventually vanish: discard a finite-dimensional
    subspace on whose orthogonal complement the operator vanishes.
-/
theorem minMax_eq_zero_of_vanishes (A : H →L[𝕜] H) (V : Submodule 𝕜 H)
    [FiniteDimensional 𝕜 V] (hA : ∀ x ∈ Vᗮ, A x = 0)
    {n : ℕ} (hn : Module.finrank 𝕜 V ≤ n) : minMax A n = 0 := by
  apply le_antisymm _ (minMax_nonneg A n)
  apply (minMax_le_rayleighSup A n ⟨V, inferInstance, hn⟩).trans
  apply ciSup_le
  intro x
  have hx : A (x.1 : H) = 0 := hA _ x.1.2
  simp [hx]

theorem finiteRankSum_minMax_eventually_zero (A : H →L[𝕜] H) (hA : A ∈ finiteRankSums) :
    ∃ N : ℕ, ∀ n ≥ N, minMax A n = 0 := by
  classical
  obtain ⟨m, p, rfl⟩ := mem_iUnion.mp hA
  let V := Submodule.span 𝕜 (range p.2)
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (finite_range p.2)
  refine ⟨Module.finrank 𝕜 V, fun n hn => minMax_eq_zero_of_vanishes _ V ?_ hn⟩
  intro x hx
  simp only [rankOneSum, sum_apply, InnerProductSpace.rankOne_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hi : p.2 i ∈ V := Submodule.subset_span (mem_range_self i)
  rw [(V.mem_orthogonal x).mp hx _ hi, zero_smul]

variable [CompleteSpace H]

/-- Compactness makes the nonnegative min–max coordinates tend to zero. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Finite-rank approximation therefore gives
    $\MinMaxValue{A}{n}\to0$ for compact $A$.
-/
theorem tendsto_minMax_zero (A : H →L[𝕜] H) (hA : IsCompactOperator A) :
    Tendsto (minMax A) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨B, hB, hAB⟩ := exists_finiteRankSum_approx A hA hε
  obtain ⟨N, hN⟩ := finiteRankSum_minMax_eventually_zero B hB
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right, Real.norm_of_nonneg (minMax_nonneg A n)]
  have h := minMax_le_add_norm A B n
  rw [hN n hn, zero_add] at h
  exact h.trans_lt hAB

end PolishSpaceBook.CompactMinMax
