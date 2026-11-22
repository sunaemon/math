module

public import PolishSpaceBook.HilbertProjectionTrace
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Order.IsLUB

@[expose] public section

/-!
# Borel kernel dimension in a separable Hilbert space

The norm of the projection of `x` onto `ker A` is its distance to the
closure of the range of `A†`. A dense sequence in the Hilbert space expresses
this distance as a countable infimum of norm-continuous scalar functions.
Together with the nonnegative extended trace identity, this proves Borel
measurability of kernel dimension for all bounded operators. Compactness
and self-adjointness are not required for this coordinate of the invariant.
-/

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace PolishSpaceBook.HilbertKernelBorel

open HilbertProjectionTrace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H] [SeparableSpace H]

omit [CompleteSpace H] in
/-- A separable inner product space has no uncountable orthonormal family. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Choose a fixed orthonormal basis $\IndexedFamily{e_j}{j\in J}$ of $H$, where $J$ is finite or countable.
-/
theorem countable_orthonormal {ι : Type*} {v : ι → H} (hv : Orthonormal 𝕜 v) :
    Countable ι := by
  classical
  have hnear (i : ι) : ∃ n : ℕ, dist (v i) (denseSeq H n) < (1 / 3 : ℝ) :=
    Metric.denseRange_iff.mp (denseRange_denseSeq H) (v i) (1 / 3) (by norm_num)
  choose f hf using hnear
  apply Function.Injective.countable (f := f)
  intro i j hij
  by_contra hne
  have hd : dist (v i) (v j) < (2 / 3 : ℝ) := by
    calc
      dist (v i) (v j) ≤ dist (v i) (denseSeq H (f i)) +
          dist (v j) (denseSeq H (f i)) := dist_triangle_right _ _ _
      _ < 2 / 3 := by
        have hi := hf i
        rw [hij] at hi ⊢
        linarith [hf j]
  have hin : inner 𝕜 (v i) (v i - v j) = 1 := by
    rw [inner_sub_right, hv.inner_eq_zero hne]
    simp [inner_self_eq_norm_sq_to_K, hv.norm_eq_one i]
  have hnorm := norm_inner_le_norm (𝕜 := 𝕜) (v i) (v i - v j)
  rw [hin, norm_one, hv.norm_eq_one i, one_mul, ← dist_eq_norm] at hnorm
  linarith

omit [SeparableSpace H] in
/-- Kernel projection norm as distance to the adjoint range. -/
theorem norm_kernelProjection_eq_infDist (A : H →L[𝕜] H) (x : H) :
    ‖A.ker.orthogonalProjectionOnto x‖ = Metric.infDist x (A.adjoint.range : Set H) := by
  change ‖A.ker.starProjection x‖ = _
  rw [Submodule.norm_starProjection_eq_infDist, A.orthogonal_ker,
    Submodule.topologicalClosure_coe, Metric.infDist_closure]

/-- The distance formula uses a fixed dense sequence and a countable infimum. -/
theorem norm_kernelProjection_eq_iInf (A : H →L[𝕜] H) (x : H) :
    ‖A.ker.orthogonalProjectionOnto x‖ =
      ⨅ n : ℕ, dist x (A.adjoint (denseSeq H n)) := by
  rw [norm_kernelProjection_eq_infDist, Metric.infDist_eq_iInf]
  change (⨅ y : range A.adjoint, dist x y.1) = _
  rw [iInf_range']
  have hd := (denseRange_denseSeq H).ciInf' (f := fun y => dist x (A.adjoint y))
    (continuous_const.dist (A.adjoint.continuous))
  exact hd.symm.trans (iInf_range' (fun y => dist x (A.adjoint y)) (denseSeq H))

/-- For self-adjoint operators the same formula uses the operator itself. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    To check the remaining coordinate, let $P_A$ be the orthogonal projection onto
    $\ker(A)$. Fix a dense sequence $\Sequence{d_n}{n\in\omega}$ in $H$.
    Since $A$ is self-adjoint, the closure of its range is the orthogonal complement of its kernel.
    The projection theorem and density therefore give, for each $x\in H$,
    $$\|P_Ax\|=\inf_{n\in\omega}\|x-Ad_n\|.$$
-/
theorem norm_kernelProjection_eq_iInf_of_isSelfAdjoint
    (A : H →L[𝕜] H) (hA : IsSelfAdjoint A) (x : H) :
    ‖A.ker.orthogonalProjectionOnto x‖ =
      ⨅ n : ℕ, dist x (A (denseSeq H n)) := by
  simpa only [hA.adjoint_eq] using norm_kernelProjection_eq_iInf A x

section Borel

variable [MeasurableSpace (H →L[𝕜] H)] [BorelSpace (H →L[𝕜] H)]

/-- The norm of each kernel-projection coordinate is Borel for operator norm. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Each function on the right depends norm-continuously on $A$, so this countable infimum is Borel.
-/
theorem measurable_norm_kernelProjection (x : H) :
    Measurable (fun A : H →L[𝕜] H => ‖A.ker.orthogonalProjectionOnto x‖) := by
  simp_rw [norm_kernelProjection_eq_iInf]
  apply Measurable.iInf
  intro n
  have hc : Continuous (fun A : H →L[𝕜] H => A.adjoint (denseSeq H n)) :=
    ContinuousLinearMap.adjoint.continuous.clm_apply continuous_const
  exact (continuous_const.dist hc).measurable

/-- Kernel Hilbert dimension is Borel, with `∞` retained for every infinite kernel. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    The countable sum is Borel.
-/
theorem measurable_kernelDimension :
    Measurable (kernelDimension : (H →L[𝕜] H) → ℝ≥0∞) := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis 𝕜 H
  have : Countable ι := countable_orthonormal b.orthonormal
  exact measurable_hilbertDimension b (fun A : H →L[𝕜] H => A.ker)
    (fun i => (measurable_norm_kernelProjection (b i)).pow_const 2)

end Borel

end PolishSpaceBook.HilbertKernelBorel
