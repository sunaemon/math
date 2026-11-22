module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

/-!
# Extended traces of Hilbert space projections

The dimension of a closed subspace is the extended nonnegative trace of its
orthogonal projection in any fixed Hilbert basis. In particular an infinite
kernel has dimension `∞`, rather than the junk value of algebraic `finrank`.
All sums defining traces take values in `ℝ≥0∞`.

This is infrastructure for the compact self-adjoint classification argument.
`HilbertKernelBorel.lean` supplies the Borel kernel-dimension theorem using
distance to the adjoint range. The ordered eigenvalue invariant remains
separate. The scalar field can be real or complex.
-/

noncomputable section

open scoped ENNReal
open MeasureTheory

namespace PolishSpaceBook.HilbertProjectionTrace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {ι κ : Type*}

/-- Parseval's identity with nonnegative extended-real summands. -/
theorem tsum_inner_sq (b : HilbertBasis ι 𝕜 H) (x : H) :
    (∑' i, ENNReal.ofReal (‖inner 𝕜 (b i) x‖ ^ 2)) =
      ENNReal.ofReal (‖x‖ ^ 2) := by
  have hs : HasSum (fun i => ‖inner 𝕜 (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      HilbertBasis.repr_apply_apply, LinearIsometryEquiv.norm_map] using
      lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (b.repr x)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable,
    hs.tsum_eq]

/-- The extended trace of the projection onto `K`, measured in the ambient basis `b`. -/
def projectionTrace (b : HilbertBasis ι 𝕜 H) (K : Submodule 𝕜 H)
    [K.HasOrthogonalProjection] : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (‖K.orthogonalProjectionOnto (b i)‖ ^ 2)

/-- Agreement with the usual diagonal formula for the trace of a projection. -/
theorem projectionTrace_eq_diagonal (b : HilbertBasis ι 𝕜 H)
    (K : Submodule 𝕜 H) [K.HasOrthogonalProjection] :
    projectionTrace b K =
      ∑' i, ENNReal.ofReal (RCLike.re (inner 𝕜 (K.starProjection (b i)) (b i))) := by
  simp only [Submodule.re_inner_starProjection_eq_normSq, projectionTrace]

/-- The projection trace counts the vectors of any Hilbert basis of the subspace.
Tonelli's theorem for nonnegative sums makes this valid for infinite dimension. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Parseval's identity and interchange of nonnegative sums give
    $$\kappa(A)=\sum_{j\in J}\|P_Ae_j\|^2.$$
    Indeed, expanding each $P_Ae_j$ in an orthonormal basis of the kernel and interchanging the sums makes
    each kernel basis vector contribute $1$. This is a sum of nonnegative extended real numbers, so an
    infinite-dimensional kernel gives $\infty$.
-/
theorem projectionTrace_eq_card (b : HilbertBasis ι 𝕜 H) (K : Submodule 𝕜 H)
    [K.HasOrthogonalProjection] (c : HilbertBasis κ 𝕜 K) :
    projectionTrace b K = (ENat.card κ : ℝ≥0∞) := by
  unfold projectionTrace
  calc
    (∑' i, ENNReal.ofReal (‖K.orthogonalProjectionOnto (b i)‖ ^ 2)) =
        ∑' i, ∑' j, ENNReal.ofReal (‖inner 𝕜 (c j : H) (b i)‖ ^ 2) := by
      apply tsum_congr
      intro i
      simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using
        (tsum_inner_sq c (K.orthogonalProjectionOnto (b i))).symm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner 𝕜 (c j : H) (b i)‖ ^ 2) :=
      ENNReal.tsum_comm
    _ = ∑' j : κ, (1 : ℝ≥0∞) := by
      apply tsum_congr
      intro j
      simp_rw [norm_inner_symm]
      rw [tsum_inner_sq b]
      have hn : ‖(c j : H)‖ = 1 := c.orthonormal.norm_eq_one j
      rw [hn]
      norm_num
    _ = (ENat.card κ : ℝ≥0∞) := ENNReal.tsum_one

/-- The trace is independent of the ambient Hilbert basis. -/
theorem projectionTrace_basis_independent [CompleteSpace H]
    (b : HilbertBasis ι 𝕜 H) (b' : HilbertBasis κ 𝕜 H)
    (K : Submodule 𝕜 H) [CompleteSpace K] :
    projectionTrace b K = projectionTrace b' K := by
  obtain ⟨_, c, _⟩ := exists_hilbertBasis 𝕜 K
  rw [projectionTrace_eq_card b K c, projectionTrace_eq_card b' K c]

/-- Hilbert dimension, with all infinite dimensions recorded as `∞`.
For separable Hilbert spaces this is exactly the finite-or-countably-infinite
dimension. The finite rank function is used only in its finite-dimensional branch. -/
def hilbertDimension (𝕜 : Type*) [RCLike 𝕜] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] : ℝ≥0∞ := by
  classical
  exact if FiniteDimensional 𝕜 H then (Module.finrank 𝕜 H : ℝ≥0∞) else ∞

theorem hilbertDimension_of_finiteDimensional [FiniteDimensional 𝕜 H] :
    hilbertDimension 𝕜 H = (Module.finrank 𝕜 H : ℝ≥0∞) := by
  simp [hilbertDimension, (inferInstance : FiniteDimensional 𝕜 H)]

theorem hilbertDimension_of_not_finiteDimensional
    (h : ¬ FiniteDimensional 𝕜 H) : hilbertDimension 𝕜 H = ∞ := by
  simp [hilbertDimension, h]

/-- A Hilbert basis counts dimension correctly in both the finite and infinite cases. -/
theorem hilbertDimension_eq_card (b : HilbertBasis ι 𝕜 H) :
    hilbertDimension 𝕜 H = (ENat.card ι : ℝ≥0∞) := by
  classical
  by_cases h : FiniteDimensional 𝕜 H
  · let := h
    let : Finite ι := b.orthonormal.linearIndependent.finite
    let : Fintype ι := Fintype.ofFinite ι
    rw [hilbertDimension_of_finiteDimensional,
      Module.finrank_eq_card_basis b.toOrthonormalBasis.toBasis]
    simp
  · have : Infinite ι := by
      cases finite_or_infinite ι with
      | inl hf =>
        let := hf
        let : Fintype ι := Fintype.ofFinite ι
        exact False.elim (h (Module.Finite.of_basis b.toOrthonormalBasis.toBasis))
      | inr hi => exact hi
    simp [hilbertDimension, h]

/-- The trace of an orthogonal projection is its Hilbert dimension. -/
theorem projectionTrace_eq_hilbertDimension (b : HilbertBasis ι 𝕜 H)
    (K : Submodule 𝕜 H) [CompleteSpace K] :
    projectionTrace b K = hilbertDimension 𝕜 K := by
  obtain ⟨_, c, _⟩ := exists_hilbertBasis 𝕜 K
  rw [projectionTrace_eq_card b K c, hilbertDimension_eq_card c]

/-- In particular an infinite-dimensional range has infinite projection trace. -/
theorem projectionTrace_eq_top (b : HilbertBasis ι 𝕜 H)
    (K : Submodule 𝕜 H) [CompleteSpace K] (h : ¬ FiniteDimensional 𝕜 K) :
    projectionTrace b K = ∞ := by
  rw [projectionTrace_eq_hilbertDimension, hilbertDimension_of_not_finiteDimensional h]

section Measurability

variable {X : Type*} [MeasurableSpace X] [Countable ι]

/-- Coordinate measurability of a family of projections implies measurability
of its extended trace. The projections may have infinite-dimensional ranges. -/
theorem measurable_projectionTrace (b : HilbertBasis ι 𝕜 H)
    (K : X → Submodule 𝕜 H) [∀ x, (K x).HasOrthogonalProjection]
    (h : ∀ i, Measurable (fun x => ‖(K x).orthogonalProjectionOnto (b i)‖ ^ 2)) :
    Measurable (fun x => projectionTrace b (K x)) := by
  exact Measurable.tsum (fun i => (h i).ennreal_ofReal)

/-- The trace bridge used after proving coordinate measurability of the kernel
projection. The hypothesis is explicitly about the scalar projection coordinates. -/
theorem measurable_hilbertDimension (b : HilbertBasis ι 𝕜 H)
    (K : X → Submodule 𝕜 H) [∀ x, CompleteSpace (K x)]
    (h : ∀ i, Measurable (fun x => ‖(K x).orthogonalProjectionOnto (b i)‖ ^ 2)) :
    Measurable (fun x => hilbertDimension 𝕜 (K x)) := by
  simpa only [projectionTrace_eq_hilbertDimension] using measurable_projectionTrace b K h

end Measurability

section Kernel

variable [CompleteSpace H]

/-- Kernel dimension for bounded operators, retaining infinite kernels. -/
def kernelDimension (A : H →L[𝕜] H) : ℝ≥0∞ :=
  hilbertDimension 𝕜 A.ker

theorem kernelDimension_eq_projectionTrace (b : HilbertBasis ι 𝕜 H)
    (A : H →L[𝕜] H) :
    kernelDimension A = projectionTrace b A.ker :=
  (projectionTrace_eq_hilbertDimension b A.ker).symm

end Kernel

end PolishSpaceBook.HilbertProjectionTrace
