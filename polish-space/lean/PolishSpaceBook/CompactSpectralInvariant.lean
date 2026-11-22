module

public import PolishSpaceBook.CompactMinMaxClassifies
public import PolishSpaceBook.CompactMinMaxMultiplicity
public import PolishSpaceBook.HilbertKernelBorel
public import PolishSpaceBook.CompactOperatorStandardBorel
public import PolishSpaceBook.BorelReducibilitySynthesis

@[expose] public section

/-! # A Borel complete invariant for compact self-adjoint operators

The two min–max lists record the positive and negative eigenvalues with
multiplicity, padded by zero. The third coordinate is the kernel's Hilbert
dimension in `ℝ≥0∞`; it keeps every infinite-dimensional kernel distinct from
all finite-dimensional kernels. The construction works over either real or
complex scalars and includes the zero-dimensional ambient space.
-/

noncomputable section

open Set TopologicalSpace
open scoped ENNReal

namespace PolishSpaceBook.CompactSpectralInvariant

open HilbertMinMax HilbertProjectionTrace HilbertKernelBorel CompactSpectralUnitary
  CompactOperatorStandardBorel CompactMinMaxClassifies

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] [SeparableSpace H]

/-- A concrete standard Borel target for both eigenvalue lists and the kernel dimension. -/
abbrev SpectralData := ((ℕ → ℝ) × (ℕ → ℝ)) × ℝ≥0∞

theorem spectralData_standardBorel : StandardBorelSpace SpectralData := by infer_instance

/-- The actual spectral invariant on the norm space of compact self-adjoint operators. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the last example, fix a separable Hilbert space $H$. If $A$ is compact and self-adjoint, let
    $$
    \lambda^+_0(A)\ge\lambda^+_1(A)\ge\cdots\ge0,
    \qquad
    \lambda^-_0(A)\ge\lambda^-_1(A)\ge\cdots\ge0
    $$
    list, with multiplicity and padded by zeros, the positive eigenvalues of $A$ and the absolute values of its negative
    eigenvalues. Let $\kappa(A):=\dim\ker(A)\in\omega\cup\{\infty\}$.
-/
def spectralInvariant (A : CompactSelfAdjoint 𝕜 H) : SpectralData :=
  ((minMax A.val, minMax (-A.val)), kernelDimension A.val)

/-- Both lists are norm-continuous; kernel dimension is Borel. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Thus the displayed complete invariant is Borel and reduces unitary
    equivalence to equality on a standard Borel sequence space.
-/
theorem measurable_spectralInvariant :
    Measurable (spectralInvariant : CompactSelfAdjoint 𝕜 H → SpectralData) := by
  let : MeasurableSpace (H →L[𝕜] H) := borel _
  let : BorelSpace (H →L[𝕜] H) := ⟨rfl⟩
  exact ((continuous_signed_minMax.comp continuous_subtype_val).measurable).prodMk
    (measurable_kernelDimension.comp continuous_subtype_val.measurable)

/-- Equality of the invariant is exactly the existence of an intertwining
linear isometric equivalence, over either real or complex scalars. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Consequently, compact
    self-adjoint operators $A$ and $B$ are unitarily equivalent exactly when
    $$
    \big(\Sequence{\lambda^+_n(A)}{n\in\omega},\Sequence{\lambda^-_n(A)}{n\in\omega},\kappa(A)\big)
    =
    \big(\Sequence{\lambda^+_n(B)}{n\in\omega},\Sequence{\lambda^-_n(B)}{n\in\omega},\kappa(B)\big).
    $$
-/
theorem spectralInvariant_eq_iff (A B : CompactSelfAdjoint 𝕜 H) :
    spectralInvariant A = spectralInvariant B ↔
      ∃ U : H ≃ₗᵢ[𝕜] H, ∀ x, U (A.val x) = B.val (U x) := by
  change spectralInvariant A = spectralInvariant B ↔ UnitarilyEquivalent A.val B.val
  rw [unitarilyEquivalent_iff_signed_minMax_kernel A.val B.val
    A.property.1 A.property.2 B.property.1 B.property.2]
  simp only [spectralInvariant, Prod.mk.injEq, and_assoc]

omit [SeparableSpace H] in
/-- The negative list records absolute values of negative eigenvalues with
their actual eigenspace multiplicities. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Applying the same argument to $-A$ gives $\lambda^-_n(A)=\MinMaxValue{-A}{n}$.
-/
theorem negative_eigen_multiplicity (A : CompactSelfAdjoint 𝕜 H)
    {μ : ℝ} (hμ : 0 < μ) :
    hilbertDimension 𝕜 (Eigen A.val (- (μ : 𝕜))) =
      ({n | (spectralInvariant A).1.2 n = μ}.ncard : ℝ≥0∞) := by
  have h := CompactMinMaxMultiplicity.dimension_eigen_eq_minMax_fiber
    (-A.val) A.property.1.neg A.property.2.neg hμ
  rw [eigen_neg] at h
  exact h

/-- Unitary equivalence of compact self-adjoint operators is smooth. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    *Unitary equivalence of compact self-adjoint operators* on a separable Hilbert space is smooth: the ordered
        eigenvalue lists and the dimension of the kernel give a Borel complete invariant.
-/
theorem smooth_unitarilyEquivalent :
    Smooth (fun A B : CompactSelfAdjoint 𝕜 H => UnitarilyEquivalent A.val B.val) := by
  apply smooth_of_standardBorel_completeInvariant measurable_spectralInvariant
  intro A B
  exact (spectralInvariant_eq_iff A B).symm

end PolishSpaceBook.CompactSpectralInvariant
