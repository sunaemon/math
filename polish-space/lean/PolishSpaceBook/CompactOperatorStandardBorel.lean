module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-!
# Norm parameter spaces of compact operators

A compact operator on a Hilbert space is approximated in operator norm by
projecting its image onto the span of a finite net of its unit-ball image.
These approximants are finite sums of rank-one operators. On a separable
Hilbert space the set of such sums is separable, since sums of length `n`
are parametrized continuously by `n` pairs of Hilbert-space vectors.

This proves norm separability directly, without assuming separability of
the full space of bounded operators. Closedness then gives Polish and
standard Borel structures on the compact and compact self-adjoint spaces.
-/

noncomputable section

open Set TopologicalSpace InnerProductSpace

namespace PolishSpaceBook.CompactOperatorStandardBorel

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H]

/-- The norm-continuous parametrization by finite sums of rank-one maps. -/
def rankOneSum (n : ℕ) (p : (Fin n → H) × (Fin n → H)) : H →L[𝕜] H :=
  ∑ i, rankOne 𝕜 (p.1 i) (p.2 i)

omit [CompleteSpace H] in
theorem continuous_rankOneSum (n : ℕ) :
    Continuous (rankOneSum (𝕜 := 𝕜) (H := H) n) := by
  unfold rankOneSum
  apply continuous_finsetSum
  intro i _
  simp only [rankOne_def]
  exact ((ContinuousLinearMap.smulRightL 𝕜 H H).continuous.comp
    ((innerSL 𝕜).continuous.comp ((continuous_apply i).comp continuous_snd))).clm_apply
    ((continuous_apply i).comp continuous_fst)

/-- All finite rank-one sums, parametrized without choosing a basis of `H`. -/
def finiteRankSums : Set (H →L[𝕜] H) :=
  ⋃ n : ℕ, range (rankOneSum (𝕜 := 𝕜) (H := H) n)

theorem projection_comp_mem_finiteRankSums (V : Submodule 𝕜 H)
    [FiniteDimensional 𝕜 V] (A : H →L[𝕜] H) :
    V.starProjection.comp A ∈ finiteRankSums := by
  let b := stdOrthonormalBasis 𝕜 V
  refine mem_iUnion.mpr ⟨Module.finrank 𝕜 V, ?_⟩
  refine ⟨(fun i => (b i : H), fun i => A.adjoint (b i : H)), ?_⟩
  ext x
  simp only [rankOneSum, sum_apply, rankOne_apply, ContinuousLinearMap.comp_apply]
  rw [b.starProjection_eq_sum_rankOne]
  simp only [sum_apply, rankOne_apply, ContinuousLinearMap.adjoint_inner_left]

/-- Every compact operator can be uniformly approximated on the unit ball by
an operator with finite-dimensional range. -/
theorem exists_finiteRankSum_approx (A : H →L[𝕜] H) (hA : IsCompactOperator A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B ∈ finiteRankSums (𝕜 := 𝕜) (H := H), ‖A - B‖ < ε := by
  obtain ⟨s, _, hs, hcover⟩ :=
    (hA.isCompact_closure_image_closedBall 1).finite_cover_balls (half_pos hε)
  let V := Submodule.span 𝕜 s
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 hs
  refine ⟨V.starProjection.comp A, projection_comp_mem_finiteRankSums V A, ?_⟩
  have hbound : ‖A - V.starProjection.comp A‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (le_of_lt (half_pos hε))
    intro x hx
    have hAx : A x ∈ closure (A '' Metric.closedBall (0 : H) 1) :=
      subset_closure ⟨x, by simp [Metric.mem_closedBall, dist_zero_right, hx], rfl⟩
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hAx)
    have hyV : y ∈ V := Submodule.subset_span hy
    change ‖A x - V.starProjection (A x)‖ ≤ ε / 2
    rw [← dist_eq_norm, V.dist_starProjection_eq_infDist]
    exact (Metric.infDist_le_dist_of_mem hyV).trans (le_of_lt hxy)
  exact hbound.trans_lt (half_lt_self hε)

theorem compact_subset_closure_finiteRankSums :
    {A : H →L[𝕜] H | IsCompactOperator A} ⊆ closure finiteRankSums := by
  intro A hA
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨B, hB, hAB⟩ := exists_finiteRankSum_approx A hA hε
  exact ⟨B, hB, by simpa only [dist_eq_norm] using hAB⟩

variable [SeparableSpace H]

omit [CompleteSpace H] in
theorem isSeparable_finiteRankSums :
    IsSeparable (finiteRankSums (𝕜 := 𝕜) (H := H)) :=
  IsSeparable.iUnion (fun n => isSeparable_range (continuous_rankOneSum n))

/-- Compact operators on a separable Hilbert space are norm separable. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    To see separability, approximate
    a compact operator uniformly on the unit ball by projecting its image onto the span of a finite
    $\varepsilon$-net. The approximants have finite-dimensional range and are finite sums of rank-one operators.
    For each fixed number of summands these sums are continuously parameterized by finitely many pairs of vectors
    in $H$, so their union is separable. Compact operators lie in its norm closure
-/
theorem isSeparable_compactOperators :
    IsSeparable {A : H →L[𝕜] H | IsCompactOperator A} :=
  isSeparable_finiteRankSums.closure.mono compact_subset_closure_finiteRankSums

/-- Compact operators with their operator-norm topology. -/
abbrev CompactOperators (𝕜 : Type*) [RCLike 𝕜] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :=
  {A : H →L[𝕜] H // IsCompactOperator A}

instance : CompleteSpace (CompactOperators 𝕜 H) :=
  isClosed_setOfPred_isCompactOperator.completeSpace_coe

instance : SeparableSpace (CompactOperators 𝕜 H) :=
  isSeparable_compactOperators.separableSpace

instance : PolishSpace (CompactOperators 𝕜 H) := by infer_instance

instance : MeasurableSpace (CompactOperators 𝕜 H) := borel _
instance : BorelSpace (CompactOperators 𝕜 H) := ⟨rfl⟩
instance : StandardBorelSpace (CompactOperators 𝕜 H) := by infer_instance

/-- Compact self-adjoint operators with their operator-norm topology. -/
abbrev CompactSelfAdjoint (𝕜 : Type*) [RCLike 𝕜] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] :=
  {A : H →L[𝕜] H // IsCompactOperator A ∧ IsSelfAdjoint A}

omit [SeparableSpace H] in
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    and form a norm-closed subset
    of the complete space of bounded operators. The self-adjoint operators form a closed subset as well, because
    the adjoint operation is norm-continuous.
-/
theorem isClosed_compactSelfAdjoint :
    IsClosed {A : H →L[𝕜] H | IsCompactOperator A ∧ IsSelfAdjoint A} := by
  exact isClosed_setOfPred_isCompactOperator.inter
    (isClosed_eq ContinuousLinearMap.adjoint.continuous continuous_id)

instance : CompleteSpace (CompactSelfAdjoint 𝕜 H) :=
  isClosed_compactSelfAdjoint.completeSpace_coe

instance : SeparableSpace (CompactSelfAdjoint 𝕜 H) :=
  (isSeparable_compactOperators.mono (fun _ h => h.1)).separableSpace

instance : PolishSpace (CompactSelfAdjoint 𝕜 H) := by infer_instance

instance : MeasurableSpace (CompactSelfAdjoint 𝕜 H) := borel _
instance : BorelSpace (CompactSelfAdjoint 𝕜 H) := ⟨rfl⟩
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    The norm topology makes the space of compact self-adjoint operators Polish.
-/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Thus the compact self-adjoint parameter space is complete and
    separable, and its Borel structure is standard.
-/
instance : StandardBorelSpace (CompactSelfAdjoint 𝕜 H) := by infer_instance

end PolishSpaceBook.CompactOperatorStandardBorel
