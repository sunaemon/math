module

public import PolishSpaceBook.ComputableAnalysisProse
public import PolishSpaceBook.LambdaRandomnessTests
public import PolishSpaceBook.LambdaEffectiveOpenSets

@[expose] public section

namespace PolishSpaceBook
open Set Filter Topology MeasureTheory NamedLambda NamedLambda.AlphaTerm

namespace LambdaComputableMetricPresentation
variable {X : Type*} [MetricSpace X]

/-- One numerical lambda program enumerates every row's rational balls. -/
def UniformlyOpen (P : LambdaComputableMetricPresentation X) (U : ℕ → Set X) : Prop :=
  ∃ E : AlphaTerm, ∃ a : ℕ → ℕ, NumericalComputes E a ∧
    ∀ n, U n = ⋃ s, enumeratedRationalBall P.points (a (Nat.pair n s))

/-- Selecting a row is lambda composition with the fixed row index. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    The definition extends from Cantor space to any computable Polish probability space. For a
    \termuseas{computable measure}{computable probability measure} $\mu$, a Martin-Löf test relative to $\mu$ is a
    uniformly effectively open sequence $\Sequence{U_n}{n\in\omega}$ with $\mu(U_n)\le 2^{-n}$. A point is $\mu$-Martin-Löf
    random if it
    avoids all such tests.
-/
theorem UniformlyOpen.effectivelyOpen {P : LambdaComputableMetricPresentation X}
    {U : ℕ → Set X} (h : P.UniformlyOpen U) (n : ℕ) :
    LambdaEffectivelyOpen P.representation (U n) := by
  let : CompleteSpace X := P.complete
  obtain ⟨A⟩ := P.hasApproximation
  obtain ⟨E, a, ha, hU⟩ := h
  apply (lambdaEffectivelyOpen_iff_ball_enumeration A P.dense (U n)).mpr
  exact ⟨_, _, ha.comp ((numericalConstant_computes n).pair numericalIdentity_computes), hU n⟩

end LambdaComputableMetricPresentation

namespace LambdaComputableProbabilityMeasure
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {P : LambdaComputableMetricPresentation X}

/-- Martin-Löf tests for the supplied computable probability measure. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    The definition extends from Cantor space to any computable Polish probability space. For a
    \termuseas{computable measure}{computable probability measure} $\mu$, a Martin-Löf test relative to $\mu$ is a
    uniformly effectively open sequence $\Sequence{U_n}{n\in\omega}$ with $\mu(U_n)\le 2^{-n}$. A point is $\mu$-Martin-Löf
    random if it
    avoids all such tests.
-/
def MLTest (M : LambdaComputableProbabilityMeasure P) (U : ℕ → Set X) : Prop :=
  MartinLofTest P.UniformlyOpen M.measure.real U

/-- The definition quantifies over all tests using the same presentation and measure. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    The definition extends from Cantor space to any computable Polish probability space. For a
    \termuseas{computable measure}{computable probability measure} $\mu$, a Martin-Löf test relative to $\mu$ is a
    uniformly effectively open sequence $\Sequence{U_n}{n\in\omega}$ with $\mu(U_n)\le 2^{-n}$. A point is $\mu$-Martin-Löf
    random if it
    avoids all such tests.
-/
def MLRandom (M : LambdaComputableProbabilityMeasure P) (x : X) : Prop :=
  MartinLofRandom P.UniformlyOpen M.measure.real x

/-- The prescribed rate implies nullness without a convergence modulus for the valuation. -/
/-@ booklink:
  source: polish-space-book/algorithmic-randomness.md
  target: prose
  excerpt: |
    The definition extends from Cantor space to any computable Polish probability space. For a
    \termuseas{computable measure}{computable probability measure} $\mu$, a Martin-Löf test relative to $\mu$ is a
    uniformly effectively open sequence $\Sequence{U_n}{n\in\omega}$ with $\mu(U_n)\le 2^{-n}$. A point is $\mu$-Martin-Löf
    random if it
    avoids all such tests.
-/
theorem MLTest.null_intersection {M : LambdaComputableProbabilityMeasure P}
    {U : ℕ → Set X} (h : M.MLTest U) : M.measure (⋂ n, U n) = 0 := by
  let : IsProbabilityMeasure M.measure := M.probability
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ measureReal_nonneg
  have ht : Tendsto (fun n => (1 / 2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  exact ge_of_tendsto ht (Eventually.of_forall (fun n =>
    (measureReal_mono (μ := M.measure) (iInter_subset U n)).trans (h.2 n)))

end LambdaComputableProbabilityMeasure
end PolishSpaceBook
