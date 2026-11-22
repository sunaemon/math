module

public import PolishSpaceBook.LambdaComputableMetricPresentations
public import PolishSpaceBook.LambdaComputableReals
public import PolishSpaceBook.LambdaZeroBoundaryMeasure
public import PolishSpaceBook.LambdaL1StepDensity
public import PolishSpaceBook.LambdaHaltingOpenMeasure

@[expose] public section

namespace PolishSpaceBook
open Set MeasureTheory Metric NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA

/-- A Borel probability measure with one valuation program for every open name
in the supplied computable metric presentation. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    A \termdefineas{computable measure}{computable probability measure} on a computable Polish space is a Borel
    probability measure supplied with a computable valuation: from an open name, one closed lambda program produces
    rational lower bounds converging to the measure of the represented open set. The program is uniform in the open
    name and the approximation stage. Use the rational-ball convention of §{sec:tte-effective-open-closed}, with zero
    for an empty entry and successor codes for balls. Every numerical stream then names an open set. A lower
    approximation need not come with a rate of convergence.
-/
structure LambdaComputableProbabilityMeasure {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (P : LambdaComputableMetricPresentation X) where
  measure : Measure X
  probability : IsProbabilityMeasure measure
  valuation : LambdaProbabilityValuation P.points measure

/-- The actual union of the metric closed balls, rather than closures of open balls. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Fix a finite list $L=((i_j,r_j))_{j<\ell}$ of basic centers and rational radii in $X$, and write
    $$\begin{aligned}
    U_L&:=\bigcup_{j<\ell}\Ball{q_{i_j}}{r_j},\\
    F_L&:=\bigcup_{j<\ell}\{x:d(x,q_{i_j})\le r_j\},\qquad V_L:=\SetDifference{X}{F_L}.
    \end{aligned}$$
    Here $F_L$ uses metric closed balls, which need not be the closures of the corresponding open balls.
-/
def finiteClosedBallUnion {X : Type*} [MetricSpace X] (q : ℕ → X) (L : List ℕ) : Set X :=
  {x | ∃ b ∈ L, x ∈ codedClosedBall q b}

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Fix a finite list $L=((i_j,r_j))_{j<\ell}$ of basic centers and rational radii in $X$, and write
    $$\begin{aligned}
    U_L&:=\bigcup_{j<\ell}\Ball{q_{i_j}}{r_j},\\
    F_L&:=\bigcup_{j<\ell}\{x:d(x,q_{i_j})\le r_j\},\qquad V_L:=\SetDifference{X}{F_L}.
    \end{aligned}$$
    Here $F_L$ uses metric closed balls, which need not be the closures of the corresponding open balls.
-/
theorem finiteClosedBallExterior_eq_compl {X : Type*} [MetricSpace X] (q : ℕ → X)
    (L : List ℕ) : finiteClosedBallExterior q L = (finiteClosedBallUnion q L)ᶜ := by
  ext x
  simp [finiteClosedBallExterior, finiteClosedBallUnion]

/-- An inherited metric on a two-point subset of the real line. -/
abbrev TwoPointMetricSpace := {x : ℝ // x = 0 ∨ x = 1}

/-- The warning persists for a strictly positive radius. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Fix a finite list $L=((i_j,r_j))_{j<\ell}$ of basic centers and rational radii in $X$, and write
    $$\begin{aligned}
    U_L&:=\bigcup_{j<\ell}\Ball{q_{i_j}}{r_j},\\
    F_L&:=\bigcup_{j<\ell}\{x:d(x,q_{i_j})\le r_j\},\qquad V_L:=\SetDifference{X}{F_L}.
    \end{aligned}$$
    Here $F_L$ uses metric closed balls, which need not be the closures of the corresponding open balls.
-/
theorem exists_positive_closedBall_not_closure_ball :
    ∃ a : TwoPointMetricSpace, closure (ball a 1) ≠ closedBall a 1 := by
  let a : TwoPointMetricSpace := ⟨0, Or.inl rfl⟩
  let b : TwoPointMetricSpace := ⟨1, Or.inr rfl⟩
  have ha : ball a 1 = {a} := by
    ext x
    rw [mem_ball, mem_singleton_iff, Subtype.ext_iff]
    change dist x.val 0 < 1 ↔ x.val = 0
    rcases x.property with hx | hx <;> norm_num [hx]
  refine ⟨a, ?_⟩
  intro he
  rw [ha, isClosed_singleton.closure_eq] at he
  have hb : b ∈ closedBall a 1 := by
    change dist (1 : ℝ) 0 ≤ 1
    norm_num
  rw [← he] at hb
  have hba : b = a := hb
  have hz := congrArg Subtype.val hba
  norm_num [a, b] at hz

/-- A supplied rational measure value is computable even with positive boundary mass. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Null spheres are a sufficient condition. A set may have computable measure even when a sphere has positive
    measure, for instance when that measure is supplied separately. For an arbitrary effectively open set, only
    the lower computation is guaranteed, as the preceding Cantor-space example shows.
-/
theorem positiveSphere_computable_ball_measure :
    IsProbabilityMeasure (Measure.dirac (1 : ℝ)) ∧
      (Measure.dirac (1 : ℝ)).real (sphere 0 1) = 1 ∧
      (Measure.dirac (1 : ℝ)).real (ball 0 1) = 0 ∧
      IsComputablePoint realRepresentation ((Measure.dirac (1 : ℝ)).real (ball 0 1)) := by
  have hs : (Measure.dirac (1 : ℝ)).real (sphere 0 1) = 1 := by
    simp [Measure.real]
  have hb : (Measure.dirac (1 : ℝ)).real (ball 0 1) = 0 := by
    simp [Measure.real, mem_ball]
  refine ⟨inferInstance, hs, hb, ?_⟩
  rw [hb]
  apply (computableReal_iff_rationalApproximation 0).mpr
  refine ⟨fun _ => 0, numericalConstant 0, numericalConstant_computes 0, fun n => ?_⟩
  norm_num [rationalPoint, RationalCode.ofNat, RationalCode.value]

end PolishSpaceBook
