module

public import PolishSpaceBook.LambdaDistanceRelations
public import PolishSpaceBook.CauchyNamesPolishRepresentations

@[expose] public section

namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm

/-- A complete metric space with dense basic points and one closed lambda
semidecider for the joint rational distance-interval relation. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    A \termdefine{computable metric presentation} is a triple
    $$\mathcal X=(X,d,\Sequence{q_n}{n\in\omega})$$
    where $(X,d)$ is a nonempty complete separable metric space, $\Sequence{q_n}{n\in\omega}$ is dense in $X$, and the
    distance data is effective
    in the following uniform sense: the set
    $$\{(i,j,a,b)\in\omega^2\times\QQ^2 : a<d(q_i,q_j)<b\}$$
    is recursively enumerable after fixing an effective coding of rationals. The next proposition justifies the equivalent
    formulation by rational approximations.
-/
structure LambdaComputableMetricPresentation (X : Type*) [MetricSpace X] where
  complete : CompleteSpace X
  points : ℕ → X
  dense : DenseRange points
  intervalProgram : AlphaTerm
  intervals : NumericallySemidecides intervalProgram
    {z | DistanceInterval points (decodeDistanceInterval z)}

namespace LambdaComputableMetricPresentation
variable {X : Type*} [MetricSpace X]

theorem nonempty (P : LambdaComputableMetricPresentation X) : Nonempty X :=
  ⟨P.points 0⟩

theorem separableSpace (P : LambdaComputableMetricPresentation X) : TopologicalSpace.SeparableSpace X :=
  P.dense.separableSpace'

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    A \termuse{computable metric presentation} $\mathcal X=(X,d,(q_n))$ gives a represented space $(X,\rho_X)$ by its fast
    Cauchy representation. A \termdefine{computable Polish space} is a Polish space equipped with such a computable metric
    presentation, viewed through its fast Cauchy representation. The preceding constructions specialize to the expected
    operations on computable Polish spaces.
-/
theorem polishSpace (P : LambdaComputableMetricPresentation X) : PolishSpace X := by
  let : CompleteSpace X := P.complete
  let : TopologicalSpace.SeparableSpace X := P.separableSpace
  infer_instance

/-- This packages an existential witness; it does not assert a computable choice
of metric approximation from an unspecified presentation. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    A \termdefine{computable metric presentation} is a triple
    $$\mathcal X=(X,d,\Sequence{q_n}{n\in\omega})$$
    where $(X,d)$ is a nonempty complete separable metric space, $\Sequence{q_n}{n\in\omega}$ is dense in $X$, and the
    distance data is effective
    in the following uniform sense: the set
    $$\{(i,j,a,b)\in\omega^2\times\QQ^2 : a<d(q_i,q_j)<b\}$$
    is recursively enumerable after fixing an effective coding of rationals. The next proposition justifies the equivalent
    formulation by rational approximations.
-/
theorem hasApproximation (P : LambdaComputableMetricPresentation X) :
    Nonempty (LambdaMetricApproximation P.points) :=
  (lambda_distance_data_equivalence P.points).mp ⟨P.intervalProgram, P.intervals⟩

/-- The same presentation can be supplied by a uniform lambda approximation. -/
def ofApproximation [CompleteSpace X] (q : ℕ → X) (hq : DenseRange q)
    (A : LambdaMetricApproximation q) : LambdaComputableMetricPresentation X where
  complete := inferInstance
  points := q
  dense := hq
  intervalProgram := distanceIntervalSemidecider A.program
  intervals := A.semidecides_distanceIntervals

/-- The represented computable Polish space uses the actual fast Cauchy domain
and the actual limit map of these basic points. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    A \termuse{computable metric presentation} $\mathcal X=(X,d,(q_n))$ gives a represented space $(X,\rho_X)$ by its fast
    Cauchy representation. A \termdefine{computable Polish space} is a Polish space equipped with such a computable metric
    presentation, viewed through its fast Cauchy representation. The preceding constructions specialize to the expected
    operations on computable Polish spaces.
-/
noncomputable def representation (P : LambdaComputableMetricPresentation X) : Representation X := by
  letI := P.complete
  exact cauchyRepresentationObject P.points P.dense

theorem representation_admissible (P : LambdaComputableMetricPresentation X) :
    P.representation.IsAdmissible := by
  let : CompleteSpace X := P.complete
  exact cauchyRepresentationObject_isAdmissible P.points P.dense

end LambdaComputableMetricPresentation
end PolishSpaceBook
