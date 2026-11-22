module

public import PolishSpaceBook.LambdaBallExteriors

@[expose] public section

/-! # Computing measures of finite ball unions with null spheres

A computable valuation supplies rational lower approximations on open names.
The two enumerators here come from actual lambda semidecision programs. Applying
the valuation programs to them and running the gap search gives a Cauchy name.
-/
namespace PolishSpaceBook
open Set Filter Topology MeasureTheory Metric NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

variable {X : Type*} [PseudoMetricSpace X] {ι : Type*} (c : ι → X) (r : ι → ℝ)

theorem ballUnion_subset_closedBallUnion :
    (⋃ i, ball (c i) (r i)) ⊆ ⋃ i, closedBall (c i) (r i) :=
  iUnion_mono (fun _ => ball_subset_closedBall)

theorem closedBallUnion_diff_subset_spheres :
    (⋃ i, closedBall (c i) (r i)) \ (⋃ i, ball (c i) (r i)) ⊆ ⋃ i, sphere (c i) (r i) := by
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx.1
  refine mem_iUnion.mpr ⟨i,?_⟩
  rw [← closedBall_sdiff_ball]
  exact ⟨hi,fun h => hx.2 (mem_iUnion.mpr ⟨i,h⟩)⟩

variable [MeasurableSpace X] [BorelSpace X] [Fintype ι] (μ : Measure X)

omit [BorelSpace X] in
theorem ballUnion_measure_eq_closedBallUnion
    (h : ∀ i, μ (sphere (c i) (r i)) = 0) :
    μ (⋃ i, ball (c i) (r i)) = μ (⋃ i, closedBall (c i) (r i)) := by
  apply measure_congr
  rw [ae_eq_set]
  refine ⟨?_,measure_mono_null (closedBallUnion_diff_subset_spheres c r) (measure_iUnion_null h)⟩
  rw [sdiff_eq_empty.mpr (ballUnion_subset_closedBallUnion c r)]
  exact measure_empty

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: theorem
  title: Computing finite ball-union measures
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    The relevant geometric comparison is
    $$U_L\IncludedIn F_L,\qquad \SetDifference{F_L}{U_L}\IncludedIn
     \bigcup_{j<\ell}\{x:d(x,q_{i_j})=r_j\}.$$
    For the second inclusion, a point of $\SetDifference{F_L}{U_L}$ lies in some closed ball and in none of the open
    balls, so its distance to that closed ball's center equals the radius. The hypothesis makes this difference
    null. The finite union $F_L$ is closed, and hence
    $$\mu(U_L)=\mu(F_L),\qquad \mu(U_L)+\mu(V_L)=1.$$
    Apply the valuation program to the computable enumerations of $U_L$ and $V_L$. Substitution of each numerical
    enumerator for the input function gives closed numerical programs computing lower bounds $u_s,v_s$ for these
    two measures, converging to them. The complementary-lower-bound lemma with the family index fixed then gives
    a fast Cauchy name of $\mu(U_L)$.
-/
theorem ballUnion_complement_measure [IsProbabilityMeasure μ]
    (h : ∀ i, μ (sphere (c i) (r i)) = 0) :
    μ.real (⋃ i, ball (c i) (r i)) + μ.real (⋃ i, closedBall (c i) (r i))ᶜ = 1 := by
  rw [measureReal_compl (isClosed_iUnion_of_finite (fun _ => isClosed_closedBall)).measurableSet]
  have he : μ.real (⋃ i, ball (c i) (r i)) = μ.real (⋃ i, closedBall (c i) (r i)) :=
    congrArg ENNReal.toReal (ballUnion_measure_eq_closedBallUnion c r μ h)
  rw [he]
  simp

section Computation
variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (q : ℕ → Y) (ν : Measure Y)

/-- Operational data for a valuation: one closed term works on every open name.
All numerical streams are valid with the zero-padding convention for balls. -/
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
structure LambdaProbabilityValuation where
  program : AlphaTerm
  codes : (ℕ → ℕ) → ℕ → ℕ
  computes : UniformNumericalComputes program codes
  lower : ∀ p n, rationalPoint (codes p n) ≤ ν.real (⋃ k, enumeratedRationalBall q (p k))
  limit : ∀ p, Tendsto (fun n => rationalPoint (codes p n)) atTop
    (𝓝 (ν.real (⋃ k, enumeratedRationalBall q (p k))))

namespace LambdaProbabilityValuation
variable {q ν} (V : LambdaProbabilityValuation q ν)

omit [BorelSpace Y] in
theorem on_computable {E : AlphaTerm} {p : ℕ → ℕ} (hp : NumericalComputes E p) :
    NumericalComputes (app V.program E) (V.codes p) :=
  ⟨closed_app V.computes.1 hp.1,fun n => (V.computes.2 p n).apply_numerical V.computes.1 hp⟩

omit [BorelSpace Y] in
/-- The actual program needs only enumerators of complementary masses. -/
theorem from_complementary_opens {U W : Set Y} {E D : AlphaTerm} {u w : ℕ → ℕ}
    (hu : NumericalComputes E u) (hw : NumericalComputes D w)
    (hU : U = ⋃ n, enumeratedRationalBall q (u n))
    (hW : W = ⋃ n, enumeratedRationalBall q (w n)) (hm : ν.real U + ν.real W = 1) :
    ∃ p : realRepresentation.domain, realRepresentation.toFun p = ν.real U ∧
      NumericalComputes (measureAtParameter
        (numericalCompose (app V.program E) (numericalProjectionTerm false))
        (numericalCompose (app V.program D) (numericalProjectionTerm false)) 0) p.val := by
  have ha := (V.on_computable hu).comp (projection_computes false)
  have hb := (V.on_computable hw).comp (projection_computes false)
  apply measureAtParameter_computes_name ha hb
  have he : ν.real W = 1 - ν.real U := by linarith
  refine ⟨?_,?_,?_,?_⟩
  · intro s
    simpa only [Nat.unpair_pair,Bool.false_eq_true,ite_false,← hU] using V.lower u s
  · intro s
    simpa only [Nat.unpair_pair,Bool.false_eq_true,ite_false,← hW,he] using V.lower w s
  · simpa only [Nat.unpair_pair,Bool.false_eq_true,ite_false,← hU] using V.limit u
  · simpa only [Nat.unpair_pair,Bool.false_eq_true,ite_false,← hW,he] using V.limit w

end LambdaProbabilityValuation

omit [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
private theorem list_union_eq (L : List ℕ) (S : ℕ → Set Y) :
    {x | ∃ b ∈ L, x ∈ S b} = ⋃ i : Fin L.length, S (L.get i) := by
  ext x
  simp only [mem_ofPred_eq,mem_iUnion,List.mem_iff_get]
  constructor
  · rintro ⟨b,⟨i,rfl⟩,h⟩
    exact ⟨i,h⟩
  · rintro ⟨i,h⟩
    exact ⟨L.get i,⟨i,rfl⟩,h⟩

theorem finiteBallUnion_complement_measure [IsProbabilityMeasure ν] (L : List ℕ)
    (h : ∀ b ∈ L, ν (sphere (q b.unpair.1) ((RationalCode.ofNat b.unpair.2).value : ℝ)) = 0) :
    ν.real (finiteBallUnion q L) + ν.real (finiteClosedBallExterior q L) = 1 := by
  have hU := list_union_eq L (codedBall q)
  have hF : finiteClosedBallExterior q L =
      (⋃ i : Fin L.length, codedClosedBall q (L.get i))ᶜ := by
    rw [← list_union_eq L (codedClosedBall q)]
    ext x
    simp [finiteClosedBallExterior]
  change ν.real {x | ∃ b ∈ L, x ∈ codedBall q b} + _ = 1
  rw [hU,hF]
  exact ballUnion_complement_measure
    (fun i : Fin L.length => q (L.get i).unpair.1)
    (fun i => ((RationalCode.ofNat (L.get i).unpair.2).value : ℝ)) ν
    (fun i => h (L.get i) (List.get_mem L i))

variable [CompleteSpace Y]

/-- Null spheres make the measures of the two enumerated open sets complementary.
The concluding numerical program computes a genuine fast Cauchy name. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: theorem
  title: Computing finite ball-union measures
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Null spheres are a sufficient condition. A set may have computable measure even when a sphere has positive
    measure, for instance when that measure is supplied separately. For an arbitrary effectively open set, only
    the lower computation is guaranteed, as the preceding Cantor-space example shows.
-/
theorem finiteBallUnion_measure_computable [IsProbabilityMeasure ν]
    (A : LambdaMetricApproximation q) (hq : DenseRange q)
    (V : LambdaProbabilityValuation q ν) (L : List ℕ)
    (h : ∀ b ∈ L, ν (sphere (q b.unpair.1) ((RationalCode.ofNat b.unpair.2).value : ℝ)) = 0) :
    ∃ P : AlphaTerm, ∃ p : realRepresentation.domain,
      NumericalComputes P p.val ∧ realRepresentation.toFun p = ν.real (finiteBallUnion q L) := by
  obtain ⟨E,u,hu,hU⟩ := A.finiteBall_has_enumeration hq false L
  obtain ⟨D,w,hw,hW⟩ := A.finiteBall_has_enumeration hq true L
  simp only [Bool.false_eq_true,ite_false,ite_true] at hU hW
  obtain ⟨p,hp,hP⟩ := V.from_complementary_opens hu hw hU hW
    (finiteBallUnion_complement_measure q ν L h)
  exact ⟨_,p,hP,hp⟩

end Computation
end PolishSpaceBook
