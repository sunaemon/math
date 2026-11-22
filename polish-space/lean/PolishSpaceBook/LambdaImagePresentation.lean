module

public import PolishSpaceBook.EffectiveDensePresentations

@[expose] public section

/-! # The metric presentation of a computable image

Apply the realizer to constant names, then approximate distances with a fixed
precision shift. All numerical computations are ordinary closed lambda terms.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]

/-- Constant input names give uniform ordinary approximations to image points. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $Q$ compute a realizer $F$ of $f$. The constant name $p_i(k)=i$ names $q_i$, so put
    $$t(i,k):=F(p_i)(k).$$
    The Cauchy-name estimate gives $d(r_i,s_{t(i,k)})\le 2^{-k}$. To obtain an ordinary numerical program,
    write $\pi_a:=\LambdaNumericProjection{a}$ and define
    $$\begin{aligned}
    H&:=\lambdaab{i}{\lambdaab{k}{Q\,(\lambdaab{u}{i})\,k}},\\
    T&:=\lambdaab{z}{H\,(\pi_1z)\,(\pi_2z)}.
    \end{aligned}$$
    Substituting the closed constant-name term for each input oracle turns its queries into ordinary beta
    reductions, as in §{sec:tte-effective-dense-changes}. Thus $T\ChurchNumeral{\NatPair{i}{k}}$ reduces to
    $\ChurchNumeral{t(i,k)}$ for all $i,k$. The same closed term works uniformly for the entire image sequence.
-/
theorem imagePointApproximation_of_realizer [CompleteSpace X] [CompleteSpace Y]
    {qX : ℕ → X} {qY : ℕ → Y} (hqX : DenseRange qX) (hqY : DenseRange qY)
    {f : X → Y} (hf : HasComputableRealizer (cauchyRepresentationObject qX hqX)
      (cauchyRepresentationObject qY hqY) f) :
    Nonempty (DensePointApproximation (fun i => f (qX i)) qY) := by
  obtain ⟨F,⟨Q,hQ⟩,hF⟩ := hf
  let t (z : ℕ × ℕ) : ℕ := (F (constantCauchyName qX z.1)).val z.2
  have ht : NumericalComputes (uncurryNumerical (constantInputProgram Q))
      (fun z => t z.unpair) :=
    constantInputProgram_computes hQ.1 (fun i k => t (i,k))
      (fun i k => (hQ.2 (constantCauchyName qX i) k _).mpr rfl)
  refine ⟨⟨t,uncurryNumerical (constantInputProgram Q),ht,fun i k => ?_⟩⟩
  have hx : cauchyRepresentation qY (F (constantCauchyName qX i)) = f (qX i) := by
    simpa only [cauchyRepresentationObject,cauchyRepresentation_constantName] using
      hF (constantCauchyName qX i)
  simpa only [t,hx,dist_comm] using
    cauchyRepresentation_dist_le qY (F (constantCauchyName qX i)) k

/-- Replace both centers by approximations two precision levels finer. -/
def transportedMetricProgram (M T : AlphaTerm) : AlphaTerm :=
  let i := numericalProjectionTerm true
  let j := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
  let n := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
  let k := numericalCompose successorTerm (numericalCompose successorTerm n)
  numericalCompose M (pairNumerical (numericalCompose T (pairNumerical i k))
    (pairNumerical (numericalCompose T (pairNumerical j k)) k))

namespace DensePointApproximation
variable {r q : ℕ → Y} (T : DensePointApproximation r q) (A : LambdaMetricApproximation q)

def transportedApprox (z : ℕ × (ℕ × ℕ)) : RationalCode :=
  A.approx (T.index (z.1,z.2.2+2),(T.index (z.2.1,z.2.2+2),z.2.2+2))

theorem transportedMetricProgram_computes :
    NumericalComputes (transportedMetricProgram A.program T.program)
      (fun z => (T.transportedApprox A (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode) := by
  have hi := projection_computes true
  have hj := (projection_computes true).comp (projection_computes false)
  have hn := (projection_computes false).comp (projection_computes false)
  have hk := successor_computes.comp (successor_computes.comp hn)
  have h := A.computes.comp ((T.computes.comp (hi.pair hk)).pair
    ((T.computes.comp (hj.pair hk)).pair hk))
  refine ⟨h.1,fun z => ?_⟩
  simpa [transportedMetricProgram,transportedApprox,Nat.succ_eq_add_one,Nat.add_assoc] using h.2 z

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Let $A(a,b,k)$ be the rational distance approximation for $Y$, computed in coded form by a closed term $M$.
    Define
    $$B(i,j,n):=A(t(i,n+2),t(j,n+2),n+2).$$
    Put $a=s_{t(i,n+2)}$ and $b=s_{t(j,n+2)}$. The triangle inequality gives
    $$\begin{aligned}
    |B(i,j,n)-d(r_i,r_j)|
    &\le |B(i,j,n)-d(a,b)|+|d(a,b)-d(r_i,r_j)|\\
    &\le 2^{-(n+2)}+d(a,r_i)+d(b,r_j)\\
    &\le 3\cdot2^{-(n+2)}\le 2^{-n}.
    \end{aligned}$$
    Only total numerical computations are needed. On the paired triple $z=\NatPair{i}{\NatPair{j}{n}}$, use
    $$\begin{aligned}
    L&:=\lambdaab{z}{\LambdaSucc(\LambdaSucc(\pi_2(\pi_2z)))},\\
    U&:=\lambdaab{z}{T(\LambdaNumericPair\,(\pi_1z)\,(Lz))},\\
    V&:=\lambdaab{z}{T(\LambdaNumericPair\,(\pi_1(\pi_2z))\,(Lz))},\\
    D&:=\lambdaab{z}{M(\LambdaNumericPair\,(Uz)\,
     (\LambdaNumericPair\,(Vz)\,(Lz)))}.
    \end{aligned}$$
    Beta reduction of the projections, successors, applications of $T$, and finally $M$ shows that $D$ returns
    the rational code of $B(i,j,n)$. These terms are closed after expanding the displayed definitions.
-/
theorem transportedApprox_error (i j n : ℕ) :
    |((T.transportedApprox A (i,(j,n))).value : ℝ) - dist (r i) (r j)| ≤ (1/2:ℝ)^n := by
  let a := q (T.index (i,n+2))
  let b := q (T.index (j,n+2))
  have hA := A.error (T.index (i,n+2)) (T.index (j,n+2)) (n+2)
  have hi := T.error i (n+2)
  have hj := T.error j (n+2)
  have hd := dist_dist_dist_le a b (r i) (r j)
  change |dist a b - dist (r i) (r j)| ≤ dist a (r i) + dist b (r j) at hd
  rw [dist_comm a (r i),dist_comm b (r j)] at hd
  have ht := abs_sub_le ((T.transportedApprox A (i,(j,n))).value : ℝ) (dist a b) (dist (r i) (r j))
  change |((T.transportedApprox A (i,(j,n))).value : ℝ) - dist a b| ≤ (1/2:ℝ)^(n+2) at hA
  have hp : 3 * (1/2:ℝ)^(n+2) ≤ (1/2:ℝ)^n := by
    rw [pow_add]; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]
  dsimp [a,b] at hd ht hA
  linarith

/-- The same construction works for any uniformly computable sequence. -/
def metricApproximation : LambdaMetricApproximation r where
  approx := T.transportedApprox A
  error := T.transportedApprox_error A
  program := transportedMetricProgram A.program T.program
  computes := T.transportedMetricProgram_computes A

end DensePointApproximation

/-- Image points belong to the image even when the map is not injective. -/
def imageDenseSequence (qX : ℕ → X) (f : X → Y) : ℕ → Set.range f :=
  fun i => ⟨f (qX i),qX i,rfl⟩

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    Finally, $f$ is continuous by the continuity theorem for computably realizable maps. Any nonempty relatively
    open subset of $f[K]$ has nonempty open preimage in $K$, which contains some $q_i$; hence it contains $r_i$.
    Thus the image sequence is dense. The continuous image of compact $K$ is compact, so its restricted metric
    is complete. That metric has the same distances as $Y$, and therefore the program just constructed gives
    the required presentation.
    \end{proof}
-/
theorem denseRange_imageDenseSequence {qX : ℕ → X} (hqX : DenseRange qX)
    {f : X → Y} (hf : Continuous f) : DenseRange (imageDenseSequence qX f) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨y,hy⟩ := hne
  obtain ⟨x,hx⟩ := Set.rangeFactorization_surjective (f := f) y
  have hpre : (Set.rangeFactorization f ⁻¹' U).Nonempty := ⟨x,by simpa [hx] using hy⟩
  obtain ⟨i,hi⟩ := hqX.exists_mem_open (hU.preimage hf.rangeFactorization) hpre
  exact ⟨imageDenseSequence qX f i,hi,⟨i,rfl⟩⟩

/-- The restricted metric uses exactly the same rational values and program. -/
def imageMetricApproximation {qX : ℕ → X} {qY : ℕ → Y} {f : X → Y}
    (T : DensePointApproximation (fun i => f (qX i)) qY) (A : LambdaMetricApproximation qY) :
    LambdaMetricApproximation (imageDenseSequence qX f) where
  approx := (T.metricApproximation A).approx
  error := (T.metricApproximation A).error
  program := (T.metricApproximation A).program
  computes := (T.metricApproximation A).computes

/-- Compactness supplies completeness; constant-name substitution supplies the program. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Metric presentation of a computable image
-/
theorem computable_image_presentation [CompleteSpace X] [CompleteSpace Y] [CompactSpace X]
    {qX : ℕ → X} {qY : ℕ → Y} (hqX : DenseRange qX) (hqY : DenseRange qY)
    (A : LambdaMetricApproximation qY) {f : X → Y}
    (hf : HasComputableRealizer (cauchyRepresentationObject qX hqX)
      (cauchyRepresentationObject qY hqY) f) :
    CompactSpace (Set.range f) ∧ CompleteSpace (Set.range f) ∧
      DenseRange (imageDenseSequence qX f) ∧
      Nonempty (LambdaMetricApproximation (imageDenseSequence qX f)) := by
  have hc := hf.continuous (cauchyRepresentationObject_isAdmissible qX hqX)
    (continuous_cauchyRepresentation qY)
  let : CompactSpace (Set.range f) := isCompact_iff_compactSpace.mp (isCompact_range hc)
  obtain ⟨T⟩ := imagePointApproximation_of_realizer hqX hqY hf
  exact ⟨inferInstance,inferInstance,denseRange_imageDenseSequence hqX hc,⟨imageMetricApproximation T A⟩⟩

end PolishSpaceBook
