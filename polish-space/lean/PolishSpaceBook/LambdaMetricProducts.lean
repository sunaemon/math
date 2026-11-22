module

public import PolishSpaceBook.LambdaMetricBalls
public import PolishSpaceBook.LambdaRationalOrder

@[expose] public section

/-! # Computable maximum metrics and the unchanged product Cauchy names

The dense sequence uses the same numerical pairing as the product representation.
Distance approximations retain their precision under the rational maximum.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm Set Filter Topology
universe u v

/-- Taking the maximum does not amplify a common absolute error bound. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Let $A_X(i,i',k)$ and $A_Y(j,j',k)$ be the given rational distance approximations with error at most $2^{-k}$.
    Define
    $$A(\NatPair{i}{j},\NatPair{i'}{j'},k):=\max\{A_X(i,i',k),A_Y(j,j',k)\}.$$
    The elementary estimate
    $$|\max\{a,b\}-\max\{x,y\}|\le\varepsilon
    \quad\text{if}\quad |a-x|\le\varepsilon,\ |b-y|\le\varepsilon$$
    shows that $A$ has the same error bound $2^{-k}$. Indeed, both $a,b$ are at most $\max\{x,y\}+\varepsilon$,
    and both $x,y$ are at most $\max\{a,b\}+\varepsilon$.
-/
theorem max_approximation_error {a b x y ε : ℝ}
    (ha : |a-x| ≤ ε) (hb : |b-y| ≤ ε) :
    |max a b-max x y| ≤ ε := by
  rcases abs_le.mp ha with ⟨ha₁,ha₂⟩
  rcases abs_le.mp hb with ⟨hb₁,hb₂⟩
  apply abs_le.mpr
  constructor
  · have hx : x ≤ max a b+ε := by linarith [le_max_left a b]
    have hy : y ≤ max a b+ε := by linarith [le_max_right a b]
    linarith [max_le hx hy]
  · have ha' : a ≤ max x y+ε := by linarith [le_max_left x y]
    have hb' : b ≤ max x y+ε := by linarith [le_max_right x y]
    linarith [max_le ha' hb']

variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]

/-- The enumeration of product centers uses the established numerical pairing. -/
def metricProductSequence (q : ℕ → X) (r : ℕ → Y) (i : ℕ) : X × Y :=
  (q i.unpair.1,r i.unpair.2)

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For the maximum metric, convergence and the Cauchy condition are both coordinatewise. Completeness of the two
    factors therefore gives completeness of the product, and the metric induces the product topology. The sequence
    enumerates every pair of component centers: given $(x,y)$ and
    $\varepsilon>0$, choose $q_i$ within $\varepsilon$ of $x$ and $r_j$ within $\varepsilon$ of $y$. Then
    $$d_{X\times Y}(s_{\NatPair{i}{j}},(x,y))<\varepsilon.$$
-/
theorem metricProductSequence_dense {q : ℕ → X} {r : ℕ → Y}
    (hq : DenseRange q) (hr : DenseRange r) : DenseRange (metricProductSequence q r) := by
  rw [Metric.denseRange_iff]
  intro z ε hε
  obtain ⟨i,hi⟩ := hq.exists_dist_lt z.1 hε
  obtain ⟨j,hj⟩ := hr.exists_dist_lt z.2 hε
  refine ⟨Nat.pair i j,?_⟩
  simpa only [metricProductSequence,Nat.unpair_pair,Prod.dist_eq] using max_lt hi hj

/-- Project both center indices but preserve the requested precision. -/
def metricProductInput (first : Bool) : AlphaTerm :=
  let coord := numericalProjectionTerm first
  pairNumerical (numericalCompose coord (numericalProjectionTerm true))
    (pairNumerical
      (numericalCompose coord (numericalCompose (numericalProjectionTerm true)
        (numericalProjectionTerm false)))
      (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)))

theorem metricProductInput_computes (first : Bool) : NumericalComputes (metricProductInput first)
    (fun z => Nat.pair (if first then z.unpair.1.unpair.1 else z.unpair.1.unpair.2)
      (Nat.pair (if first then z.unpair.2.unpair.1.unpair.1 else z.unpair.2.unpair.1.unpair.2)
        z.unpair.2.unpair.2)) := by
  exact ((projection_computes first).comp (projection_computes true)).pair
    (((projection_computes first).comp
      ((projection_computes true).comp (projection_computes false))).pair
      ((projection_computes false).comp (projection_computes false)))

def metricProductDistanceProgram (A B : AlphaTerm) : AlphaTerm :=
  numericalCompose rationalMaxProgram (pairNumerical
    (numericalCompose A (metricProductInput true))
    (numericalCompose B (metricProductInput false)))

/-- The maximum metric has a single closed program for all distance approximations. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    There is a single closed lambda program for $A$. Decode the two center indices by the numerical projections,
    retain the precision $k$, and run the supplied distance programs on $(i,i',k)$ and $(j,j',k)$. Compare the two
    returned rational codes using §{sec:lambda-rational-arithmetic}; return the second code if the first rational is
    strictly smaller, and otherwise return the first. Numerical pairing, projections, comparison, and the Church
    conditional compose to a closed term. Both distance computations and the comparison terminate on every input.
    Selecting one of the existing codes avoids any need to choose a canonical code for the maximum.
-/
def LambdaMetricApproximation.prod {q : ℕ → X} {r : ℕ → Y}
    (A : LambdaMetricApproximation q) (B : LambdaMetricApproximation r) :
    LambdaMetricApproximation (metricProductSequence q r) where
  approx z := RationalCode.ofNat (rationalMaxCode
    (A.approx (z.1.unpair.1,(z.2.1.unpair.1,z.2.2))).natCode
    (B.approx (z.1.unpair.2,(z.2.1.unpair.2,z.2.2))).natCode)
  error i j n := by
    rw [rationalMaxCode_value]
    simp only [RationalCode.ofNat_natCode,Prod.dist_eq,metricProductSequence]
    exact max_approximation_error (A.error _ _ _) (B.error _ _ _)
  program := metricProductDistanceProgram A.program B.program
  computes := by
    have h := rationalMaxProgram_computes.comp
      ((A.computes.comp (metricProductInput_computes true)).pair
        (B.computes.comp (metricProductInput_computes false)))
    refine ⟨h.1,fun z => ?_⟩
    simpa only [metricProductDistanceProgram,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false,
      RationalCode.natCode_ofNat] using h.2 z

theorem metricProduct_isCauchy_iff (q : ℕ → X) (r : ℕ → Y) (p : ℕ → ℕ) :
    IsCauchyName (metricProductSequence q r) p ↔
      IsCauchyName q (typeTwoLeftName p) ∧ IsCauchyName r (typeTwoRightName p) := by
  constructor
  · intro hp
    constructor
    · intro n m hnm
      exact (le_max_left _ _).trans (hp n m hnm)
    · intro n m hnm
      exact (le_max_right _ _).trans (hp n m hnm)
  · rintro ⟨hp,hq⟩ n m hnm
    exact max_le (hp n m hnm) (hq n m hnm)

variable [CompleteSpace X] [CompleteSpace Y]

theorem metricProduct_limit (q : ℕ → X) (r : ℕ → Y)
    (p : cauchyNameDomain (metricProductSequence q r)) :
    cauchyRepresentation (metricProductSequence q r) p =
      (cauchyRepresentation q ⟨typeTwoLeftName p.val,((metricProduct_isCauchy_iff q r p.val).mp p.2).1⟩,
       cauchyRepresentation r ⟨typeTwoRightName p.val,((metricProduct_isCauchy_iff q r p.val).mp p.2).2⟩) := by
  apply tendsto_nhds_unique (tendsto_cauchyRepresentation _ p)
  exact (tendsto_cauchyRepresentation q _).prodMk_nhds (tendsto_cauchyRepresentation r _)

private theorem representation_eq_of_names {Z : Type*} (δ ε : Representation Z)
    (hd : δ.domain = ε.domain)
    (hv : ∀ p : δ.domain, δ.toFun p = ε.toFun ⟨p.val,hd ▸ p.property⟩) : δ = ε := by
  cases δ with
  | mk D f hf =>
    cases ε with
    | mk E g hg =>
      dsimp only at hd
      subst E
      congr 1
      funext p
      exact hv p

/-- For the fixed pairing convention the two representations are equal, not just equivalent. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    For a name $p$, put $p_1:=\NameProjection{1}{p}$ and $p_2:=\NameProjection{2}{p}$. For $m\ge n$,
    $$\begin{aligned}
    d_{X\times Y}(s_{p(n)},s_{p(m)})\le2^{-n}
    \quad\Longleftrightarrow\quad& d_X(q_{p_1(n)},q_{p_1(m)})\le2^{-n}\\
    &\text{and}\quad d_Y(r_{p_2(n)},r_{p_2(m)})\le2^{-n}.
    \end{aligned}$$
    Thus the two representations have exactly the same name domain. Convergence in the maximum metric is coordinatewise,
    so on this common domain
    $$\rho_{X\times Y}(p)=(\rho_X(p_1),\rho_Y(p_2))=(\rho_X\times\rho_Y)(p).$$
-/
theorem metricProduct_representation_eq (q : ℕ → X) (r : ℕ → Y)
    (hq : DenseRange q) (hr : DenseRange r) :
    cauchyRepresentationObject (metricProductSequence q r) (metricProductSequence_dense hq hr) =
      typeTwoProductRepresentation (cauchyRepresentationObject q hq) (cauchyRepresentationObject r hr) := by
  have hd : cauchyNameDomain (metricProductSequence q r) =
      {p | typeTwoLeftName p ∈ cauchyNameDomain q ∧ typeTwoRightName p ∈ cauchyNameDomain r} := by
    ext p; exact metricProduct_isCauchy_iff q r p
  apply representation_eq_of_names _ _ hd
  exact metricProduct_limit q r

/-- Both translations keep the name and are realized by the closed identity lambda term. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    The closed term $\lambdaab{a}{a}$ therefore realizes both translations: on input name $p$ and coordinate $n$,
    one beta step exposes the query $o\ChurchNumeral{n}$, which returns $\ChurchNumeral{p(n)}$.
    If the two component names are needed separately, apply the numerical projections to each digit; in the other
    direction, pair their digits. The previously constructed pairing and projection programs implement these operations
    without changing the precision index or testing membership in a name domain.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Computable metric products
-/
theorem metricProduct_computable_equivalence (q : ℕ → X) (r : ℕ → Y)
    (hq : DenseRange q) (hr : DenseRange r) :
    HasComputableRealizer
      (cauchyRepresentationObject (metricProductSequence q r) (metricProductSequence_dense hq hr))
      (typeTwoProductRepresentation (cauchyRepresentationObject q hq) (cauchyRepresentationObject r hr)) id ∧
    HasComputableRealizer
      (typeTwoProductRepresentation (cauchyRepresentationObject q hq) (cauchyRepresentationObject r hr))
      (cauchyRepresentationObject (metricProductSequence q r) (metricProductSequence_dense hq hr)) id := by
  rw [metricProduct_representation_eq q r hq hr]
  exact ⟨hasComputableRealizer_id _,hasComputableRealizer_id _⟩

end PolishSpaceBook
