module

public import PolishSpaceBook.ComputableRepresentationEquivalence

@[expose] public section

/-!
# Effective translations between dense sequences for a fixed metric

Uniform approximations of the old basic points by the new ones translate
names with a two-coordinate shift. Conversely, applying a name translator
to constant names gives the required ordinary computable approximation data.
-/
namespace PolishSpaceBook
open Set Filter Topology NamedLambda NamedLambda.AlphaTerm
universe u
variable {X : Type u} [MetricSpace X] {q r : ℕ → X}

/-- One numerical algorithm approximates every old basic point to every precision. -/
structure DensePointApproximation (q r : ℕ → X) where
  index : ℕ × ℕ → ℕ
  program : AlphaTerm
  computes : NumericalComputes program (fun z => index z.unpair)
  error : ∀ i k, dist (q i) (r (index (i,k))) ≤ (1 / 2 : ℝ)^k

/-- Non-strict half-error bounds suffice for the fast pairwise Cauchy condition. -/
theorem isCauchyName_of_halfError_le {p : ℕ → ℕ} {x : X}
    (hp : ∀ n, dist (q (p n)) x ≤ (1 / 2 : ℝ)^(n+1)) : IsCauchyName q p := by
  intro n m hnm
  have hn := hp n
  have hm := hp m
  have ht := dist_triangle (q (p n)) x (q (p m))
  rw [dist_comm x] at ht
  have hpow : (1 / 2 : ℝ)^(m+1) ≤ (1 / 2 : ℝ)^(n+1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have he : (1 / 2 : ℝ)^(n+1) + (1 / 2 : ℝ)^(n+1) = (1 / 2 : ℝ)^n := by ring
  linarith

/-- Each basic point has its uniform constant name. -/
def constantCauchyName (q : ℕ → X) (i : ℕ) : cauchyNameDomain q :=
  ⟨fun _ => i,by intro n m h; simp only [dist_self]; positivity⟩

variable [CompleteSpace X]

theorem cauchyRepresentation_constantName (q : ℕ → X) (i : ℕ) :
    cauchyRepresentation q (constantCauchyName q i) = q i :=
  tendsto_nhds_unique (tendsto_cauchyRepresentation q (constantCauchyName q i)) tendsto_const_nhds

/-- The half-error estimates also identify the represented point. -/
theorem cauchyRepresentation_eq_of_halfError_le (p : ℕ → ℕ) (x : X)
    (hp : ∀ n, dist (q (p n)) x ≤ (1 / 2 : ℝ)^(n+1)) :
    cauchyRepresentation q ⟨p,isCauchyName_of_halfError_le hp⟩ = x := by
  apply tendsto_nhds_unique (tendsto_cauchyRepresentation q ⟨p,isCauchyName_of_halfError_le hp⟩)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N,fun n hn => ?_⟩
  exact (hp n).trans_lt ((pow_le_pow_of_le_one (by norm_num) (by norm_num)
    (show N ≤ n+1 by omega)).trans_lt hN)

namespace DensePointApproximation
variable (T : DensePointApproximation q r)

omit [CompleteSpace X] in
/-- The shift leaves room for both the input-name error and the approximation error. -/
def translateName (p : ℕ → ℕ) (n : ℕ) : ℕ := T.index (p (n+2),n+2)

omit [CompleteSpace X] in
theorem uniform_translateName : ∃ P, UniformNumericalComputes P T.translateName := by
  let N := addNumerical numericalIdentity (numericalConstant 2)
  have hn : NumericalComputes N (fun n => n+2) :=
    numericalIdentity_computes.add (numericalConstant_computes 2)
  refine ⟨mapOutputProgram T.program
    (pairOutputProgram (queryOutputProgram (liftNumericalProgram N)) (liftNumericalProgram N)), ?_⟩
  change UniformNumericalComputes _ (fun p n => T.index (p (n+2),n+2))
  simpa only [Nat.unpair_pair] using (hn.uniform.query.pair hn.uniform).map T.computes

theorem translateName_error (p : cauchyNameDomain q) (n : ℕ) :
    dist (r (T.translateName p.val n)) (cauchyRepresentation q p) ≤ (1 / 2 : ℝ)^(n+1) := by
  have hT := T.error (p.val (n+2)) (n+2)
  have hp := cauchyRepresentation_dist_le q p (n+2)
  have ht := dist_triangle (r (T.translateName p.val n)) (q (p.val (n+2))) (cauchyRepresentation q p)
  have he : (1 / 2 : ℝ)^(n+2) + (1 / 2 : ℝ)^(n+2) = (1 / 2 : ℝ)^(n+1) := by ring
  change dist (q (p.val (n+2))) (r (T.translateName p.val n)) ≤ _ at hT
  rw [dist_comm] at hT
  linarith

include T in
/-- The translated name is valid and keeps the represented point. -/

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Suppose first that $T$ is given, computed by a closed term $B$ on the paired input $\NatPair{i}{k}$.
    Let $N$ be a closed term computing $n\mapsto n+2$. The closed term
    $$Q:=\lambdaab{o}{\lambdaab{n}{B\bigl(\LambdaNumericPair\,(o(Nn))\,(Nn)\bigr)}}$$
    computes
    $$F(p)(n)=T(p(n+2),n+2).$$
    Its reductions first compute the shifted coordinate, query that coordinate, pair the answer with the coordinate,
    and apply $B$. If $p$ names $x$, the input Cauchy estimate and the approximation bound give
    $$
    \begin{aligned}
    d(r_{F(p)(n)},x)
    &\le d(r_{F(p)(n)},q_{p(n+2)})\\
    &\quad+d(q_{p(n+2)},x)\\
    &\le 2\cdot2^{-(n+2)}=2^{-(n+1)}.
    \end{aligned}
    $$
    For $m\ge n$, the triangle inequality therefore yields
    $$d(r_{F(p)(n)},r_{F(p)(m)})\le 2^{-(n+1)}+2^{-(m+1)}\le 2^{-n}.$$
    Thus the output satisfies the fast Cauchy condition, and the first estimate proves convergence to $x$. It is a valid
    name of the same point.
-/
theorem computablyReduces (hq : DenseRange q) (hr : DenseRange r) :
    ComputablyReduces (cauchyRepresentationObject q hq) (cauchyRepresentationObject r hr) := by
  let F (p : cauchyNameDomain q) : cauchyNameDomain r :=
    ⟨T.translateName p.val,isCauchyName_of_halfError_le (T.translateName_error p)⟩
  obtain ⟨c,hc⟩ := T.uniform_translateName
  exact ⟨F,⟨c,typeTwoComputes_iff_runs.mpr ⟨hc.1,fun p n => hc.2 p.val n⟩⟩,
    fun p => cauchyRepresentation_eq_of_halfError_le _ _ (T.translateName_error p)⟩

end DensePointApproximation

/-- Constant lambda terms extract one numerical approximation algorithm
from a uniform name translator. -/

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Conversely, let a closed term $P$ compute a translator $F$ from $\rho_q$ to $\rho_r$.
    The constant sequence $p_i(n)=i$ is a valid name of $q_i$, computed by
    $K_i:=\lambdaab{u}{\ChurchNumeral{i}}$. Define
    $$T(i,k)=F(p_i)(k).$$
    By the preceding substitution argument, $PK_i\ChurchNumeral{k}$ reduces by ordinary beta steps to
    $\ChurchNumeral{T(i,k)}$. This is uniform in both arguments: the fixed closed term
    $$H:=\lambdaab{a}{\lambdaab{b}{P\,(\lambdaab{u}{a})\,b}}$$
    computes $T$ on two numerals. Numerical projections turn it into a program on $\NatPair{i}{k}$.
    Each computation terminates because the constant name is valid. Its output is the $k$th coordinate of a Cauchy
    name of $q_i$, so
    $$d(q_i,r_{T(i,k)})\le 2^{-k}.$$
    Applying the criterion in both directions proves the assertion about computable equivalence.
-/
theorem densePointApproximation_of_computablyReduces (hq : DenseRange q) (hr : DenseRange r)
    (h : ComputablyReduces (cauchyRepresentationObject q hq) (cauchyRepresentationObject r hr)) :
    Nonempty (DensePointApproximation q r) := by
  obtain ⟨F,⟨c,hc⟩,hF⟩ := h
  let t (z : ℕ × ℕ) : ℕ := (F (constantCauchyName q z.1)).val z.2
  have ht : NumericalComputes (uncurryNumerical (constantInputProgram c))
      (fun z => t z.unpair) :=
    constantInputProgram_computes hc.1 (fun i k => t (i,k))
      (fun i k => (hc.2 (constantCauchyName q i) k _).mpr rfl)
  refine ⟨⟨t,uncurryNumerical (constantInputProgram c),ht,fun i k => ?_⟩⟩
  have hx : cauchyRepresentation r (F (constantCauchyName q i)) = q i := by
    simpa only [cauchyRepresentationObject, id_eq, cauchyRepresentation_constantName] using
      hF (constantCauchyName q i)
  simpa only [t, hx, dist_comm] using cauchyRepresentation_dist_le r (F (constantCauchyName q i)) k

/-- Exact criterion for effective change of dense sequence, with the metric fixed. -/

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Effective dense-sequence criterion
-/
theorem computablyReduces_cauchy_iff (hq : DenseRange q) (hr : DenseRange r) :
    ComputablyReduces (cauchyRepresentationObject q hq) (cauchyRepresentationObject r hr) ↔
      Nonempty (DensePointApproximation q r) :=
  ⟨densePointApproximation_of_computablyReduces hq hr,fun ⟨T⟩ => T.computablyReduces hq hr⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For a fixed complete metric, changing the dense sequence preserves computability exactly when the basic points of each
    sequence can be approximated uniformly by those of the other. The construction and the converse are proved in
    §{sec:tte-effective-dense-changes}. Compatibility of metrics alone does not supply an effective change of presentation.
-/
theorem computablyEquivalent_cauchy_iff (hq : DenseRange q) (hr : DenseRange r) :
    ComputablyEquivalent (cauchyRepresentationObject q hq) (cauchyRepresentationObject r hr) ↔
      Nonempty (DensePointApproximation q r) ∧ Nonempty (DensePointApproximation r q) :=
  and_congr (computablyReduces_cauchy_iff hq hr) (computablyReduces_cauchy_iff hr hq)

end PolishSpaceBook
