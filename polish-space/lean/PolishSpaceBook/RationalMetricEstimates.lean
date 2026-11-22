module

public import PolishSpaceBook.ComputableRationalCodes
public import PolishSpaceBook.CauchyNamesPolishRepresentations

@[expose] public section

/-! # Rational approximation data and metric-ball estimates

Only the rational error bound is assumed here. Computation of this data is
supplied separately by a closed lambda program in LambdaMetricBalls.
-/
namespace PolishSpaceBook
open Set
universe u
variable {X : Type u} [MetricSpace X]

structure RationalMetricApproximation (q : ℕ → X) where
  approx : ℕ × (ℕ × ℕ) → RationalCode
  error : ∀ i j n,
    |(RationalCode.value (approx (i, (j, n))) : ℝ) - dist (q i) (q j)| ≤ (1 / 2 : ℝ) ^ n

abbrev MetricBallCode := ℕ × RationalCode

namespace RationalMetricApproximation
variable {q : ℕ → X} (A : RationalMetricApproximation q)

/-- The rational upper bound includes both sources of approximation error. -/
def ballUpper (p : ℕ → ℕ) (i n : ℕ) : RationalCode :=
  ((A.approx (p n, (i, n))).add (RationalCode.dyadic n)).add (RationalCode.dyadic n)

def ballTest (p : ℕ → ℕ) (z : MetricBallCode × ℕ) : Bool :=
  decide ((A.ballUpper p z.1.1 z.2).lt z.1.2)

theorem ballTest_iff (p : ℕ → ℕ) (i : ℕ) (r : RationalCode) (n : ℕ) :
    A.ballTest p ((i, r), n) = true ↔
      (RationalCode.value (A.approx (p n, (i, n))) : ℝ) +
        (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n < r.value := by
  simp only [ballTest, decide_eq_true_eq, RationalCode.lt_iff]
  rw [← Rat.cast_lt (K := ℝ)]
  simp [ballUpper]

variable [CompleteSpace X]

/-- Success of any stage certifies membership. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    \clubpenalties 2 10000 0
    Put $\varepsilon_n=2^{-n}$ and $A_n=A(p(n),i,n)$. At stage $n$, query $p(n)$, compute $A_n$, and test the rational inequality
    $$A_n+2\varepsilon_n<r.$$
    Each stage terminates. If it succeeds, the Cauchy-name estimate and the error bound on $A$ give
    $$
    d(x,q_i)\le d(x,q_{p(n)})+d(q_{p(n)},q_i)
    \le \varepsilon_n+(A_n+\varepsilon_n)<r.
    $$
    Conversely, if $d(x,q_i)<r$, then
    $$
    A_n+2\varepsilon_n
    \le d(q_{p(n)},q_i)+3\varepsilon_n
    \le d(x,q_i)+4\varepsilon_n.
    $$
    Choose $n$ so large that the last expression is less than $r$. Thus sequential search through the terminating stage tests halts exactly on names of points in the ball.
-/
theorem mem_ball_of_test (p : cauchyNameDomain q) (i : ℕ) (r : RationalCode) (n : ℕ)
    (h : A.ballTest p.val ((i, r), n) = true) :
    cauchyRepresentation q p ∈ Metric.ball (q i) (r.value : ℝ) := by
  have ht := (A.ballTest_iff p.val i r n).mp h
  have ha := (abs_le.mp (A.error (p.val n) i n)).1
  have hx := cauchyRepresentation_dist_le q p n
  have htri := dist_triangle_left (cauchyRepresentation q p) (q i) (q (p.val n))
  rw [Metric.mem_ball]
  linarith

/-- Every point inside the ball eventually passes a rational stage test. -/
theorem exists_ballTest_of_mem (p : cauchyNameDomain q) (i : ℕ) (r : RationalCode)
    (h : cauchyRepresentation q p ∈ Metric.ball (q i) (r.value : ℝ)) :
    ∃ n, A.ballTest p.val ((i, r), n) = true := by
  have hgap : 0 < ((r.value : ℝ) - dist (cauchyRepresentation q p) (q i)) / 4 := by
    rw [Metric.mem_ball] at h
    linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hgap (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, (A.ballTest_iff p.val i r n).mpr ?_⟩
  have ha := (abs_le.mp (A.error (p.val n) i n)).2
  have hx := cauchyRepresentation_dist_le q p n
  have htri := dist_triangle (q (p.val n)) (cauchyRepresentation q p) (q i)
  linarith

end RationalMetricApproximation
end PolishSpaceBook
