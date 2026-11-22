module

public import PolishSpaceBook.StrongChoquetGame
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# The shrinking-ball strong Choquet strategy

In a complete metric space, respond to a point in an open set with an open ball
whose closure remains in that set and whose diameter is at most `2⁻ⁿ`. The chosen
points form a Cauchy sequence along every legal play. Its limit lies in every
response closure, and hence in every move of Player I.
-/
noncomputable section
namespace PolishSpaceBook.StrongChoquetGame
open Set Metric Filter Topology TopologicalSpace
variable {X : Type*}

section Metric
variable [MetricSpace X]

/-- Choose an ambient ball contained in the current open move. -/
def containingBallRadius (m : Move X) : ℝ :=
  (Metric.isOpen_iff.mp m.isOpen m.point m.mem).choose

lemma containingBallRadius_spec (m : Move X) :
    0 < containingBallRadius m ∧ ball m.point (containingBallRadius m) ⊆ m.openSet :=
  (Metric.isOpen_iff.mp m.isOpen m.point m.mem).choose_spec

/-- Halve the ambient radius and impose the round's geometric bound. -/
def smallBallRadius (n : ℕ) (m : Move X) : ℝ :=
  min (containingBallRadius m / 2) ((1 / 2 : ℝ) ^ n / 2)

lemma smallBallRadius_spec (n : ℕ) (m : Move X) :
    0 < smallBallRadius n m ∧ closure (ball m.point (smallBallRadius n m)) ⊆ m.openSet ∧
      2 * smallBallRadius n m ≤ (1 / 2 : ℝ) ^ n := by
  obtain ⟨hε, hball⟩ := containingBallRadius_spec m
  have hr : 0 < smallBallRadius n m :=
    lt_min (half_pos hε) (half_pos (pow_pos (by norm_num) n))
  have hrε : smallBallRadius n m < containingBallRadius m :=
    (min_le_left _ _).trans_lt (half_lt_self hε)
  refine ⟨hr, ?_, ?_⟩
  · exact (closure_ball_subset_closedBall.trans (closedBall_subset_ball hrε)).trans hball
  · have h := min_le_right (containingBallRadius m / 2) ((1 / 2 : ℝ) ^ n / 2)
    dsimp [smallBallRadius]
    linarith

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Fix a complete compatible metric $d$. When Player I plays $x_n\in U_n$, choose $\varepsilon_n>0$ with
    $\Ball{x_n}{\varepsilon_n}\IncludedIn U_n$, and set
    $$
    r_n:=\min\{\varepsilon_n/2,2^{-n}/2\},\qquad V_n:=\Ball{x_n}{r_n}.
    $$
    Since $0<r_n<\varepsilon_n$, these open responses satisfy
    $$
    x_n\in V_n,\qquad \Closure{V_n}\IncludedIn U_n,\qquad
    \Diameter{\Closure{V_n}}\le 2r_n\le 2^{-n}.
    $$
    The rule uses only the round number and the current point and open set, so it defines a strategy on every
    finite history. All closures and diameters here are taken in $X$ with the chosen metric.
-/
/-- The response is the small open ball, not its closure. -/
def metricResponse (n : ℕ) (m : Move X) : Response X m where
  openSet := ball m.point (smallBallRadius n m)
  isOpen := isOpen_ball
  mem := mem_ball_self (smallBallRadius_spec n m).1
  subset := subset_closure.trans (smallBallRadius_spec n m).2.1

lemma metricResponse_closure_subset (n : ℕ) (m : Move X) :
    closure (metricResponse n m).openSet ⊆ m.openSet := (smallBallRadius_spec n m).2.1

lemma metricResponse_bounded_closure (n : ℕ) (m : Move X) :
    Bornology.IsBounded (closure (metricResponse n m).openSet) :=
  isBounded_closedBall.subset closure_ball_subset_closedBall

lemma metricResponse_diam_closure (n : ℕ) (m : Move X) :
    diam (closure (metricResponse n m).openSet) ≤ (1 / 2 : ℝ) ^ n :=
  (diam_le_of_subset_closedBall (smallBallRadius_spec n m).1.le
    closure_ball_subset_closedBall).trans (smallBallRadius_spec n m).2.2

/-- Only the current point/open set and the number of preceding rounds are needed. -/
def metricStrategy : Strategy X := fun history m => metricResponse history.length m

lemma metricStrategy_responseAt (p : ℕ → Move X) (n : ℕ) :
    responseAt X metricStrategy p n = metricResponse n (p n) := by
  simp only [responseAt, metricStrategy, List.length_map, List.length_range]

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Consider a legal play following this strategy, and put $K_n:=\Closure{V_n}$. Legality gives
    $$
    K_{n+1}\IncludedIn U_{n+1}\IncludedIn V_n\IncludedIn K_n.
    $$
    Each $K_n$ is closed and bounded, and $x_n\in K_n$. For $m,k\ge n$, both $x_m$ and $x_k$ belong to $K_n$, so
    $$
    d(x_m,x_k)\le\Diameter{K_n}\le 2^{-n}.
    $$
    Thus the sequence of chosen points is Cauchy. Completeness gives a limit $x$. For every $n$, the closed set
    $K_n$ contains the tail of this sequence, so $x\in K_n\IncludedIn U_n$. Hence every open set chosen by I
    contains $x$, and the strategy is winning.
    \end{proof}
-/
/-- Along a legal play, response closures are nested, and the played points converge inside all of them. -/
theorem metricStrategy_winning [CompleteSpace X] : Winning X metricStrategy := by
  intro p hp
  let K : ℕ → Set X := fun n => closure (metricResponse n (p n)).openSet
  have hKstep (n : ℕ) : K (n + 1) ⊆ K n := by
    have hlegal := hp n
    rw [metricStrategy_responseAt] at hlegal
    exact (metricResponse_closure_subset (n + 1) (p (n + 1))).trans
      (hlegal.trans subset_closure)
  have hKmono : Antitone K := antitone_nat_of_succ_le hKstep
  have hpoint (n : ℕ) : (p n).point ∈ K n := subset_closure (metricResponse n (p n)).mem
  have htail {m n : ℕ} (h : n ≤ m) : (p m).point ∈ K n := hKmono h (hpoint m)
  have hbound (n : ℕ) : diam (K n) ≤ (1 / 2 : ℝ) ^ n := metricResponse_diam_closure n (p n)
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hc : CauchySeq (fun n => (p n).point) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hpow).2 ε hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    exact ((dist_le_diam_of_mem (metricResponse_bounded_closure N (p N))
      (htail hm) (htail hn)).trans (hbound N)).trans_lt (hN N le_rfl)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  have hxK (n : ℕ) : x ∈ K n :=
    isClosed_closure.mem_of_tendsto hx ((eventually_ge_atTop n).mono fun m hm => htail hm)
  exact ⟨x, fun n => metricResponse_closure_subset n (p n) (hxK n)⟩

theorem completeMetric_isStrongChoquet [CompleteSpace X] : IsStrongChoquet X :=
  ⟨metricStrategy, metricStrategy_winning⟩

end Metric

/-- The construction depends only on the existence of a complete compatible metric. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: proposition
  title: Metric strategy
-/
theorem completelyMetrizable_isStrongChoquet [TopologicalSpace X] [IsCompletelyMetrizableSpace X] :
    IsStrongChoquet X := by
  let := upgradeIsCompletelyMetrizable X
  exact completeMetric_isStrongChoquet

theorem polish_isStrongChoquet [TopologicalSpace X] [PolishSpace X] : IsStrongChoquet X :=
  completelyMetrizable_isStrongChoquet

end PolishSpaceBook.StrongChoquetGame
