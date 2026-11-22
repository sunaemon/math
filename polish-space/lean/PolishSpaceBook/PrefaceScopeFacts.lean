module

public import PolishSpaceBook.BaireClassFunctions
public import PolishSpaceBook.LambdaZeroInputHalting

@[expose] public section

/-! # The exact distance approximants displayed in the preface -/
namespace PolishSpaceBook
open Filter Metric Set Topology

/-- Keep the coefficient `n`, including the initial constant-one approximant. -/
/-@ booklink:
  source: polish-space-book/preface.md
  target: prose
  excerpt: |
    For a subset $A\IncludedIn\R$, consider its \termforward{indicator function} $u_A$:
    $$
    u_A(x)=\begin{cases}
    1 & x\in A, \\
    0 & x\notin A.
    \end{cases}
    $$
    Can continuous real-valued functions approximate $u_A$ pointwise? For a nonempty
    closed set $F$, the answer is yes:
    $$
    u_{F,n}(x)=\max\{0,1-n d(x,F)\}\longrightarrow u_F(x).
    $$
    The distance to $F$ is continuous. At a point of $F$ each approximant equals $1$; outside $F$, the positive
    distance makes the approximants eventually $0$.
-/
theorem closed_indicator_distance_approximants {X : Type*} [MetricSpace X]
    {F : Set X} (hF : IsClosed F) (hne : F.Nonempty) :
    (∀ n : ℕ, Continuous (fun x : X => max 0 (1 - (n : ℝ) * infDist x F))) ∧
      ∀ x, Tendsto (fun n : ℕ => max 0 (1 - (n : ℝ) * infDist x F))
        atTop (𝓝 (F.indicator (fun _ => (1 : ℝ)) x)) := by
  classical
  refine ⟨fun n => continuous_const.max (continuous_const.sub
    (continuous_const.mul (continuous_infDist_pt F))), fun x => ?_⟩
  by_cases hx : x ∈ F
  · simp only [Set.indicator_of_mem hx, infDist_zero_of_mem hx, mul_zero, sub_zero,
      max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
    exact tendsto_const_nhds
  · rw [Set.indicator_of_notMem hx]
    have hr := (hF.notMem_iff_infDist_pos hne).mp hx
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / infDist x F)
    have hNr : 1 < (N : ℝ) * infDist x F := (div_lt_iff₀ hr).mp hN
    apply tendsto_const_nhds.congr'
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hmul : 1 ≤ (n : ℝ) * infDist x F := by nlinarith
    exact (max_eq_left (by linarith)).symm

/-@ booklink:
  source: polish-space-book/preface.md
  target: prose
  excerpt: |
    When is a condition defining a set simple? On the real line, consider the rationals and the irrationals:
    $$
    \QQ = \bigcup_{q\in\QQ}\{q\}, \qquad
    \SetDifference{\R}{\QQ} = \bigcap_{q\in\QQ}(\SetDifference{\R}{\{q\}}).
    $$
    Each singleton is closed, so the first expression displays the rationals as a countable union of closed sets,
    an $\Fsigma$ set. Its complement is a countable intersection of open sets, a $\Gdelta$ set. These descriptions
    illustrate how operations used to build or define a set measure its descriptive complexity. A set can have
    many descriptions; we ask how simple a description it admits.
-/
theorem preface_rational_complexity :
    IsFsigma (Set.range ((↑) : ℚ → ℝ)) ∧ IsGδ {x : ℝ | Irrational x} :=
  ⟨rationals_are_fsigma, irrationals_are_gdelta⟩

/-@ booklink:
  source: polish-space-book/preface.md
  target: prose
  excerpt: |
    The indicator of the rationals behaves differently: no sequence of continuous real-valued functions
    converges to it at every point. The obstruction comes from the complexity of inverse images. For any
    pointwise limit of continuous functions, the inverse image of an open set is $\Fsigma$. But
    $$
    u_{\QQ}^{-1}\bigl((-1/2,1/2)\bigr)=\SetDifference{\R}{\QQ},
    $$
    and the irrationals are not $\Fsigma$, as the Baire category theorem shows. Thus the complexity of a set can
    rule out a proposed continuous approximation.
-/
/-@ booklink:
  source: polish-space-book/preface.md
  target: prose
  excerpt: |
    Two successive stages of pointwise limits do suffice. Enumerate the rationals and let $F_n$ consist of the
    first $n+1$ of them. Each $u_{F_n}$ is a pointwise limit of continuous functions by the closed-set
    construction, and $u_{F_n}$ in turn converges pointwise to $u_{\QQ}$. The number of successive limit stages
    is recorded by the Baire classes of functions: $u_{\QQ}$ has class $2$ and cannot have class $1$.
    §{sec:baire-class-functions} proves these claims and relates the Baire classes to the Borel complexity of
    inverse images. The distinction between one limit and two is a concrete consequence of that complexity.
-/
theorem preface_dirichlet_complexity :
    IsBaireClass (2 : Ordinal.{0}) dirichlet ∧ ¬ IsBaireClass (1 : Ordinal.{0}) dirichlet :=
  dirichlet_exact_baire_two

end PolishSpaceBook
