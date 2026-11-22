module

public import PolishSpaceBook.CauchyNamesPolishRepresentations

@[expose] public section

/-!
# Strict margins for finite Cauchy prefixes

A prefix whose points are strictly within half the prescribed error of a
point can be completed by a fast dense name of that point. This gives the
geometric certificate used when extracting balls from accepted prefixes.
-/

namespace PolishSpaceBook
open Filter Set Topology
universe u
variable {X : Type u} [MetricSpace X] {q : ℕ → X}

/-- Half-error approximations satisfy all pairwise fast-Cauchy bounds. -/
theorem isCauchyName_of_halfError {p : ℕ → ℕ} {x : X}
    (hp : ∀ n, dist (q (p n)) x < (1 / 2 : ℝ)^(n+1)) : IsCauchyName q p := by
  intro n m hnm
  have hpow : (1 / 2 : ℝ)^(m+1) ≤ (1 / 2 : ℝ)^(n+1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htri := dist_triangle (q (p n)) x (q (p m))
  rw [dist_comm x] at htri
  have hn := hp n
  have hm := hp m
  have he : (1 / 2 : ℝ)^(n+1) + (1 / 2 : ℝ)^(n+1) = (1 / 2 : ℝ)^n := by ring
  linarith

/-- Retain the given prefix and use a dense name at every remaining coordinate. -/
noncomputable def completeCauchyPrefix (hq : DenseRange q) (s : List ℕ) (x : X) : ℕ → ℕ :=
  fun n => if n < s.length then s.getD n 0 else denseCauchyName q hq x n

theorem completeCauchyPrefix_mem_cyl (hq : DenseRange q) (s : List ℕ) (x : X) :
    completeCauchyPrefix hq s x ∈ cyl s := by
  intro n hn
  simp only [completeCauchyPrefix, ite_eq_left hn]
  simp [List.getD, hn]

theorem completeCauchyPrefix_halfError (hq : DenseRange q) (s : List ℕ) (x : X)
    (hs : ∀ n < s.length, dist (q (s.getD n 0)) x < (1 / 2 : ℝ)^(n+1)) :
    ∀ n, dist (q (completeCauchyPrefix hq s x n)) x < (1 / 2 : ℝ)^(n+1) := by
  intro n
  by_cases hn : n < s.length
  · simpa [completeCauchyPrefix, hn] using hs n hn
  · simpa [completeCauchyPrefix, hn, dist_comm] using denseCauchyName_approx q hq x n

theorem tendsto_completeCauchyPrefix (hq : DenseRange q) (s : List ℕ) (x : X) :
    Tendsto (fun n => q (completeCauchyPrefix hq s x n)) atTop (𝓝 x) := by
  apply (tendsto_denseCauchyName q hq x).congr'
  filter_upwards [eventually_ge_atTop s.length] with n hn
  simp [completeCauchyPrefix, Nat.not_lt.mpr hn]

variable [CompleteSpace X]

/-- The prefix is preserved and the represented point is the prescribed point. -/
theorem exists_cauchyName_extending (hq : DenseRange q) (s : List ℕ) (x : X)
    (hs : ∀ n < s.length, dist (q (s.getD n 0)) x < (1 / 2 : ℝ)^(n+1)) :
    ∃ p : cauchyNameDomain q, p.val ∈ cyl s ∧ cauchyRepresentation q p = x := by
  let p : cauchyNameDomain q := ⟨completeCauchyPrefix hq s x,
    isCauchyName_of_halfError (completeCauchyPrefix_halfError hq s x hs)⟩
  exact ⟨p, completeCauchyPrefix_mem_cyl hq s x,
    tendsto_nhds_unique (tendsto_cauchyRepresentation q p) (tendsto_completeCauchyPrefix hq s x)⟩

/-- A uniform half-error margin around a ball lets every point extend the prefix. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: lemma
  title: Cauchy-prefix margin lemma
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For $y\in\Ball{q_i}{r}$, retain $p(n)=s(n)$ for $n<N$. For every $n\ge N$, use density to choose $p(n)$ with $d(q_{p(n)},y)<2^{-(n+1)}$. The triangle inequality and the assumed margins give the same strict bound for $n<N$. Thus, for $m\ge n$,
    $$d(q_{p(n)},q_{p(m)})<2^{-(n+1)}+2^{-(m+1)}\le 2^{-n}.$$
    The sequence converges to $y$, so $p$ is a name of $y$ extending $s$. The extension is used to prove containment; the extraction algorithm does not need a name of $y$ as input.
    \end{proof}
-/
theorem ball_extends_cauchyPrefix (hq : DenseRange q) (s : List ℕ) (i : ℕ) (r : ℝ)
    (hs : ∀ n < s.length, dist (q (s.getD n 0)) (q i) + r < (1 / 2 : ℝ)^(n+1))
    {x : X} (hx : x ∈ Metric.ball (q i) r) :
    ∃ p : cauchyNameDomain q, p.val ∈ cyl s ∧ cauchyRepresentation q p = x := by
  apply exists_cauchyName_extending hq s x
  intro n hn
  have ht := dist_triangle (q (s.getD n 0)) (q i) x
  have hx' : dist (q i) x < r := by simpa [Metric.mem_ball, dist_comm] using hx
  linarith [hs n hn]

omit [CompleteSpace X] in
/-- Finitely many strict gaps admit a common dyadic error bound. -/
theorem exists_dyadic_prefix_margin (p : ℕ → ℕ) (x : X)
    (hp : ∀ n, dist (q (p n)) x < (1 / 2 : ℝ)^(n+1)) (N : ℕ) :
    ∃ k, ∀ n < N, dist (q (p n)) x + 4 * (1 / 2 : ℝ)^k < (1 / 2 : ℝ)^(n+1) := by
  induction N with
  | zero => exact ⟨0, by simp⟩
  | succ N ih =>
    obtain ⟨k, hk⟩ := ih
    have hg : 0 < ((1 / 2 : ℝ)^(N+1) - dist (q (p N)) x) / 4 := by linarith [hp N]
    obtain ⟨l, hl⟩ := exists_pow_lt_of_lt_one hg (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨max k l, fun n hn => ?_⟩
    have hkl : (1 / 2 : ℝ)^(max k l) ≤ (1 / 2 : ℝ)^k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
    have hll : (1 / 2 : ℝ)^(max k l) ≤ (1 / 2 : ℝ)^l :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
    by_cases h : n < N
    · linarith [hk n h]
    · have : n = N := by omega
      subst n
      linarith

end PolishSpaceBook
