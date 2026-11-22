module

public import PolishSpaceBook.CantorBaireSpace
public import Mathlib.Topology.Compactification.OnePoint.Basic

@[expose] public section

/-!
# Cauchy names and Polish representations

Formalization targets for
`polish-space/src/polish-space-book/cauchy-names-polish-representations.md`.

Formalized here are the fast Cauchy-name predicate, its closed Polish domain,
the represented limit and workhorse estimate, uniform continuity and
surjectivity of the Cauchy representation, the explicit first-failure retraction
and resulting universal continuous-surjection theorem, continuous reducibility and equivalence of
representations, and the formal consequences of admissibility.

Admissibility is proved by disjointifying relative clopen cylinders. The
partial-map characterization uses tagged names, and topology recovery uses
the zero name and single-1 names for a convergent sequence. Binary names are
formalized in `BinaryRepresentations.lean`, including greedy surjectivity,
the finite-sum translator, and the dyadic nonreducibility argument.
`SignedDigitRepresentations.lean` proves the signed-digit range, explicit
translations in both directions, the closed Baire coding, and admissibility.
-/

namespace PolishSpaceBook

universe u

open Filter Function Set Topology

section CauchyNames

variable {X : Type u} [MetricSpace X]

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Fix a nonempty Polish space $X$ with complete compatible metric $d$ and a countable dense subset
    $D = \IndexedFamily{q_n}{n\in\omega}$.
    Call $p \in \BaireSpace$ a **\termdefine{Cauchy name}** if, for all $m\ge n\ge0$,
    $$d(q_{p(n)},\, q_{p(m)}) \;\le\; 2^{-n}.$$
-/
/-- A fast Cauchy name relative to a fixed dense sequence `q`. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For Polish spaces with a chosen computable metric presentation, the representation $\rho_X$ used in
    §{sec:cauchy-representation-admissibility} takes a name to the
    limit of a fast Cauchy sequence in a fixed computable dense set. Thus a computable real is a real with a computable fast
    Cauchy name, and a computable function between Polish spaces is one whose action on such names is computed by a lambda
    realizer with the input name as a function argument.
-/
def IsCauchyName (q : ℕ → X) (p : baire_space) : Prop :=
  ∀ n m, n ≤ m → dist (q (p n)) (q (p m)) ≤ (1 / 2 : ℝ) ^ n

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Let $\DomainOf{\rho_X} \IncludedIn \BaireSpace$ be the set of Cauchy names.
-/
/-- The domain of fast Cauchy names. -/
def cauchyNameDomain (q : ℕ → X) : Set baire_space :=
  {p | IsCauchyName q p}

theorem IsCauchyName.cauchySeq {q : ℕ → X} {p : baire_space}
    (hp : IsCauchyName q p) :
    CauchySeq (fun n ↦ q (p n)) := by
  exact cauchySeq_of_le_tendsto_0' (fun n ↦ (1 / 2 : ℝ) ^ n)
    (fun n m hnm ↦ hp n m hnm)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    **Closed domain.** Each constraint $d(q_{p(n)},\, q_{p(m)}) \le 2^{-n}$ depends only on finitely many coordinates of
    $p$, so it cuts out a clopen subset of $\BaireSpace$. The domain is the countable intersection of these clopen sets,
    hence closed in $\BaireSpace$. By the closed-subspace result of §{sec:polish-key-properties}, the domain is itself
    Polish.
-/
theorem isClopen_cauchyNameConstraint (q : ℕ → X) (n m : ℕ) :
    IsClopen {p : baire_space | dist (q (p n)) (q (p m)) ≤ (1 / 2 : ℝ) ^ n} := by
  let S : Set (ℕ × ℕ) := {ij | dist (q ij.1) (q ij.2) ≤ (1 / 2 : ℝ) ^ n}
  have hpair : Continuous (fun p : baire_space ↦ (p n, p m)) :=
    (continuous_apply n).prodMk (continuous_apply m)
  exact (isClopen_discrete S).preimage hpair

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] The first assertion is immediate from the Cauchy representation: $\DomainOf{\rho_X}$ is closed in
    $\BaireSpace$, and $\rho_X : \DomainOf{\rho_X} \to X$ is continuous and surjective.
-/
theorem isClosed_cauchyNameDomain (q : ℕ → X) :
    IsClosed (cauchyNameDomain q) := by
  rw [show cauchyNameDomain q =
      ⋂ n : ℕ, ⋂ m : ℕ, ⋂ (_h : n ≤ m),
        {p : baire_space | dist (q (p n)) (q (p m)) ≤ (1 / 2 : ℝ) ^ n} by
    ext p
    simp only [cauchyNameDomain, IsCauchyName, Set.mem_ofPred_eq, Set.mem_iInter]]
  refine isClosed_iInter fun n ↦ isClosed_iInter fun m ↦ isClosed_iInter fun _hnm ↦ ?_
  exact (isClopen_cauchyNameConstraint q n m).isClosed

theorem cauchyNameDomain_polish (q : ℕ → X) :
    PolishSpace (cauchyNameDomain q) :=
  (isClosed_cauchyNameDomain q).polishSpace

variable [CompleteSpace X]

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    The
    \termdefine{Cauchy representation} is the map
    $$\rho_X : \DomainOf{\rho_X} \twoheadrightarrow X, \qquad \rho_X(p) \;=\; \lim_{n \to \infty} q_{p(n)},$$
    where the limit exists because the Cauchy-name condition makes $(q_{p(n)})$ a $d$-Cauchy sequence and $X$ is complete.
    Letting $m \to \infty$ in the defining inequality yields the workhorse bound
    $$d(q_{p(n)},\, \rho_X(p)) \;\le\; 2^{-n},$$
    used repeatedly below.
-/
/-- The represented limit of a fast Cauchy name. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For Polish spaces with a chosen computable metric presentation, the representation $\rho_X$ used in
    §{sec:cauchy-representation-admissibility} takes a name to the
    limit of a fast Cauchy sequence in a fixed computable dense set. Thus a computable real is a real with a computable fast
    Cauchy name, and a computable function between Polish spaces is one whose action on such names is computed by a lambda
    realizer with the input name as a function argument.
-/
noncomputable def cauchyRepresentation (q : ℕ → X) : cauchyNameDomain q → X :=
  fun p ↦ Classical.choose (cauchySeq_tendsto_of_complete p.2.cauchySeq)

theorem tendsto_cauchyRepresentation (q : ℕ → X) (p : cauchyNameDomain q) :
    Tendsto (fun n ↦ q (p.1 n)) atTop (𝓝 (cauchyRepresentation q p)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete p.2.cauchySeq)

theorem cauchyRepresentation_dist_le (q : ℕ → X) (p : cauchyNameDomain q) (n : ℕ) :
    dist (q (p.1 n)) (cauchyRepresentation q p) ≤ (1 / 2 : ℝ) ^ n := by
  apply le_of_tendsto
    (tendsto_const_nhds.dist (tendsto_cauchyRepresentation q p))
  filter_upwards [eventually_ge_atTop n] with m hm
  exact p.2 n m hm

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    **Continuous.** If two Cauchy names $p, p'$ agree on the first $n+1$ coordinates (indices $0, \ldots, n$), then
    $p(n) = p'(n)$, and the workhorse bound puts both $\rho_X(p)$ and $\rho_X(p')$ within $2^{-n}$ of the common point
    $q_{p(n)}$, so $d(\rho_X(p), \rho_X(p')) \le 2 \cdot 2^{-n}$ by the triangle inequality. Thus agreement on a
    sufficiently long prefix forces the images to be arbitrarily close, and $\rho_X : \DomainOf{\rho_X} \to X$ is
    continuous.
-/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] The first assertion is immediate from the Cauchy representation: $\DomainOf{\rho_X}$ is closed in
    $\BaireSpace$, and $\rho_X : \DomainOf{\rho_X} \to X$ is continuous and surjective.
-/
theorem continuous_cauchyRepresentation (q : ℕ → X) :
    Continuous (cauchyRepresentation q) := by
  rw [continuous_iff_continuousAt]
  intro p
  change Tendsto (cauchyRepresentation q) (𝓝 p) (𝓝 (cauchyRepresentation q p))
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < ε / 2 :=
    exists_pow_lt_of_lt_one (half_pos hε) (by norm_num)
  let U : Set (cauchyNameDomain q) :=
    {p' | p'.1 ∈ cyl (seqPrefix p.1 (n + 1))}
  have hU_open : IsOpen U := by
    exact (baire_cyl_clopen (seqPrefix p.1 (n + 1))).isOpen.preimage continuous_subtype_val
  have hpU : p ∈ U := mem_cyl_seqPrefix p.1 (n + 1)
  filter_upwards [hU_open.mem_nhds hpU] with p' hp'U
  have heq : p'.1 n = p.1 n := by
    have hnlen : n < (seqPrefix p.1 (n + 1)).length := by simp
    calc
      p'.1 n = (seqPrefix p.1 (n + 1)).get ⟨n, hnlen⟩ := hp'U n hnlen
      _ = p.1 n := seqPrefix_get p.1 hnlen
  calc
    dist (cauchyRepresentation q p') (cauchyRepresentation q p)
        ≤ dist (cauchyRepresentation q p') (q (p'.1 n)) +
          dist (q (p'.1 n)) (cauchyRepresentation q p) :=
      dist_triangle _ _ _
    _ = dist (q (p'.1 n)) (cauchyRepresentation q p') +
          dist (q (p.1 n)) (cauchyRepresentation q p) := by
      rw [dist_comm (cauchyRepresentation q p')]
      rw [heq]
    _ ≤ (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n :=
      add_le_add (cauchyRepresentation_dist_le q p' n)
        (cauchyRepresentation_dist_le q p n)
    _ < ε := by linarith

/-- A fast name chosen from a dense sequence. -/
noncomputable def denseCauchyName (q : ℕ → X) (hq : DenseRange q) (x : X) : baire_space :=
  fun n ↦ Classical.choose
    (hq.exists_dist_lt x (by positivity : 0 < (1 / 2 : ℝ) ^ (n + 1)))

omit [CompleteSpace X] in
theorem denseCauchyName_approx (q : ℕ → X) (hq : DenseRange q) (x : X) (n : ℕ) :
    dist x (q (denseCauchyName q hq x n)) < (1 / 2 : ℝ) ^ (n + 1) :=
  Classical.choose_spec
    (hq.exists_dist_lt x (by positivity : 0 < (1 / 2 : ℝ) ^ (n + 1)))

omit [CompleteSpace X] in
theorem denseCauchyName_isCauchy (q : ℕ → X) (hq : DenseRange q) (x : X) :
    IsCauchyName q (denseCauchyName q hq x) := by
  intro n m hnm
  have hn := denseCauchyName_approx q hq x n
  have hm := denseCauchyName_approx q hq x m
  have hpow : (1 / 2 : ℝ) ^ (m + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right hnm 1)
  calc
    dist (q (denseCauchyName q hq x n)) (q (denseCauchyName q hq x m))
        ≤ dist (q (denseCauchyName q hq x n)) x +
          dist x (q (denseCauchyName q hq x m)) := dist_triangle _ _ _
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) + (1 / 2 : ℝ) ^ (m + 1) :=
      add_le_add (by simpa [dist_comm] using hn.le) hm.le
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) + (1 / 2 : ℝ) ^ (n + 1) :=
      add_le_add le_rfl hpow
    _ = (1 / 2 : ℝ) ^ n := by ring

omit [CompleteSpace X] in
theorem tendsto_denseCauchyName (q : ℕ → X) (hq : DenseRange q) (x : X) :
    Tendsto (fun n ↦ q (denseCauchyName q hq x n)) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun n hn ↦ ?_⟩
  calc
    dist (q (denseCauchyName q hq x n)) x =
        dist x (q (denseCauchyName q hq x n)) := dist_comm _ _
    _ < (1 / 2 : ℝ) ^ (n + 1) := denseCauchyName_approx q hq x n
    _ ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
    _ ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    _ < ε := hN

theorem cauchyRepresentation_denseCauchyName
    (q : ℕ → X) (hq : DenseRange q) (x : X) :
    cauchyRepresentation q
        ⟨denseCauchyName q hq x, denseCauchyName_isCauchy q hq x⟩ = x := by
  exact tendsto_nhds_unique
    (tendsto_cauchyRepresentation q
      ⟨denseCauchyName q hq x, denseCauchyName_isCauchy q hq x⟩)
    (tendsto_denseCauchyName q hq x)

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    **Surjective.** For every $x \in X$ pick $a_n \in D$ with $d(a_n, x) \le 2^{-(n+1)}$ (possible by density). Then for
    $m \ge n$ the triangle inequality gives $d(a_n, a_m) \le 2^{-(n+1)} + 2^{-(m+1)} \le 2^{-n}$. Writing $a_n =
    q_{p(n)}$ produces a Cauchy name $p$, and since $a_n \to x$, its represented limit is $\rho_X(p)=x$.
-/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] The first assertion is immediate from the Cauchy representation: $\DomainOf{\rho_X}$ is closed in
    $\BaireSpace$, and $\rho_X : \DomainOf{\rho_X} \to X$ is continuous and surjective.
-/
theorem surjective_cauchyRepresentation (q : ℕ → X) (hq : DenseRange q) :
    Surjective (cauchyRepresentation q) := by
  intro x
  exact ⟨⟨denseCauchyName q hq x, denseCauchyName_isCauchy q hq x⟩,
    cauchyRepresentation_denseCauchyName q hq x⟩

end CauchyNames

section FirstFailureRetraction

/- The first-failure case analysis is adapted from
Mathlib/Topology/MetricSpace/PiNat.lean.
Copyright (c) 2022 Sébastien Gouëzel. Released under Apache 2.0 license. -/
open Set Function Topology PiNat
noncomputable local instance : MetricSpace baire_space := PiNat.metricSpaceNatNat
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    Define $r : \BaireSpace \to F$ as follows. If $x \in F$, set $r(x) = x$. Otherwise let $n$ be least such that
    $\restrict{x}{n} \in T_F$ but $\restrict{x}{n+1} \notin T_F$, and set $r(x) = b_{\restrict{x}{n}}$. This is a retraction
    because it fixes every point of $F$ and always lands in $F$.
-/
/-- Choose the last prefix still meeting the closed set and a branch extending it.
The imported prefix lemmas express the minimality of `Nat.find`; the map and
its prefix-preserving case analysis are constructed here. -/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    For the stronger assertion, it remains to see that every nonempty closed $F \IncludedIn \BaireSpace$ is a continuous
    retract of $\BaireSpace$. Let
    $$T_F := \{s \in \finseq{\omega} : \cyl{s} \cap F \ne \emptyset\}$$
    be the tree of finite prefixes realized by points of $F$. Since $F$ is closed, $F = [T_F]$, the set of infinite branches
    through $T_F$: if $x \notin F$, some basic cylinder around $x$ is disjoint from $F$, so some prefix of $x$ is not in
    $T_F$. For each $s \in T_F$, choose once and for all a branch $b_s \in F \cap \cyl{s}$.
-/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    It is continuous. If $x \notin F$, the same first failure of membership in $T_F$ occurs throughout the cylinder
    $\cyl{\restrict{x}{n+1}}$, so $r$ is locally constant there. If $x \in F$ and a basic neighborhood
    $\cyl{\restrict{x}{k}}$ of $r(x)=x$ is given, then every $y \in \cyl{\restrict{x}{k}}$ either belongs to $F$, in which
    case $r(y)=y \in \cyl{\restrict{x}{k}}$, or first leaves $T_F$ at some stage $m \ge k$ (since $\restrict{y}{k} =
    \restrict{x}{k} \in T_F$), in which case $r(y)=b_{\restrict{y}{m}} \in \cyl{\restrict{y}{m}} \IncludedIn
    \cyl{\restrict{y}{k}} = \cyl{\restrict{x}{k}}$. Thus $r$ is continuous at every point. Therefore $\rho_X \circ r :
    \BaireSpace \to X$ is a continuous surjection.
    \end{proof}
-/
theorem baire_firstFailure_lipschitz_retraction {s : Set baire_space}
    (hs : IsClosed s) (hne : s.Nonempty) :
    ∃ f : baire_space → baire_space, (∀ x ∈ s, f x = x) ∧ range f = s ∧
      LipschitzWith 1 f := by
  /- The map `f` is defined as follows. For `x ∈ s`, let `f x = x`. Otherwise, consider the longest
    prefix `w` that `x` shares with an element of `s`, and let `f x = z_w` where `z_w` is an element
    of `s` starting with `w`. All the desired properties are clear, except the fact that `f` is
    `1`-Lipschitz: if two points `x, y` belong to a common cylinder of length `n`, one should show
    that their images also belong to a common cylinder of length `n`. This is a case analysis:
    * if both `x, y ∈ s`, then this is clear.
    * if `x ∈ s` but `y ∉ s`, then the longest prefix `w` of `y` shared by an element of `s` is of
    length at least `n` (because of `x`), and then `f y` starts with `w` and therefore stays in the
    same length `n` cylinder.
    * if `x ∉ s`, `y ∉ s`, let `w` be the longest prefix of `x` shared by an element of `s`. If its
    length is `< n`, then it is also the longest prefix of `y`, and we get `f x = f y = z_w`.
    Otherwise, `f x` remains in the same `n`-cylinder as `x`. Similarly for `y`. Finally, `f x` and
    `f y` are again in the same `n`-cylinder, as desired. -/
  classical
  set f := fun x => if x ∈ s then x else (inter_cylinder_longestPrefix_nonempty hs hne x).some
  have fs : ∀ x ∈ s, f x = x := fun x xs => by simp [f, xs]
  refine ⟨f, fs, ?_, ?_⟩
  -- check that the range of `f` is `s`.
  · apply Subset.antisymm
    · rintro x ⟨y, rfl⟩
      by_cases hy : y ∈ s
      · rwa [fs y hy]
      simpa [f, ite_eq_right hy] using! (inter_cylinder_longestPrefix_nonempty hs hne y).choose_spec.1
    · intro x hx
      rw [← fs x hx]
      exact mem_range_self _
  -- check that `f` is `1`-Lipschitz, by a case analysis.
  · refine LipschitzWith.mk_one fun x y => ?_
    -- exclude the trivial cases where `x = y`, or `f x = f y`.
    rcases eq_or_ne x y with (rfl | hxy)
    · simp
    rcases eq_or_ne (f x) (f y) with (h' | hfxfy)
    · simp [h']
    have I2 : cylinder x (firstDiff x y) = cylinder y (firstDiff x y) := by
      rw [← mem_cylinder_iff_eq]
      apply mem_cylinder_firstDiff
    suffices firstDiff x y ≤ firstDiff (f x) (f y) by
      rw [dist_eq_of_ne hxy, dist_eq_of_ne hfxfy]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) this
    -- case where `x ∈ s`
    by_cases xs : x ∈ s
    · rw [fs x xs] at hfxfy ⊢
      -- case where `y ∈ s`, trivial
      by_cases ys : y ∈ s
      · rw [fs y ys]
      -- case where `y ∉ s`
      have A : (s ∩ cylinder y (longestPrefix y s)).Nonempty :=
        inter_cylinder_longestPrefix_nonempty hs hne y
      have fy : f y = A.some := by simp_rw [f, ite_eq_right ys]
      have I : cylinder A.some (firstDiff x y) = cylinder y (firstDiff x y) := by
        rw [← mem_cylinder_iff_eq, firstDiff_comm]
        apply cylinder_anti y _ A.some_mem.2
        exact firstDiff_le_longestPrefix hs ys xs
      rwa [← fy, ← I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_firstDiff hfxfy.symm,
        firstDiff_comm _ x] at I
    -- case where `x ∉ s`
    · by_cases ys : y ∈ s
      -- case where `y ∈ s` (similar to the above)
      · have A : (s ∩ cylinder x (longestPrefix x s)).Nonempty :=
          inter_cylinder_longestPrefix_nonempty hs hne x
        have fx : f x = A.some := by simp_rw [f, ite_eq_right xs]
        have I : cylinder A.some (firstDiff x y) = cylinder x (firstDiff x y) := by
          rw [← mem_cylinder_iff_eq]
          apply cylinder_anti x _ A.some_mem.2
          apply firstDiff_le_longestPrefix hs xs ys
        rw [fs y ys] at hfxfy ⊢
        rwa [← fx, I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_firstDiff hfxfy] at I
      -- case where `y ∉ s`
      · have Ax : (s ∩ cylinder x (longestPrefix x s)).Nonempty :=
          inter_cylinder_longestPrefix_nonempty hs hne x
        have fx : f x = Ax.some := by simp_rw [f, ite_eq_right xs]
        have Ay : (s ∩ cylinder y (longestPrefix y s)).Nonempty :=
          inter_cylinder_longestPrefix_nonempty hs hne y
        have fy : f y = Ay.some := by simp_rw [f, ite_eq_right ys]
        -- case where the common prefix to `x` and `s`, or `y` and `s`, is shorter than the
        -- common part to `x` and `y` -- then `f x = f y`.
        by_cases! H : longestPrefix x s < firstDiff x y ∨ longestPrefix y s < firstDiff x y
        · have : cylinder x (longestPrefix x s) = cylinder y (longestPrefix y s) := by
            rcases H with H | H
            · exact cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff hs hne H xs ys
            · symm
              rw [firstDiff_comm] at H
              exact cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff hs hne H ys xs
          rw [fx, fy] at hfxfy
          apply (hfxfy _).elim
          congr
        -- case where the common prefix to `x` and `s` is long, as well as the common prefix to
        -- `y` and `s`. Then all points remain in the same cylinders.
        · have I1 : cylinder Ax.some (firstDiff x y) = cylinder x (firstDiff x y) := by
            rw [← mem_cylinder_iff_eq]
            exact cylinder_anti x H.1 Ax.some_mem.2
          have I3 : cylinder y (firstDiff x y) = cylinder Ay.some (firstDiff x y) := by
            rw [eq_comm, ← mem_cylinder_iff_eq]
            exact cylinder_anti y H.2 Ay.some_mem.2
          have : cylinder Ax.some (firstDiff x y) = cylinder Ay.some (firstDiff x y) := by
            rw [I1, I2, I3]
          rw [← fx, ← fy, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_firstDiff hfxfy] at this
          exact this

theorem baire_firstFailure_retraction {s : Set baire_space}
    (hs : IsClosed s) (hne : s.Nonempty) :
    ∃ r : baire_space → s, (∀ x : s, r x = x) ∧ Continuous r ∧ Surjective r := by
  obtain ⟨f, hf, hrange, hcont⟩ := baire_firstFailure_lipschitz_retraction hs hne
  have hmem (x) : f x ∈ s := hrange ▸ mem_range_self x
  let r : baire_space → s := fun x => ⟨f x, hmem x⟩
  have hfix (x : s) : r x = x := Subtype.ext (hf x x.property)
  exact ⟨r, hfix, hcont.continuous.subtype_mk _, fun x => ⟨x, hfix x⟩⟩

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: statement
  kind: theorem
  title: ""
-/
/-- Compose the Cauchy representation with the explicit closed-domain retraction. -/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    It is continuous. If $x \notin F$, the same first failure of membership in $T_F$ occurs throughout the cylinder
    $\cyl{\restrict{x}{n+1}}$, so $r$ is locally constant there. If $x \in F$ and a basic neighborhood
    $\cyl{\restrict{x}{k}}$ of $r(x)=x$ is given, then every $y \in \cyl{\restrict{x}{k}}$ either belongs to $F$, in which
    case $r(y)=y \in \cyl{\restrict{x}{k}}$, or first leaves $T_F$ at some stage $m \ge k$ (since $\restrict{y}{k} =
    \restrict{x}{k} \in T_F$), in which case $r(y)=b_{\restrict{y}{m}} \in \cyl{\restrict{y}{m}} \IncludedIn
    \cyl{\restrict{y}{k}} = \cyl{\restrict{x}{k}}$. Thus $r$ is continuous at every point. Therefore $\rho_X \circ r :
    \BaireSpace \to X$ is a continuous surjection.
    \end{proof}
-/
theorem exists_baire_continuous_surjection (X : Type u) [TopologicalSpace X]
    [PolishSpace X] [Nonempty X] :
    ∃ f : baire_space → X, Continuous f ∧ Surjective f := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  let q := TopologicalSpace.denseSeq X
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq X
  have hs : (cauchyNameDomain q).Nonempty := by
    obtain ⟨p, _⟩ := surjective_cauchyRepresentation q hq (Classical.arbitrary X)
    exact ⟨p, p.property⟩
  obtain ⟨r, _, hr, hsurj⟩ := baire_firstFailure_retraction (isClosed_cauchyNameDomain q) hs
  exact ⟨cauchyRepresentation q ∘ r, (continuous_cauchyRepresentation q).comp hr,
    (surjective_cauchyRepresentation q hq).comp hsurj⟩
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    In fact, with the \termuse{standard sequence metric} on $\BaireSpace$, this gives uniform continuity on
    $\DomainOf{\rho_X}$.
-/
/-- A prefix length depending only on the target error proves uniform continuity. -/
theorem uniformContinuous_cauchyRepresentation {X : Type*}
    [MetricSpace X] [CompleteSpace X] (q : ℕ → X) :
    UniformContinuous (cauchyRepresentation q) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < ε / 2 :=
    exists_pow_lt_of_lt_one (half_pos hε) (by norm_num)
  refine ⟨(1 / 2 : ℝ) ^ (n + 1), by positivity, ?_⟩
  intro p p' hp
  have hc : p.1 ∈ PiNat.cylinder p'.1 (n + 1) :=
    PiNat.mem_cylinder_iff_dist_le.mpr hp.le
  have heq : p.1 n = p'.1 n := hc n (by omega)
  calc
    dist (cauchyRepresentation q p) (cauchyRepresentation q p')
        ≤ dist (cauchyRepresentation q p) (q (p.1 n)) +
          dist (q (p.1 n)) (cauchyRepresentation q p') := dist_triangle _ _ _
    _ = dist (q (p.1 n)) (cauchyRepresentation q p) +
          dist (q (p'.1 n)) (cauchyRepresentation q p') := by
      rw [dist_comm (cauchyRepresentation q p), heq]
    _ ≤ (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n :=
      add_le_add (cauchyRepresentation_dist_le q p n)
        (cauchyRepresentation_dist_le q p' n)
    _ < ε := by linarith

end FirstFailureRetraction

section Representations

variable (X : Type u)

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    A \termdefine{representation} of a set $X$ is a partial function $\PartialFunctionMap{\delta}{\BaireSpace}{X}$
    whose range is all of $X$. Its domain carries the subspace topology inherited from $\BaireSpace$.
    The Cauchy representation is one example. Compare two representations $\PartialFunctionMap{\delta_1}{\BaireSpace}{X}$
    and $\PartialFunctionMap{\delta_2}{\BaireSpace}{X}$ of the same set $X$ via continuous translation.
-/
/-- A partial representation of `X` whose names lie in Baire space. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    A \termdefine{represented space} is a pair
    $$\mathbf X=(X,\delta_X)$$
    where $X$ is a set and $\PartialFunctionMap{\delta_X}{\BaireSpace}{X}$ is a partial function whose range is all of $X$.
    A point $p\in \DomainOf{\delta_X}$ is a \termdefineas{represented-space name}{name} of $x$ when $\delta_X(p)=x$. The
    topology induced by $\delta_X$ is the final topology: $U\IncludedIn X$ is open when $\delta_X^{-1}(U)$ is open in
    $\DomainOf{\delta_X}$. For
    \termuseas{admissible representation of topological space}{admissible representations} of Polish spaces this recovers
    the original topology.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termuse{represented space} is a set $X$ together with a partial surjection
    $\PartialFunctionMap{\delta_X}{\BaireSpace}{X}$. A name of $x$ is a point $p\in\DomainOf{\delta_X}$ with
    $\delta_X(p)=x$. A point $x$ is \termdefineas{computable point in represented space}{computable} if it has a computable
    name.
-/
structure Representation where
  domain : Set baire_space
  toFun : domain → X
  surjective : Surjective toFun

variable {X : Type u}

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Say that $\delta_1$ is
    \termdefineas{continuous reducibility of representations}{continuously reducible} to $\delta_2$, written
    $$\delta_1 \ContinuouslyReducesTo \delta_2,$$
    if there exists a continuous $f : \DomainOf{\delta_1} \to \DomainOf{\delta_2}$ with $\delta_2 \circ f = \delta_1$.
    Thus every $\delta_1$-name can be continuously translated into a $\delta_2$-name of the same point.
-/
/-- Continuous reducibility of representations. -/
def ContinuouslyReduces (δ₁ δ₂ : Representation X) : Prop :=
  ∃ f : δ₁.domain → δ₂.domain, Continuous f ∧ ∀ p, δ₂.toFun (f p) = δ₁.toFun p

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Representations
    reducible in both directions are \termdefineas{continuous equivalence of representations}{continuously equivalent},
    written $\delta_1 \ContinuouslyEquivalentTo \delta_2$.
-/
/-- Bidirectional continuous reducibility. -/
def ContinuouslyEquivalent (δ₁ δ₂ : Representation X) : Prop :=
  ContinuouslyReduces δ₁ δ₂ ∧ ContinuouslyReduces δ₂ δ₁

theorem ContinuouslyReduces.refl (δ : Representation X) :
    ContinuouslyReduces δ δ := by
  exact ⟨id, continuous_id, fun _ ↦ rfl⟩

theorem ContinuouslyReduces.trans {δ₁ δ₂ δ₃ : Representation X}
    (h₁₂ : ContinuouslyReduces δ₁ δ₂) (h₂₃ : ContinuouslyReduces δ₂ δ₃) :
    ContinuouslyReduces δ₁ δ₃ := by
  obtain ⟨f, hf, hfc⟩ := h₁₂
  obtain ⟨g, hg, hgc⟩ := h₂₃
  refine ⟨g ∘ f, hg.comp hf, fun p ↦ ?_⟩
  rw [Function.comp_apply, hgc, hfc]

section CauchyRepresentationObject

variable [MetricSpace X] [CompleteSpace X]

/-- The Cauchy limit map packaged as a representation. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The associated Cauchy representation is the one already defined:
    $$p \in \DomainOf{\rho_X}
    \quad\Longleftrightarrow\quad
    d(q_{p(n)},q_{p(m)})\le 2^{-n}\quad(m\ge n),$$
    and
    $$\rho_X(p)=\lim_n q_{p(n)}.$$
    The representation is \termdefineas{effective Cauchy representation}{effective} because the Cauchy-name condition is a
    uniformly effectively closed condition on finite coordinates: failure is witnessed by rational bounds proving
    $d(q_{p(n)},q_{p(m)})>2^{-n}$ for some $m\ge n$. Metric balls around dense points can likewise be semidecided at
    rational precisions from the computable distance data.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The \termuse{Cauchy representation} in §{sec:cauchy-representation-admissibility} was purely topological: a name was an
    element of
    $\BaireSpace$ coding a fast Cauchy sequence, and a continuous translator between name spaces witnessed reducibility of
    representations. **\termdefineas{Type-Two Effectivity}{Type-2 Theory of Effectivity}** (TTE) adds the algorithmic
    requirement: names are input functions $p:\NN\to\NN$, and a realizer is a lambda program transforming names into names.
    The program obtains information from an input name by querying its entries as needed.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For Polish spaces with a chosen computable metric presentation, the representation $\rho_X$ used in
    §{sec:cauchy-representation-admissibility} takes a name to the
    limit of a fast Cauchy sequence in a fixed computable dense set. Thus a computable real is a real with a computable fast
    Cauchy name, and a computable function between Polish spaces is one whose action on such names is computed by a lambda
    realizer with the input name as a function argument.
-/
noncomputable def cauchyRepresentationObject (q : ℕ → X) (hq : DenseRange q) :
    Representation X where
  domain := cauchyNameDomain q
  toFun := cauchyRepresentation q
  surjective := surjective_cauchyRepresentation q hq

end CauchyRepresentationObject

section Admissibility

variable [TopologicalSpace X]

/-- A representation is continuous when its partial map is continuous on its domain. -/
def Representation.IsContinuous (δ : Representation X) : Prop :=
  Continuous δ.toFun

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    A representation $\rho$ of a topological space $X$ is
    \termdefineas{admissible representation of topological space}{admissible} if it is continuous and every continuous
    representation $\delta$ of $X$ satisfies $\delta \ContinuouslyReducesTo \rho$. Equivalently, $\rho$ is a greatest
    element of the preorder of continuous representations ordered by $\ContinuouslyReducesTo$.
-/
/-- A continuous representation greatest under continuous reducibility. -/
def Representation.IsAdmissible (ρ : Representation X) : Prop :=
  ρ.IsContinuous ∧ ∀ δ : Representation X, δ.IsContinuous → ContinuouslyReduces δ ρ

theorem ContinuouslyReduces.continuous_left {δ₁ δ₂ : Representation X}
    (h : ContinuouslyReduces δ₁ δ₂) (hδ₂ : δ₂.IsContinuous) :
    δ₁.IsContinuous := by
  obtain ⟨f, hf, hcomm⟩ := h
  have heq : δ₁.toFun = δ₂.toFun ∘ f := by
    funext p
    exact (hcomm p).symm
  change Continuous δ₁.toFun
  change Continuous δ₂.toFun at hδ₂
  rw [heq]
  exact hδ₂.comp hf

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    If $\alpha$ and $\beta$ are admissible representations of the same space, applying admissibility first to $\beta$ and
    then to $\alpha$ gives $\beta \ContinuouslyReducesTo \alpha$ and $\alpha \ContinuouslyReducesTo \beta$, so
    $\alpha \ContinuouslyEquivalentTo \beta$. In particular, every admissible representation is equivalent to $\rho_X$.
    Conversely, if $\delta \ContinuouslyEquivalentTo \rho_X$, then $\delta$ is continuous because
    $\delta = \rho_X \circ f$ for a continuous translator $f$, and every continuous representation $\gamma$ satisfies
    $\gamma \ContinuouslyReducesTo \rho_X \ContinuouslyReducesTo \delta$; hence $\delta$ is admissible.
-/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Changing the complete compatible metric or the countable dense sequence gives a continuously equivalent Cauchy
    representation, since each such representation is admissible. No effectiveness of these choices is required here.
-/
theorem continuouslyEquivalent_of_admissible {δ₁ δ₂ : Representation X}
    (h₁ : δ₁.IsAdmissible) (h₂ : δ₂.IsAdmissible) :
    ContinuouslyEquivalent δ₁ δ₂ :=
  ⟨h₂.2 δ₁ h₁.1, h₁.2 δ₂ h₂.1⟩

theorem admissible_of_continuouslyEquivalent {ρ δ : Representation X}
    (hρ : ρ.IsAdmissible) (hδρ : ContinuouslyEquivalent δ ρ) :
    δ.IsAdmissible := by
  refine ⟨hδρ.1.continuous_left hρ.1, ?_⟩
  intro γ hγ
  exact (hρ.2 γ hγ).trans hδρ.2

theorem admissible_iff_continuouslyEquivalent {ρ δ : Representation X}
    (hρ : ρ.IsAdmissible) :
    δ.IsAdmissible ↔ ContinuouslyEquivalent δ ρ := by
  constructor
  · intro hδ
    exact continuouslyEquivalent_of_admissible hδ hρ
  · exact admissible_of_continuouslyEquivalent hρ

end Admissibility

end Representations

/-- Names for two partial maps, separated by their initial digit. -/
def taggedNameDomain (E F : Set baire_space) : Set baire_space :=
  {p | (p 0 = 0 ∧ (fun n => p (n + 1)) ∈ E) ∨
       (p 0 = 1 ∧ (fun n => p (n + 1)) ∈ F)}

theorem taggedNameDomain_tail_zero {E F : Set baire_space} (p : taggedNameDomain E F)
    (h : p.val 0 = 0) : (fun n => p.val (n + 1)) ∈ E := by
  rcases p.property with ⟨_, he⟩ | ⟨h1, _⟩
  · exact he
  · omega

theorem taggedNameDomain_tail_one {E F : Set baire_space} (p : taggedNameDomain E F)
    (h : p.val 0 ≠ 0) : (fun n => p.val (n + 1)) ∈ F := by
  rcases p.property with ⟨h0, _⟩ | ⟨_, hf⟩
  · exact (h h0).elim
  · exact hf

noncomputable def taggedNameMap {X : Type*} {E F : Set baire_space}
    (g : E → X) (r : F → X) (p : taggedNameDomain E F) : X :=
  open Classical in
  if h : p.val 0 = 0 then g ⟨fun n => p.val (n + 1), taggedNameDomain_tail_zero p h⟩
  else r ⟨fun n => p.val (n + 1), taggedNameDomain_tail_one p h⟩

def prefixName (tag : ℕ) (p : baire_space) : baire_space
  | 0 => tag
  | n + 1 => p n

def taggedNameLeft {E F : Set baire_space} (p : E) : taggedNameDomain E F :=
  ⟨prefixName 0 p.val, Or.inl ⟨rfl, p.property⟩⟩

def taggedNameRight {E F : Set baire_space} (p : F) : taggedNameDomain E F :=
  ⟨prefixName 1 p.val, Or.inr ⟨rfl, p.property⟩⟩

theorem continuous_taggedNameLeft {E F : Set baire_space} :
    Continuous (taggedNameLeft (E := E) (F := F)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  cases n with
  | zero => exact continuous_const
  | succ n => exact (continuous_apply n).comp continuous_subtype_val

theorem continuous_taggedNameMap {X : Type*} [TopologicalSpace X]
    {E F : Set baire_space} {g : E → X} {r : F → X}
    (hg : Continuous g) (hr : Continuous r) : Continuous (taggedNameMap g r) := by
  classical
  let S : Set (taggedNameDomain E F) := {p | p.val 0 = 0}
  have hS : IsClopen S := (isClopen_discrete ({0} : Set ℕ)).preimage
    ((continuous_apply 0).comp continuous_subtype_val)
  have hleft : ContinuousOn (taggedNameMap g r) S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let tail : S → E := fun p =>
      ⟨fun n => p.val.val (n + 1), taggedNameDomain_tail_zero p.val p.property⟩
    have ht : Continuous tail := by
      apply Continuous.subtype_mk
      exact continuous_pi (fun n => (continuous_apply (n + 1)).comp
        (continuous_subtype_val.comp continuous_subtype_val))
    convert hg.comp ht using 1
    funext p
    exact dite_eq_left p.property
  have hright : ContinuousOn (taggedNameMap g r) Sᶜ := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let tail : ↥(Sᶜ) → F := fun p =>
      ⟨fun n => p.val.val (n + 1), taggedNameDomain_tail_one p.val p.property⟩
    have ht : Continuous tail := by
      apply Continuous.subtype_mk
      exact continuous_pi (fun n => (continuous_apply (n + 1)).comp
        (continuous_subtype_val.comp continuous_subtype_val))
    convert hr.comp ht using 1
    funext p
    exact dite_eq_right p.property
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p ∈ S
  · exact hleft.continuousAt (hS.isOpen.mem_nhds hp)
  · exact hright.continuousAt (hS.compl.isOpen.mem_nhds hp)

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Schröder's universal-property
    formulation quantifies over every continuous partial map $\PartialFunctionMap{g}{\BaireSpace}{X}$ rather than only
    representations. It is equivalent to the greatest-element formulation without any Polishness assumption. Given such a
    map $g$, prefix its names by $0$ and prefix $\rho$-names by $1$ to combine $g$ and $\rho$ into a continuous
    representation of $X$. A translator from this combined representation to $\rho$ restricts to a translator from $g$ to
    $\rho$.
-/
/-- Admissibility is equivalent to lifting every continuous partial map. -/
theorem admissible_iff_partial_lifting {X : Type*} [TopologicalSpace X]
    (ρ : Representation X) : ρ.IsAdmissible ↔
    ρ.IsContinuous ∧ ∀ (E : Set baire_space) (g : E → X), Continuous g →
      ∃ h : E → ρ.domain, Continuous h ∧ ∀ p, ρ.toFun (h p) = g p := by
  classical
  constructor
  · intro hρ
    refine ⟨hρ.1, ?_⟩
    intro E g hg
    let δ : Representation X := {
      domain := taggedNameDomain E ρ.domain
      toFun := taggedNameMap g ρ.toFun
      surjective := by
        intro x
        obtain ⟨p, hp⟩ := ρ.surjective x
        refine ⟨taggedNameRight p, ?_⟩
        simpa [taggedNameMap, taggedNameRight, prefixName] using hp }
    have hδ : δ.IsContinuous := continuous_taggedNameMap hg hρ.1
    obtain ⟨f, hf, hcomm⟩ := hρ.2 δ hδ
    refine ⟨f ∘ taggedNameLeft, hf.comp continuous_taggedNameLeft, ?_⟩
    intro p
    simpa [δ, taggedNameMap, taggedNameLeft, prefixName] using hcomm (taggedNameLeft p)
  · rintro ⟨hc, hlift⟩
    exact ⟨hc, fun δ hδ => hlift δ.domain δ.toFun hδ⟩

/-- Enumerate subordinate cylinders and disjointify them to choose a locally
constant approximation to an arbitrary continuous partial map. -/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    Fix $n$. The sets
    $$U_i^n := \delta^{-1}\big(\Ball{q_i}{2^{-(n+2)}}\big) \qquad (i \in \omega)$$
    cover $E$, by density of $\{q_i\}$. Since $E$ is a subspace of the zero-dimensional space $\BaireSpace$, it has the
    relative clopen cylinder base $\{E \cap \cyl{s} : s \in \finseq{\omega}\}$. Enumerate all pairs $(s,i)$ such that
    $$E \cap \cyl{s} \IncludedIn U_i^n.$$
    These relative clopen sets cover $E$: for $p \in E$, continuity of $\delta$ gives a cylinder neighborhood of $p$ whose
    $\delta$-image lies in some ball $\Ball{q_i}{2^{-(n+2)}}$. Disjointify the enumeration by replacing each listed $E \cap
    \cyl{s_j}$ with
    $$C_j^n := \SetDifference{(E \cap \cyl{s_j})}{\bigcup_{k<j} (E \cap \cyl{s_k})}.$$
    The nonempty $C_j^n$ form a disjoint clopen partition of $E$. Define $h_n : E \to \omega$ by setting $h_n(p)=i_j$ on
    $C_j^n$, where $(s_j,i_j)$ is the $j$-th listed pair. Because the pieces are clopen, $h_n$ is continuous as a map into
    the discrete space $\omega$, and
    $$d(q_{h_n(p)}, \delta(p)) < 2^{-(n+2)}.$$
-/
theorem exists_continuous_cylinder_approximation {X : Type*} [MetricSpace X]
    (q : ℕ → X) (hq : DenseRange q) {E : Set baire_space} (g : E → X)
    (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : E → ℕ, Continuous h ∧ ∀ p, dist (q (h p)) (g p) < ε := by
  classical
  by_cases hE : Nonempty E
  · let := hE
    let Good := {v : finseq ℕ × ℕ //
      ∀ p : E, p.val ∈ cyl v.1 → dist (q v.2) (g p) < ε}
    have cover (p : E) : ∃ v : Good, p.val ∈ cyl v.val.1 := by
      obtain ⟨i, hi⟩ := hq.exists_dist_lt (g p) hε
      let U : Set E := g ⁻¹' Metric.ball (q i) ε
      have hU : IsOpen U := Metric.isOpen_ball.preimage hg
      have hp : p ∈ U := hi
      obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hU
      have hpO : p.val ∈ O := by change p ∈ Subtype.val ⁻¹' O; rw [hOU]; exact hp
      obtain ⟨s, hps, hsO⟩ := exists_cyl_subset_of_mem_open hpO hO
      refine ⟨⟨(s, i), ?_⟩, hps⟩
      intro z hz
      have hzU : z ∈ U := by rw [← hOU]; exact hsO hz
      simpa only [U, mem_preimage, Metric.mem_ball, dist_comm] using hzU
    obtain ⟨v, _⟩ := cover (Classical.arbitrary E)
    let : Nonempty Good := ⟨v⟩
    obtain ⟨e, he⟩ := exists_surjective_nat Good
    let A : ℕ → Set E := fun n => Subtype.val ⁻¹' cyl (e n).val.1
    have hA (n) : IsClopen (A n) :=
      (baire_cyl_clopen (e n).val.1).preimage continuous_subtype_val
    have hcover (p : E) : ∃ n, p ∈ A n := by
      obtain ⟨v, hv⟩ := cover p
      obtain ⟨n, rfl⟩ := he v
      exact ⟨n, hv⟩
    let pick : E → ℕ := fun p => Nat.find (hcover p)
    have hpick (p : E) : p ∈ disjointSeq A (pick p) := by
      refine ⟨Nat.find_spec (hcover p), ?_⟩
      intro hp
      obtain ⟨k, hp⟩ := mem_iUnion.mp hp
      obtain ⟨hk, hp⟩ := mem_iUnion.mp hp
      exact Nat.find_min (hcover p) (Finset.mem_range.mp hk) hp
    have hconstant {p z : E} (hz : z ∈ disjointSeq A (pick p)) : pick z = pick p := by
      by_contra hne
      exact Set.disjoint_left.mp (disjointSeq_pairwiseDisjoint A hne) (hpick z) hz
    let h : E → ℕ := fun p => (e (pick p)).val.2
    refine ⟨h, ?_, fun p => (e (pick p)).property p (hpick p).1⟩
    apply continuous_def.mpr
    intro U _hU
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    apply Filter.mem_of_superset ((disjointSeq_isClopen hA (pick p)).isOpen.mem_nhds (hpick p))
    intro z hz
    change h z ∈ U
    simpa only [h, hconstant hz, mem_preimage] using hp
  · let : IsEmpty E := not_nonempty_iff.mp hE
    exact ⟨fun p => isEmptyElim p, (continuous_iff_continuousAt.mpr fun p => isEmptyElim p), fun p => isEmptyElim p⟩

/-- Coordinatewise clopen choices translate any continuous partial map into
fast Cauchy names, with the same represented limit. -/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    Now define $f : E \to \BaireSpace$ by
    $$f(p)(n) := h_n(p).$$
    Each coordinate is continuous, hence $f$ is continuous into the product space $\BaireSpace$. For $m \ge n$,
    $$
    \begin{aligned}
    d(q_{f(p)(n)}, q_{f(p)(m)})
    &\le d(q_{f(p)(n)}, \delta(p)) + d(\delta(p), q_{f(p)(m)})\\
    &< 2^{-(n+2)} + 2^{-(m+2)}\\
    &\le 2^{-n},
    \end{aligned}
    $$
    so $f(p)$ is a Cauchy name. Moreover $q_{f(p)(n)} \to \delta(p)$, so $\rho_X(f(p))=\delta(p)$. Thus
    $\delta \ContinuouslyReducesTo \rho_X$, and since $\delta$ was arbitrary, $\rho_X$ is admissible.
-/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Let $\delta : E \to X$ be any
    continuous representation, with $E \IncludedIn \BaireSpace$. We must continuously translate each $\delta$-name into a
    Cauchy name for the same point.
-/
theorem cauchyRepresentation_lifts_partial {X : Type*} [MetricSpace X] [CompleteSpace X]
    (q : ℕ → X) (hq : DenseRange q) {E : Set baire_space} (g : E → X)
    (hg : Continuous g) :
    ∃ f : E → cauchyNameDomain q, Continuous f ∧ ∀ p, cauchyRepresentation q (f p) = g p := by
  classical
  have hchoose (n : ℕ) := exists_continuous_cylinder_approximation q hq g hg
    (show (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 2) by positivity)
  choose h hcont happrox using hchoose
  let names : E → baire_space := fun p n => h n p
  have hnames : Continuous names := continuous_pi hcont
  have hfast (p : E) : IsCauchyName q (names p) := by
    intro n m hnm
    have hn := happrox n p
    have hm := happrox m p
    have hpow : (1 / 2 : ℝ) ^ (m + 2) ≤ (1 / 2 : ℝ) ^ (n + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right hnm 2)
    have hsum : (1 / 2 : ℝ) ^ (n + 2) + (1 / 2 : ℝ) ^ (n + 2) ≤ (1 / 2 : ℝ) ^ n := by
      rw [pow_add]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]
    have ht := dist_triangle_right (q (h n p)) (q (h m p)) (g p)
    change dist (q (h n p)) (q (h m p)) ≤ _
    linarith
  let f : E → cauchyNameDomain q := fun p => ⟨names p, hfast p⟩
  refine ⟨f, hnames.subtype_mk _, ?_⟩
  intro p
  have hlim : Tendsto (fun n => q (names p n)) atTop (𝓝 (g p)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < ε :=
      exists_pow_lt_of_lt_one hε (by norm_num)
    refine ⟨N, fun n hn => ?_⟩
    have hb : (1 / 2 : ℝ) ^ (n + 2) ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact (happrox n p).trans_le hb |>.trans hN
  exact tendsto_nhds_unique (tendsto_cauchyRepresentation q (f p)) hlim

theorem cauchyRepresentationObject_isAdmissible {X : Type*}
    [MetricSpace X] [CompleteSpace X] (q : ℕ → X) (hq : DenseRange q) :
    (cauchyRepresentationObject q hq).IsAdmissible := by
  apply (admissible_iff_partial_lifting _).mpr
  refine ⟨continuous_cauchyRepresentation q, ?_⟩
  intro E g hg
  exact cauchyRepresentation_lifts_partial q hq g hg

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: statement
  kind: theorem
  title: Kreitz–Weihrauch
-/
/-- The canonical Cauchy representation is admissible, and all admissible
representations are exactly those continuously equivalent to it. -/
theorem kreitzWeihrauch_admissibility {X : Type*} [MetricSpace X] [CompleteSpace X]
    (q : ℕ → X) (hq : DenseRange q) :
    (cauchyRepresentationObject q hq).IsAdmissible ∧
      ∀ δ : Representation X, δ.IsAdmissible ↔
        ContinuouslyEquivalent δ (cauchyRepresentationObject q hq) := by
  have h := cauchyRepresentationObject_isAdmissible q hq
  exact ⟨h, fun _ => admissible_iff_continuouslyEquivalent h⟩

open scoped OnePoint

/-- The zero name is the limit of the names with a single 1 at position n. -/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    \begin{proof}
    The forward implication follows from continuity of $\rho$. Suppose that $\rho^{-1}(U)$ is open but $U$ is not.
    Since $X$ is metrizable, there are $x\in U$ and a sequence $\Sequence{x_n}{n\in\omega}$ in $\SetDifference{X}{U}$
    converging to $x$.
    In $\BaireSpace$, define
    $$
    e_\infty(k)=0,\qquad
     e_n(k)=\begin{cases}1&k=n,\\0&k\ne n.\end{cases}
    $$
    The subspace $E:=\{e_\infty\}\cup\{e_n:n\in\omega\}$ has isolated points $e_n$ and $e_n\to e_\infty$.
    Hence the map $g:E\to X$ defined by $g(e_\infty)=x$ and $g(e_n)=x_n$ is continuous.
    The partial-map form of admissibility gives a continuous $h:E\to\DomainOf{\rho}$ with $\rho\circ h=g$.
    But then
    $$
    h^{-1}(\rho^{-1}(U))=g^{-1}(U)=\{e_\infty\}
    $$
    is open in $E$, contradicting $e_n\to e_\infty$. Thus $U$ is open.
    \end{proof}
-/
noncomputable def convergentSequenceName (z : OnePoint ℕ) : baire_space :=
  open Classical in
  fun k => if z = (k : OnePoint ℕ) then 1 else 0

theorem continuous_convergentSequenceName : Continuous convergentSequenceName := by
  classical
  apply continuous_pi
  intro k
  apply (OnePoint.continuous_iff_from_nat _).mpr
  have heq : (fun n : ℕ => convergentSequenceName n k) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_gt_atTop k] with n hn
    simp [convergentSequenceName, ne_of_gt hn]
  simpa [convergentSequenceName] using tendsto_const_nhds.congr' heq.symm

theorem injective_convergentSequenceName : Injective convergentSequenceName := by
  classical
  intro x y h
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty => rfl
    | coe n =>
      have := congrFun h n
      simp [convergentSequenceName] at this
  | coe n =>
    have hval := congrFun h n
    have hy : y = (n : OnePoint ℕ) := by
      by_contra hn
      simp [convergentSequenceName, hn] at hval
    exact hy.symm

noncomputable def convergentSequenceNameHomeomorph :
    OnePoint ℕ ≃ₜ range convergentSequenceName :=
  (continuous_convergentSequenceName.isClosedEmbedding injective_convergentSequenceName).isEmbedding.toHomeomorph

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: statement
  kind: corollary
  title: Recovery of the topology
-/
/-- The closed-set formulation of the book's convergent-sequence argument. -/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: proof
  excerpt: |
    \begin{proof}
    The forward implication follows from continuity of $\rho$. Suppose that $\rho^{-1}(U)$ is open but $U$ is not.
    Since $X$ is metrizable, there are $x\in U$ and a sequence $\Sequence{x_n}{n\in\omega}$ in $\SetDifference{X}{U}$
    converging to $x$.
    In $\BaireSpace$, define
    $$
    e_\infty(k)=0,\qquad
     e_n(k)=\begin{cases}1&k=n,\\0&k\ne n.\end{cases}
    $$
    The subspace $E:=\{e_\infty\}\cup\{e_n:n\in\omega\}$ has isolated points $e_n$ and $e_n\to e_\infty$.
    Hence the map $g:E\to X$ defined by $g(e_\infty)=x$ and $g(e_n)=x_n$ is continuous.
    The partial-map form of admissibility gives a continuous $h:E\to\DomainOf{\rho}$ with $\rho\circ h=g$.
    But then
    $$
    h^{-1}(\rho^{-1}(U))=g^{-1}(U)=\{e_\infty\}
    $$
    is open in $E$, contradicting $e_n\to e_\infty$. Thus $U$ is open.
    \end{proof}
-/
theorem isQuotientMap_of_admissible {X : Type*} [TopologicalSpace X]
    [SequentialSpace X] (ρ : Representation X) (hρ : ρ.IsAdmissible) :
    IsQuotientMap ρ.toFun := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨ρ.surjective, fun C => ⟨fun hC => hC.preimage hρ.1, ?_⟩⟩
  intro hC
  apply isSeqClosed_iff_isClosed.mp
  intro u x hu hlim
  let a := OnePoint.continuousMapMkNat u x hlim
  let e := convergentSequenceNameHomeomorph
  let g : range convergentSequenceName → X := fun p => a (e.symm p)
  have hg : Continuous g := a.continuous.comp e.symm.continuous
  obtain ⟨h, hh, heq⟩ := (admissible_iff_partial_lifting ρ).mp hρ |>.2 _ g hg
  have hc : IsClosed ((fun z => h (e z)) ⁻¹' (ρ.toFun ⁻¹' C)) :=
    hC.preimage (hh.comp e.continuous)
  have ht : Tendsto (fun n : ℕ => (n : OnePoint ℕ)) atTop (𝓝 ∞) :=
    (OnePoint.continuous_iff_from_nat id).mp continuous_id
  have hmem : ∀ n : ℕ, (n : OnePoint ℕ) ∈ (fun z => h (e z)) ⁻¹' (ρ.toFun ⁻¹' C) := by
    intro n
    change ρ.toFun (h (e n)) ∈ C
    rw [heq]
    simpa [g, a, OnePoint.continuousMapMkNat, OnePoint.continuousMapMkDiscrete, OnePoint.continuousMapMk] using hu n
  have hx := hc.mem_of_tendsto ht (Eventually.of_forall hmem)
  change ρ.toFun (h (e ∞)) ∈ C at hx
  rw [heq] at hx
  simpa [g, a, OnePoint.continuousMapMkNat, OnePoint.continuousMapMkDiscrete, OnePoint.continuousMapMk] using hx

end PolishSpaceBook
