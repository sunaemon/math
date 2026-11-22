module

public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Instances.Irrational
public import Mathlib.Topology.Order
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.InductiveDimension.Functions
public import Mathlib.Analysis.Normed.Lp.LpEquiv
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

/-!
# Polish spaces

Lean entry point for `polish-space/src/polish-space-book/polish-spaces.md`.
-/

noncomputable section

open Filter Metric Set TopologicalSpace Topology
open scoped Uniformity ENNReal BoundedContinuousFunction

namespace PolishSpaceBook

/-!
## Definition

| Book term | Lean name |
| --- | --- |
| `\termdefine{Polish space}` | mathlib class `PolishSpace` |
| `\termdefine{separable}` | `IsSeparableByCountableDense` (defeq mathlib class `SeparableSpace`) |
| `\termdefine{completely metrizable}` | `IsCompletelyMetrizableByMetric` |
-/

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    $X$ is \termdefine{separable}: there exists a countable dense subset $D \IncludedIn X$.
-/
def IsSeparableByCountableDense (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∃ D : Set Y, D.Countable ∧ Dense D

theorem isSeparableByCountableDense_iff_separableSpace (Y : Type*) [TopologicalSpace Y] :
    IsSeparableByCountableDense Y ↔ SeparableSpace Y :=
  ⟨fun h => ⟨h⟩, fun h => h.exists_countable_dense⟩

abbrev IsMetricComplete (Y : Type*) [MetricSpace Y] : Prop :=
  ∀ u : ℕ -> Y, CauchySeq u -> ∃ y, Tendsto u atTop (𝓝 y)

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    $X$ is \termdefine{completely metrizable}: there exists a complete metric compatible with the topology of $X$.
-/
def IsCompletelyMetrizableByMetric (Y : Type*) [t : TopologicalSpace Y] : Prop :=
  ∃ compatibleMetric : MetricSpace Y,
    compatibleMetric.toUniformSpace.toTopologicalSpace = t ∧
      @IsMetricComplete Y compatibleMetric

theorem isMetricComplete_iff_completeSpace (Y : Type*) [MetricSpace Y] :
    IsMetricComplete Y ↔ CompleteSpace Y := by
  constructor
  · intro h
    exact Metric.complete_of_cauchySeq_tendsto h
  · intro h u hu
    have : CompleteSpace Y := h
    exact cauchySeq_tendsto_of_complete hu

theorem isCompletelyMetrizableByMetric_iff_mathlib (Y : Type*) [t : TopologicalSpace Y] :
    IsCompletelyMetrizableByMetric Y ↔ IsCompletelyMetrizableSpace Y := by
  constructor
  · rintro ⟨compatibleMetric, htopology, hcomplete⟩
    refine ⟨⟨compatibleMetric, htopology, ?_⟩⟩
    exact (@isMetricComplete_iff_completeSpace Y compatibleMetric).1 hcomplete
  · intro h
    rcases h.complete with ⟨compatibleMetric, htopology, hcomplete⟩
    exact
      ⟨compatibleMetric, htopology,
        (@isMetricComplete_iff_completeSpace Y compatibleMetric).2 hcomplete⟩

private theorem isMetricComplete_of_mathlib (Y : Type*) [MetricSpace Y] [CompleteSpace Y] :
    IsMetricComplete Y :=
  (isMetricComplete_iff_completeSpace Y).2 inferInstance

private theorem isMetricComplete_of_upgraded (Y : Type*) [TopologicalSpace Y]
    (m : UpgradedIsCompletelyMetrizableSpace Y) :
    @IsMetricComplete Y m.toMetricSpace :=
  (@isMetricComplete_iff_completeSpace Y m.toMetricSpace).2 m.toCompleteSpace

variable {X : Type*} [TopologicalSpace X] [PolishSpace X]

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: statement
  kind: proposition
  title: Separability and second countability
-/
-- The countable-basis construction is provided by mathlib's uniform-space
-- version; the text specializes it to rational-radius balls in a compatible metric.
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    \begin{proof}
    Choose a compatible metric. If $D$ is a countable dense subset, the balls $\Ball{a}{q}$ with $a\in D$ and
    $q\in\RestrictedSet{\QQ}{>0}$ form a countable base. Indeed, for $x\in U$ with $U$ open, choose $\varepsilon>0$
    with $\Ball{x}{\varepsilon}\IncludedIn U$, then $a\in D$ with $d(x,a)<\varepsilon/3$ and a rational $q$ with
    $d(x,a)<q<\varepsilon-d(x,a)$. The triangle inequality gives
    $x\in\Ball{a}{q}\IncludedIn\Ball{x}{\varepsilon}\IncludedIn U$.
    Conversely, choose one point from each nonempty member of a countable base. The chosen points form a countable dense
    subset, since every nonempty open set contains a nonempty basic open set.
    \end{proof}
-/
theorem metrizable_separable_iff_second_countable (Y : Type*) [TopologicalSpace Y]
    [PseudoMetrizableSpace Y] :
    SeparableSpace Y ↔ SecondCountableTopology Y := by
  constructor
  · intro hsep
    have : SeparableSpace Y := hsep
    let : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
    have : (𝓤 Y).IsCountablyGenerated :=
      pseudoMetrizableSpaceUniformity_countably_generated Y
    exact UniformSpace.secondCountable_of_separable Y
  · intro
    infer_instance

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: recall
  title: Two facts about metrizable spaces
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: statement
  kind: corollary
  title: Separability of subspaces
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    \begin{proof}
    A countable base $\mathcal B$ for $X$ restricts to the countable base $\{B\cap A:B\in\mathcal B\}$ for a subspace
    $A\IncludedIn X$. Thus $A$ is second countable, and choosing one point from each nonempty basic open set proves
    that $A$ is separable. This also covers the empty subspace, whose empty subset is dense.
    \end{proof}
-/
/-- A countable base restricts to the subspace, where choosing a point in each
nonempty basic open set gives separability. -/
theorem metrizable_subspace_separable (Y : Type*) [TopologicalSpace Y]
    [PseudoMetrizableSpace Y] [SeparableSpace Y] (A : Set Y) : SeparableSpace A := by
  have : SecondCountableTopology Y :=
    (metrizable_separable_iff_second_countable Y).mp inferInstance
  have : SecondCountableTopology A := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  infer_instance

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: statement
  kind: lemma
  title: Closed sets and sequences
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    \begin{proof}
    A closed set contains every limit of a sequence of its points. Conversely, let $A$ contain every such limit and
    let $x\in\Closure{A}$. Choose a countable neighborhood base at $x$ and replace each member by the intersection of
    itself and all its predecessors to obtain a decreasing base $\Sequence{U_n}{n\in\omega}$. Each $U_n$ meets $A$, so choose
    $x_n\in A\cap U_n$. Then $x_n\to x$, and hence $x\in A$. Thus $\Closure{A}\IncludedIn A$, so $A$ is closed.
    \end{proof}
-/
theorem first_countable_closed_iff_seq_closed (Y : Type*) [TopologicalSpace Y]
    [FirstCountableTopology Y] (s : Set Y) :
    IsClosed s ↔ IsSeqClosed s := by
  constructor
  · exact IsClosed.isSeqClosed
  · intro hs
    apply isClosed_of_closure_subset
    intro x hx
    obtain ⟨u, hu, hxlim⟩ := mem_closure_iff_seq_limit.mp hx
    exact hs hu hxlim

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: statement
  kind: proposition
  title: Sequential criterion for continuity
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    \begin{proof}
    Continuity preserves convergence: the inverse image of a neighborhood of $f(x)$ is a neighborhood of $x$.
    Conversely, suppose $f$ preserves convergence, and let $C\IncludedIn Y$ be closed. If a sequence in $f^{-1}(C)$
    converges to $x$, its image converges to $f(x)\in C$, since $C$ is closed. Thus $f^{-1}(C)$ contains the limit of
    every convergent sequence drawn from it. The preceding lemma shows that $f^{-1}(C)$ is closed, so $f$ is continuous.
    Every metrizable space is first countable: for a compatible metric, the balls $\Ball{x}{1/(n+1)}$, $n\in\omega$,
    form a countable neighborhood base at $x$.
    \end{proof}
-/
/-- The converse follows by checking closed preimages with the sequential
closed-set criterion. No separation axiom is needed on the codomain. -/
theorem first_countable_continuous_iff_seqContinuous {Y Z : Type*}
    [TopologicalSpace Y] [FirstCountableTopology Y] [TopologicalSpace Z] (f : Y → Z) :
    Continuous f ↔ SeqContinuous f := by
  constructor
  · exact Continuous.seqContinuous
  · intro hf
    apply continuous_iff_isClosed.mpr
    intro C hC
    apply (first_countable_closed_iff_seq_closed Y (f ⁻¹' C)).mpr
    intro u x hu hx
    exact hC.mem_of_tendsto (hf hx) (Filter.Eventually.of_forall hu)

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: recall
  title: Two facts about metrizable spaces
-/
/-- A compatible metric supplies a countable neighborhood base, so sequence
convergence detects continuity. The codomain may be any topological space. -/
theorem metrizable_continuous_iff_seqContinuous {Y Z : Type*}
    [TopologicalSpace Y] [PseudoMetrizableSpace Y] [TopologicalSpace Z] (f : Y → Z) :
    Continuous f ↔ SeqContinuous f := by
  constructor
  · intro hf u x hx
    exact (hf.tendsto x).comp hx
  · exact (first_countable_continuous_iff_seqContinuous f).mpr

/-- The real function used to replace a nonnegative distance by a bounded one. -/
noncomputable abbrev boundedMetricTransform (t : ℝ) : ℝ := t / (1 + t)

/-- The bounding map $\phi(t)=t/(1+t)$ does not increase distances: $\phi(t)\le t$ for $t\ge 0$. -/
private lemma phi_le_self {a : ℝ} (ha : 0 ≤ a) : a / (1 + a) ≤ a := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg a]

/-- $\phi(t)=t/(1+t)$ is monotone on $[0,\infty)$. -/
private lemma phi_le_phi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a / (1 + a) ≤ b / (1 + b) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- $\phi(t)=t/(1+t)$ is strictly monotone on $[0,\infty)$. -/
private lemma phi_lt_phi_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a / (1 + a) < b / (1 + b) ↔ a < b := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- Subadditivity of $\phi(t)=t/(1+t)$, the key step in the triangle inequality for $\hat d$. -/
private lemma phi_add_le_phi_add_phi {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / (1 + (a + b)) ≤ a / (1 + a) + b / (1 + b) := by
  have hsplit : (a + b) / (1 + (a + b))
      = a / (1 + (a + b)) + b / (1 + (a + b)) := by ring
  rw [hsplit]
  gcongr <;> linarith

private lemma min_add_one_le_min_add_min {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min (a + b) 1 ≤ min a 1 + min b 1 := by
  by_cases ha1 : a ≤ 1
  · by_cases hb1 : b ≤ 1
    · rw [min_eq_left ha1, min_eq_left hb1]
      exact min_le_left _ _
    · rw [min_eq_left ha1, min_eq_right (le_of_not_ge hb1)]
      exact (min_le_right _ _).trans (by linarith)
  · rw [min_eq_right (le_of_not_ge ha1)]
    exact (min_le_right _ _).trans (by
      have hbmin : 0 ≤ min b 1 := le_min hb zero_le_one
      linarith)

private lemma min_lt_min_one_iff {a ε : ℝ} (_ha : 0 ≤ a) (_hε : 0 < ε)
    (h : min a 1 < min ε 1) :
    a < ε := by
  by_cases hε1 : ε ≤ 1
  · have h' : min a 1 < ε := by simpa [min_eq_left hε1] using h
    by_cases ha1 : a ≤ 1
    · simpa [min_eq_left ha1] using h'
    · have h_one_lt_eps : (1 : ℝ) < ε := by
        simpa [min_eq_right (le_of_not_ge ha1)] using h'
      linarith
  · have h' : min a 1 < 1 := by simpa [min_eq_right (le_of_not_ge hε1)] using h
    by_cases ha1 : a ≤ 1
    · have ha_lt_one : a < 1 := by simpa [min_eq_left ha1] using h'
      linarith [lt_of_not_ge hε1]
    · have : (1 : ℝ) < 1 := by
        simp [min_eq_right (le_of_not_ge ha1)] at h'
      linarith

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: lemma
  title: Bounded complete compatible metric
-/
/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Write $\phi(t):=t/(1+t)$ for $t\ge 0$, so that $\hat d=\phi\circ d$. The map $\phi$ is strictly increasing, vanishes
    only at $0$, and is subadditive: for $a,b\ge 0$,
    $$
    \phi(a+b)=\frac{a+b}{1+a+b}=\frac{a}{1+a+b}+\frac{b}{1+a+b}\le\frac{a}{1+a}+\frac{b}{1+b}=\phi(a)+\phi(b).
    $$
    
    Hence $\hat d$ is symmetric, vanishes exactly on the diagonal, and satisfies the triangle inequality
    $$
    \hat d(x,z)=\phi(d(x,z))\le\phi\bigl(d(x,y)+d(y,z)\bigr)\le\hat d(x,y)+\hat d(y,z),
    $$
    where the first step uses monotonicity and the second subadditivity.
    
    Since $\phi$ is a strictly increasing bijection of $\LeftClosedInterval{0}{\infty}$ onto
    $\LeftClosedInterval{0}{1}$, for every $0<r<1$ the inequality
    $\hat d(x,y)<r$ is equivalent to $d(x,y)<r/(1-r)$, so the $\hat d$-ball of radius $r$ about a point equals the
    $d$-ball of radius $r/(1-r)$ about it. As $r$ ranges over $\OpenInterval{0}{1}$ the radius $r/(1-r)$ ranges over all of
    $\OpenInterval{0}{\infty}$. Thus the $\hat d$-balls of radius less than $1$ coincide with the $d$-balls;
    these balls form a base
    for both metric topologies, so the two metrics induce the same topology.
    
    It remains to check completeness. Since $\phi(t)\le t$, we have $\hat d\le d$, so every $d$-Cauchy sequence is
    $\hat d$-Cauchy. Conversely, let $\Sequence{x_n}{n\in\omega}$ be $\hat d$-Cauchy and fix $\epsilon>0$. Eventually
    $\hat d(x_m,x_n)<\phi(\epsilon)$, and since $\phi$ is strictly increasing this gives $d(x_m,x_n)<\epsilon$. Thus
    $\Sequence{x_n}{n\in\omega}$ is $d$-Cauchy, so it $d$-converges to some $x$, and since $\hat d\le d$ it $\hat
    d$-converges to $x$ as well.
    
    \end{proof}
-/
theorem complete_compatible_metric_bounded_by_one (Y : Type*) [originalMetric : MetricSpace Y]
    (originalComplete : IsMetricComplete Y) :
    ∃ boundedMetric : MetricSpace Y,
      (boundedMetric.toUniformSpace.toTopologicalSpace =
        originalMetric.toUniformSpace.toTopologicalSpace) ∧
        ((@IsMetricComplete Y boundedMetric) ∧
          ((∀ x y : Y,
            @dist Y (boundedMetric.toDist) x y =
              @dist Y (originalMetric.toDist) x y / (1 + @dist Y (originalMetric.toDist) x y)) ∧
            (∀ x y : Y, @dist Y (boundedMetric.toDist) x y ≤ 1))) := by
  let originalDist : Y -> Y -> ℝ := fun x y => @dist Y originalMetric.toDist x y
  let boundedDist : Y -> Y -> ℝ := fun x y => boundedMetricTransform (originalDist x y)
  have hnn : ∀ x y : Y, (0 : ℝ) ≤ originalDist x y := fun x y => dist_nonneg
  have boundedDist_le_one : ∀ x y : Y, boundedDist x y ≤ 1 := by
    intro x y
    show originalDist x y / (1 + originalDist x y) ≤ 1
    rw [div_le_one (by linarith [hnn x y])]
    linarith [hnn x y]
  let boundedMetric : MetricSpace Y := by
    refine MetricSpace.ofDistTopology boundedDist (fun x => ?_) (fun x y => ?_)
      (fun x y z => ?_) (fun t => ?_) (fun x y hxy => ?_)
    · simp [boundedDist, originalDist]
    · simp [boundedDist, originalDist, dist_comm]
    · calc
        boundedDist x z = originalDist x z / (1 + originalDist x z) := rfl
        _ ≤ (originalDist x y + originalDist y z) / (1 + (originalDist x y + originalDist y z)) :=
          phi_le_phi dist_nonneg (dist_triangle x y z)
        _ ≤ originalDist x y / (1 + originalDist x y)
              + originalDist y z / (1 + originalDist y z) :=
          phi_add_le_phi_add_phi dist_nonneg dist_nonneg
        _ = boundedDist x y + boundedDist y z := rfl
    · have radius_iff (x y : Y) (r : ℝ) (_hr : 0 < r) (hr1 : r < 1) :
          boundedDist x y < r ↔ originalDist x y < r / (1 - r) := by
        change originalDist x y / (1 + originalDist x y) < r ↔
          originalDist x y < r / (1 - r)
        rw [div_lt_iff₀ (by linarith [hnn x y]), lt_div_iff₀ (by linarith)]
        constructor <;> intro h <;> nlinarith
      have radius_range (ε : ℝ) (hε : 0 < ε) :
          ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r / (1 - r) = ε := by
        have hden : 0 < 1 + ε := by linarith
        have hlt : ε / (1 + ε) < 1 := (div_lt_one hden).2 (by linarith)
        refine ⟨ε / (1 + ε), div_pos hε hden, hlt, ?_⟩
        apply (div_eq_iff (ne_of_gt (sub_pos.mpr hlt))).2
        field_simp
        ring
      constructor
      · intro ht x hx
        rcases (Metric.isOpen_iff (α := Y)).1 ht x hx with ⟨ε, hεpos, hε⟩
        obtain ⟨r, hr, hr1, hinverse⟩ := radius_range ε hεpos
        refine ⟨r, hr, fun y hy => ?_⟩
        have hdist : originalDist x y < ε := by
          rw [← hinverse]
          exact (radius_iff x y r hr hr1).1 hy
        exact hε <| by simpa [originalDist, dist_comm] using hdist
      · intro ht
        exact (Metric.isOpen_iff (α := Y)).2 fun x hx => by
          rcases ht x hx with ⟨ε, hεpos, hε⟩
          let r := min ε (1 / 2)
          have hr : 0 < r := lt_min hεpos (by norm_num)
          have hr1 : r < 1 := (min_le_right ε (1 / 2)).trans_lt (by norm_num)
          refine ⟨r / (1 - r), div_pos hr (sub_pos.mpr hr1), fun y hy => ?_⟩
          have hxy : originalDist x y < r / (1 - r) := by
            simpa [originalDist, dist_comm] using hy
          exact hε y (((radius_iff x y r hr hr1).2 hxy).trans_le (min_le_left _ _))
    · have hxy' : originalDist x y / (1 + originalDist x y) = 0 := hxy
      rcases div_eq_zero_iff.1 hxy' with h | h
      · exact eq_of_dist_eq_zero (by simpa [originalDist] using h)
      · exfalso; linarith [hnn x y]
  have boundedMetric_dist :
      ∀ x y : Y, @dist Y (boundedMetric.toDist) x y = boundedDist x y := by
    intro x y
    rfl
  have boundedComplete : @IsMetricComplete Y boundedMetric := by
    let : MetricSpace Y := boundedMetric
    intro u hu
    have h_bounded_cauchy :
        ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, boundedDist (u m) (u n) < ε := by
      intro ε hεpos
      rcases (Metric.cauchySeq_iff.1 hu) ε hεpos with ⟨N, hN⟩
      refine ⟨N, fun m hm n hn => ?_⟩
      simpa [boundedMetric_dist] using hN m hm n hn
    have h_original_cauchy : (letI : MetricSpace Y := originalMetric; CauchySeq u) := by
      let : MetricSpace Y := originalMetric
      rw [Metric.cauchySeq_iff]
      intro ε hεpos
      have hδpos : 0 < ε / (1 + ε) := div_pos hεpos (by linarith)
      rcases h_bounded_cauchy (ε / (1 + ε)) hδpos with ⟨N, hN⟩
      refine ⟨N, fun m hm n hn => ?_⟩
      have hbounded : dist (u m) (u n) / (1 + dist (u m) (u n)) < ε / (1 + ε) := by
        simpa [boundedDist, originalDist] using hN m hm n hn
      exact (phi_lt_phi_iff dist_nonneg hεpos.le).1 hbounded
    obtain ⟨x, hx⟩ : ∃ x, Tendsto u atTop (𝓝 x) := by
      let : MetricSpace Y := originalMetric
      exact originalComplete u h_original_cauchy
    exact ⟨x, hx⟩
  have h_dist_eq :
      ∀ x y : Y,
        @dist Y (boundedMetric.toDist) x y =
          @dist Y (originalMetric.toDist) x y / (1 + @dist Y (originalMetric.toDist) x y) := by
    intro x y
    exact boundedMetric_dist x y
  have h_le_one : ∀ x y : Y, @dist Y (boundedMetric.toDist) x y ≤ 1 := by
    intro x y
    rw [boundedMetric_dist]
    exact boundedDist_le_one x y
  refine ⟨boundedMetric, ?_⟩
  refine And.intro rfl ?_
  refine And.intro boundedComplete ?_
  refine And.intro ?_ h_le_one
  intro x y
  exact h_dist_eq x y

/-!
## Examples

| Book term | Lean name |
| --- | --- |
| `\termdefine{Euclidean space}` | `euclidean_space n` |
| `\termdefineas{irrational}{irrationals}` | mathlib predicate `Irrational` |
| `\termdefine{infinite-dimensional separable Banach space}` | theorem `infinite_dimensional_separable_banach_space_polish` |
| `\ell^\infty` | `ell_infty` |
-/

theorem metric_complete_separable_polish (Y : Type*) [MetricSpace Y]
    (h_complete : IsMetricComplete Y) [SeparableSpace Y] :
    PolishSpace Y := by
  have h_second_countable : SecondCountableTopology Y :=
    (metrizable_separable_iff_second_countable Y).1 inferInstance
  have h_completely_metrizable : IsCompletelyMetrizableSpace Y := by
    exact (isCompletelyMetrizableByMetric_iff_mathlib Y).1
      ⟨inferInstance, rfl, h_complete⟩
  exact
    { toSecondCountableTopology := h_second_countable
      toIsCompletelyMetrizableSpace := h_completely_metrizable }

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    For $n=1$, the rationals $\QQ \IncludedIn \R$ are
        countable and dense in $\R$, while the standard metric $d(x, y) = \Abs{x - y}$ is complete on $\R$.
-/
theorem real_polish : PolishSpace ℝ :=
  metric_complete_separable_polish ℝ (isMetricComplete_of_mathlib ℝ)

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    \termdefine{Euclidean space} $\R^n$.
-/
/-- Book term `\termdefine{Euclidean space}`: `ℝ^n` is modeled as `Fin n -> ℝ`. -/
abbrev euclidean_space (n : ℕ) : Type :=
  Fin n -> ℝ

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The higher-dimensional cases use the Euclidean metric and the countable dense set $\QQ^n$.
-/
theorem euclidean_space_polish (n : ℕ) : PolishSpace (euclidean_space n) :=
  metric_complete_separable_polish (euclidean_space n) (isMetricComplete_of_mathlib _)

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The \termdefineas{irrational}{irrationals} $\SetDifference{\R}{\QQ}$ with the subspace topology from $\R$.
        See §{sec:alexandrov-theorem} for the proof.
-/
-- Follows the book's duality route: `ℚ` is a countable union of closed singletons, so its
-- complement is a countable intersection of open sets. (`rationals_are_fsigma` and
-- `IsFsigma.isGdelta_compl` package the same argument generically further below, but are not yet
-- available at this point in the file, so the argument is inlined here.)
theorem irrationals_are_gdelta :
    IsGδ ({x : ℝ | Irrational x} : Set ℝ) := by
  have h_compl : (Set.range ((↑) : ℚ -> ℝ))ᶜ = {x : ℝ | Irrational x} := by
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq, Irrational]
  rw [← h_compl, Set.range_eq_iUnion, compl_iUnion]
  exact IsGδ.iInter_of_isOpen fun q => isClosed_singleton.isOpen_compl

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    Every \termdefine{separable Banach space} with its norm topology, for example the real sequence spaces $\ell^p$ for
        $1\le p<\infty$ and the space $C(\ClosedInterval{0}{1})$ of real-valued continuous functions.
-/
theorem separable_banach_space_polish (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h_complete : IsMetricComplete E) [SeparableSpace E] :
    PolishSpace E :=
  metric_complete_separable_polish E h_complete

/-- Finite-exponent real sequence spaces are separable: the countable coordinate
unit vectors have dense real linear span, by the finite-support approximations. -/
theorem real_lp_separable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    SeparableSpace (lp (fun _ : ℕ => ℝ) p) := by
  let S : Submodule ℝ (lp (fun _ : ℕ => ℝ) p) :=
    Submodule.span ℝ (Set.range fun n : ℕ => lp.single p n (1 : ℝ))
  have hs : IsSeparable (S : Set (lp (fun _ : ℕ => ℝ) p)) :=
    (Set.countable_range fun n : ℕ => lp.single p n (1 : ℝ)).isSeparable.span
  have hd : Dense (S : Set (lp (fun _ : ℕ => ℝ) p)) := by
    intro f
    apply mem_closure_of_tendsto (lp.hasSum_single hp f)
    apply Filter.Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro n _
    have h := S.smul_mem (f n) (Submodule.subset_span (Set.mem_range_self n))
    simpa only [← lp.single_smul, smul_eq_mul, mul_one] using h
  exact hd.isSeparable_iff.mp hs

/-- The real sequence-space Banach examples have their actual completeness and
separability instances, with a finite exponent at least one. -/
theorem real_lp_polish (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p < ⊤) :
    PolishSpace (lp (fun _ : ℕ => ℝ) p) := by
  let : SeparableSpace (lp (fun _ : ℕ => ℝ) p) := real_lp_separable p hp.ne
  exact separable_banach_space_polish (lp (fun _ : ℕ => ℝ) p)
    (isMetricComplete_of_mathlib _)

/-- Real-valued continuous functions on a subset of the real line, with its induced topology. -/
abbrev real_continuous_functions (S : Set ℝ) : Type :=
  ContinuousMap S ℝ

/-- The continuous-function example is a separable complete Banach space with the uniform norm. -/
theorem continuous_unit_interval_polish :
    PolishSpace (real_continuous_functions (Set.Icc (0 : ℝ) 1)) :=
  separable_banach_space_polish (real_continuous_functions (Set.Icc (0 : ℝ) 1))
    (isMetricComplete_of_mathlib _)

/-- The book phrases this for the infinite-dimensional case, but the proof does
not use that hypothesis: every separable complete Banach space is Polish
regardless of dimension. `_hE` is kept (underscore-prefixed, deliberately unused)
only to mirror the book statement. -/
theorem infinite_dimensional_separable_banach_space_polish (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (h_complete : IsMetricComplete E) [SeparableSpace E]
    (_hE : ¬ FiniteDimensional ℝ E) :
    PolishSpace E :=
  separable_banach_space_polish E h_complete

/-- Book term `\termdefine{Cantor space}`: `2^ω`, with `2` modeled by `Bool`. -/
abbrev cantor_space : Type :=
  ℕ -> Bool

/- In the book's notation, `{0,1}^ω` is represented in Lean as `cantor_space`.
The function below embeds those binary sequences into the bounded real sequences. -/
def bounded_binary_sequence (b : cantor_space) : ℕ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfDiscrete
    (fun n => if b n then (1 : ℝ) else 0) 1 (by
      intro x y
      by_cases hx : b x <;> by_cases hy : b y <;> simp [hx, hy, dist_eq_norm])

theorem bounded_binary_sequence_dist {b c : cantor_space} (h : b ≠ c) :
    dist (bounded_binary_sequence b) (bounded_binary_sequence c) = 1 := by
  have hle : dist (bounded_binary_sequence b) (bounded_binary_sequence c) ≤ 1 := by
    rw [BoundedContinuousFunction.dist_le zero_le_one]
    intro n
    by_cases hb : b n <;> by_cases hc : c n <;>
      simp [bounded_binary_sequence, hb, hc, dist_eq_norm]
  have hge : 1 ≤ dist (bounded_binary_sequence b) (bounded_binary_sequence c) := by
    rw [Function.ne_iff] at h
    rcases h with ⟨n, hn⟩
    have hpoint : dist ((bounded_binary_sequence b) n) ((bounded_binary_sequence c) n) = 1 := by
      by_cases hb : b n <;> by_cases hc : c n <;>
        simp [bounded_binary_sequence, hb, hc, dist_eq_norm] at *
    simpa [hpoint] using
      BoundedContinuousFunction.dist_coe_le_dist
        (f := bounded_binary_sequence b) (g := bounded_binary_sequence c) n
  exact le_antisymm hle hge

theorem cantor_space_not_countable : ¬ Countable cantor_space := by
  intro hcount
  have : Countable cantor_space := hcount
  rcases exists_surjective_nat cantor_space with ⟨f, hf⟩
  let g : cantor_space := fun n => ! f n n
  rcases hf g with ⟨k, hk⟩
  have hkg := congrFun hk k
  by_cases hfk : f k k <;> simp [g, hfk] at hkg

theorem bounded_real_sequences_not_separable : ¬ SeparableSpace (ℕ →ᵇ ℝ) := by
  intro hsep
  have : SeparableSpace (ℕ →ᵇ ℝ) := hsep
  let balls : cantor_space -> Set (ℕ →ᵇ ℝ) := fun b =>
    ball (bounded_binary_sequence b) (1 / 3 : ℝ)
  have hdisjoint : Pairwise fun b c => Disjoint (balls b) (balls c) := by
    intro b c hbc
    rw [Set.disjoint_left]
    intro z hzb hzc
    have hbz : dist (bounded_binary_sequence b) z < 1 / 3 := by
      simpa [balls, dist_comm] using hzb
    have hcz : dist z (bounded_binary_sequence c) < 1 / 3 := by
      simpa [balls] using hzc
    have hbc_dist_lt : dist (bounded_binary_sequence b) (bounded_binary_sequence c) < 1 := by
      calc
        dist (bounded_binary_sequence b) (bounded_binary_sequence c) ≤
            dist (bounded_binary_sequence b) z + dist z (bounded_binary_sequence c) :=
          dist_triangle _ _ _
        _ < 1 / 3 + 1 / 3 := add_lt_add hbz hcz
        _ < 1 := by norm_num
    have hdist_eq : dist (bounded_binary_sequence b) (bounded_binary_sequence c) = 1 :=
      bounded_binary_sequence_dist hbc
    linarith
  have hopen : ∀ b, IsOpen (balls b) := fun _ => isOpen_ball
  have hnonempty : ∀ b, (balls b).Nonempty := fun b =>
    ⟨bounded_binary_sequence b, mem_ball_self (by norm_num)⟩
  have hcountable : Countable cantor_space :=
    Pairwise.countable_of_isOpen_disjoint hdisjoint hopen hnonempty
  exact cantor_space_not_countable hcountable

theorem bounded_real_sequences_complete : IsMetricComplete (ℕ →ᵇ ℝ) :=
  isMetricComplete_of_mathlib (ℕ →ᵇ ℝ)

theorem bounded_real_sequences_not_polish : ¬ PolishSpace (ℕ →ᵇ ℝ) := by
  intro hpolish
  have : PolishSpace (ℕ →ᵇ ℝ) := hpolish
  have hsep : SeparableSpace (ℕ →ᵇ ℝ) :=
    (metrizable_separable_iff_second_countable _).2 inferInstance
  exact bounded_real_sequences_not_separable hsep

/- The book's `ℓ∞` is formalized both as bounded real sequences `ℕ →ᵇ ℝ`
and as mathlib's `lp (fun _ : ℕ => ℝ) ∞`; `lpBCFₗᵢ` identifies these models. -/
/-- Book notation `ℓ∞`: bounded real sequences with the sup norm. -/
abbrev ell_infty : Type :=
  lp (fun _ : ℕ => ℝ) ∞

theorem ell_infty_real_sequences_complete :
    IsMetricComplete ell_infty :=
  isMetricComplete_of_mathlib ell_infty

theorem ell_infty_real_sequences_not_separable :
    ¬ SeparableSpace ell_infty := by
  intro hsep
  let : SeparableSpace ell_infty := hsep
  let e : ell_infty ≃ₗᵢ[ℝ] ℕ →ᵇ ℝ := lpBCFₗᵢ ℝ ℝ
  have hsep_bounded : SeparableSpace (ℕ →ᵇ ℝ) :=
    e.surjective.denseRange.separableSpace e.continuous
  exact bounded_real_sequences_not_separable hsep_bounded

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The Banach space $\ell^\infty$ with the sup norm is complete but not separable, hence not Polish. Indeed, the binary
        sequences in $\seqPower{\{0,1\}}{\omega}$ are pairwise distance $1$ apart, so the balls of radius $1/3$ around them
        are pairwise disjoint. A countable dense set would have to meet each of these uncountably many disjoint balls,
        which is impossible.
-/
theorem ell_infty_real_sequences_not_polish :
    ¬ PolishSpace ell_infty := by
  intro hpolish
  have : PolishSpace ell_infty := hpolish
  have hsep : SeparableSpace ell_infty :=
    (metrizable_separable_iff_second_countable _).2 inferInstance
  exact ell_infty_real_sequences_not_separable hsep

/-! ## Key properties -/

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: proposition
  title: Closed subspaces
-/
/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $X$ be a Polish space, choose a complete compatible metric $d$ on $X$, and let $C \IncludedIn X$ be closed. The
    restriction $\restrict{d}{C\times C}$ induces the subspace topology and is complete: a Cauchy sequence in $C$ is Cauchy
    in $X$, hence converges in $X$, and the limit lies in $C$ because $C$ is closed. The subspace $C$ is separable.
    \end{proof}
-/
theorem closed_subspace_polish {C : Set X} (hC : IsClosed C) :
    PolishSpace C := by
  let completeMetricOnX : UpgradedIsCompletelyMetrizableSpace X :=
    upgradeIsCompletelyMetrizable X
  let : MetricSpace X := completeMetricOnX.toMetricSpace
  have hX_complete : IsMetricComplete X :=
    isMetricComplete_of_upgraded X completeMetricOnX
  let dC : C -> C -> ℝ := fun x y => dist (x : X) (y : X)
  let metricC : MetricSpace C := inferInstance
  have metricC_dist :
      ∀ x y : C, @dist C metricC.toDist x y = dC x y := by
    intro x y
    rfl
  let : MetricSpace C := metricC
  have h_separable : SeparableSpace C := metrizable_subspace_separable X C
  have h_second_countable : SecondCountableTopology C :=
    (metrizable_separable_iff_second_countable C).mp h_separable
  have h_complete : IsMetricComplete C := by
    intro u hu
    have h_cauchy_in_X : CauchySeq (((↑) : C -> X) ∘ u) :=
      uniformContinuous_subtype_val.comp_cauchySeq hu
    rcases hX_complete _ h_cauchy_in_X with ⟨x, hxlim⟩
    have hxmem : x ∈ C :=
      hC.mem_of_tendsto hxlim (Filter.Eventually.of_forall fun n => (u n).2)
    refine ⟨⟨x, hxmem⟩, ?_⟩
    exact (Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff).2 hxlim
  have h_completely_metrizable : IsCompletelyMetrizableSpace C := by
    exact (isCompletelyMetrizableByMetric_iff_mathlib C).1
      ⟨metricC, rfl, h_complete⟩
  exact
    { toSecondCountableTopology := h_second_countable
      toIsCompletelyMetrizableSpace := h_completely_metrizable }

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: proposition
  title: Open subspaces
-/
/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Choose a complete compatible metric $d$ on $X$, and let $U \IncludedIn X$ be open.
    The case $U = X$ is trivial, so assume $U \ne X$. The restricted metric
    $\restrict{d}{U\times U}$ is generally not complete, because a Cauchy sequence in $U$ may converge in $X$ to a boundary
    point. Define a new metric on $U$ by
    $$d'(x, y) \;:=\; d(x, y) \;+\; \Abs{\frac{1}{d(x,\, \SetDifference{X}{U})} - \frac{1}{d(y,\, \SetDifference{X}{U})}
    }.$$
    
    Here the distance to a nonempty set is defined by $d(z,S):=\inf\{d(z,s):s\in S\}$.
    
    This is well-defined because $d(x, \SetDifference{X}{U})>0$ for every $x\in U$.
    The absolute-value term is a pseudometric obtained by pulling back the Euclidean metric along
    $z \mapsto 1/d(z, \SetDifference{X}{U})$, so adding it to $d$ gives a metric. Since $d \le d'$, convergence in
    $d'$ implies convergence in $d$.
    
    Conversely, suppose $x_n \to x$ in $d$ and all $x_n,x$ lie in $U$. The function
    $z \mapsto d(z, \SetDifference{X}{U})$ is continuous by the distance estimate in
    \BookSectionLink{sec:appendix-distance-to-set}{the appendix section on distance to a set} and is positive at $x$, so
    $$\frac{1}{d(x_n, \SetDifference{X}{U})} \longrightarrow \frac{1}{d(x, \SetDifference{X}{U})}.$$
    Hence $d'(x_n,x)\to 0$. The identity maps between the two metric topologies therefore preserve convergence of
    sequences in both directions, so both maps are continuous and $d'$ induces the subspace topology.
    
    The metric $d'$ is complete. Suppose $\Sequence{x_n}{n\in\omega}$ is $d'$-Cauchy in $U$. Then the sequence
    $$\Sequence{1/d(x_n,\SetDifference{X}{U})}{n\in\omega}$$
    is Cauchy in $\R$ and hence bounded. Thus the points $x_n$ stay a positive distance from $\SetDifference{X}{U}$. The
    sequence is also $d$-Cauchy, so it converges in $X$ to some point $x$. The positive distance from
    $\SetDifference{X}{U}$ forces $x \in U$.
    
    The preceding topology comparison gives $x_n \to x$ in $d'$.
    The subspace $U$ is separable.
    \end{proof}
-/
theorem open_subspace_polish {U : Set X} (hU : IsOpen U) :
    PolishSpace U := by
  by_cases hU_all : U = Set.univ
  · subst U
    exact closed_subspace_polish isClosed_univ
  have h_compl_nonempty : Uᶜ.Nonempty := Set.nonempty_compl.mpr hU_all
  let completeMetricOnX : UpgradedIsCompletelyMetrizableSpace X :=
    upgradeIsCompletelyMetrizable X
  let : MetricSpace X := completeMetricOnX.toMetricSpace
  have hX_complete : IsMetricComplete X :=
    isMetricComplete_of_upgraded X completeMetricOnX
  let Uopen : Opens X := ⟨U, hU⟩
  change PolishSpace Uopen
  let d' : Uopen.CompleteCopy -> Uopen.CompleteCopy -> ℝ := fun x y =>
    dist x.1 y.1 + |1 / infDist x.1 Uopenᶜ - 1 / infDist y.1 Uopenᶜ|
  have d'_val_le :
      ∀ x y : Uopen.CompleteCopy, dist x.1 y.1 ≤ d' x y := fun x y =>
    le_add_of_nonneg_right (abs_nonneg _)
  -- The sequential criterion supplies the neighborhood comparison required by
  -- `PseudoMetricSpace.ofDistTopology`, using the sequence argument in the text.
  let d'_metric : MetricSpace Uopen.CompleteCopy := by
    refine @MetricSpace.ofT0PseudoMetricSpace Uopen.CompleteCopy
      (PseudoMetricSpace.ofDistTopology d'
        (fun x => ?_) (fun x y => ?_) (fun x y z => ?_) fun t => ?_) _
    · simp [d']
    · calc
        d' x y =
            dist x.1 y.1 + |1 / infDist x.1 Uopenᶜ - 1 / infDist y.1 Uopenᶜ| := rfl
        _ = dist y.1 x.1 + |1 / infDist y.1 Uopenᶜ - 1 / infDist x.1 Uopenᶜ| := by
          rw [dist_comm, abs_sub_comm]
        _ = d' y x := rfl
    · calc
        d' x z =
            dist x.1 z.1 + |1 / infDist x.1 Uopenᶜ - 1 / infDist z.1 Uopenᶜ| := rfl
        _ ≤ dist x.1 y.1 + dist y.1 z.1 +
              (|1 / infDist x.1 Uopenᶜ - 1 / infDist y.1 Uopenᶜ| +
                |1 / infDist y.1 Uopenᶜ - 1 / infDist z.1 Uopenᶜ|) :=
          add_le_add (dist_triangle _ _ _) (dist_triangle (1 / infDist _ _) _ _)
        _ = d' x y + d' y z := add_add_add_comm ..
    · refine ⟨fun h x hx => ?_, fun h => isOpen_iff_mem_nhds.2 fun x hx => ?_⟩
      · rcases (Metric.isOpen_iff (α := Uopen)).1 h x hx with ⟨ε, ε0, hε⟩
        exact ⟨ε, ε0, fun y hy => by
          have hxy : dist x.1 y.1 < ε := (d'_val_le x y).trans_lt hy
          exact hε <| (dist_comm _ _).trans_lt hxy⟩
      · rcases h x hx with ⟨ε, ε0, hε⟩
        have h_seq (u : ℕ → Uopen) (hu : Tendsto u atTop (𝓝 x)) :
            Tendsto (fun n => d' (u n) x) atTop (𝓝 0) := by
          have h_val : Tendsto (fun n => (u n).1) atTop (𝓝 x.1) :=
            continuous_subtype_val.continuousAt.tendsto.comp hu
          have h_recip :
              Tendsto (fun n => 1 / infDist (u n).1 Uopenᶜ) atTop
                (𝓝 (1 / infDist x.1 Uopenᶜ)) := by
            simp only [one_div]
            have h_pos : 0 < infDist x.1 Uopenᶜ :=
              (Uopen.isOpen.isClosed_compl.notMem_iff_infDist_pos h_compl_nonempty).mp
                (fun h => h x.2)
            exact (((continuous_infDist_pt (Uopenᶜ : Set X)).tendsto x.1).inv₀ (ne_of_gt h_pos)).comp h_val
          have h_new := (h_val.dist (tendsto_const_nhds (x := x.1))).add
            (h_recip.sub (tendsto_const_nhds (x := 1 / infDist x.1 Uopenᶜ))).abs
          simpa only [d', dist_self, sub_self, abs_zero, zero_add] using h_new
        have h_tendsto : Tendsto (fun y : Uopen => d' y x) (𝓝 x) (𝓝 0) :=
          tendsto_nhds_iff_seq_tendsto.mpr h_seq
        exact mem_of_superset (h_tendsto <| gt_mem_nhds ε0) (by
          intro y hy
          -- hy is membership in a preimage of `Iio ε`; defeq to the inequality.
          have hy' : _ < ε := hy
          exact hε y (by simpa [d', dist_comm, abs_sub_comm] using hy'))
  have d'_metric_dist :
      ∀ x y : Uopen.CompleteCopy, @dist Uopen.CompleteCopy d'_metric.toDist x y = d' x y := by
    intro x y
    rfl
  let : MetricSpace Uopen.CompleteCopy := d'_metric
  have h_separable : SeparableSpace Uopen.CompleteCopy :=
    metrizable_subspace_separable X (Uopen : Set X)
  have h_second_countable : SecondCountableTopology Uopen.CompleteCopy :=
    (metrizable_separable_iff_second_countable Uopen.CompleteCopy).mp h_separable
  have h_complete : IsMetricComplete Uopen.CompleteCopy := by
    intro u hu
    have h_recip_cauchy : CauchySeq (fun n => 1 / infDist (u n).1 Uopenᶜ) := by
      refine Metric.cauchySeq_iff.mpr ?_
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
      refine ⟨N, fun m hm n hn => ?_⟩
      calc
        dist (1 / infDist (u m).1 Uopenᶜ) (1 / infDist (u n).1 Uopenᶜ) =
            |1 / infDist (u m).1 Uopenᶜ - 1 / infDist (u n).1 Uopenᶜ| := rfl
        _ ≤ dist (u m) (u n) := by
          change _ ≤ d' (u m) (u n)
          exact le_add_of_nonneg_left dist_nonneg
        _ < ε := hN m hm n hn
    obtain ⟨R, _hR_pos, hR⟩ := cauchySeq_bdd h_recip_cauchy
    obtain ⟨M, hM⟩ : ∃ M, ∀ n, 1 / infDist (u n).1 Uopenᶜ < M := by
      refine ⟨R + 1 / infDist (u 0).1 Uopenᶜ, fun n => ?_⟩
      rw [← sub_lt_iff_lt_add]
      exact (le_abs_self _).trans_lt (hR n 0)
    have h_cauchy_in_X : CauchySeq fun n => (u n).1 := by
      refine Metric.cauchySeq_iff.mpr ?_
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
      exact ⟨N, fun m hm n hn => (d'_val_le (u m) (u n)).trans_lt (hN m hm n hn)⟩
    obtain ⟨x, xlim⟩ :
        ∃ x, Tendsto (fun n => (u n).1) atTop (𝓝 x) :=
      hX_complete _ h_cauchy_in_X
    have Mpos : 0 < M := lt_of_le_of_lt (div_nonneg zero_le_one infDist_nonneg) (hM 0)
    have Hmem : ∀ {y}, y ∈ Uopen ↔ 0 < infDist y Uopenᶜ := fun {y} => by
      rw [← Uopen.isOpen.isClosed_compl.notMem_iff_infDist_pos h_compl_nonempty]
      exact not_not.symm
    have h_lower_bound : ∀ n, 1 / M ≤ infDist (u n).1 Uopenᶜ := fun n => by
      have h_pos : 0 < infDist (u n).1 Uopenᶜ := Hmem.1 (u n).2
      rw [div_le_iff₀' Mpos]
      exact (div_le_iff₀ h_pos).1 (hM n).le
    have h_limit_lower_bound : 1 / M ≤ infDist x Uopenᶜ :=
      have h_tendsto_infDist :
          Tendsto (fun n => infDist (u n).1 Uopenᶜ) atTop (𝓝 (infDist x Uopenᶜ)) :=
        ((continuous_infDist_pt (Uopenᶜ : Set X)).tendsto x).comp xlim
      ge_of_tendsto' h_tendsto_infDist h_lower_bound
    have hxU : x ∈ Uopen :=
      Hmem.2 <| lt_of_lt_of_le (div_pos one_pos Mpos) h_limit_lower_bound
    let limitInU : Uopen.CompleteCopy := ⟨x, hxU⟩
    exact ⟨limitInU, tendsto_subtype_rng.2 xlim⟩
  have distance_definition (z : X) (S : Set X) (hS : S.Nonempty) :
      infDist z S = sInf ((fun s : X => dist z s) '' S) :=
    ((Metric.isGLB_infDist hS).csInf_eq (hS.image _)).symm
  have h_completely_metrizable : IsCompletelyMetrizableSpace Uopen.CompleteCopy := by
    exact (isCompletelyMetrizableByMetric_iff_mathlib Uopen.CompleteCopy).1
      ⟨d'_metric, rfl, h_complete⟩
  exact
    { toSecondCountableTopology := h_second_countable
      toIsCompletelyMetrizableSpace := h_completely_metrizable }

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: proposition
  title: Countable disjoint unions
-/
/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Given Polish spaces $\Sequence{X_n}{n\in\omega}$, choose complete compatible metrics $d_n \le 1$ on the $X_n$.
    
    On the
    topological sum $\ExternalDisjointUnion_{n \in \omega} X_n$, define
    $$d(\Pair{n}{x}, \Pair{m}{y}) \;=\;
    \begin{cases}
    d_n(x, y), & n = m, \\
    1, & n \ne m.
    \end{cases}$$
    
    Nonnegativity, symmetry, and separation of distinct points follow directly from the definition.
    For the triangle inequality, write $p=\Pair{n}{x}$, $q=\Pair{m}{y}$, and $r=\Pair{k}{z}$.
    If $n=m=k$, then
    
    $$d(p,r)=d_n(x,z)\le d_n(x,y)+d_n(y,z)=d(p,q)+d(q,r).$$
    
    If $n=k\ne m$, then
    
    $$d(p,r)=d_n(x,z)\le 1\le 1+1=d(p,q)+d(q,r).$$
    
    If $n\ne k$, then $n\ne m$ or $m\ne k$, so at least one of $d(p,q)$ and $d(q,r)$ equals $1$. Hence
    
    $$d(p,r)=1\le d(p,q)+d(q,r).$$
    
    These cases exhaust all possibilities, so $d$ is a metric. It induces the disjoint-union topology: each
    summand is clopen, and balls of radius $< 1$ stay inside a single summand.
    
    It is complete because a Cauchy sequence is
    eventually trapped in one summand, where it converges by completeness of $d_n$.
    
    It is separable because a countable
    union of countable dense subsets is countable and dense.
    
    \end{proof}
-/
theorem countable_disjoint_union_polish {ι : Type*} [Countable ι] {Y : ι -> Type*}
    [∀ i, TopologicalSpace (Y i)] [∀ i, PolishSpace (Y i)] :
    PolishSpace (Sigma Y) := by
  classical
  let completeMetricOn : ∀ i, UpgradedIsCompletelyMetrizableSpace (Y i) := fun i =>
    upgradeIsCompletelyMetrizable (Y i)
  let : ∀ i, MetricSpace (Y i) := fun i => (completeMetricOn i).toMetricSpace
  have originalComplete : ∀ i, IsMetricComplete (Y i) := fun i =>
    isMetricComplete_of_upgraded (Y i) (completeMetricOn i)
  choose metrics topology complete formula bound using
    fun i => complete_compatible_metric_bounded_by_one (Y i) (originalComplete i)
  let boundedMetricOn : ∀ i, MetricSpace (Y i) := fun i =>
    (metrics i).replaceTopology (topology i).symm
  have metric_eq : ∀ i, boundedMetricOn i = metrics i := fun i =>
    MetricSpace.replaceTopology_eq (metrics i) (topology i).symm
  let : ∀ i, MetricSpace (Y i) := boundedMetricOn
  have hY_complete : ∀ i, IsMetricComplete (Y i) := by
    intro i
    change @IsMetricComplete (Y i) (boundedMetricOn i)
    rw [metric_eq i]
    exact complete i
  have hY_bound : ∀ i (x y : Y i), dist x y ≤ 1 := by
    intro i x y
    change @dist (Y i) (boundedMetricOn i).toDist x y ≤ 1
    rw [metric_eq i]
    exact bound i x y
  let dSigma : Sigma Y -> Sigma Y -> ℝ := fun a b =>
    match a, b with
    | ⟨i, x⟩, ⟨j, y⟩ =>
        if h : i = j then
          dist x (cast (by rw [h]) y)
        else
          1
  have dSigma_self : ∀ x : Sigma Y, dSigma x x = 0 := by
    rintro ⟨i, x⟩
    simp [dSigma]
  have dSigma_comm : ∀ x y : Sigma Y, dSigma x y = dSigma y x := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    by_cases h : i = j
    · subst j
      simp [dSigma, dist_comm]
    · have h' : j ≠ i := h ∘ Eq.symm
      simp [dSigma, h, h']
  have dSigma_nonneg : ∀ x y : Sigma Y, 0 ≤ dSigma x y := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    by_cases h : i = j
    · subst j
      simp [dSigma, dist_nonneg]
    · simp [dSigma, h]
  have dSigma_triangle : ∀ x y z : Sigma Y, dSigma x z ≤ dSigma x y + dSigma y z := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
    let p : Sigma Y := ⟨i, x⟩
    let q : Sigma Y := ⟨j, y⟩
    let r : Sigma Y := ⟨k, z⟩
    change dSigma p r ≤ dSigma p q + dSigma q r
    simp only [p, q, r]
    by_cases hik : i = k
    · subst k
      by_cases hij : i = j
      · subst j
        simp only [dSigma, dite_eq_left rfl, cast_eq]
        exact dist_triangle x y z
      · have hji : j ≠ i := hij ∘ Eq.symm
        simp only [dSigma, dite_eq_left rfl, dite_eq_right hij, dite_eq_right hji, cast_eq]
        exact (hY_bound i x z).trans (by norm_num)
    · by_cases hij : i = j
      · subst j
        have hik' : i ≠ k := hik
        simp only [dSigma, dite_eq_right hik', dite_eq_left rfl, cast_eq]
        exact le_add_of_nonneg_left dist_nonneg
      · by_cases hjk : j = k
        · subst k
          have hij' : i ≠ j := hij
          simp only [dSigma, dite_eq_right hij', dite_eq_left rfl, cast_eq]
          exact le_add_of_nonneg_right dist_nonneg
        · simp only [dSigma, dite_eq_right hik, dite_eq_right hij, dite_eq_right hjk]
          norm_num
  have dSigma_eq_zero : ∀ x y : Sigma Y, dSigma x y = 0 -> x = y := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    by_cases hij : i = j
    · subst j
      simp only [dSigma, dite_eq_left rfl, cast_eq] at hxy
      exact congrArg (Sigma.mk i) (eq_of_dist_eq_zero hxy)
    · simp [dSigma, hij] at hxy
  let sigmaMetric : MetricSpace (Sigma Y) := by
    refine MetricSpace.ofDistTopology dSigma dSigma_self dSigma_comm dSigma_triangle ?_ dSigma_eq_zero
    intro s
    constructor
    · intro hs
      refine fun x hx => ?_
      rcases x with ⟨i, x⟩
      rcases (Metric.isOpen_iff.1 (isOpen_sigma_iff.1 hs i) x hx) with ⟨ε, εpos, hε⟩
      refine ⟨min ε 1, lt_min εpos zero_lt_one, ?_⟩
      rintro ⟨j, y⟩ hy
      by_cases hij : i = j
      · subst j
        simp only [dSigma, dite_eq_left rfl, cast_eq] at hy
        have hdist : dist x y < ε :=
          hy.trans_le (min_le_left _ _)
        exact hε (mem_ball'.2 hdist)
      · have : (1 : ℝ) < min ε 1 := by
          simp [dSigma, hij] at hy
        linarith [min_le_right ε (1 : ℝ)]
    · intro hs
      refine isOpen_sigma_iff.2 fun i => Metric.isOpen_iff.2 fun x hx => ?_
      rcases hs ⟨i, x⟩ hx with ⟨ε, εpos, hε⟩
      refine ⟨min ε 1, lt_min εpos zero_lt_one, fun y hy => ?_⟩
      apply hε ⟨i, y⟩
      simp only [dSigma, dite_eq_left rfl, cast_eq]
      have hy' : dist x y < min ε 1 := mem_ball'.1 hy
      exact hy'.trans_le (min_le_left _ _)
  have sigmaMetric_dist :
      ∀ x y : Sigma Y, @dist (Sigma Y) sigmaMetric.toDist x y = dSigma x y := by
    intro x y
    rfl
  let : MetricSpace (Sigma Y) := sigmaMetric
  have h_complete : IsMetricComplete (Sigma Y) := by
    intro u hu
    rcases Metric.cauchySeq_iff.1 hu (1 / 2) (by norm_num) with ⟨N, hN⟩
    rcases hUN : u N with ⟨i, xN⟩
    have h_eventually_i : ∀ n ≥ N, (u n).1 = i := by
      intro n hn
      rcases hun : u n with ⟨j, y⟩
      have hdist : dSigma (⟨j, y⟩ : Sigma Y) ⟨i, xN⟩ < 1 / 2 := by
        simpa [hun, hUN, sigmaMetric_dist] using hN n hn N le_rfl
      by_cases hji : j = i
      · exact hji
      · have : (1 : ℝ) < 1 / 2 := by simpa [dSigma, hji] using hdist
        norm_num at this
    have h_lift : ∀ n, N ≤ n -> ∃ y : Y i, u n = ⟨i, y⟩ := by
      intro n hn
      rcases hun : u n with ⟨j, y⟩
      have hji : j = i := by simpa [hun] using h_eventually_i n hn
      subst j
      exact ⟨y, by simp⟩
    let v : ℕ -> Y i := fun n =>
      if h : N ≤ n then Classical.choose (h_lift n h) else xN
    have hv_spec : ∀ n (hn : N ≤ n), u n = ⟨i, v n⟩ := by
      intro n hn
      have hchoose := Classical.choose_spec (h_lift n hn)
      simpa [v, hn] using hchoose
    have hv_cauchy : CauchySeq v := by
      rw [Metric.cauchySeq_iff]
      intro ε εpos
      have hδpos : 0 < min ε 1 := lt_min εpos zero_lt_one
      rcases Metric.cauchySeq_iff.1 hu (min ε 1) hδpos with ⟨M, hM⟩
      refine ⟨max N M, fun m hm n hn => ?_⟩
      have hNm : N ≤ m := le_trans (le_max_left _ _) hm
      have hNn : N ≤ n := le_trans (le_max_left _ _) hn
      have hMm : M ≤ m := le_trans (le_max_right _ _) hm
      have hMn : M ≤ n := le_trans (le_max_right _ _) hn
      have hdistSigma : dSigma (u m) (u n) < min ε 1 := by
        simpa [sigmaMetric_dist] using hM m hMm n hMn
      have hum : u m = ⟨i, v m⟩ := hv_spec m hNm
      have hun : u n = ⟨i, v n⟩ := hv_spec n hNn
      simp only [hum, hun, dSigma, dite_eq_left rfl, cast_eq] at hdistSigma
      exact hdistSigma.trans_le (min_le_left _ _)
    obtain ⟨x, hx⟩ : ∃ x, Tendsto v atTop (𝓝 x) :=
      hY_complete i v hv_cauchy
    refine ⟨⟨i, x⟩, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε εpos
    rcases (Metric.tendsto_atTop.1 hx) ε εpos with ⟨M, hM⟩
    refine ⟨max N M, fun n hn => ?_⟩
    have hNn : N ≤ n := le_trans (le_max_left _ _) hn
    have hMn : M ≤ n := le_trans (le_max_right _ _) hn
    have hun : u n = ⟨i, v n⟩ := hv_spec n hNn
    have hd : dist (v n) x < ε := hM n hMn
    simp [sigmaMetric_dist, dSigma, hun]
    exact hd
  have h_separable : SeparableSpace (Sigma Y) := by
    choose D hD_count hD_dense using fun i : ι => TopologicalSpace.exists_countable_dense (Y i)
    let Dsigma : Set (Sigma Y) := ⋃ i, Sigma.mk i '' D i
    refine ⟨⟨Dsigma, ?_, ?_⟩⟩
    · exact countable_iUnion fun i => (hD_count i).image _
    · rw [dense_iff_inter_open]
      intro O hO hOne
      rcases hOne with ⟨⟨i, x⟩, hxO⟩
      have hsection_open : IsOpen {y : Y i | Sigma.mk i y ∈ O} :=
        isOpen_sigma_iff.1 hO i
      have hsection_nonempty : ({y : Y i | Sigma.mk i y ∈ O} : Set (Y i)).Nonempty :=
        ⟨x, hxO⟩
      rcases (hD_dense i).inter_open_nonempty
          {y : Y i | Sigma.mk i y ∈ O} hsection_open hsection_nonempty with
        ⟨y, hyO, hyD⟩
      exact ⟨⟨i, y⟩, hyO, by
        exact mem_iUnion.2 ⟨i, mem_image_of_mem (Sigma.mk i) hyD⟩⟩
  have h_second_countable : SecondCountableTopology (Sigma Y) :=
    (metrizable_separable_iff_second_countable (Sigma Y)).1 h_separable
  have h_completely_metrizable : IsCompletelyMetrizableSpace (Sigma Y) := by
    exact (isCompletelyMetrizableByMetric_iff_mathlib (Sigma Y)).1
      ⟨sigmaMetric, rfl, h_complete⟩
  exact
    { toSecondCountableTopology := h_second_countable
      toIsCompletelyMetrizableSpace := h_completely_metrizable }

/-- The natural-number family used in the book's disjoint-union construction. -/
theorem countable_disjoint_union_polish_nat {Y : ℕ → Type*}
    [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)] :
    PolishSpace (Sigma Y) :=
  countable_disjoint_union_polish (ι := ℕ) (Y := Y)

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: proposition
  title: Countable products
-/
/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Given Polish spaces $\Sequence{X_n}{n\in\omega}$, choose complete compatible metrics $d_n \le 1$ on the $X_n$ and define
    on
    $\prod_{n \in \omega} X_n$
    $$d\big(\Sequence{x_n}{n\in\omega},\Sequence{y_n}{n\in\omega}\big) \;=\; \sum_{n \in \omega} 2^{-n}d_n(x_n,y_n).$$
    Each summand $2^{-n}d_n(x_n,y_n)$ is at most $2^{-n}$, so the series converges, and the metric axioms follow
    term by term from the metric axioms for the $d_n$. Thus $d$ is a metric.
    
    This metric induces the product topology. For each coordinate $n$,
    $$2^{-n}d_n(x_n,y_n)\le d(x,y),$$
    so each coordinate projection is continuous for $d$. Hence the identity map from the $d$-topology to the product
    topology is continuous.
    
    Conversely, fix $x$ and $\varepsilon>0$. Choose $M$ so that
    $\sum_{n\ge M}2^{-n}<\varepsilon/2$. The set
    $$V=\left\{y:\sum_{n<M}2^{-n}d_n(x_n,y_n)<\varepsilon/2\right\}$$
    is a product-open neighborhood of $x$, since the finite sum is a continuous function of finitely many coordinates.
    For $y\in V$,
    $$d(x,y)\le\sum_{n<M}2^{-n}d_n(x_n,y_n)+\sum_{n\ge M}2^{-n}<\varepsilon.$$
    Thus every $d$-ball about $x$ contains a product-open neighborhood of $x$, proving continuity of the identity in
    the other direction. The two topologies agree. In particular, convergence for $d$ is exactly coordinate-wise
    convergence.
    
    For completeness, let $\Sequence{x^k}{k\in\omega}$ be $d$-Cauchy. Then each coordinate sequence
    $\Sequence{x^k_n}{k\in\omega}$ is Cauchy for $d_n$,
    so it converges to some $x_n \in X_n$. By the convergence criterion just proved, the point
    $x=\Sequence{x_n}{n\in\omega}$ is the
    $d$-limit of $\Sequence{x^k}{k\in\omega}$.
    
    For separability, if the product is empty there is nothing to prove.
    Otherwise fix countable dense sets
    $D_n \IncludedIn X_n$ and a reference point $x^* \in \prod X_n$. The countable set of sequences agreeing with $x^*$ in
    all but finitely many coordinates, with the differing coordinates ranging over the corresponding $D_n$, is dense.
    
    \end{proof}
-/
theorem countable_product_polish {Y : ℕ -> Type*}
    [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)] :
    PolishSpace (∀ n, Y n) := by
  classical
  let completeMetricOn : ∀ i, UpgradedIsCompletelyMetrizableSpace (Y i) := fun i =>
    upgradeIsCompletelyMetrizable (Y i)
  let : ∀ i, MetricSpace (Y i) := fun i => (completeMetricOn i).toMetricSpace
  have originalComplete : ∀ i, IsMetricComplete (Y i) := fun i =>
    isMetricComplete_of_upgraded (Y i) (completeMetricOn i)
  choose metrics topology complete formula bound using
    fun i => complete_compatible_metric_bounded_by_one (Y i) (originalComplete i)
  let boundedMetricOn : ∀ i, MetricSpace (Y i) := fun i =>
    (metrics i).replaceTopology (topology i).symm
  have metric_eq : ∀ i, boundedMetricOn i = metrics i := fun i =>
    MetricSpace.replaceTopology_eq (metrics i) (topology i).symm
  let : ∀ i, MetricSpace (Y i) := boundedMetricOn
  have hY_complete : ∀ i, IsMetricComplete (Y i) := by
    intro i
    change @IsMetricComplete (Y i) (boundedMetricOn i)
    rw [metric_eq i]
    exact complete i
  have hY_bound : ∀ i (x y : Y i), dist x y ≤ 1 := by
    intro i x y
    change @dist (Y i) (boundedMetricOn i).toDist x y ≤ 1
    rw [metric_eq i]
    exact bound i x y
  let weight : ℕ -> ℝ := fun n => ((1 / 2 : ℝ) ^ n)
  let term : (∀ n, Y n) -> (∀ n, Y n) -> ℕ -> ℝ := fun x y n =>
    weight n * dist (x n) (y n)
  let dPi : (∀ n, Y n) -> (∀ n, Y n) -> ℝ := fun x y =>
    ∑' n, term x y n
  have weight_pos : ∀ n, 0 < weight n := by
    intro n
    positivity
  have weight_nonneg : ∀ n, 0 ≤ weight n := fun n => (weight_pos n).le
  have weight_summable : Summable weight := by
    simpa [weight] using summable_geometric_two
  have term_nonneg : ∀ x y n, 0 ≤ term x y n := by
    intro x y n
    exact mul_nonneg (weight_nonneg n) dist_nonneg
  have term_le_weight : ∀ x y n, term x y n ≤ weight n := by
    intro x y n
    exact mul_le_of_le_one_right (weight_nonneg n) (hY_bound n (x n) (y n))
  have term_summable : ∀ x y, Summable fun n => term x y n := by
    intro x y
    exact Summable.of_nonneg_of_le (term_nonneg x y) (term_le_weight x y)
      weight_summable
  have dPi_self : ∀ x : ∀ n, Y n, dPi x x = 0 := by
    intro x
    simp [dPi, term]
  have dPi_comm : ∀ x y : ∀ n, Y n, dPi x y = dPi y x := by
    intro x y
    simp [dPi, term, dist_comm]
  have dPi_triangle : ∀ x y z : ∀ n, Y n, dPi x z ≤ dPi x y + dPi y z := by
    intro x y z
    have hle : ∀ n, term x z n ≤ term x y n + term y z n := by
      intro n
      change weight n * dist (x n) (z n) ≤
        weight n * dist (x n) (y n) + weight n * dist (y n) (z n)
      calc
        _ ≤ weight n * (dist (x n) (y n) + dist (y n) (z n)) :=
          mul_le_mul_of_nonneg_left (dist_triangle _ _ _) (weight_nonneg n)
        _ = _ := by ring
    calc
      dPi x z = ∑' n, term x z n := rfl
      _ ≤ ∑' n, (term x y n + term y z n) :=
        (term_summable x z).tsum_le_tsum hle ((term_summable x y).add (term_summable y z))
      _ = dPi x y + dPi y z := by
        simpa [dPi] using (term_summable x y).tsum_add (term_summable y z)
  have dPi_eq_zero : ∀ x y : ∀ n, Y n, dPi x y = 0 -> x = y := by
    intro x y hxy
    funext n
    have hterm_le : term x y n ≤ dPi x y :=
      (term_summable x y).le_tsum n fun k _ => term_nonneg x y k
    have hterm_zero : term x y n = 0 :=
      le_antisymm (by simpa [hxy] using hterm_le) (term_nonneg x y n)
    have hdist_zero : dist (x n) (y n) = 0 := by
      change weight n * dist (x n) (y n) = 0 at hterm_zero
      exact (mul_eq_zero.1 hterm_zero).resolve_left (ne_of_gt (weight_pos n))
    exact eq_of_dist_eq_zero hdist_zero
  have product_ball_neighborhood (x : ∀ n, Y n) (ε : ℝ) (hε : 0 < ε) :
      ∃ M : ℕ, ∃ V : Set (∀ n, Y n), IsOpen V ∧ x ∈ V ∧
        V = {y | ∑ n ∈ Finset.range M, term x y n < ε / 2} ∧
        (∑' n, weight (n + M)) < ε / 2 ∧ ∀ y ∈ V, dPi x y < ε := by
    obtain ⟨M, hM⟩ := Filter.Eventually.exists
      ((tendsto_sum_nat_add weight).eventually (gt_mem_nhds (half_pos hε)))
    let V : Set (∀ n, Y n) := {y | ∑ n ∈ Finset.range M, term x y n < ε / 2}
    have hV : IsOpen V := by
      have hc : Continuous (fun y : ∀ n, Y n => ∑ n ∈ Finset.range M, term x y n) := by
        apply continuous_finsetSum
        intro n _
        dsimp [term]
        fun_prop
      exact hc.isOpen_preimage _ isOpen_Iio
    refine ⟨M, V, hV, ?_, rfl, hM, ?_⟩
    · simpa [V, term] using half_pos hε
    · intro y hy
      have htail : (∑' n, term x y (n + M)) ≤ ∑' n, weight (n + M) :=
        ((summable_nat_add_iff M).2 (term_summable x y)).tsum_le_tsum
          (fun n => term_le_weight x y (n + M)) ((summable_nat_add_iff M).2 weight_summable)
      change (∑' n, term x y n) < ε
      rw [← (term_summable x y).sum_add_tsum_nat_add M]
      have hpartial : (∑ n ∈ Finset.range M, term x y n) < ε / 2 := hy
      linarith
  -- Finite-coordinate balls give one inclusion; the named finite-sum
  -- neighborhood and its uniform tail estimate give the reverse inclusion.
  let productMetric : MetricSpace (∀ n, Y n) := by
    refine MetricSpace.ofDistTopology dPi dPi_self dPi_comm dPi_triangle ?_ dPi_eq_zero
    intro s
    constructor
    · intro hs x hx
      rcases isOpen_pi_iff.1 hs x hx with ⟨I, U, hU, hIU⟩
      have hcoord :
          ∀ n, n ∈ I -> ∃ ε > 0, ∀ y : Y n, dist (x n) y < ε -> y ∈ U n := by
        intro n hn
        rcases Metric.isOpen_iff.1 (hU n hn).1 (x n) (hU n hn).2 with
          ⟨ε, εpos, hε⟩
        exact ⟨ε, εpos, fun y hy => hε (mem_ball'.2 hy)⟩
      let coordRadius : ℕ -> ℝ := fun n =>
        if h : n ∈ I then Classical.choose (hcoord n h) else 1
      have coordRadius_pos : ∀ n, n ∈ I -> 0 < coordRadius n := by
        intro n hn
        simpa [coordRadius, hn] using (Classical.choose_spec (hcoord n hn)).1
      have coordRadius_mem :
          ∀ n (hn : n ∈ I) (y : Y n),
            dist (x n) y < coordRadius n -> y ∈ U n := by
        intro n hn y hy
        have hspec := (Classical.choose_spec (hcoord n hn)).2
        exact hspec y (by simpa [coordRadius, hn] using hy)
      by_cases hIempty : I = ∅
      · refine ⟨1, zero_lt_one, fun y _ => hIU ?_⟩
        intro n hn
        simp [hIempty] at hn
      · have hIne : I.Nonempty := Finset.nonempty_iff_ne_empty.2 hIempty
        let coordBound : ℕ -> ℝ := fun n => weight n * min (coordRadius n) 1
        let δ : ℝ := (I.image coordBound).min' (hIne.image coordBound)
        have coordBound_pos : ∀ n, n ∈ I -> 0 < coordBound n := by
          intro n hn
          exact mul_pos (weight_pos n) (lt_min (coordRadius_pos n hn) zero_lt_one)
        have δpos : 0 < δ := by
          dsimp [δ]
          rw [Finset.lt_min'_iff]
          intro a ha
          rcases Finset.mem_image.1 ha with ⟨n, hn, rfl⟩
          exact coordBound_pos n hn
        refine ⟨δ, δpos, fun y hy => hIU ?_⟩
        intro n hn
        have hterm_le : term x y n ≤ dPi x y :=
          (term_summable x y).le_tsum n fun k _ => term_nonneg x y k
        have hδ_le_bound : δ ≤ coordBound n := by
          exact Finset.min'_le _ _ (Finset.mem_image.2 ⟨n, hn, rfl⟩)
        have hterm_lt_bound : term x y n < coordBound n :=
          hterm_le.trans_lt (hy.trans_le hδ_le_bound)
        have hmin_lt : dist (x n) (y n) < min (coordRadius n) 1 := by
          exact lt_of_mul_lt_mul_left (by
            simpa [term, coordBound] using hterm_lt_bound)
            (weight_nonneg n)
        have hdist : dist (x n) (y n) < coordRadius n :=
          hmin_lt.trans_le (min_le_left _ _)
        exact coordRadius_mem n hn (y n) hdist
    · intro hs
      refine isOpen_iff_mem_nhds.2 fun x hx => ?_
      rcases hs x hx with ⟨ε, εpos, hε⟩
      obtain ⟨M, V, hV, hxV, _, _, hVball⟩ := product_ball_neighborhood x ε εpos
      exact mem_of_superset (hV.mem_nhds hxV) (fun y hy => hε y (hVball y hy))
  have productMetric_dist :
      ∀ x y : ∀ n, Y n, @dist (∀ n, Y n) productMetric.toDist x y = dPi x y := by
    intro x y
    rfl
  let : MetricSpace (∀ n, Y n) := productMetric
  have h_complete : @IsMetricComplete (∀ n, Y n) productMetric := by
    intro u hu
    have hcoord_cauchy : ∀ k, CauchySeq fun m => u m k := by
      intro k
      rw [Metric.cauchySeq_iff]
      intro ε εpos
      let δ := weight k * min ε 1
      have δpos : 0 < δ := mul_pos (weight_pos k) (lt_min εpos zero_lt_one)
      rcases Metric.cauchySeq_iff.1 hu δ δpos with ⟨N, hN⟩
      refine ⟨N, fun m hm n hn => ?_⟩
      have hdPi : dPi (u m) (u n) < δ := by
        simpa [productMetric_dist] using hN m hm n hn
      have hterm_le : term (u m) (u n) k ≤ dPi (u m) (u n) :=
        (term_summable (u m) (u n)).le_tsum k fun j _ => term_nonneg (u m) (u n) j
      have hterm_lt : term (u m) (u n) k < δ :=
        hterm_le.trans_lt hdPi
      have hmin_lt : dist (u m k) (u n k) < min ε 1 := by
        exact lt_of_mul_lt_mul_left (by
          simpa [term, δ] using hterm_lt)
          (weight_nonneg k)
      exact hmin_lt.trans_le (min_le_left _ _)
    have hcoord_limit : ∀ k, ∃ xk : Y k, Tendsto (fun m => u m k) atTop (𝓝 xk) := by
      intro k
      exact hY_complete k (fun m => u m k) (hcoord_cauchy k)
    choose x hx using hcoord_limit
    have coordinate_convergence (n : ℕ) :
        Tendsto (fun k => u k n) atTop (𝓝 (x n)) := hx n
    exact ⟨x, tendsto_pi_nhds.2 coordinate_convergence⟩
  have h_separable : SeparableSpace (∀ n, Y n) := by
    by_cases hprod : Nonempty (∀ n, Y n)
    · let x0 : ∀ n, Y n := Classical.choice hprod
      have : ∀ n, Nonempty (Y n) := fun n => ⟨x0 n⟩
      let coordinateDense (n : ℕ) : Set (Y n) :=
        Set.range (TopologicalSpace.denseSeq (Y n))
      let densePoint : (F : Finset ℕ) -> (∀ n : {n // n ∈ F}, ℕ) -> ∀ n, Y n :=
        fun F k n => if h : n ∈ F then TopologicalSpace.denseSeq (Y n) (k ⟨n, h⟩) else x0 n
      let Dprod : Set (∀ n, Y n) :=
        Set.range fun p : Sigma (fun F : Finset ℕ => ∀ n : {n // n ∈ F}, ℕ) =>
          densePoint p.1 p.2
      -- This is exactly the finite-modification set described in the book.
      have Dprod_description : Dprod =
          {y | Set.Finite {n | y n ≠ x0 n} ∧
            ∀ n, y n ≠ x0 n → y n ∈ coordinateDense n} := by
        ext y
        change (∃ p : Sigma (fun F : Finset ℕ => ∀ n : {n // n ∈ F}, ℕ),
          densePoint p.1 p.2 = y) ↔ _
        constructor
        · rintro ⟨⟨F, k⟩, rfl⟩
          refine ⟨F.finite_toSet.subset ?_, ?_⟩
          · intro n hn
            by_contra hnot
            have hnotF : n ∉ F := hnot
            exact hn (by simp [densePoint, hnotF])
          · intro n hn
            by_cases hmem : n ∈ F
            · exact ⟨k ⟨n, hmem⟩, by simp [densePoint, hmem]⟩
            · exact False.elim (hn (by simp [densePoint, hmem]))
        · rintro ⟨hfinite, hvalues⟩
          let F := hfinite.toFinset
          have hindices (n : {n // n ∈ F}) :
              ∃ k, TopologicalSpace.denseSeq (Y n) k = y n :=
            hvalues n (hfinite.mem_toFinset.mp n.2)
          choose k hk using hindices
          refine ⟨⟨F, k⟩, ?_⟩
          funext n
          by_cases hn : n ∈ F
          · simpa [densePoint, hn] using hk ⟨n, hn⟩
          · have heq : y n = x0 n := by
              by_contra hne
              exact hn (hfinite.mem_toFinset.mpr hne)
            simpa [densePoint, hn] using heq.symm
      have coordinateDense_spec (n : ℕ) :
          (coordinateDense n).Countable ∧ Dense (coordinateDense n) :=
        ⟨countable_range _, TopologicalSpace.denseRange_denseSeq (α := Y n)⟩
      refine ⟨⟨{y | Set.Finite {n | y n ≠ x0 n} ∧
        ∀ n, y n ≠ x0 n → y n ∈ coordinateDense n}, ?_, ?_⟩⟩
      · rw [← Dprod_description]
        exact countable_range _
      · rw [← Dprod_description]
        rw [dense_iff_inter_open]
        intro O hO hOne
        rcases hOne with ⟨x, hxO⟩
        rcases isOpen_pi_iff.1 hO x hxO with ⟨I, U, hU, hIU⟩
        have hcoord :
            ∀ n : {n // n ∈ I}, ∃ k : ℕ, TopologicalSpace.denseSeq (Y n) k ∈ U n := by
          intro n
          rcases ((coordinateDense_spec n).2).inter_open_nonempty
              (U n) (hU n n.2).1 ⟨x n, (hU n n.2).2⟩ with
            ⟨y, hyU, hyRange⟩
          rcases hyRange with ⟨k, rfl⟩
          exact ⟨k, hyU⟩
        choose k hk using hcoord
        let y : ∀ n, Y n := densePoint I k
        refine ⟨y, hIU ?_, ?_⟩
        · intro n hn
          have hnI : n ∈ I := hn
          have : y n = TopologicalSpace.denseSeq (Y n) (k ⟨n, hn⟩) := by
            simp [y, densePoint, hnI]
          simpa [this] using hk ⟨n, hn⟩
        · exact ⟨⟨I, k⟩, rfl⟩
    · refine ⟨⟨∅, countable_empty, ?_⟩⟩
      intro x
      exact False.elim (hprod ⟨x⟩)
  have h_second_countable : SecondCountableTopology (∀ n, Y n) :=
    (metrizable_separable_iff_second_countable (∀ n, Y n)).1 h_separable
  have h_completely_metrizable : IsCompletelyMetrizableSpace (∀ i, Y i) := by
    exact (isCompletelyMetrizableByMetric_iff_mathlib (∀ i, Y i)).1
      ⟨productMetric, rfl, h_complete⟩
  exact
    { toSecondCountableTopology := h_second_countable
      toIsCompletelyMetrizableSpace := h_completely_metrizable }

/-!
## Baire category

| Book term | Lean name |
| --- | --- |
| `\termdefineas{nowhere dense set}{nowhere dense}` | mathlib predicate `IsNowhereDense` |
| `\termdefineas{meager set}{meager}` | mathlib predicate `IsMeagre` |
| `\termdefineas{comeager set}{comeager}` | `IsComeager`, equivalent to membership in mathlib's `residual` filter |
| `\termdefineas{Baire space (category sense)}{Baire space}` | mathlib class `BaireSpace` |
-/

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    For Baire-category arguments, a set is \termdefineas{nowhere dense set}{nowhere dense} if the interior of its closure is
    empty, \termdefineas{meager set}{meager} if it is a countable union of nowhere-dense sets, and
    \termdefineas{comeager set}{comeager} if its complement is meager. All three notions depend on the ambient space; we
    leave it implicit when
    context fixes it.
-/
abbrev IsComeager {Y : Type*} [TopologicalSpace Y] (s : Set Y) : Prop :=
  IsMeagre sᶜ

theorem isComeager_iff_mem_residual {Y : Type*} [TopologicalSpace Y] {s : Set Y} :
    IsComeager s ↔ s ∈ residual Y := by
  simp [IsComeager, IsMeagre]



/-- The ball data retained by the Baire construction. -/
structure BaireBallData {Y : Type*} [MetricSpace Y] (W : Set Y) (ε : ℝ) where
  center : Y
  outerRadius : ℝ
  radius : ℝ
  outer_pos : 0 < outerRadius
  outer_subset : ball center outerRadius ⊆ W
  radius_eq : radius = min (outerRadius / 2) (ε / 2)
  radius_pos : 0 < radius
  radius_lt_outer : radius < outerRadius
  closure_subset_outer : closure (ball center radius) ⊆ ball center outerRadius
  bounded : Bornology.IsBounded (closure (ball center radius))
  diameter_le : diam (closure (ball center radius)) ≤ ε

/-- Choose an outer ball and retain the explicitly smaller radius. -/
def choose_baire_ball {Y : Type*} [MetricSpace Y]
    {W : Set Y} (hWopen : IsOpen W) (hWne : W.Nonempty)
    {ε : ℝ} (hε : 0 < ε) : BaireBallData W ε := by
  let x := Classical.choose hWne
  have hx : x ∈ W := Classical.choose_spec hWne
  let r₀ := Classical.choose (Metric.isOpen_iff.1 hWopen x hx)
  have hr₀ : 0 < r₀ := (Classical.choose_spec (Metric.isOpen_iff.1 hWopen x hx)).1
  have hball : ball x r₀ ⊆ W := (Classical.choose_spec (Metric.isOpen_iff.1 hWopen x hx)).2
  let r := min (r₀ / 2) (ε / 2)
  have hr : 0 < r := lt_min (half_pos hr₀) (half_pos hε)
  have hrr₀ : r < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨x, r₀, r, hr₀, hball, rfl, hr, hrr₀, ?_, ?_, ?_⟩
  · exact closure_ball_subset_closedBall.trans (closedBall_subset_ball hrr₀)
  · exact isBounded_closedBall.subset closure_ball_subset_closedBall
  · rw [diam_closure]
    exact (diam_ball hr.le).trans (by dsimp [r]; linarith [min_le_right (r₀ / 2) (ε / 2)])

/-- Nested open sets retain the chosen ball at each recursive step. -/
theorem baire_nested_open_sets {Y : Type*} [MetricSpace Y]
    {U : Set Y} (hUopen : IsOpen U) (hUne : U.Nonempty)
    {G : ℕ → Set Y} (hGopen : ∀ n, IsOpen (G n))
    (hGdense : ∀ n, U ⊆ closure (G n)) :
    ∃ V : ℕ → Set Y,
      (∀ n, IsOpen (V n) ∧ (V n).Nonempty ∧ V n ⊆ U ∧
        Bornology.IsBounded (closure (V n)) ∧ diam (closure (V n)) ≤ (2 : ℝ) ^ (-(n : ℤ))) ∧
      ∀ n, closure (V (n + 1)) ⊆ V n ∩ G n := by
  let P (n : ℕ) (V : Set Y) := IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
    Bornology.IsBounded (closure V) ∧ diam (closure V) ≤ (2 : ℝ) ^ (-(n : ℤ))
  let first := choose_baire_ball hUopen hUne (by norm_num : (0 : ℝ) < 1)
  have hfirst : P 0 (ball first.center first.radius) := by
    refine ⟨isOpen_ball, ⟨first.center, mem_ball_self first.radius_pos⟩,
      subset_closure.trans (first.closure_subset_outer.trans first.outer_subset), first.bounded, ?_⟩
    simpa using first.diameter_le
  let pick (n : ℕ) (W : Set Y) (hW : P n W) : BaireBallData (W ∩ G n) ((2 : ℝ) ^ (-(↑(n + 1) : ℤ))) := by
    have hne : (W ∩ G n).Nonempty := by
      obtain ⟨x, hx⟩ := hW.2.1
      exact _root_.mem_closure_iff.1 (hGdense n (hW.2.2.1 hx)) W hW.1 hx
    exact choose_baire_ball (hW.1.inter (hGopen n)) hne (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
  let step (n : ℕ) (W : {W : Set Y // P n W}) : {W : Set Y // P (n + 1) W} := by
    let B := pick n W.val W.property
    refine ⟨ball B.center B.radius, isOpen_ball, ⟨B.center, mem_ball_self B.radius_pos⟩, ?_, B.bounded, B.diameter_le⟩
    exact subset_closure.trans (B.closure_subset_outer.trans
      (B.outer_subset.trans (inter_subset_left.trans W.property.2.2.1)))
  let state : (n : ℕ) → {W : Set Y // P n W} :=
    Nat.rec ⟨ball first.center first.radius, hfirst⟩ step
  let V : ℕ → Set Y := fun n => (state n).val
  refine ⟨V, fun n => (state n).property, ?_⟩
  intro n
  let B := pick n (state n).val (state n).property
  let x := B.center
  let r := B.radius
  have hVnext : V (n + 1) = ball x r := rfl
  rw [hVnext]
  exact B.closure_subset_outer.trans B.outer_subset

/-- The selected points converge in the original complete ambient metric. -/
theorem baire_open_intersection {Y : Type*} [MetricSpace Y]
    (hcomplete : IsMetricComplete Y)
    {U : Set Y} (hUopen : IsOpen U) (hUne : U.Nonempty)
    {G : ℕ → Set Y} (hGopen : ∀ n, IsOpen (G n))
    (hGdense : ∀ n, U ⊆ closure (G n)) :
    (U ∩ ⋂ n, G n).Nonempty := by
  obtain ⟨V, hV, hnest⟩ := baire_nested_open_sets hUopen hUne hGopen hGdense
  choose x hx using fun n => (hV n).2.1
  have hanti : Antitone V := antitone_nat_of_succ_le fun n =>
    subset_closure.trans ((hnest n).trans inter_subset_left)
  have htail : ∀ n m, n ≤ m → x m ∈ closure (V n) := by
    intro n m hnm
    exact subset_closure (hanti hnm (hx m))
  have hzero : Tendsto (fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
    simpa only [zpow_neg, zpow_natCast, inv_pow] using h
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hzero.eventually (gt_mem_nhds hε))
    refine ⟨N, fun m hm n hn => ?_⟩
    exact lt_of_le_of_lt ((dist_le_diam_of_mem (hV N).2.2.2.1
      (htail N m hm) (htail N n hn)).trans (hV N).2.2.2.2) (hN N le_rfl)
  obtain ⟨y, hy⟩ := hcomplete x hcauchy
  have hyclosure : ∀ n, y ∈ closure (V n) := by
    intro n
    exact isClosed_closure.mem_of_tendsto hy (eventually_atTop.2 ⟨n, htail n⟩)
  refine ⟨y, (hV 0).2.2.1 ((hnest 0 (hyclosure 1)).1), ?_⟩
  exact mem_iInter.2 fun n => (hnest n (hyclosure (n + 1))).2

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: theorem
  title: Theorem (Baire category)
-/
/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Let $X$ be Polish, fix a complete compatible metric $d$, let $U\IncludedIn X$ be nonempty open, and
    let $\Sequence{G_n}{n\in\omega}$ be dense open subsets of $U$ in the relative topology. We show that $U\cap\bigcap_n
    G_n$ is
    nonempty.
    
    Construct nonempty open sets $V_n\IncludedIn U$ recursively so that
    $$
    \begin{aligned}
    \Closure{V_{n+1}} &\IncludedIn V_n\cap G_n,\\
    \MetricDiameter{d}{\Closure{V_n}} &\le 2^{-n}.
    \end{aligned}
    $$
    Start with any nonempty open $V_0\IncludedIn U$ whose closure has diameter at most $1$. Given $V_n$, the set $V_n\cap
    G_n$ is nonempty because $G_n$ is dense in $U$. Since $U$ is open in $X$, the set $V_n\cap G_n$ is open in $X$, so it
    contains some ball $\Ball{x}{r_0}$. Choose $0<r<r_0$ small enough that
    $\Closure{\Ball{x}{r}}\IncludedIn \Ball{x}{r_0}$ and $\MetricDiameter{d}{\Closure{\Ball{x}{r}}}\le 2^{-(n+1)}$,
    and put $V_{n+1}:=\Ball{x}{r}$.
    
    Pick $x_n\in V_n$. The nesting and diameter bounds make $\Sequence{x_n}{n\in\omega}$ Cauchy:
    for $m\ge n$, both $x_m$
    and $x_n$ lie in
    $\Closure{V_n}$, whose diameter is at most $2^{-n}$.
    Completeness gives a limit $x\in X$. Since each $\Closure{V_n}$ is
    closed and contains the tail of the sequence, $x\in\Closure{V_n}$ for every $n$. The nesting also gives
    $\Closure{V_{n+1}}\IncludedIn G_n$, so $x\in G_n$ for every $n$, and $x\in U$. Thus $U\cap\bigcap_n G_n\ne\emptyset$
    whenever $\Sequence{G_n}{n\in\omega}$ are dense open in $U$'s relative topology.
    
    To prove the theorem, fix $\Sequence{G_n}{n\in\omega}$ dense open in $X$ and let $U$ be an arbitrary nonempty open set.
    The traces
    $G_n\cap U$ are dense open in $U$'s relative topology,
    and $U\cap\bigcap_n(G_n\cap U)=U\cap\bigcap_n G_n$, so the
    construction above gives $U\cap\bigcap_n G_n\ne\emptyset$. Since $U$ was arbitrary, $\bigcap_n G_n$ is dense in $X$.
    
    Now suppose a nonempty open $U$ were meager in itself, say $U=\bigcup_n N_n$ with each $N_n$ nowhere dense in $U$. Then
    $\SetDifference{U}{\AmbientClosure{U}{N_n}}$ is dense open in $U$ for each $n$, so the first part gives a point in their
    intersection, contradicting $U=\bigcup_n N_n$.
    \end{proof}
-/
theorem completely_metrizable_baire_space_book (Y : Type*) [TopologicalSpace Y]
    [IsCompletelyMetrizableSpace Y] :
    BaireSpace Y := by
  let completeMetricOnY : UpgradedIsCompletelyMetrizableSpace Y :=
    upgradeIsCompletelyMetrizable Y
  let : MetricSpace Y := completeMetricOnY.toMetricSpace
  have hY_complete : IsMetricComplete Y :=
    isMetricComplete_of_upgraded Y completeMetricOnY
  refine ⟨fun G hGopen hGdense => ?_⟩
  intro x
  apply _root_.mem_closure_iff.2
  intro U hUopen hxU
  let H : ℕ → Set Y := fun n => G n ∩ U
  have hHopen : ∀ n, IsOpen (H n) := fun n => (hGopen n).inter hUopen
  have hHdense : ∀ n, U ⊆ closure (H n) := by
    intro n z hz
    apply _root_.mem_closure_iff.2
    intro W hW hzW
    obtain ⟨w, hw⟩ := _root_.mem_closure_iff.1 (hGdense n z)
      (W ∩ U) (hW.inter hUopen) ⟨hzW, hz⟩
    exact ⟨w, hw.1.1, hw.2, hw.1.2⟩
  have hintersection : U ∩ ⋂ n, H n = U ∩ ⋂ n, G n := by
    ext z
    simp only [H, mem_inter_iff, mem_iInter]
    constructor
    · exact fun h => ⟨h.1, fun n => (h.2 n).1⟩
    · exact fun h => ⟨h.1, fun n => ⟨h.2 n, h.1⟩⟩
  have hnonempty := baire_open_intersection hY_complete hUopen ⟨x, hxU⟩ hHopen hHdense
  rwa [hintersection] at hnonempty

theorem polish_baire_space (X : Type*) [TopologicalSpace X] [PolishSpace X] :
    BaireSpace X := by
  exact completely_metrizable_baire_space_book X

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: theorem
  title: Theorem (Baire category)
-/
theorem baire_category_dense_iInter {G : ℕ -> Set X} (hGopen : ∀ n, IsOpen (G n))
    (hGdense : ∀ n, Dense (G n)) :
    Dense (⋂ n, G n) := by
  exact (polish_baire_space X).baire_property G hGopen hGdense

theorem baire_category_dense_iInter_countable {ι : Type*} [Countable ι] {G : ι -> Set X}
    (hGopen : ∀ i, IsOpen (G i)) (hGdense : ∀ i, Dense (G i)) :
    Dense (⋂ i, G i) := by
  by_cases hι : Nonempty ι
  · let : Nonempty ι := hι
    rcases exists_surjective_nat ι with ⟨e, he⟩
    have hnat : Dense (⋂ n, G (e n)) :=
      baire_category_dense_iInter (fun n => hGopen (e n)) fun n => hGdense (e n)
    have h_eq : (⋂ n, G (e n)) = ⋂ i, G i := by
      ext x
      constructor
      · intro hx
        rw [mem_iInter]
        intro i
        rcases he i with ⟨n, rfl⟩
        exact mem_iInter.1 hx n
      · intro hx
        rw [mem_iInter]
        intro n
        exact mem_iInter.1 hx (e n)
    simpa [h_eq] using hnat
  · have h_eq : (⋂ i, G i) = (Set.univ : Set X) := by
      ext x
      constructor
      · intro
        trivial
      · intro _
        rw [mem_iInter]
        intro i
        exact False.elim (hι ⟨i⟩)
    rw [h_eq]
    exact dense_univ

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    Completeness has a strong topological consequence: nonempty Polish spaces cannot be exhausted by countably many closed
    nowhere-dense pieces. This is the Baire-category principle, and it is one of the main reasons complete metrizability
    matters.
-/
theorem nonempty_open_not_meagre {U : Set X} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ¬ IsMeagre U := by
  intro hmeagre
  rcases isMeagre_iff_countable_union_isNowhereDense.1 hmeagre with
    ⟨S, hS_nowhere, hS_count, hU_subset⟩
  by_cases hS_nonempty : S.Nonempty
  · rcases hS_count.exists_eq_range hS_nonempty with ⟨F, hF⟩
    have hGopen : ∀ n, IsOpen ((closure (F n))ᶜ : Set X) := fun n =>
      isClosed_closure.isOpen_compl
    have hGdense : ∀ n, Dense ((closure (F n))ᶜ : Set X) := by
      intro n
      have hFn : F n ∈ S := by
        rw [hF]
        exact mem_range_self n
      exact (isClosed_isNowhereDense_iff_compl.1
        ⟨isClosed_closure, (hS_nowhere (F n) hFn).closure⟩).2
    have h_inter_dense : Dense (⋂ n, (closure (F n))ᶜ : Set X) :=
      baire_category_dense_iInter hGopen hGdense
    rcases h_inter_dense.inter_open_nonempty U hUopen hUne with ⟨x, hxU, hxG⟩
    have hx_union : x ∈ ⋃₀ S := hU_subset hxU
    rcases mem_sUnion.1 hx_union with ⟨T, hTS, hxT⟩
    rw [hF] at hTS
    rcases hTS with ⟨n, rfl⟩
    exact (mem_iInter.1 hxG n) (subset_closure hxT)
  · rcases hUne with ⟨x, hxU⟩
    have hx_union : x ∈ ⋃₀ S := hU_subset hxU
    rcases mem_sUnion.1 hx_union with ⟨T, hTS, _⟩
    exact hS_nonempty ⟨T, hTS⟩

theorem dense_gdelta_not_meagre [Nonempty X] {A : Set X} (hG : IsGδ A) (hDense : Dense A) :
    ¬ IsMeagre A := by
  intro hmeagre
  rcases isGδ_iff_eq_iInter_nat.1 hG with ⟨G, hGopen, rfl⟩
  rcases isMeagre_iff_countable_union_isNowhereDense.1 hmeagre with
    ⟨S, hS_nowhere, hS_count, hA_subset⟩
  by_cases hS_nonempty : S.Nonempty
  · rcases hS_count.exists_eq_range hS_nonempty with ⟨F, hF⟩
    let H : Sum ℕ ℕ -> Set X := fun k =>
      match k with
      | Sum.inl n => G n
      | Sum.inr n => (closure (F n))ᶜ
    have hHopen : ∀ k, IsOpen (H k) := by
      rintro (n | n)
      · exact hGopen n
      · exact isClosed_closure.isOpen_compl
    have hHdense : ∀ k, Dense (H k) := by
      rintro (n | n)
      · exact hDense.mono (iInter_subset G n)
      · have hFn : F n ∈ S := by
          rw [hF]
          exact mem_range_self n
        exact (isClosed_isNowhereDense_iff_compl.1
          ⟨isClosed_closure, (hS_nowhere (F n) hFn).closure⟩).2
    have h_inter_dense : Dense (⋂ k, H k) :=
      baire_category_dense_iInter_countable hHopen hHdense
    rcases h_inter_dense.nonempty with ⟨x, hxH⟩
    have hxA : x ∈ ⋂ n, G n := by
      rw [mem_iInter]
      intro n
      exact mem_iInter.1 hxH (Sum.inl n)
    have hx_union : x ∈ ⋃₀ S := hA_subset hxA
    rcases mem_sUnion.1 hx_union with ⟨T, hTS, hxT⟩
    rw [hF] at hTS
    rcases hTS with ⟨n, rfl⟩
    exact (mem_iInter.1 hxH (Sum.inr n)) (subset_closure hxT)
  · rcases hDense.nonempty with ⟨x, hxA⟩
    have hx_union : x ∈ ⋃₀ S := hA_subset hxA
    rcases mem_sUnion.1 hx_union with ⟨T, hTS, _⟩
    exact hS_nonempty ⟨T, hTS⟩

theorem nonempty_open_not_meagre_in_itself {U : Set X} (hUopen : IsOpen U)
    (hUne : U.Nonempty) :
    ¬ IsMeagre (Set.univ : Set U) := by
  let completeMetricOnX : UpgradedIsCompletelyMetrizableSpace X :=
    upgradeIsCompletelyMetrizable X
  let : MetricSpace X := completeMetricOnX.toMetricSpace
  have hX_complete : IsMetricComplete X :=
    isMetricComplete_of_upgraded X completeMetricOnX
  let relativeSpace : Type _ := U
  change ¬ IsMeagre (Set.univ : Set relativeSpace)
  intro hmeagre
  rcases isMeagre_iff_countable_union_isNowhereDense.1 hmeagre with
    ⟨S, hS_nowhere, hS_count, hcover⟩
  by_cases hS_nonempty : S.Nonempty
  · rcases hS_count.exists_eq_range hS_nonempty with ⟨N, hN⟩
    have hNnowhere : ∀ n, IsNowhereDense (N n) := by
      intro n
      apply hS_nowhere
      rw [hN]
      exact mem_range_self n
    have hNcover : (Set.univ : Set relativeSpace) = ⋃ n, N n := by
      apply subset_antisymm
      · intro x hx
        rcases mem_sUnion.1 (hcover hx) with ⟨T, hTS, hxT⟩
        rw [hN] at hTS
        rcases hTS with ⟨n, rfl⟩
        exact mem_iUnion.2 ⟨n, hxT⟩
      · exact subset_univ _
    let H : ℕ → Set relativeSpace := fun n => (closure (N n))ᶜ
    let G : ℕ → Set X := fun n => Subtype.val '' H n
    have hHopen : ∀ n, IsOpen (H n) := fun _ => isClosed_closure.isOpen_compl
    have hHdense : ∀ n, Dense (H n) := fun n =>
      (isClosed_isNowhereDense_iff_compl.1 ⟨isClosed_closure, (hNnowhere n).closure⟩).2
    have hGopen : ∀ n, IsOpen (G n) := fun n =>
      hUopen.isOpenEmbedding_subtypeVal.isOpenMap _ (hHopen n)
    have hGdense : ∀ n, U ⊆ closure (G n) := by
      intro n x hx
      have h := hHdense n (⟨x, hx⟩ : U)
      rw [hUopen.isOpenEmbedding_subtypeVal.isEmbedding.closure_eq_preimage_closure_image] at h
      exact h
    obtain ⟨x, hxU, hxG⟩ := baire_open_intersection hX_complete hUopen hUne hGopen hGdense
    have hxH : (⟨x, hxU⟩ : U) ∈ ⋂ n, H n := by
      apply mem_iInter.2
      intro n
      rcases mem_iInter.1 hxG n with ⟨y, hy, hyx⟩
      have heq : y = (⟨x, hxU⟩ : U) := Subtype.ext hyx
      rwa [← heq]
    have hxN : (⟨x, hxU⟩ : U) ∈ ⋃ n, N n := by
      rw [← hNcover]
      trivial
    obtain ⟨n, hxn⟩ := mem_iUnion.1 hxN
    exact (mem_iInter.1 hxH n) (subset_closure hxn)
  · obtain ⟨x, hx⟩ := hUne
    rcases mem_sUnion.1 (hcover (mem_univ (⟨x, hx⟩ : U))) with ⟨T, hTS, _⟩
    exact hS_nonempty ⟨T, hTS⟩

/-!
## Alexandrov's theorem

| Book term | Lean name |
| --- | --- |
| `\termdefineas{Fsigma set@$\Fsigma$ set}{$\Fsigma$}` | `IsFsigma` |
| `\termdefineas{Gdelta set@$\Gdelta$ set}{$\Gdelta$}` | mathlib predicate `IsGδ` |
-/

def IsFsigma {Y : Type*} [TopologicalSpace Y] (s : Set Y) : Prop :=
  ∃ S : Set (Set Y), S.Countable ∧ (∀ t ∈ S, IsClosed t) ∧ s = ⋃₀ S

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    A subset of a topological space is \termdefineas{Fsigma set@$\Fsigma$ set}{$\Fsigma$} if it is a countable union of
    closed sets, and \termdefineas{Gdelta set@$\Gdelta$ set}{$\Gdelta$} if it is a countable intersection of open sets.
-/
theorem IsFsigma.isGdelta_compl {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (hs : IsFsigma s) :
    IsGδ sᶜ := by
  rcases hs with ⟨S, hScount, hSclosed, rfl⟩
  rw [compl_sUnion]
  exact IsGδ.sInter
    (fun t ht => by
      rcases ht with ⟨u, hu, rfl⟩
      exact (hSclosed u hu).isOpen_compl.isGδ)
    (hScount.image _)

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: theorem
  title: Theorem (Alexandrov)
-/
/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: proof
  excerpt: |
    Write
    $$A = \bigcap_{n \in \omega} U_n$$
    with each $U_n \IncludedIn X$ open. By the open-subspace result above, each $U_n$ is Polish.
    
    The diagonal embedding
    $$\iota : A \to \prod_{n} U_n, \qquad \iota(x) = \Tuple{x, x, x, \ldots}$$
    is a homeomorphism onto its image. By the universal property of the product topology, the coordinate inclusions
    $A \hookrightarrow U_n$ assemble into the continuous map $\iota$; by the universal property of the subspace topology,
    the zeroth-coordinate projection restricts to a continuous inverse on $\iota(A)$.
    The product $\prod_n U_n$ is Polish.
    
    We show that $\iota(A)$ is closed in $\prod_n U_n$; since the product is metrizable, it suffices to check closedness on
    convergent sequences. Suppose
    $$\iota(a^k)=\Tuple{a^k,a^k,\ldots}$$
    converges in the product to $\Sequence{b_n}{n\in\omega}$. Then $a^k \to b_n$ in each $U_n$, hence also in $X$.
    Since $X$
    is
    Hausdorff, limits in $X$ are unique, so all $b_n$ are one and the same point $x$. Because $x=b_n \in U_n$ for every $n$,
    we have $x \in A$, hence $\Sequence{b_n}{n\in\omega} = \iota(x) \in \iota(A)$.
    
    Thus $\iota(A)$ is closed. Hence $A$ is homeomorphic to a closed subspace of a Polish space, and is Polish.
-/
theorem gdelta_subspace_polish {s : Set X} (hs : IsGδ s) :
    PolishSpace s := by
  rcases isGδ_iff_eq_iInter_nat.1 hs with ⟨U, hUopen, hsU⟩
  have : ∀ n, PolishSpace (U n) := fun n => open_subspace_polish (hUopen n)
  let diag : s -> ∀ n, U n := fun x n =>
    ⟨x.1, by
      have hx : x.1 ∈ ⋂ n, U n := by simpa [hsU] using x.2
      exact mem_iInter.1 hx n⟩
  have hdiag_cont : Continuous diag := by
    refine continuous_pi fun n => ?_
    exact continuous_subtype_val.subtype_mk fun x =>
      (diag x n).2
  have hproj_cont : Continuous fun y : (∀ n, U n) => ((y 0 : U 0) : X) :=
    continuous_subtype_val.comp (continuous_apply 0)
  have hcomp :
    Topology.IsEmbedding ((fun y : (∀ n, U n) => ((y 0 : U 0) : X)) ∘ diag) := by
    have heq : (fun y : (∀ n, U n) => ((y 0 : U 0) : X)) ∘ diag = ((↑) : s → X) := rfl
    rw [heq]
    exact Topology.IsEmbedding.subtypeVal
  have hdiag_emb : Topology.IsEmbedding diag :=
    Topology.IsEmbedding.of_comp hdiag_cont hproj_cont hcomp
  have hclosed_range : IsClosed (Set.range diag) := by
    -- The product of the Polish spaces `U n` is metrizable, so closedness may
    -- be checked on convergent sequences, as in the book.
    refine IsSeqClosed.isClosed ?_
    intro y b hy hyb
    choose a ha using hy
    -- Every coordinate of `y k = diag (a k)` is the point `a k` of `X`, so for
    -- each `n` the sequence `a k` converges to `b n` in `X`.
    have hcoord : ∀ n, Tendsto (fun k => ((a k : s) : X)) atTop (𝓝 ((b n : U n) : X)) := by
      intro n
      have h1 : Tendsto (fun k => ((y k n : U n) : X)) atTop (𝓝 ((b n : U n) : X)) :=
        (continuous_subtype_val.tendsto (b n)).comp (tendsto_pi_nhds.1 hyb n)
      have h2 : (fun k => ((y k n : U n) : X)) = fun k => ((a k : s) : X) := by
        funext k
        rw [← ha k]
      rwa [h2] at h1
    -- Limits in the Hausdorff space `X` are unique, so all `b n` are one and
    -- the same point of `X`.
    let x : X := ((b 0 : U 0) : X)
    have hb : ∀ n, ((b n : U n) : X) = x := fun n =>
      tendsto_nhds_unique (hcoord n) (hcoord 0)
    -- That common point lies in every `U n`, hence in `A`, and the limit is
    -- its image under the diagonal.
    have hx : x ∈ s := by
      rw [hsU]
      refine mem_iInter.2 fun n => ?_
      rw [← hb n]
      exact (b n).2
    let xA : s := ⟨x, hx⟩
    have hdiag_xA : b = diag xA := by
      funext n
      exact Subtype.ext (hb n)
    exact ⟨xA, hdiag_xA.symm⟩
  exact ({ toIsEmbedding := hdiag_emb, isClosed_range := hclosed_range } :
    Topology.IsClosedEmbedding diag).polishSpace

/-- In a metric space every closed set `C` is `Gδ`, witnessed by the book's
explicit countable intersection of open `d(·, C) < 1/(n+1)` neighbourhoods. -/
theorem isGδ_of_isClosed_metric_neighborhoods {Z : Type*} [MetricSpace Z] {s : Set Z}
    (hs : IsClosed s) : IsGδ s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact IsGδ.empty
  · have hcov : s = ⋂ n : ℕ, {x : Z | Metric.infDist x s < 1 / (n + 1 : ℝ)} := by
      ext x
      simp only [mem_iInter, mem_ofPred_eq]
      rw [hs.mem_iff_infDist_zero hne]
      refine ⟨fun hx n => by rw [hx]; positivity, fun hx => ?_⟩
      by_contra hne0
      have hpos : 0 < Metric.infDist x s :=
        lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hne0)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact absurd (hx n) (not_lt.2 hn.le)
    rw [hcov]
    exact IsGδ.iInter_of_isOpen fun n =>
      isOpen_lt (Metric.continuous_infDist_pt s) continuous_const

private lemma ediam_lt_of_subset_ball {Y : Type*} [MetricSpace Y]
    {S : Set Y} {a : Y} {r ε : ℝ} (hr : 0 ≤ r)
    (hS : S ⊆ Metric.ball a r) (hε : r + r < ε) :
    ediam S < ENNReal.ofReal ε := by
  have hdiam : ediam S ≤ ENNReal.ofReal (r + r) := by
    apply Metric.ediam_le_of_forall_dist_le
    intro b hb c hc
    calc
      dist b c ≤ dist b a + dist c a := dist_triangle_right _ _ _
      _ ≤ r + r := (add_lt_add (Metric.mem_ball.1 (hS hb))
        (Metric.mem_ball.1 (hS hc))).le
  exact hdiam.trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (add_nonneg hr hr)).2 hε)

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: theorem
  title: Theorem (Alexandrov)
-/
/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: proof
  excerpt: |
    \textbf{From Polish to $\Gdelta$.} Suppose $A$ carries a complete metric $\rho$ inducing the subspace topology from $X$,
    and fix a compatible metric $d$ on $X$. For each $n \in \omega$, using explicit $d$-balls in $X$, define
    
    $$V_n \;=\; \bigcup\, \{\MetricBall{d}{x}{\delta} \,:\, x \in X,\; \delta > 0,\;
    \MetricDiameter{\rho}{\MetricBall{d}{x}{\delta} \cap A} < 1/(n+1)\},$$
    
    where only balls whose trace on $A$ is $\rho$-bounded are included in the union.
    
     Each $V_n$ is open, being a union
    of open $d$-balls in $X$. Since $\rho$ induces the subspace topology on $A$, every
    point of $A$ has arbitrarily small $X$-neighborhoods whose trace on $A$ has small $\rho$-diameter, so
    $A \IncludedIn V_n$ for every $n \in \omega$.
    
    We claim $A = \AmbientClosure{X}{A} \cap \bigcap_{n\in\omega} V_n$,
    where $\AmbientClosure{X}{A}$ denotes the closure of $A$
    in $X$.
    The closure factor excludes points away from $A$; the $V_n$'s force nearby traces of $A$ to have vanishing
    $\rho$-diameter.
    
    The inclusion $A \IncludedIn \AmbientClosure{X}{A} \cap \bigcap_{n\in\omega} V_n$ follows immediately from the preceding
    paragraph.
    
    For the reverse inclusion, take
    $$x \in \AmbientClosure{X}{A} \cap \bigcap_{n\in\omega} V_n.$$
    
    For each $n \in \omega$, choose an open neighborhood $B_n$ of $x$ in $X$ such that
    $$\MetricDiameter{\rho}{B_n \cap A} < 1/(n+1).$$
    Replacing $B_n$ by
    $$B_0 \cap \cdots \cap B_n \cap \MetricBall{d}{x}{1/(n+1)},$$
    we may assume
    
    $$B_0 \supseteq B_1 \supseteq \cdots
    \qquad\text{and}\qquad
    \MetricDiameter{d}{B_n}\to 0.$$
    Since $x \in \AmbientClosure{X}{A}$, every $B_n$ meets $A$. Choose $a_n \in B_n \cap A$.
    
    The sequence $\Sequence{a_n}{n\in\omega}$ is $\rho$-Cauchy because
    the $\rho$-diameters of the traces $B_n \cap A$ tend to
    $0$. Since $\rho$
    is complete, $a_n \to a$ in $\rho$ for some $a \in A$. 
    The $\rho$-topology agrees with the subspace topology, so $a_n
    \to a$ in $X$. On the other hand, $\MetricDiameter{d}{B_n}\to 0$ and $a_n \in B_n$ force $a_n \to x$ in $X$. Uniqueness
    of limits in the metric space $X$ gives $a=x$, hence $x \in A$.
    
    The set $\AmbientClosure{X}{A}$ is closed, and closed subsets of metric spaces are $\Gdelta$. The empty set is open and
    hence $\Gdelta$. 
    If $F\ne\emptyset$ is closed, then
    $$
    F = \bigcap_{n \in \omega} \{x \in X : d(x,F) < 1/(n+1)\},
    $$
    a countable intersection of open sets.
    
    Also, $\bigcap_{n\in\omega} V_n$ is $\Gdelta$ because each $V_n$ is open. Therefore
    $$A=\AmbientClosure{X}{A}\cap\bigcap_{n\in\omega} V_n$$
    is $\Gdelta$ in $X$.
-/
theorem polish_subspace_isGdelta {A : Set X} [PolishSpace A] :
    IsGδ A := by
  classical
  let completeMetricOnX : UpgradedIsCompletelyMetrizableSpace X :=
    upgradeIsCompletelyMetrizable X
  let : MetricSpace X := completeMetricOnX.toMetricSpace
  let completeMetricOnA : UpgradedIsCompletelyMetrizableSpace A :=
    upgradeIsCompletelyMetrizable A
  let : PseudoMetricSpace A := completeMetricOnA.toPseudoMetricSpace
  let : MetricSpace A := completeMetricOnA.toMetricSpace
  let : PseudoEMetricSpace A := completeMetricOnA.toMetricSpace.toEMetricSpace.toPseudoEMetricSpace
  let : WeakPseudoEMetricSpace A := PseudoEMetricSpace.toWeakPseudoEMetricSpace A
  let : EDist A := completeMetricOnA.toMetricSpace.toEDist
  let : UniformSpace A := completeMetricOnA.toPseudoMetricSpace.toUniformSpace
  have hA_complete : IsMetricComplete A :=
    isMetricComplete_of_upgraded A completeMetricOnA
  -- Use the same zero-based indices as the book.
  let bound : ℕ -> ℝ := fun n => 1 / ((n : ℝ) + 1)
  -- The preimage is the trace on A, measured with its complete metric ρ.
  -- Use extended diameter so an unbounded trace cannot have real diameter zero.
  let smallTrace : Set X -> ℕ -> Prop := fun U n =>
    ediam (((↑) : A -> X) ⁻¹' U) < ENNReal.ofReal (bound n)
  let V : ℕ -> Set X := fun n =>
    ⋃₀ {B : Set X | ∃ x : X, ∃ δ > 0, B = Metric.ball x δ ∧ smallTrace B n}
  have bound_pos : ∀ n, 0 < bound n := by
    intro n
    positivity
  have bound_third_pos : ∀ n, 0 < bound n / 3 := by
    intro n
    positivity
  have bound_third_add : ∀ n, bound n / 3 + bound n / 3 < bound n := by
    intro n
    have hpos := bound_pos n
    linarith
  have hVopen : ∀ n, IsOpen (V n) := by
    intro n
    apply isOpen_sUnion
    rintro B ⟨x, δ, _, rfl, _⟩
    exact isOpen_ball
  have hA_subset_V : A ⊆ ⋂ n, V n := by
    intro x hx
    rw [mem_iInter]
    intro n
    let a : A := ⟨x, hx⟩
    let r : ℝ := bound n / 3
    have hrpos : 0 < r := bound_third_pos n
    have hball_open : IsOpen (Metric.ball a r : Set A) := isOpen_ball
    rcases isOpen_induced_iff.mp hball_open with ⟨U, hUopen, hUpre⟩
    have hxU : x ∈ U := by
      have : a ∈ Metric.ball a r := mem_ball_self hrpos
      have : a ∈ ((↑) : A -> X) ⁻¹' U := by simpa [hUpre] using this
      exact this
    obtain ⟨δ, hδpos, hδU⟩ := Metric.isOpen_iff.1 hUopen x hxU
    have hsmall : smallTrace (Metric.ball x δ) n := by
      dsimp only [smallTrace]
      apply ediam_lt_of_subset_ball hrpos.le (a := a) _ (bound_third_add n)
      intro b hb
      have : b ∈ ((↑) : A -> X) ⁻¹' U := hδU hb
      simpa [hUpre] using this
    exact mem_sUnion.2 ⟨Metric.ball x δ,
      ⟨x, δ, hδpos, rfl, hsmall⟩, Metric.mem_ball_self hδpos⟩
  have hclosure_inter_subset : closure A ∩ ⋂ n, V n ⊆ A := by
    intro x hx
    have hx_closure : x ∈ closure A := hx.1
    have hxV : ∀ n, x ∈ V n := by
      intro n
      exact mem_iInter.1 hx.2 n
    have hU_exists :
        ∀ n, ∃ U : Set X, IsOpen U ∧ smallTrace U n ∧ x ∈ U := by
      intro n
      rcases mem_sUnion.1 (hxV n) with ⟨U, hU, hxU⟩
      rcases hU with ⟨y, δ, _, hUball, hUsmall⟩
      exact ⟨U, hUball ▸ isOpen_ball, hUsmall, hxU⟩
    choose U hU_spec using hU_exists
    have hUopen : ∀ n, IsOpen (U n) := fun n => (hU_spec n).1
    have hUsmall : ∀ n, smallTrace (U n) n := fun n => (hU_spec n).2.1
    have hxU : ∀ n, x ∈ U n := fun n => (hU_spec n).2.2
    let W : ℕ -> Set X := fun N =>
      (⋂₀ Set.range (fun i : Fin (N + 1) => U i)) ∩ Metric.ball x (bound N)
    have hWopen : ∀ N, IsOpen (W N) := by
      intro N
      have hfinite_open : IsOpen (⋂₀ Set.range (fun i : Fin (N + 1) => U i)) := by
        exact (finite_range _).isOpen_sInter (by
          rintro T ⟨i, rfl⟩
          exact hUopen i)
      exact hfinite_open.inter isOpen_ball
    have hxW : ∀ N, x ∈ W N := by
      intro N
      constructor
      · intro T hT
        rcases hT with ⟨i, rfl⟩
        exact hxU i
      · exact mem_ball_self (bound_pos N)
    have hA_W_nonempty : ∀ N, (A ∩ W N).Nonempty := by
      intro N
      rcases mem_closure_iff_nhds'.1 hx_closure (W N)
          ((hWopen N).mem_nhds (hxW N)) with ⟨a, haW⟩
      exact ⟨a, a.2, haW⟩
    let aSeq : ℕ -> A := fun N =>
      ⟨Classical.choose (hA_W_nonempty N),
        (Classical.choose_spec (hA_W_nonempty N)).1⟩
    have haSeq_W : ∀ N, (aSeq N : X) ∈ W N := by
      intro N
      exact (Classical.choose_spec (hA_W_nonempty N)).2
    have haSeq_cauchy : CauchySeq aSeq := by
      exact (Metric.cauchySeq_iff (u := aSeq)).2 fun ε εpos => by
        rcases exists_nat_one_div_lt εpos with ⟨N, hN⟩
        refine ⟨N, fun m hm n hn => ?_⟩
        have hmU : (aSeq m : X) ∈ U N := by
          exact (haSeq_W m).1 (U N) ⟨⟨N, Nat.lt_succ_of_le hm⟩, rfl⟩
        have hnU : (aSeq n : X) ∈ U N := by
          exact (haSeq_W n).1 (U N) ⟨⟨N, Nat.lt_succ_of_le hn⟩, rfl⟩
        have hdist : dist (aSeq m) (aSeq n) < bound N := by
          apply edist_lt_ofReal.1
          exact (edist_le_ediam_of_mem
            (s := ((↑) : A -> X) ⁻¹' U N) hmU hnU).trans_lt (hUsmall N)
        exact hdist.trans hN
    obtain ⟨a, ha_lim⟩ : ∃ a, Tendsto aSeq atTop (𝓝 a) :=
      hA_complete aSeq haSeq_cauchy
    have ha_lim_X : Tendsto (fun n => (aSeq n : X)) atTop (𝓝 (a : X)) :=
      continuous_subtype_val.tendsto a |>.comp ha_lim
    have hx_lim_X : Tendsto (fun n => (aSeq n : X)) atTop (𝓝 x) := by
      rw [Metric.tendsto_atTop]
      intro ε εpos
      rcases exists_nat_one_div_lt εpos with ⟨N, hN⟩
      refine ⟨N, fun n hn => ?_⟩
      have hball : (aSeq n : X) ∈ Metric.ball x (bound n) := (haSeq_W n).2
      have hle : bound n ≤ bound N := by
        dsimp [bound]
        gcongr
      exact (Metric.mem_ball.1 hball).trans_le hle |>.trans hN
    have hax : (a : X) = x :=
      tendsto_nhds_unique ha_lim_X hx_lim_X
    exact hax ▸ a.2
  have h_eq : A = closure A ∩ ⋂ n, V n := by
    exact Set.Subset.antisymm
      (fun x hx => ⟨subset_closure hx, hA_subset_V hx⟩)
      hclosure_inter_subset
  rw [h_eq]
  exact (isGδ_of_isClosed_metric_neighborhoods isClosed_closure).inter (IsGδ.iInter_of_isOpen hVopen)

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: theorem
  title: Theorem (Alexandrov)
-/
theorem alexandrov_theorem {A : Set X} :
    PolishSpace A ↔ IsGδ A := by
  constructor
  · intro hA
    have : PolishSpace A := hA
    exact polish_subspace_isGdelta
  · exact gdelta_subspace_polish

theorem irrationals_polish :
    PolishSpace ({x : ℝ | Irrational x} : Set ℝ) :=
  gdelta_subspace_polish irrationals_are_gdelta

/-! ## Fsigma and Gdelta examples in the real line -/

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: proposition
  title: Rationals and irrationals
-/
/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The rationals $\QQ = \bigcup_{q \in \QQ} \{q\}$ are $\Fsigma$, since singletons are closed. They are not $\Gdelta$:
    $\QQ$ is meager, since each singleton is closed and nowhere dense, while a dense $\Gdelta$ subset of $\R$ is comeager
    since its complement is a countable union of closed sets with empty interior. If $\QQ$ were $\Gdelta$, it would be
    both meager and comeager, so its complement $\SetDifference{\R}{\QQ}$ would also be meager. Then $\R$ would be a
    union of two \termuseas{meager set}{meager sets}, contradicting the \termuse{Baire category theorem} in
    §{sec:baire-category}. By duality, the irrationals $\SetDifference{\R}{\QQ}$ are $\Gdelta$ but not $\Fsigma$.
    \end{proof}
-/
theorem rationals_are_fsigma :
    IsFsigma (Set.range ((↑) : ℚ -> ℝ)) := by
  refine ⟨Set.range (fun q : ℚ => ({(q : ℝ)} : Set ℝ)), countable_range _, ?_, ?_⟩
  · rintro t ⟨q, rfl⟩
    exact isClosed_singleton
  · ext x
    simp

theorem real_singleton_nowhere_dense (x : ℝ) :
    IsNowhereDense ({x} : Set ℝ) := by
  rw [isClosed_singleton.isNowhereDense_iff]
  exact interior_singleton x

theorem rational_singleton_nowhere_dense (q : ℚ) :
    IsNowhereDense ({q} : Set ℚ) := by
  rw [isClosed_singleton.isNowhereDense_iff]
  exact interior_singleton q

theorem rationals_are_meagre :
    IsMeagre (Set.range ((↑) : ℚ -> ℝ)) := by
  rw [Set.range_eq_iUnion]
  exact isMeagre_iUnion fun q : ℚ =>
    (real_singleton_nowhere_dense (q : ℝ)).isMeagre

theorem rational_space_meagre :
    IsMeagre (Set.univ : Set ℚ) := by
  rw [← Set.iUnion_of_singleton ℚ]
  exact isMeagre_iUnion fun q : ℚ =>
    (rational_singleton_nowhere_dense q).isMeagre

theorem rationals_not_polish :
    ¬ PolishSpace ℚ := by
  intro hpolish
  have : PolishSpace ℚ := hpolish
  exact (nonempty_open_not_meagre (X := ℚ) isOpen_univ univ_nonempty) rational_space_meagre

theorem rationals_not_gdelta :
    ¬ IsGδ (Set.range ((↑) : ℚ -> ℝ)) := by
  intro hG
  exact (dense_gdelta_not_meagre hG Rat.denseRange_cast) rationals_are_meagre

/-- Matches the book's route via Alexandrov's theorem: unlike `rationals_not_polish`, which argues
directly from meagreness of `ℚ` in itself, this goes through `alexandrov_theorem` and
`rationals_not_gdelta` applied to the rationals as a subspace of `ℝ`. -/
theorem rationals_range_not_polish :
    ¬ PolishSpace (Set.range ((↑) : ℚ -> ℝ)) := fun hpolish =>
  rationals_not_gdelta (alexandrov_theorem.1 hpolish)

theorem irrationals_not_fsigma :
    ¬ IsFsigma ({x : ℝ | Irrational x} : Set ℝ) := by
  intro hF
  have hG : IsGδ (({x : ℝ | Irrational x} : Set ℝ)ᶜ) := hF.isGdelta_compl
  have h_compl :
      (({x : ℝ | Irrational x} : Set ℝ)ᶜ) = Set.range ((↑) : ℚ -> ℝ) := by
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq, Irrational, not_not]
  exact rationals_not_gdelta (by simpa [h_compl] using hG)

/-!
## Sequence spaces

| Book term | Lean name |
| --- | --- |
| `\termdefine{zero-dimensional}` | `IsZeroDimensional` |
| `\termdefine{isolated point}` | `IsIsolatedPointByOpenSingleton` |
| `\termdefineas{perfect space}{perfect}` | `IsPerfectSpaceByNoIsolatedPoint` (iff mathlib class `PerfectSpace`) |
| `\termdefine{Cantor space}` | `cantor_space` |
| `\termdefine{Baire space}` | `baire_space` |
| `\termdefine{Hilbert cube}` | `hilbert_cube` |
| `\termdefine{space of real sequences}` | `real_sequence_space` |
-/

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    A topological space is \termdefine{zero-dimensional} if it has a base
    of clopen sets.
-/
/-- Book term `\termdefine{zero-dimensional}`:
a space has a base of clopen sets. -/
abbrev IsZeroDimensional (Y : Type*) [TopologicalSpace Y] : Prop :=
  IsTopologicalBasis {s : Set Y | IsClopen s}

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The name zero-dimensional reflects the equivalence of this condition with having small inductive dimension at most $\NonnegativeDimensionLevel{0}$.
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{zero-dimension equivalence}{The three conditions for zero dimension}]
-/
/-@ booklink:
  exclude-books: polish-space-ch1
  source: polish-space-book/appendix-metric-spaces.md
  target: prose
  excerpt: |
    The empty space satisfies all four conditions, so suppose $X$ is nonempty.
    The equivalence between a clopen base and $\SmallInductiveDimension{X}\le 0$ follows directly from the definition.
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, $\SmallInductiveDimension{X}\le 0$ means that each point $x$ and its open neighborhood $U$ admit an open
    set $V$ with
    $$x\in V\IncludedIn U,\qquad \AmbientBoundary{X}{V}=\emptyset.$$
    Indeed, the boundary must have dimension $-1$, so it must be empty. Thus every open neighborhood of a point contains a
    clopen neighborhood of that point.
-/
theorem zero_dimensional_iff_small_inductive (Y : Type) [TopologicalSpace Y] :
    IsZeroDimensional Y ↔ HasSmallInductiveDimensionLE Y 0 :=
  zeroDimensionalSpace_iff_isTopologicalBasis_isClopen.symm

/-! ### Big inductive dimension and covering dimension at `0`

Mathlib has no large-inductive-dimension or covering-dimension theory, so we build the `≤ 0`
case for each directly. The hard direction below (a clopen basis gives closed/open separation)
is the dimension-`0` case of Urysohn's dimension-coincidence theorem; the proof builds a
shrinking sequence of finite clopen partitions from a countable clopen basis, and for each point
of the closed set picks out its shallowest safely-contained partition cell. -/

/-- `Ind Y ≤ 0`: every closed set contained in an open set can be separated from its complement
by a clopen set. -/
def HasBigInductiveDimensionLEZero (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ ⦃A U : Set Y⦄, IsClosed A → IsOpen U → A ⊆ U → ∃ V, IsClopen V ∧ A ⊆ V ∧ V ⊆ U

/-@ booklink:
  exclude-books: polish-space-ch1
  source: polish-space-book/appendix-metric-spaces.md
  target: prose
  excerpt: |
    Conversely, $\LargeInductiveDimension{X}\le 0$ gives a clopen base by taking $F=\{x\}$, which is closed in a metrizable
    space. If $\CoveringDimension{X}\le 0$, apply its defining property to $\{U,\SetDifference{X}{\{x\}}\}$, where $U$ is
    an open neighborhood of $x$. The member of the disjoint refinement containing $x$ is clopen and is contained in $U$.
    This also gives a clopen base and completes the proof.
-/
/-- The easy direction: closed/open separation gives a clopen basis, by separating each point
from any open neighbourhood. -/
theorem HasBigInductiveDimensionLEZero.isZeroDimensional {Y : Type*} [TopologicalSpace Y]
    [T1Space Y] (h : HasBigInductiveDimensionLEZero Y) : IsZeroDimensional Y := by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun s hs => hs.2) fun x U hxU hUopen => ?_
  obtain ⟨V, hV, hxV, hVU⟩ := h isClosed_singleton hUopen (Set.singleton_subset_iff.2 hxU)
  exact ⟨V, hV, Set.singleton_subset_iff.1 hxV, hVU⟩

/-- A countable family of clopen sets that is still a topological basis. -/
theorem IsZeroDimensional.exists_countable_clopen_basis {Y : Type*} [TopologicalSpace Y]
    [SecondCountableTopology Y] (hY : IsZeroDimensional Y) :
    ∃ B : ℕ → Set Y, (∀ n, IsClopen (B n)) ∧ IsTopologicalBasis (Set.range B) := by
  obtain ⟨s, hst, hs_count, hs_basis⟩ := hY.exists_countable
  obtain ⟨B, hB⟩ := (hs_count.insert ∅).exists_eq_range (Set.insert_nonempty ∅ s)
  refine ⟨B, fun n => ?_, ?_⟩
  · rcases (hB ▸ Set.mem_range_self n : B n ∈ insert ∅ s) with h | h
    · exact h ▸ isClopen_empty
    · exact hst h
  · rw [← hB]
    refine isTopologicalBasis_of_isOpen_of_nhds
      (fun t ht => ht.elim (fun h => h ▸ isOpen_empty) fun h => hs_basis.isOpen h)
      fun x U hxU hUopen => ?_
    obtain ⟨t, ht, hxt, htU⟩ := hs_basis.exists_subset_of_mem_open hxU hUopen
    exact ⟨t, Set.mem_insert_of_mem _ ht, hxt, htU⟩

section AtomAt

variable {Y : Type*} [TopologicalSpace Y]

open Classical in
/-- The atom, at level `k`, of the finite clopen partition generated by `B 0, ..., B (k - 1)`,
containing `x`: the intersection over `i < k` of `B i` or its complement, whichever contains `x`.
Shrinking `k` gives a neighbourhood basis at `x` once `Set.range B` is a topological basis. -/
noncomputable def atomAt (B : ℕ → Set Y) (k : ℕ) (x : Y) : Set Y :=
  ⋂ i ∈ Finset.range k, if x ∈ B i then B i else (B i)ᶜ

theorem isClopen_atomAt {B : ℕ → Set Y} (hB : ∀ n, IsClopen (B n)) (k : ℕ) (x : Y) :
    IsClopen (atomAt B k x) := by
  refine isClopen_biInter_finset fun i _ => ?_
  classical
  split_ifs
  · exact hB i
  · exact (hB i).compl

omit [TopologicalSpace Y] in
theorem mem_atomAt (B : ℕ → Set Y) (k : ℕ) (x : Y) : x ∈ atomAt B k x := by
  refine Set.mem_iInter₂.2 fun i _ => ?_
  classical
  split_ifs with h
  · exact h
  · exact h

omit [TopologicalSpace Y] in
theorem atomAt_antitone (B : ℕ → Set Y) (x : Y) : Antitone fun k => atomAt B k x := by
  intro j k hjk y hy
  simp only [atomAt, Set.mem_iInter₂] at hy ⊢
  exact fun i hi => hy i (Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hjk))

omit [TopologicalSpace Y] in
theorem atomAt_eq_of_mem (B : ℕ → Set Y) {k : ℕ} {x y : Y} (hy : y ∈ atomAt B k x) :
    atomAt B k y = atomAt B k x := by
  classical
  simp only [atomAt]
  refine Set.iInter₂_congr fun i hi => ?_
  have hyi := Set.mem_iInter₂.1 hy i hi
  by_cases hxi : x ∈ B i
  · rw [ite_eq_left hxi] at hyi ⊢
    rw [ite_eq_left hyi]
  · rw [ite_eq_right hxi] at hyi ⊢
    rw [ite_eq_right hyi]

theorem exists_atomAt_subset (B : ℕ → Set Y) {x : Y} {U : Set Y} (hU : IsOpen U) (hxU : x ∈ U)
    (hbasis : IsTopologicalBasis (Set.range B)) :
    ∃ k, atomAt B k x ⊆ U := by
  classical
  obtain ⟨_, ⟨n, rfl⟩, hxn, hnU⟩ := hbasis.exists_subset_of_mem_open hxU hU
  refine ⟨n + 1, fun y hy => ?_⟩
  have hyn := Set.mem_iInter₂.1 hy n (Finset.self_mem_range_succ n)
  rw [ite_eq_left hxn] at hyn
  exact hnU hyn

end AtomAt

/-- The hard direction: a countable clopen basis lets us separate any closed `A` from the
complement of any open `U ⊇ A` by a clopen set. -/
theorem IsZeroDimensional.hasBigInductiveDimensionLEZero {Y : Type*} [TopologicalSpace Y]
    [SecondCountableTopology Y] (hY : IsZeroDimensional Y) :
    HasBigInductiveDimensionLEZero Y := by
  obtain ⟨B, hB, hbasis⟩ := hY.exists_countable_clopen_basis
  intro A U hA hU hAU
  classical
  set firstSafe : Y → ℕ := fun x =>
    if h : ∃ k, atomAt B k x ⊆ U then Nat.find h else 0 with hfirstSafe
  have firstSafe_spec : ∀ x ∈ U, atomAt B (firstSafe x) x ⊆ U := by
    intro x hx
    have h := exists_atomAt_subset B hU hx hbasis
    simp only [hfirstSafe, dite_eq_left h]
    exact Nat.find_spec h
  set V : Set Y := ⋃ x ∈ A, atomAt B (firstSafe x) x with hV
  have hVopen : IsOpen V := isOpen_biUnion fun x _ => (isClopen_atomAt hB _ _).isOpen
  have hAV : A ⊆ V := fun x hx => Set.mem_biUnion hx (mem_atomAt B (firstSafe x) x)
  have hVU : V ⊆ U := Set.iUnion₂_subset fun x hx => firstSafe_spec x (hAU hx)
  have hVclosed : IsClosed V := by
    rw [← isOpen_compl_iff]
    refine isOpen_iff_forall_mem_open.2 fun p hp => ?_
    have hpA : p ∉ A := fun hpA => hp (hAV hpA)
    obtain ⟨K, hK⟩ := exists_atomAt_subset B hA.isOpen_compl hpA hbasis
    refine ⟨atomAt B K p, ?_, (isClopen_atomAt hB K p).isOpen, mem_atomAt B K p⟩
    rw [Set.subset_compl_iff_disjoint_right, Set.disjoint_left]
    rintro y hyK hyV
    simp only [hV, Set.mem_iUnion] at hyV
    obtain ⟨x, hxA, hyx⟩ := hyV
    have hxU : x ∈ U := hAU hxA
    set j := firstSafe x with hj
    rcases le_or_gt j K with hjK | hjK
    · -- `y`'s atom at level `j` is shared by `x` and, via the same atom, by `p`.
      have hyj : y ∈ atomAt B j p := atomAt_antitone B p hjK hyK
      have hxy : atomAt B j y = atomAt B j x := atomAt_eq_of_mem B hyx
      have hpy : atomAt B j y = atomAt B j p := atomAt_eq_of_mem B hyj
      have hpx : atomAt B j p = atomAt B j x := hpy ▸ hxy
      have hpx' : p ∈ atomAt B j x := hpx ▸ mem_atomAt B j p
      exact hp (Set.mem_biUnion hxA hpx')
    · -- `y`'s atom at level `j` is nested inside `x`'s and `p`'s atoms at level `K`.
      have hyxK : y ∈ atomAt B K x := atomAt_antitone B x hjK.le hyx
      have hxpK : atomAt B K x = atomAt B K p :=
        (atomAt_eq_of_mem B hyxK).symm.trans (atomAt_eq_of_mem B hyK)
      have hxK : x ∈ atomAt B K p := hxpK ▸ mem_atomAt B K x
      exact hK hxK hxA
  exact ⟨V, ⟨hVclosed, hVopen⟩, hAV, hVU⟩

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    For separable metrizable spaces, having large inductive dimension at most $\NonnegativeDimensionLevel{0}$ and having Lebesgue covering dimension
    at most $\NonnegativeDimensionLevel{0}$ are also equivalent to this condition.
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{zero-dimension equivalence}{The three conditions for zero dimension}]
-/
theorem zero_dimensional_iff_big_inductive (Y : Type) [TopologicalSpace Y] [T1Space Y]
    [SecondCountableTopology Y] :
    IsZeroDimensional Y ↔ HasBigInductiveDimensionLEZero Y :=
  ⟨IsZeroDimensional.hasBigInductiveDimensionLEZero, HasBigInductiveDimensionLEZero.isZeroDimensional⟩

/-! ### Lebesgue covering dimension `≤ 0` -/

/-- `dim Y ≤ 0`: every finite open cover has a pairwise disjoint open refinement that still
covers the space. -/
def HasCoveringDimensionLEZero (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ {I : Type} [Finite I] (U : I → Set Y), (∀ i, IsOpen (U i)) → (⋃ i, U i) = Set.univ →
    ∃ V : I → Set Y, (∀ i, IsOpen (V i)) ∧ (⋃ i, V i) = Set.univ ∧
      Pairwise (fun i j => Disjoint (V i) (V j)) ∧ ∀ i, V i ⊆ U i

/-- A finite family of pairwise disjoint open sets covering the space is automatically a family
of clopen sets: each member is the complement of the (open) union of the others. -/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $\CoveringDimension{X}\le 0$, the refinement must therefore have pairwise disjoint members.
    After empty members are discarded, it is a partition into clopen sets: the complement of each member is the union of the
    others.
    All three dimensions are $-1$ exactly for the empty space, so for a nonempty space the corresponding bound by $0$ means
    that the dimension is $0$.
-/
theorem isClopen_of_pairwiseDisjoint_iUnion_eq_univ {Y : Type*} [TopologicalSpace Y]
    {I : Type*} [Finite I] {V : I → Set Y} (hVo : ∀ i, IsOpen (V i))
    (hVU : (⋃ i, V i) = Set.univ) (hVd : Pairwise (fun i j => Disjoint (V i) (V j))) (i : I) :
    IsClopen (V i) := by
  refine ⟨?_, hVo i⟩
  have hcompl : V i = (⋃ j ∈ ({i}ᶜ : Set I), V j)ᶜ := by
    rw [Set.compl_eq_univ_sdiff, ← hVU]
    ext x
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_sdiff]
    constructor
    · intro hx
      refine ⟨⟨i, hx⟩, fun ⟨j, hji, hxj⟩ => ?_⟩
      exact Set.disjoint_left.mp (hVd hji) hxj hx
    · rintro ⟨⟨j, hxj⟩, hforall⟩
      rcases eq_or_ne j i with rfl | hji
      · exact hxj
      · exact absurd ⟨j, hji, hxj⟩ hforall
  rw [hcompl]
  exact (isOpen_biUnion fun j _ => hVo j).isClosed_compl

/-- The key induction, relativised to an arbitrary closed set `S`: shrinks a finite open cover
of `S` to a pairwise disjoint open refinement still covering `S`. Relativising is needed for the
induction step, which only knows how to cover the closed leftover `S \ W` after peeling off one
set of the cover. -/
theorem HasBigInductiveDimensionLEZero.exists_pairwiseDisjoint_refinement {Y : Type*}
    [TopologicalSpace Y] (h : HasBigInductiveDimensionLEZero Y) {I : Type} [Finite I] :
    ∀ (S : Set Y), IsClosed S → ∀ (U : I → Set Y), (∀ i, IsOpen (U i)) → (S ⊆ ⋃ i, U i) →
      ∃ V : I → Set Y, (∀ i, IsOpen (V i)) ∧ (S ⊆ ⋃ i, V i) ∧
        Pairwise (fun i j => Disjoint (V i) (V j)) ∧ ∀ i, V i ⊆ U i := by
  induction I using Finite.induction_empty_option with
  | of_equiv e IH =>
    intro S hS U hUo hUcov
    obtain ⟨V, hVo, hVcov, hVd, hVsub⟩ := IH S hS (U ∘ e) (fun i => hUo (e i))
      (by rwa [show (⋃ i, (U ∘ e) i) = ⋃ i, U i from e.surjective.iUnion_comp U])
    refine ⟨V ∘ e.symm, fun i => hVo _,
      by rwa [show (⋃ i, (V ∘ e.symm) i) = ⋃ i, V i from e.symm.surjective.iUnion_comp V],
      fun i j hij => hVd (e.symm.injective.ne hij), fun i => by simpa using hVsub (e.symm i)⟩
  | h_empty =>
    intro S hS U _ hUcov
    have hSempty : S = ∅ := by
      have : (⋃ i : PEmpty, U i) = (∅ : Set Y) := Set.iUnion_of_empty U
      rw [this] at hUcov
      exact Set.subset_empty_iff.mp hUcov
    exact ⟨U, fun i => i.elim, hSempty ▸ Set.empty_subset _, fun i _ _ => i.elim,
      fun i => Subset.rfl⟩
  | @h_option I _ IH =>
    intro S hSclosed U hUo hUcov
    set A : Set Y := S \ (⋃ i : I, U (some i)) with hAdef
    have hAclosed : IsClosed A := hSclosed.sdiff (isOpen_iUnion fun i => hUo (some i))
    have hAU : A ⊆ U none := by
      intro x hx
      have hxS : x ∈ S := hx.1
      have hxnotsome : x ∉ ⋃ i : I, U (some i) := hx.2
      rcases Set.mem_iUnion.1 (hUcov hxS) with ⟨i, hi⟩
      cases i with
      | none => exact hi
      | some j => exact absurd (Set.mem_iUnion.2 ⟨j, hi⟩) hxnotsome
    obtain ⟨W, hWclopen, hAW, hWU⟩ := h hAclosed (hUo none) hAU
    have hS'closed : IsClosed (S \ W) := hSclosed.sdiff hWclopen.isOpen
    have hS'cov : (S \ W) ⊆ ⋃ i : I, (U (some i) ∩ Wᶜ) := by
      intro x hx
      have hxS : x ∈ S := hx.1
      have hxW : x ∉ W := hx.2
      have hxA : x ∉ A := fun hxA => hxW (hAW hxA)
      rw [hAdef, Set.mem_sdiff, not_and, not_not] at hxA
      rcases Set.mem_iUnion.1 (hxA hxS) with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi, hxW⟩
    obtain ⟨V', hV'o, hV'cov, hV'd, hV'sub⟩ := IH (S \ W) hS'closed (fun i => U (some i) ∩ Wᶜ)
      (fun i => (hUo (some i)).inter hWclopen.compl.isOpen) hS'cov
    refine ⟨fun i => Option.rec W V' i, ?_, ?_, ?_, ?_⟩
    · rintro (_ | i)
      · exact hWclopen.isOpen
      · exact hV'o i
    · intro x hxS
      by_cases hxW : x ∈ W
      · exact Set.mem_iUnion.2 ⟨none, hxW⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hV'cov ⟨hxS, hxW⟩)
        exact Set.mem_iUnion.2 ⟨some i, hi⟩
    · rintro (_ | i) (_ | j) hij
      · exact absurd rfl hij
      · exact Set.disjoint_left.2 fun x hxW hxV' => (hV'sub j hxV').2 hxW
      · exact Set.disjoint_left.2 fun x hxV' hxW => (hV'sub i hxV').2 hxW
      · exact hV'd (fun h => hij (congrArg some h))
    · rintro (_ | i)
      · exact hWU
      · exact (hV'sub i).trans Set.inter_subset_left

theorem HasBigInductiveDimensionLEZero.hasCoveringDimensionLEZero {Y : Type*}
    [TopologicalSpace Y] (h : HasBigInductiveDimensionLEZero Y) :
    HasCoveringDimensionLEZero Y := by
  intro I _ U hUo hUcov
  obtain ⟨V, hVo, hVcov, hVd, hVsub⟩ :=
    h.exists_pairwiseDisjoint_refinement Set.univ isClosed_univ U hUo (hUcov ▸ Set.Subset.rfl)
  exact ⟨V, hVo, Set.univ_subset_iff.mp hVcov, hVd, hVsub⟩

theorem HasCoveringDimensionLEZero.hasBigInductiveDimensionLEZero {Y : Type*}
    [TopologicalSpace Y] (h : HasCoveringDimensionLEZero Y) :
    HasBigInductiveDimensionLEZero Y := by
  intro A U hA hU hAU
  obtain ⟨V, hVo, hVcov, hVd, hVsub⟩ := h (I := Bool) (fun b => bif b then U else Aᶜ)
    (by rintro (_ | _)
        · exact hA.isOpen_compl
        · exact hU)
    (by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases hxA : x ∈ A
      · exact ⟨true, hAU hxA⟩
      · exact ⟨false, hxA⟩)
  have hclopen := isClopen_of_pairwiseDisjoint_iUnion_eq_univ hVo hVcov hVd
  refine ⟨V true, hclopen true, ?_, hVsub true⟩
  intro x hxA
  by_contra hxV
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hVcov ▸ Set.mem_univ x)
  cases b with
  | false => exact (hVsub false hb) hxA
  | true => exact hxV hb

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    For separable metrizable spaces, having large inductive dimension at most $\NonnegativeDimensionLevel{0}$ and having Lebesgue covering dimension
    at most $\NonnegativeDimensionLevel{0}$ are also equivalent to this condition.
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{zero-dimension equivalence}{The three conditions for zero dimension}]
-/
theorem zero_dimensional_iff_lebesgue_covering_dimension (Y : Type) [TopologicalSpace Y]
    [T1Space Y] [SecondCountableTopology Y] :
    IsZeroDimensional Y ↔ HasCoveringDimensionLEZero Y :=
  (zero_dimensional_iff_big_inductive Y).trans
    ⟨HasBigInductiveDimensionLEZero.hasCoveringDimensionLEZero,
      HasCoveringDimensionLEZero.hasBigInductiveDimensionLEZero⟩

private theorem product_discrete_has_clopen_basis (ι : Type) (Y : ι -> Type)
    [∀ i, TopologicalSpace (Y i)] [∀ i, DiscreteTopology (Y i)] :
    IsTopologicalBasis {s : Set (∀ i, Y i) | IsClopen s} := by
  let singletonBasis : ∀ i, Set (Set (Y i)) := fun i => {s | ∃ y : Y i, s = {y}}
  have h_basis :
      IsTopologicalBasis
        {S : Set (∀ i, Y i) | ∃ (U : ∀ i, Set (Y i)) (F : Finset ι),
          (∀ i, i ∈ F -> U i ∈ singletonBasis i) ∧ S = (F : Set ι).pi U} :=
    isTopologicalBasis_pi (X := Y) (T := singletonBasis) fun i =>
      isTopologicalBasis_singletons (Y i)
  refine h_basis.of_isOpen_of_subset (s' := {s : Set (∀ i, Y i) | IsClopen s})
    (fun _ hs => hs.isOpen) ?_
  intro S hS
  rcases hS with ⟨U, F, hU, rfl⟩
  rw [Set.pi_def]
  exact isClopen_biInter_finset fun i hi => by
    rcases hU i hi with ⟨y, hy⟩
    rw [hy]
    exact (isClopen_discrete ({y} : Set (Y i))).preimage (continuous_apply i)

private theorem product_discrete_zero_dimensional (ι : Type) (Y : ι -> Type)
    [∀ i, TopologicalSpace (Y i)] [∀ i, DiscreteTopology (Y i)] :
    IsZeroDimensional (∀ i, Y i) :=
  product_discrete_has_clopen_basis ι Y

private theorem not_preconnected_of_totally_disconnected_nontrivial
    (Y : Type) [TopologicalSpace Y] [PreconnectedSpace Y]
    [TotallyDisconnectedSpace Y] [Nontrivial Y] : False := by
  have hsub : Subsingleton Y := subsingleton_of_preconnected_totallyDisconnected
  rcases exists_pair_ne Y with ⟨x, y, hxy⟩
  exact hxy (Subsingleton.elim x y)

private theorem not_zeroDimensional_of_preconnected_nontrivial
    (Y : Type) [TopologicalSpace Y] [T0Space Y] [PreconnectedSpace Y] [Nontrivial Y] :
    ¬ IsZeroDimensional Y := by
  intro h_zero
  have h_basis :
      IsTopologicalBasis {s : Set Y | IsClopen s} :=
    h_zero
  let : ZeroDimensionalSpace Y := zeroDimensionalSpace_iff_isTopologicalBasis_isClopen.mpr h_basis
  have : TotallySeparatedSpace Y := inferInstance
  have : TotallyDisconnectedSpace Y := inferInstance
  exact not_preconnected_of_totally_disconnected_nontrivial Y

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    A point $x$ of a topological space is an \termdefine{isolated point} if $\{x\}$ is open. A space is
    \termdefineas{perfect space}{perfect} if it has no isolated points.
-/
/-- Book term `\termdefine{isolated point}`: the singleton `{x}` is open. -/
def IsIsolatedPointByOpenSingleton {Y : Type*} [TopologicalSpace Y] (x : Y) : Prop :=
  IsOpen ({x} : Set Y)

/-- Book term `\termdefineas{perfect space}{perfect}`: the space has no isolated points.
Callers reach the mathlib class `PerfectSpace` through
`isPerfectSpaceByNoIsolatedPoint_iff_perfectSpace`. -/
def IsPerfectSpaceByNoIsolatedPoint (Y : Type*) [TopologicalSpace Y] : Prop :=
  ∀ x : Y, ¬ IsIsolatedPointByOpenSingleton x

theorem isPerfectSpaceByNoIsolatedPoint_iff_perfectSpace (Y : Type*) [TopologicalSpace Y] :
    IsPerfectSpaceByNoIsolatedPoint Y ↔ PerfectSpace Y := by
  unfold IsPerfectSpaceByNoIsolatedPoint IsIsolatedPointByOpenSingleton
  rw [perfectSpace_iff_forall_not_isolated]
  refine forall_congr' fun x => ?_
  rw [Filter.neBot_iff]
  exact not_congr (isOpen_singleton_iff_punctured_nhds x)

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    Here $\TwoPointSpace$ and $\omega$ are countable discrete spaces, hence Polish because their discrete metrics are complete and the
    spaces are countable. Also $\ClosedInterval{0}{1}$ is a closed subspace of $\R$, and $\R$ itself is Polish. Hence the countable-products
    proposition gives the following standard Polish product spaces, each with the product topology:
-/
theorem bool_polish :
    PolishSpace Bool := by
  infer_instance

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The \termdefine{Cantor space} $\CantorSpace$.
    \termforwardas{Brouwer's Cantor-space characterization}{Brouwer's characterization} in \BookSectionLink{sec:clopen-scheme-characterizations}{the next chapter} identifies it as the compact
    zero-dimensional \termuseas{perfect space}{perfect} model.
-/
theorem cantor_space_polish :
    PolishSpace cantor_space := by
  have : PolishSpace Bool := bool_polish
  exact countable_product_polish

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The following quick invariants separate the four examples up to homeomorphism. Tychonoff's theorem makes $\CantorSpace$
    and $\HilbertCube$ compact, because $\TwoPointSpace$ and $\ClosedInterval{0}{1}$ are compact.
-/
theorem cantor_space_compact :
    CompactSpace cantor_space := by
  infer_instance

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The spaces $\CantorSpace$ and $\BaireSpace$ have clopen
    \termforward{cylinder} bases, so they are zero-dimensional.
-/
theorem cantor_space_zero_dimensional :
    IsZeroDimensional cantor_space :=
  product_discrete_zero_dimensional ℕ fun _ => Bool

/-- The cylinder whose initial coordinate is the specified symbol. -/
def initialSymbolCylinder {A : Type*} (a : A) : Set (ℕ → A) :=
  {x | x 0 = a}

/-- The constant sequence lies in its initial-symbol cylinder. -/
theorem initialSymbolCylinder_nonempty {A : Type*} (a : A) :
    (initialSymbolCylinder a).Nonempty :=
  ⟨fun _ => a, rfl⟩

/-- An initial-symbol cylinder over a discrete alphabet is clopen. -/
theorem initialSymbolCylinder_isClopen {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (a : A) : IsClopen (initialSymbolCylinder a) :=
  (isClopen_discrete ({a} : Set A)).preimage (continuous_apply 0)

/-- A different constant sequence witnesses that the cylinder is proper. -/
theorem initialSymbolCylinder_ne_univ {A : Type*} (a b : A) (hba : b ≠ a) :
    initialSymbolCylinder a ≠ Set.univ := by
  intro h
  have hb : (fun _ : ℕ => b) ∈ initialSymbolCylinder a := by rw [h]; trivial
  exact hba hb

/-- A nonempty proper initial-symbol cylinder separates the sequence space. -/
theorem not_connected_of_initialSymbolCylinder {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (a b : A) (hba : b ≠ a) : ¬ ConnectedSpace (ℕ → A) := by
  intro h
  let : ConnectedSpace (ℕ → A) := h
  exact initialSymbolCylinder_ne_univ a b hba
    ((initialSymbolCylinder_isClopen a).eq_univ (initialSymbolCylinder_nonempty a))

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    In each of $\CantorSpace$ and $\BaireSpace$, the \termforward{cylinder} consisting of sequences whose initial term is $0$
    is nonempty, proper, and clopen, so both spaces are disconnected.
-/
theorem cantor_space_not_connected :
    ¬ ConnectedSpace cantor_space :=
  not_connected_of_initialSymbolCylinder false true (by decide)

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The \termdefine{Baire space} $\BaireSpace$. The
    \termforwardas{Alexandrov--Urysohn theorem}{Alexandrov--Urysohn characterization} in \BookSectionLink{sec:clopen-scheme-characterizations}{the next chapter} identifies it as the nowhere
    locally compact analogue of Cantor space.
-/
/-- Book term `\termdefine{Baire space}`: `ω^ω`. -/
abbrev baire_space : Type :=
  ℕ -> ℕ

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A notational warning: the expression $\omega^\omega$ above is \termdefine{ordinal exponentiation} as defined here, a
    countable ordinal. The identical-looking expression $\BaireSpace$ used throughout the main text is the
    \termuse{Baire space} of functions $\omega \to \omega$, an uncountable Polish space. Context fixes which is meant; the
    rendered glyphs
    coincide.
-/
theorem baire_space_polish :
    PolishSpace baire_space := by
  have : PolishSpace ℕ :=
    metric_complete_separable_polish ℕ (isMetricComplete_of_mathlib ℕ)
  exact countable_product_polish

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The spaces $\BaireSpace$ and
    $\RealSequenceSpace$ are not compact: if either product were compact, then each coordinate projection would have
    compact image, forcing $\omega$ or $\R$ to be compact.
-/
theorem baire_space_noncompact :
    NoncompactSpace baire_space := by
  rw [← not_compactSpace_iff]
  intro hcompact
  have : CompactSpace baire_space := hcompact
  have h_image :
      IsCompact ((fun x : baire_space => x 0) '' (Set.univ : Set baire_space)) :=
    isCompact_univ.image (continuous_apply 0)
  have h_range :
      (fun x : baire_space => x 0) '' (Set.univ : Set baire_space) = Set.univ := by
    ext n
    constructor
    · intro
      exact mem_univ n
    · intro
      exact ⟨fun _ => n, mem_univ _, rfl⟩
  have h_nat_compact : IsCompact (Set.univ : Set ℕ) := by
    simpa [h_range] using h_image
  exact (noncompact_univ ℕ) h_nat_compact

theorem baire_space_zero_dimensional :
    IsZeroDimensional baire_space :=
  product_discrete_zero_dimensional ℕ fun _ => ℕ

theorem baire_space_not_connected :
    ¬ ConnectedSpace baire_space :=
  not_connected_of_initialSymbolCylinder (0 : ℕ) 1 (by decide)

/-- Book notation: the closed unit interval `[0,1]`. -/
abbrev closed_unit_interval : Set ℝ :=
  Set.Icc (0 : ℝ) 1

theorem closed_unit_interval_polish :
    PolishSpace closed_unit_interval := by
  change PolishSpace (Set.Icc (0 : ℝ) 1)
  exact closed_subspace_polish isClosed_Icc

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The \termdefine{Hilbert cube} $\HilbertCube$. The Hilbert cube is compact by Tychonoff, and it is the
    universal compact target for Polish spaces: the
    \termforwardas{Hilbert-cube embedding}{Hilbert-cube embedding theorem} in \BookSectionLink{sec:hilbert-cube-embedding}{The Hilbert Cube and Universal Compact Embedding} shows that every Polish space is
    homeomorphic to a subspace of $\HilbertCube$.
-/
/-- Book term `\termdefine{Hilbert cube}`: `[0,1]^ω`. -/
abbrev hilbert_cube : Type :=
  ℕ -> closed_unit_interval

theorem hilbert_cube_polish :
    PolishSpace hilbert_cube := by
  have : PolishSpace closed_unit_interval := closed_unit_interval_polish
  exact countable_product_polish

theorem hilbert_cube_compact :
    CompactSpace hilbert_cube := by
  infer_instance

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    Products of connected spaces are connected, so $\HilbertCube$ and
    $\RealSequenceSpace$ are connected.
-/
theorem hilbert_cube_connected :
    ConnectedSpace hilbert_cube := by
  exact { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    Since both products are Hausdorff and have more than one point, neither can be
    zero-dimensional: a clopen basic neighborhood of one point inside the complement of another would disconnect the space.
-/
theorem hilbert_cube_not_zero_dimensional :
    ¬ IsZeroDimensional hilbert_cube :=
  not_zeroDimensional_of_preconnected_nontrivial hilbert_cube

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The \termdefine{space of real sequences} $\RealSequenceSpace$.
-/
/-- Book term `\termdefine{space of real sequences}`: `ℝ^ω`. -/
abbrev real_sequence_space : Type :=
  ℕ -> ℝ

theorem real_sequence_space_polish :
    PolishSpace real_sequence_space := by
  have : PolishSpace ℝ := real_polish
  exact countable_product_polish

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    Thus every
        infinite-dimensional separable Banach space from §{sec:polish-examples} is homeomorphic to
        $\RealSequenceSpace$.
-/
/-- The book's local consequence of the cited Anderson and Anderson--Kadec
results. Both external homeomorphism statements remain explicit inputs. -/
theorem banach_homeomorphic_real_sequences_of_anderson_kadec
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SeparableSpace E]
    (h_infinite : ¬ FiniteDimensional ℝ E)
    (anderson : Nonempty (real_sequence_space ≃ₜ lp (fun _ : ℕ => ℝ) 2))
    (anderson_kadec : ¬ FiniteDimensional ℝ E →
      Nonempty (E ≃ₜ lp (fun _ : ℕ => ℝ) 2)) :
    Nonempty (E ≃ₜ real_sequence_space) := by
  obtain ⟨a⟩ := anderson
  obtain ⟨e⟩ := anderson_kadec h_infinite
  exact ⟨e.trans a.symm⟩

theorem real_sequence_space_noncompact :
    NoncompactSpace real_sequence_space := by
  rw [← not_compactSpace_iff]
  intro hcompact
  have : CompactSpace real_sequence_space := hcompact
  have h_image :
      IsCompact ((fun x : real_sequence_space => x 0) '' (Set.univ : Set real_sequence_space)) :=
    isCompact_univ.image (continuous_apply 0)
  have h_range :
      (fun x : real_sequence_space => x 0) '' (Set.univ : Set real_sequence_space) = Set.univ := by
    ext r
    constructor
    · intro
      exact mem_univ r
    · intro
      exact ⟨fun _ => r, mem_univ _, rfl⟩
  have h_real_compact : IsCompact (Set.univ : Set ℝ) := by
    simpa [h_range] using h_image
  exact (noncompact_univ ℝ) h_real_compact

theorem real_sequence_space_connected :
    ConnectedSpace real_sequence_space := by
  exact { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }

theorem real_sequence_space_not_zero_dimensional :
    ¬ IsZeroDimensional real_sequence_space :=
  not_zeroDimensional_of_preconnected_nontrivial real_sequence_space

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: statement
  kind: lemma
  title: Distance to a nonempty set
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    For every $z\in F$, the triangle inequality gives
    $$d(x,F)\le d(x,z)\le d(x,y)+d(y,z).$$
    Taking the infimum over $z\in F$ yields $d(x,F)\le d(x,y)+d(y,F)$.
    Interchanging $x$ and $y$ gives the reverse bound and hence the claimed absolute-value inequality.
    The inequality implies continuity directly.
-/
theorem distance_to_set_abs_sub_le {Y : Type*} [MetricSpace Y] {F : Set Y}
    (hF : F.Nonempty) (x y : Y) : |infDist x F - infDist y F| ≤ dist x y := by
  have htriangle (x y : Y) : infDist x F - dist x y ≤ infDist y F := by
    apply (le_infDist hF).mpr
    intro z hz
    have h := (infDist_le_dist_of_mem (x := x) hz).trans (dist_triangle x y z)
    linarith
  have hxy := htriangle x y
  have hyx := htriangle y x
  rw [dist_comm y x] at hyx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem distance_to_set_continuous {Y : Type*} [MetricSpace Y] {F : Set Y}
    (hF : F.Nonempty) : Continuous (fun x : Y => infDist x F) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using distance_to_set_abs_sub_le hF x y

theorem baire_space_surjects [Nonempty X] :
    ∃ f : (Nat -> Nat) -> X, Continuous f ∧ Function.Surjective f :=
  PolishSpace.exists_nat_nat_continuous_surjective X

end PolishSpaceBook

end
