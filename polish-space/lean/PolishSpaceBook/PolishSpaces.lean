import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Sequences
import Mathlib.Topology.SmallInductiveDimension
import Mathlib.Analysis.Normed.Lp.LpEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

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
| `\termdefine{separable}` | mathlib class `SeparableSpace` |
| `\termdefine{completely metrizable}` | `IsCompletelyMetrizableByMetric` |
-/

abbrev IsMetricComplete (Y : Type*) [MetricSpace Y] : Prop :=
  ∀ u : ℕ -> Y, CauchySeq u -> ∃ y, Tendsto u atTop (𝓝 y)

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    $X$ is \termdefine{completely metrizable}: there exists a metric $d$ on $X$ such that $(X, d)$ is a complete metric
        space and $d$ induces the topology of $X$.
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
    haveI : CompleteSpace Y := h
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
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: recall
  title: Separability and second countability
-/
/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: proof
  excerpt: |
    If $D$ is countable and dense, then the balls $\Ball{a}{q}$ with $a \in D$ and $q \in \RestrictedSet{\QQ}{>0}$ form a
    countable base. Conversely, choosing one point from each nonempty basic open set in a countable base gives a countable
    dense subset.
-/
theorem metrizable_separable_iff_second_countable (Y : Type*) [TopologicalSpace Y]
    [PseudoMetrizableSpace Y] :
    SeparableSpace Y ↔ SecondCountableTopology Y := by
  constructor
  · intro hsep
    haveI : SeparableSpace Y := hsep
    letI : UniformSpace Y := pseudoMetrizableSpaceUniformity Y
    haveI : (𝓤 Y).IsCountablyGenerated :=
      pseudoMetrizableSpaceUniformity_countably_generated Y
    exact UniformSpace.secondCountable_of_separable Y
  · intro
    infer_instance

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: recall
  title: Sequential criterion for first-countable spaces
-/
theorem first_countable_closed_iff_seq_closed (Y : Type*) [TopologicalSpace Y]
    [FirstCountableTopology Y] (s : Set Y) :
    IsClosed s ↔ IsSeqClosed s := by
  exact isSeqClosed_iff_isClosed.symm

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
    The triangle inequality follows from
    $$
    \min\{d(x,z),1\}\le \min\{d(x,y)+d(y,z),1\}
    \le \min\{d(x,y),1\}+\min\{d(y,z),1\}.
    $$
    For every $0<r<1$, the $d$-ball and the $\hat d$-ball of radius $r$ around the same center are equal. Hence $d$ and
    $\hat d$ induce the same topology.

    It remains to check completeness. Let $(x_n)_n$ be $\hat d$-Cauchy. Given $\epsilon>0$, choose
    $0<\delta<\min\{\epsilon,1\}$. Eventually $\hat d(x_m,x_n)<\delta$, and then $d(x_m,x_n)<\delta<\epsilon$.
    Thus $(x_n)_n$ is $d$-Cauchy, so it $d$-converges to some $x$. Since $\hat d\le d$, the same sequence
    $\hat d$-converges to $x$.
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
              min (@dist Y (originalMetric.toDist) x y) 1) ∧
            (∀ x y : Y, @dist Y (boundedMetric.toDist) x y ≤ 1))) := by
  let originalDist : Y -> Y -> ℝ := fun x y => @dist Y originalMetric.toDist x y
  let boundedDist : Y -> Y -> ℝ := fun x y => min (originalDist x y) 1
  have boundedDist_le_one : ∀ x y : Y, boundedDist x y ≤ 1 := fun x y => min_le_right _ _
  let boundedMetric : MetricSpace Y := by
    refine MetricSpace.ofDistTopology boundedDist (fun x => ?_) (fun x y => ?_)
      (fun x y z => ?_) (fun t => ?_) (fun x y hxy => ?_)
    · simp [boundedDist, originalDist]
    · simp [boundedDist, originalDist, dist_comm]
    · calc
        boundedDist x z = min (originalDist x z) 1 := rfl
        _ ≤ min (originalDist x y + originalDist y z) 1 := by
          gcongr
          exact dist_triangle x y z
        _ ≤ min (originalDist x y) 1 + min (originalDist y z) 1 :=
          min_add_one_le_min_add_min dist_nonneg dist_nonneg
        _ = boundedDist x y + boundedDist y z := rfl
    · constructor
      · intro ht x hx
        rcases (Metric.isOpen_iff (α := Y)).1 ht x hx with ⟨ε, hεpos, hε⟩
        refine ⟨min ε 1, lt_min hεpos zero_lt_one, fun y hy => ?_⟩
        have hdist : originalDist x y < ε :=
          min_lt_min_one_iff dist_nonneg hεpos hy
        exact hε <| by simpa [originalDist, dist_comm] using hdist
      · intro ht
        exact (Metric.isOpen_iff (α := Y)).2 fun x hx => by
          rcases ht x hx with ⟨ε, hεpos, hε⟩
          refine ⟨ε, hεpos, fun y hy => ?_⟩
          have hxy : originalDist x y < ε := by
            simpa [originalDist, dist_comm] using hy
          exact hε y ((min_le_left _ _).trans_lt hxy)
    · have hmin := (min_eq_iff.1 hxy)
      rcases hmin with ⟨hdist, _⟩ | ⟨hone, _⟩
      · exact eq_of_dist_eq_zero (by simpa [originalDist] using hdist)
      · norm_num at hone
  have boundedMetric_dist :
      ∀ x y : Y, @dist Y (boundedMetric.toDist) x y = boundedDist x y := by
    intro x y
    rfl
  have boundedComplete : @IsMetricComplete Y boundedMetric := by
    letI : MetricSpace Y := boundedMetric
    intro u hu
    have h_bounded_cauchy :
        ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, boundedDist (u m) (u n) < ε := by
      intro ε hεpos
      rcases (Metric.cauchySeq_iff.1 hu) ε hεpos with ⟨N, hN⟩
      refine ⟨N, fun m hm n hn => ?_⟩
      simpa [boundedMetric_dist] using hN m hm n hn
    have h_original_cauchy : (letI : MetricSpace Y := originalMetric; CauchySeq u) := by
      letI : MetricSpace Y := originalMetric
      rw [Metric.cauchySeq_iff]
      intro ε hεpos
      have hδpos : 0 < min ε 1 := lt_min hεpos zero_lt_one
      rcases h_bounded_cauchy (min ε 1) hδpos with ⟨N, hN⟩
      refine ⟨N, fun m hm n hn => ?_⟩
      have hbounded : min (dist (u m) (u n)) 1 < min ε 1 := by
        simpa [boundedDist, originalDist] using hN m hm n hn
      exact min_lt_min_one_iff dist_nonneg hεpos hbounded
    obtain ⟨x, hx⟩ : ∃ x, Tendsto u atTop (𝓝 x) := by
      letI : MetricSpace Y := originalMetric
      exact originalComplete u h_original_cauchy
    exact ⟨x, hx⟩
  have h_dist_eq :
      ∀ x y : Y,
        @dist Y (boundedMetric.toDist) x y =
          min (@dist Y (originalMetric.toDist) x y) 1 := by
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
        countable and dense in $\R$, while the standard metric $d(x, y) = |x - y|$ is complete on $\R$.
-/
theorem real_polish : PolishSpace ℝ :=
  metric_complete_separable_polish ℝ (isMetricComplete_of_mathlib ℝ)

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    \termdefine{Euclidean space} $\R^n$ with the standard topology.
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
        The claim after Alexandrov's theorem in §{sec:alexandrov-theorem} proves that $\SetDifference{\R}{\QQ}$ is
        $\Gdelta$ in $\R$; Alexandrov's theorem then proves that this subspace is Polish.
-/
theorem irrationals_are_gdelta :
    IsGδ ({x : ℝ | Irrational x} : Set ℝ) :=
  IsGδ.setOf_irrational

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    Every \termdefine{infinite-dimensional separable Banach space} with its norm topology, for example $\ell^2$,
        $\ell^p$ for $1<p<\infty$, and $C[0,1]$. Separability is part of the hypothesis, and completeness is exactly the
        Banach-space condition.
-/
theorem separable_banach_space_polish (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h_complete : IsMetricComplete E) [SeparableSpace E] :
    PolishSpace E :=
  metric_complete_separable_polish E h_complete

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
  haveI : Countable cantor_space := hcount
  rcases exists_surjective_nat cantor_space with ⟨f, hf⟩
  let g : cantor_space := fun n => ! f n n
  rcases hf g with ⟨k, hk⟩
  have hkg := congrFun hk k
  by_cases hfk : f k k <;> simp [g, hfk] at hkg

theorem bounded_real_sequences_not_separable : ¬ SeparableSpace (ℕ →ᵇ ℝ) := by
  intro hsep
  haveI : SeparableSpace (ℕ →ᵇ ℝ) := hsep
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
  haveI : PolishSpace (ℕ →ᵇ ℝ) := hpolish
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
  letI : SeparableSpace ell_infty := hsep
  let e : ell_infty ≃ₗᵢ[ℝ] ℕ →ᵇ ℝ := lpBCFₗᵢ ℝ ℝ
  have hsep_bounded : SeparableSpace (ℕ →ᵇ ℝ) :=
    e.surjective.denseRange.separableSpace e.continuous
  exact bounded_real_sequences_not_separable hsep_bounded

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The Banach space $\ell^\infty$ with the sup norm is complete but not separable, hence not Polish. Indeed, the binary
        sequences in $\{0,1\}^\omega$ are pairwise distance $1$ apart, so the balls of radius $1/3$ around them are pairwise
        disjoint. A countable dense set would have to meet each of these uncountably many disjoint balls, which is
        impossible.
-/
theorem ell_infty_real_sequences_not_polish :
    ¬ PolishSpace ell_infty := by
  intro hpolish
  haveI : PolishSpace ell_infty := hpolish
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
    in $X$, hence converges in $X$, and the limit lies in $C$ because $C$ is closed. Separability is hereditary for metric
    spaces by the equivalence with second countability above.
    \end{proof}
-/
theorem closed_subspace_polish {C : Set X} (hC : IsClosed C) :
    PolishSpace C := by
  let completeMetricOnX : UpgradedIsCompletelyMetrizableSpace X :=
    upgradeIsCompletelyMetrizable X
  letI : MetricSpace X := completeMetricOnX.toMetricSpace
  have hX_complete : IsMetricComplete X :=
    isMetricComplete_of_upgraded X completeMetricOnX
  let dC : C -> C -> ℝ := fun x y => dist (x : X) (y : X)
  let metricC : MetricSpace C := inferInstance
  have metricC_dist :
      ∀ x y : C, @dist C metricC.toDist x y = dC x y := by
    intro x y
    rfl
  letI : MetricSpace C := metricC
  have h_second_countable : SecondCountableTopology C :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
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
    Let $U \IncludedIn X$ be open. The case $U = X$ is trivial, so assume $U \ne X$. The restricted metric
    $\restrict{d}{U\times U}$ is generally not complete, because a Cauchy sequence in $U$ may converge in $X$ to a boundary
    point. Define a new metric on $U$ by
    $$d'(x, y) \;:=\; d(x, y) \;+\; \left| \frac{1}{d(x,\, \SetDifference{X}{U})} - \frac{1}{d(y,\, \SetDifference{X}{U})}
    \right|,$$
    where $d(z,S):=\inf\{d(z,s):s\in S\}$. This is well-defined because $d(x, \SetDifference{X}{U})>0$ for every $x\in U$.
    This metric induces the subspace topology. Since $d \le d'$, convergence in $d'$ implies convergence in $d$. Conversely,
    suppose $x_n \to x$ in $d$ and all $x_n,x$ lie in $U$. The function $z \mapsto d(z, \SetDifference{X}{U})$ is continuous
    and positive at $x$, so
    $$\frac{1}{d(x_n, \SetDifference{X}{U})} \longrightarrow \frac{1}{d(x, \SetDifference{X}{U})}.$$
    Hence $d'(x_n,x)\to 0$.

    The metric $d'$ is complete. If $(x_n)$ is $d'$-Cauchy in $U$, then $\bigl(1/d(x_n, \SetDifference{X}{U})\bigr)_n$ is
    Cauchy in $\R$ and hence bounded. Thus the points $x_n$ stay a positive distance from $\SetDifference{X}{U}$. The
    sequence is also $d$-Cauchy, so it converges in $X$ to some point $x$. The positive distance from
    $\SetDifference{X}{U}$ forces $x \in U$, and the preceding topology comparison gives $x_n \to x$ in $d'$. The same
    second-countability argument used for closed subspaces gives separability of $U$.
    \end{proof}
-/
theorem open_subspace_polish {U : Set X} (hU : IsOpen U) :
    PolishSpace U := by
  let completeMetricOnX : UpgradedIsCompletelyMetrizableSpace X :=
    upgradeIsCompletelyMetrizable X
  letI : MetricSpace X := completeMetricOnX.toMetricSpace
  have hX_complete : IsMetricComplete X :=
    isMetricComplete_of_upgraded X completeMetricOnX
  let Uopen : Opens X := ⟨U, hU⟩
  change PolishSpace Uopen
  let d' : Uopen.CompleteCopy -> Uopen.CompleteCopy -> ℝ := fun x y =>
    dist x.1 y.1 + |1 / infDist x.1 Uopenᶜ - 1 / infDist y.1 Uopenᶜ|
  have d'_val_le :
      ∀ x y : Uopen.CompleteCopy, dist x.1 y.1 ≤ d' x y := fun x y =>
    le_add_of_nonneg_right (abs_nonneg _)
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
        have h_tendsto :
            Tendsto
              (fun y : Uopen =>
                dist x.1 y.1 + |(infDist x.1 Uopenᶜ)⁻¹ - (infDist y.1 Uopenᶜ)⁻¹|)
              (𝓝 x)
              (𝓝 (dist x.1 x.1 + |(infDist x.1 Uopenᶜ)⁻¹ - (infDist x.1 Uopenᶜ)⁻¹|)) := by
          refine (tendsto_const_nhds.dist continuous_subtype_val.continuousAt).add
            (tendsto_const_nhds.sub ?_).abs
          refine (continuousAt_inv_infDist_pt ?_).comp continuous_subtype_val.continuousAt
          rw [Uopen.isOpen.isClosed_compl.closure_eq, mem_compl_iff, not_not]
          exact x.2
        simp only [dist_self, sub_self, abs_zero, zero_add] at h_tendsto
        exact mem_of_superset (h_tendsto <| gt_mem_nhds ε0) (by
          intro y hy
          -- hy is membership in a preimage of `Iio ε`; defeq to the inequality.
          have hy' : _ < ε := hy
          exact hε y (by simpa [d', one_div] using hy'))
  have d'_metric_dist :
      ∀ x y : Uopen.CompleteCopy, @dist Uopen.CompleteCopy d'_metric.toDist x y = d' x y := by
    intro x y
    rfl
  letI : MetricSpace Uopen.CompleteCopy := d'_metric
  have h_second_countable : SecondCountableTopology Uopen.CompleteCopy :=
    inferInstance
  have h_complete : IsMetricComplete Uopen.CompleteCopy := by
    apply (isMetricComplete_iff_completeSpace Uopen.CompleteCopy).2
    refine Metric.complete_of_convergent_controlled_sequences ((1 / 2) ^ ·) (by simp) ?_
    intro u hu
    have h_cauchy_in_X : CauchySeq fun n => (u n).1 := by
      refine cauchySeq_of_le_tendsto_0 (fun n : ℕ => (1 / 2) ^ n)
        (fun n m N hNn hNm => ?_) ?_
      · exact (d'_val_le (u n) (u m)).trans (by
          change d' (u n) (u m) ≤ (1 / 2) ^ N
          exact (hu N n m hNn hNm).le)
      · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by simp) (by norm_num)
    obtain ⟨x, xlim⟩ :
        ∃ x, Tendsto (fun n => (u n).1) atTop (𝓝 x) :=
      hX_complete _ h_cauchy_in_X
    by_cases xs : x ∈ Uopen
    · exact ⟨⟨x, xs⟩, tendsto_subtype_rng.2 xlim⟩
    obtain ⟨M, hM⟩ : ∃ M, ∀ n, 1 / infDist (u n).1 Uopenᶜ < M := by
      refine ⟨(1 / 2) ^ 0 + 1 / infDist (u 0).1 Uopenᶜ, fun n => ?_⟩
      rw [← sub_lt_iff_lt_add]
      calc
        _ ≤ |1 / infDist (u n).1 Uopenᶜ - 1 / infDist (u 0).1 Uopenᶜ| := le_abs_self _
        _ = |1 / infDist (u 0).1 Uopenᶜ - 1 / infDist (u n).1 Uopenᶜ| := abs_sub_comm _ _
        _ ≤ dist (u 0) (u n) := by
          change |1 / infDist (u 0).1 Uopenᶜ - 1 / infDist (u n).1 Uopenᶜ| ≤ d' (u 0) (u n)
          exact le_add_of_nonneg_left dist_nonneg
        _ < (1 / 2) ^ 0 := hu 0 0 n le_rfl n.zero_le
    have Mpos : 0 < M := lt_of_le_of_lt (div_nonneg zero_le_one infDist_nonneg) (hM 0)
    have Hmem : ∀ {y}, y ∈ Uopen ↔ 0 < infDist y Uopenᶜ := fun {y} => by
      rw [← Uopen.isOpen.isClosed_compl.notMem_iff_infDist_pos ⟨x, xs⟩]
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
    exact absurd (Hmem.2 <| lt_of_lt_of_le (div_pos one_pos Mpos) h_limit_lower_bound) xs
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
    Given Polish spaces $(X_n)_{n \in \NN}$, choose complete compatible metrics $d_n \le 1$ on the $X_n$. On the topological
    sum $\ExternalDisjointUnion_{n \in \NN} X_n$, define
    $$d((n, x), (m, y)) \;=\;
    \begin{cases}
    d_n(x, y), & n = m, \\
    1, & n \ne m.
    \end{cases}$$
    This metric induces the disjoint-union topology: each summand is clopen, and balls of radius $< 1$ stay inside a single
    summand. It is complete because a Cauchy sequence is eventually trapped in one summand, where it converges by
    completeness of $d_n$. It is separable because a countable union of countable dense subsets is countable and dense.
    \end{proof}
-/
theorem countable_disjoint_union_polish {ι : Type*} [Countable ι] {Y : ι -> Type*}
    [∀ i, TopologicalSpace (Y i)] [∀ i, PolishSpace (Y i)] :
    PolishSpace (Sigma Y) := by
  classical
  let completeMetricOn : ∀ i, UpgradedIsCompletelyMetrizableSpace (Y i) := fun i =>
    upgradeIsCompletelyMetrizable (Y i)
  letI : ∀ i, MetricSpace (Y i) := fun i => (completeMetricOn i).toMetricSpace
  have hY_complete : ∀ i, IsMetricComplete (Y i) := fun i =>
    isMetricComplete_of_upgraded (Y i) (completeMetricOn i)
  let dSigma : Sigma Y -> Sigma Y -> ℝ := fun a b =>
    match a, b with
    | ⟨i, x⟩, ⟨j, y⟩ =>
        if h : i = j then
          min (dist x (cast (by rw [h]) y)) 1
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
      simp [dSigma, le_min dist_nonneg zero_le_one]
    · simp [dSigma, h]
  have dSigma_triangle : ∀ x y z : Sigma Y, dSigma x z ≤ dSigma x y + dSigma y z := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
    by_cases hik : i = k
    · subst k
      by_cases hij : i = j
      · subst j
        simp only [dSigma, dif_pos rfl, cast_eq]
        calc
          min (dist x z) 1 ≤ min (dist x y + dist y z) 1 := by
            gcongr
            exact dist_triangle x y z
          _ ≤ min (dist x y) 1 + min (dist y z) 1 :=
            min_add_one_le_min_add_min
              (@dist_nonneg (Y i) _ x y) (@dist_nonneg (Y i) _ y z)
      · have hji : j ≠ i := hij ∘ Eq.symm
        simp only [dSigma, dif_pos rfl, dif_neg hij, dif_neg hji, cast_eq]
        exact (min_le_right _ _).trans (by norm_num)
    · by_cases hij : i = j
      · subst j
        have hik' : i ≠ k := hik
        simp only [dSigma, dif_neg hik', dif_pos rfl, cast_eq]
        exact le_add_of_nonneg_left (le_min dist_nonneg zero_le_one)
      · by_cases hjk : j = k
        · subst k
          have hij' : i ≠ j := hij
          simp only [dSigma, dif_neg hij', dif_pos rfl, cast_eq]
          exact le_add_of_nonneg_right (le_min dist_nonneg zero_le_one)
        · simp only [dSigma, dif_neg hik, dif_neg hij, dif_neg hjk]
          norm_num
  have dSigma_eq_zero : ∀ x y : Sigma Y, dSigma x y = 0 -> x = y := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    by_cases hij : i = j
    · subst j
      simp only [dSigma, dif_pos rfl, cast_eq] at hxy
      have hdist : dist x y = 0 := by
        rcases min_eq_iff.1 hxy with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · norm_num at h
      exact congrArg (Sigma.mk i) (eq_of_dist_eq_zero hdist)
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
        simp only [dSigma, dif_pos rfl, cast_eq] at hy
        have hdist : dist x y < ε :=
          min_lt_min_one_iff dist_nonneg εpos hy
        exact hε (mem_ball'.2 hdist)
      · have : (1 : ℝ) < min ε 1 := by
          simp [dSigma, hij] at hy
        linarith [min_le_right ε (1 : ℝ)]
    · intro hs
      refine isOpen_sigma_iff.2 fun i => Metric.isOpen_iff.2 fun x hx => ?_
      rcases hs ⟨i, x⟩ hx with ⟨ε, εpos, hε⟩
      refine ⟨min ε 1, lt_min εpos zero_lt_one, fun y hy => ?_⟩
      apply hε ⟨i, y⟩
      simp only [dSigma, dif_pos rfl, cast_eq]
      have hy' : dist x y < min ε 1 := mem_ball'.1 hy
      by_cases hε1 : ε ≤ 1
      · exact (min_le_left _ _).trans_lt (hy'.trans_le (min_le_left _ _))
      · exact (min_le_right _ _).trans_lt (lt_of_not_ge hε1)
  have sigmaMetric_dist :
      ∀ x y : Sigma Y, @dist (Sigma Y) sigmaMetric.toDist x y = dSigma x y := by
    intro x y
    rfl
  letI : MetricSpace (Sigma Y) := sigmaMetric
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
      simp only [hum, hun, dSigma, dif_pos rfl, cast_eq] at hdistSigma
      exact min_lt_min_one_iff dist_nonneg εpos hdistSigma
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
    exact Or.inl hd
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
    Given Polish spaces $(X_n)_{n \in \NN}$, choose complete compatible metrics $d_n \le 1$ on the $X_n$ and define on
    $\prod_{n \in \NN} X_n$
    $$d\big((x_n), (y_n)\big) \;=\; \sum_{n \in \NN} 2^{-n}d_n(x_n,y_n).$$
    Each summand $2^{-n}d_n(x_n,y_n)$ is at most $2^{-n}$, so the series converges, and the metric axioms follow
    term by term from the metric axioms for the $d_n$. Thus $d$ is a metric.

    This metric induces the product topology. Indeed, write $x^k_n$ and $x_n$ for the $n$th coordinates of $x^k$ and $x$. If
    $x^k \to x$ in $d$, then for each fixed $n$,
    $$2^{-n}d_n(x^k_n,x_n) \le d(x^k,x),$$
    so $d_n(x^k_n,x_n)\to 0$. Thus $d$-convergence implies coordinate-wise convergence. Conversely, suppose $x^k_n \to x_n$
    for every $n$. Given $\varepsilon>0$, choose $M$ so that $\sum_{n\ge M}2^{-n}<\varepsilon/2$. For the finitely many
    coordinates $n<M$, choose $K$ such that whenever $k\ge K$,
    $$\sum_{n<M}2^{-n}d_n(x^k_n,x_n)<\varepsilon/2.$$
    Then for $k\ge K$,
    $$d(x^k,x) \le \sum_{n<M}2^{-n}d_n(x^k_n,x_n)+\sum_{n\ge M}2^{-n}<\varepsilon.$$
    Hence coordinate-wise convergence implies $d$-convergence. Therefore $d$ induces the product topology.

    For completeness, let $(x^k)_k$ be $d$-Cauchy. Then each coordinate sequence $(x^k_n)_k$ is Cauchy for $d_n$, so it
    converges to some $x_n \in X_n$. By the convergence criterion just proved, the point $x=(x_n)_n$ is the $d$-limit of
    $(x^k)_k$. For separability, if the product is empty there is nothing to prove. Otherwise fix countable dense sets
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
  letI : ∀ i, MetricSpace (Y i) := fun i => (completeMetricOn i).toMetricSpace
  have hY_complete : ∀ i, IsMetricComplete (Y i) := fun i =>
    isMetricComplete_of_upgraded (Y i) (completeMetricOn i)
  let weight : ℕ -> ℝ := fun n => ((1 / 2 : ℝ) ^ n)
  let term : (∀ n, Y n) -> (∀ n, Y n) -> ℕ -> ℝ := fun x y n =>
    weight n * min (dist (x n) (y n)) 1
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
    exact mul_nonneg (weight_nonneg n) (le_min dist_nonneg zero_le_one)
  have term_le_weight : ∀ x y n, term x y n ≤ weight n := by
    intro x y n
    exact mul_le_of_le_one_right (weight_nonneg n) (min_le_right _ _)
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
      calc
        term x z n = weight n * min (dist (x n) (z n)) 1 := rfl
        _ ≤ weight n * min (dist (x n) (y n) + dist (y n) (z n)) 1 := by
          gcongr
          exact dist_triangle _ _ _
        _ ≤ weight n * (min (dist (x n) (y n)) 1 + min (dist (y n) (z n)) 1) := by
          gcongr
          exact min_add_one_le_min_add_min dist_nonneg dist_nonneg
        _ = term x y n + term y z n := by ring
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
    have hmin_zero : min (dist (x n) (y n)) 1 = 0 := by
      change weight n * min (dist (x n) (y n)) 1 = 0 at hterm_zero
      rcases mul_eq_zero.1 hterm_zero with hweight | hmin
      · exact absurd hweight (ne_of_gt (weight_pos n))
      · exact hmin
    have hdist_zero : dist (x n) (y n) = 0 := by
      rcases min_eq_iff.1 hmin_zero with ⟨hdist, _⟩ | ⟨hone, _⟩
      · exact hdist
      · norm_num at hone
    exact eq_of_dist_eq_zero hdist_zero
  have dPi_ball_open : ∀ x : ∀ n, Y n, ∀ ε : ℝ, IsOpen {y | dPi x y < ε} := by
    intro x ε
    have hcont : Continuous fun y : ∀ n, Y n => dPi x y := by
      dsimp [dPi, term]
      apply continuous_tsum
      · intro n
        fun_prop
      · exact weight_summable
      · intro n y
        have hnonneg : 0 ≤ weight n * min (dist (x n) (y n)) 1 :=
          term_nonneg x y n
        have hle : weight n * min (dist (x n) (y n)) 1 ≤ weight n :=
          term_le_weight x y n
        simpa [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg n),
          abs_of_nonneg (le_min dist_nonneg zero_le_one)] using hle
    exact hcont.isOpen_preimage _ isOpen_Iio
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
        have hmin_lt : min (dist (x n) (y n)) 1 < min (coordRadius n) 1 := by
          exact lt_of_mul_lt_mul_left (by
            simpa [term, coordBound] using hterm_lt_bound)
            (weight_nonneg n)
        have hdist : dist (x n) (y n) < coordRadius n :=
          min_lt_min_one_iff dist_nonneg (coordRadius_pos n hn) hmin_lt
        exact coordRadius_mem n hn (y n) hdist
    · intro hs
      refine isOpen_iff_mem_nhds.2 fun x hx => ?_
      rcases hs x hx with ⟨ε, εpos, hε⟩
      exact mem_of_superset ((dPi_ball_open x ε).mem_nhds (by simpa [dPi_self x] using εpos)) hε
  have productMetric_dist :
      ∀ x y : ∀ n, Y n, @dist (∀ n, Y n) productMetric.toDist x y = dPi x y := by
    intro x y
    rfl
  letI : MetricSpace (∀ n, Y n) := productMetric
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
      have hmin_lt : min (dist (u m k) (u n k)) 1 < min ε 1 := by
        exact lt_of_mul_lt_mul_left (by
          simpa [term, δ] using hterm_lt)
          (weight_nonneg k)
      exact min_lt_min_one_iff dist_nonneg εpos hmin_lt
    have hcoord_limit : ∀ k, ∃ xk : Y k, Tendsto (fun m => u m k) atTop (𝓝 xk) := by
      intro k
      exact hY_complete k (fun m => u m k) (hcoord_cauchy k)
    choose x hx using hcoord_limit
    exact ⟨x, tendsto_pi_nhds.2 hx⟩
  have h_separable : SeparableSpace (∀ n, Y n) := by
    by_cases hprod : Nonempty (∀ n, Y n)
    · let x0 : ∀ n, Y n := Classical.choice hprod
      haveI : ∀ n, Nonempty (Y n) := fun n => ⟨x0 n⟩
      let densePoint : (F : Finset ℕ) -> (∀ n : {n // n ∈ F}, ℕ) -> ∀ n, Y n :=
        fun F k n => if h : n ∈ F then TopologicalSpace.denseSeq (Y n) (k ⟨n, h⟩) else x0 n
      let Dprod : Set (∀ n, Y n) :=
        Set.range fun p : Sigma (fun F : Finset ℕ => ∀ n : {n // n ∈ F}, ℕ) =>
          densePoint p.1 p.2
      refine ⟨⟨Dprod, countable_range _, ?_⟩⟩
      rw [dense_iff_inter_open]
      intro O hO hOne
      rcases hOne with ⟨x, hxO⟩
      rcases isOpen_pi_iff.1 hO x hxO with ⟨I, U, hU, hIU⟩
      have hcoord :
          ∀ n : {n // n ∈ I}, ∃ k : ℕ, TopologicalSpace.denseSeq (Y n) k ∈ U n := by
        intro n
        rcases (TopologicalSpace.denseRange_denseSeq (α := Y n)).inter_open_nonempty
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

abbrev IsComeager {Y : Type*} [TopologicalSpace Y] (s : Set Y) : Prop :=
  IsMeagre sᶜ

theorem isComeager_iff_mem_residual {Y : Type*} [TopologicalSpace Y] {s : Set Y} :
    IsComeager s ↔ s ∈ residual Y := by
  simp [IsComeager, IsMeagre]

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
    let $(G_n)_{n\in\omega}$ be dense open subsets of $U$ in the relative topology. We show that $U\cap\bigcap_n G_n$ is
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
    contains a ball $\Ball{x}{r_0}$ contained in $V_n\cap G_n$. Choose $0<r<r_0$ small enough that
    $\Closure{\Ball{x}{r}}\IncludedIn \Ball{x}{r_0}$ and $\MetricDiameter{d}{\Closure{\Ball{x}{r}}}\le 2^{-(n+1)}$, and put
    $V_{n+1}:=\Ball{x}{r}$.

    Pick $x_n\in V_n$. The nesting and diameter bounds make $(x_n)$ Cauchy: for $m\ge n$, both $x_m$ and $x_n$ lie in
    $\Closure{V_n}$, whose diameter is at most $2^{-n}$. Completeness gives a limit $x\in X$. Since each $\Closure{V_n}$ is
    closed and contains the tail of the sequence, $x\in\Closure{V_n}$ for every $n$. The nesting also gives
    $\Closure{V_{n+1}}\IncludedIn G_n$, so $x\in G_n$ for every $n$, and $x\in U$. Thus $U\cap\bigcap_n G_n\ne\emptyset$.
    Since $U$ was an arbitrary nonempty open set, $\bigcap_n G_n$ is dense in $X$.

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
  letI : MetricSpace Y := completeMetricOnY.toMetricSpace
  have hY_complete : IsMetricComplete Y :=
    isMetricComplete_of_upgraded Y completeMetricOnY
  refine ⟨fun G hGopen hGdense => ?_⟩
  let B : ℕ -> ℝ≥0∞ := fun n => 1 / 2 ^ n
  have Bpos : ∀ n, 0 < B n := fun n =>
    ENNReal.div_pos one_ne_zero (by finiteness)
  have h_step :
      ∀ n x δ, δ ≠ 0 ->
        ∃ y r, 0 < r ∧ r ≤ B (n + 1) ∧
          closedEBall y r ⊆ closedEBall x δ ∩ G n := by
    intro n x δ hδ
    have hx_closure : x ∈ closure (G n) := hGdense n x
    rcases EMetric.mem_closure_iff.1 hx_closure (δ / 2) (ENNReal.half_pos hδ)
      with ⟨y, hyG, hxy⟩
    rw [edist_comm] at hxy
    obtain ⟨r, hrpos, hr_sub⟩ : ∃ r > 0, closedEBall y r ⊆ G n :=
      nhds_basis_closedEBall.mem_iff.1 (isOpen_iff_mem_nhds.1 (hGopen n) y hyG)
    refine ⟨y, min (min (δ / 2) r) (B (n + 1)), ?_, ?_, fun z hz => ⟨?_, ?_⟩⟩
    · exact lt_min (lt_min (ENNReal.half_pos hδ) hrpos) (Bpos (n + 1))
    · exact min_le_right _ _
    · calc
        edist z x ≤ edist z y + edist y x := edist_triangle _ _ _
        _ ≤ min (min (δ / 2) r) (B (n + 1)) + δ / 2 :=
          add_le_add hz (le_of_lt hxy)
        _ ≤ δ / 2 + δ / 2 :=
          add_le_add (le_trans (min_le_left _ _) (min_le_left _ _)) le_rfl
        _ = δ := ENNReal.add_halves δ
    · exact hr_sub (calc
        edist z y ≤ min (min (δ / 2) r) (B (n + 1)) := hz
        _ ≤ r := le_trans (min_le_left _ _) (min_le_right _ _))
  choose! center radius h_radius_pos h_radius_bound h_ball using h_step
  refine fun x => (mem_closure_iff_nhds_basis nhds_basis_closedEBall).2 fun ε hε => ?_
  let F : ℕ -> Y × ℝ≥0∞ := fun n =>
    Nat.recOn n (Prod.mk x (min ε (B 0))) fun n p =>
      Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ -> Y := fun n => (F n).1
  let r : ℕ -> ℝ≥0∞ := fun n => (F n).2
  have rpos : ∀ n, 0 < r n := by
    intro n
    induction n with
    | zero => exact lt_min hε (Bpos 0)
    | succ n _ => exact h_radius_pos n (c n) (r n) (ne_of_gt ‹0 < r n›)
  have r_ne_zero : ∀ n, r n ≠ 0 := fun n => (rpos n).ne'
  have rB : ∀ n, r n ≤ B n := by
    intro n
    cases n with
    | zero => exact min_le_right _ _
    | succ n => exact h_radius_bound n (c n) (r n) (r_ne_zero n)
  have h_incl : ∀ n, closedEBall (c (n + 1)) (r (n + 1)) ⊆
      closedEBall (c n) (r n) ∩ G n := fun n =>
    h_ball n (c n) (r n) (r_ne_zero n)
  have cdist : ∀ n, edist (c n) (c (n + 1)) ≤ B n := by
    intro n
    rw [edist_comm]
    have hself : c (n + 1) ∈ closedEBall (c (n + 1)) (r (n + 1)) :=
      mem_closedEBall_self
    have hsubset : closedEBall (c (n + 1)) (r (n + 1)) ⊆ closedEBall (c n) (B n) :=
      Subset.trans (h_incl n) (Subset.trans inter_subset_left (closedEBall_subset_closedEBall (rB n)))
    exact hsubset hself
  have hcauchy : CauchySeq c :=
    cauchySeq_of_edist_le_geometric_two _ ENNReal.one_ne_top cdist
  rcases hY_complete c hcauchy with ⟨y, hy_lim⟩
  refine ⟨y, ?_⟩
  simp only [mem_iInter]
  have h_nested : ∀ n, ∀ m ≥ n, closedEBall (c m) (r m) ⊆ closedEBall (c n) (r n) := by
    intro n
    refine Nat.le_induction ?_ fun m _ hm => ?_
    · exact Subset.rfl
    · exact Subset.trans (h_incl m) (Subset.trans inter_subset_left hm)
  have hy_ball : ∀ n, y ∈ closedEBall (c n) (r n) := by
    intro n
    refine isClosed_closedEBall.mem_of_tendsto hy_lim ?_
    exact (eventually_ge_atTop n).mono fun m hm => h_nested n m hm mem_closedEBall_self
  constructor
  · intro n
    exact (Subset.trans (h_incl n) inter_subset_right) (hy_ball (n + 1))
  · change edist y x ≤ ε
    exact le_trans (hy_ball 0) (min_le_left _ _)

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
  · letI : Nonempty ι := hι
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
  rcases hUne with ⟨x, hx⟩
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI : PolishSpace U := open_subspace_polish hUopen
  exact nonempty_open_not_meagre (X := U) isOpen_univ univ_nonempty

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
    \textbf{From $\Gdelta$ to Polish.} Write
    $$A = \bigcap_{n \in \NN} U_n$$
    with each $U_n \IncludedIn X$ open. By the open-subspace result above, each $U_n$ is Polish. Choose a complete
    compatible metric $d_n \le 1$ on each $U_n$.
    Replacing any complete compatible $\rho_n$ by $d_n=\min\{\rho_n,1\}$ preserves small balls and Cauchy sequences.

    The diagonal embedding
    $$\iota : A \to \prod_{n} U_n, \qquad \iota(x) = (x, x, x, \ldots)$$
    is a homeomorphism onto its image. The product $\prod_n U_n$ is Polish.

    We show that $\iota(A)$ is closed in $\prod_n U_n$. Suppose
    $$\iota(a^k)=(a^k,a^k,\ldots)$$
    converges in the product to $(b_1,b_2,\ldots)$. Then $a^k \to b_n$ in each $U_n$, hence also in $X$. Since $X$ is
    Hausdorff, limits in $X$ are unique, so all $b_n$ are one and the same point $x$. Because $x=b_n \in U_n$ for every $n$,
    we have $x \in A$, and the limit point is $\iota(x)$.

    Thus $\iota(A)$ is closed. Hence $A$ is homeomorphic to a closed subspace of a Polish space, and is Polish.
-/
theorem gdelta_subspace_polish {s : Set X} (hs : IsGδ s) :
    PolishSpace s := by
  rcases isGδ_iff_eq_iInter_nat.1 hs with ⟨U, hUopen, hsU⟩
  haveI : ∀ n, PolishSpace (U n) := fun n => open_subspace_polish (hUopen n)
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
  have hRange :
      Set.range diag =
        ⋂ n, {y : (∀ n, U n) | ((y n : U n) : X) = ((y 0 : U 0) : X)} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      simp [diag]
    · intro hy
      have hy' : ∀ n, ((y n : U n) : X) = ((y 0 : U 0) : X) := by
        intro n
        exact mem_iInter.1 hy n
      have hy0 : ((y 0 : U 0) : X) ∈ s := by
        rw [hsU]
        exact mem_iInter.2 fun n => by
          simpa [hy' n] using (y n).2
      refine ⟨⟨((y 0 : U 0) : X), hy0⟩, ?_⟩
      funext n
      apply Subtype.ext
      exact (hy' n).symm
  have hclosed_range : IsClosed (Set.range diag) := by
    rw [hRange]
    refine isClosed_iInter fun n => ?_
    exact isClosed_eq
      (continuous_subtype_val.comp (continuous_apply n))
      (continuous_subtype_val.comp (continuous_apply 0))
  exact ({ toIsEmbedding := hdiag_emb, isClosed_range := hclosed_range } :
    Topology.IsClosedEmbedding diag).polishSpace

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
    and fix a complete compatible metric $d$ on $X$. For each $n \ge 1$, using explicit $d$-balls in $X$, define
    $$V_n \;=\; \bigcup\, \{\MetricBall{d}{x}{\delta} \,:\, x \in X,\; \delta > 0,\;
    \MetricDiameter{\rho}{\MetricBall{d}{x}{\delta} \cap A} < 1/n\},$$
    a union of open $d$-balls in $X$. Hence each $V_n$ is open. Since $\rho$ induces the subspace topology on $A$, every
    point of $A$ has arbitrarily small $X$-neighborhoods whose trace on $A$ has small $\rho$-diameter, so
    $A \IncludedIn V_n$ for every positive integer $n$.

    We claim $A = \AmbientClosure{X}{A} \cap \bigcap_{n\ge 1} V_n$, where $\AmbientClosure{X}{A}$ denotes the closure of $A$
    in $X$.
    The closure factor excludes points away from $A$; the $V_n$'s force nearby traces of $A$ to have vanishing
    $\rho$-diameter.

    The inclusion $A \IncludedIn \AmbientClosure{X}{A} \cap \bigcap_{n\ge 1} V_n$ follows immediately from the preceding
    paragraph.

    For the reverse inclusion, take
    $$x \in \AmbientClosure{X}{A} \cap \bigcap_{n\ge 1} V_n.$$
    For each positive integer $n$, choose an open neighborhood $B_n$ of $x$ in $X$ such that
    $$\MetricDiameter{\rho}{B_n \cap A} < 1/n.$$
    Replacing $B_n$ by
    $$B_1 \cap \cdots \cap B_n \cap \MetricBall{d}{x}{1/n},$$
    we may assume
    $$B_1 \supseteq B_2 \supseteq \cdots
    \qquad\text{and}\qquad
    \MetricDiameter{d}{B_n}\to 0.$$
    Since $x \in \AmbientClosure{X}{A}$, every $B_n$ meets $A$. Choose $a_n \in B_n \cap A$.

    The sequence $(a_n)$ is $\rho$-Cauchy because the $\rho$-diameters of the traces $B_n \cap A$ tend to $0$. Since $\rho$
    is complete, $a_n \to a$ in $\rho$ for some $a \in A$. The $\rho$-topology agrees with the subspace topology, so $a_n
    \to a$ in $X$. On the other hand, $\MetricDiameter{d}{B_n}\to 0$ and $a_n \in B_n$ force $a_n \to x$ in $X$. Uniqueness
    of limits in the metric space $X$ gives $a=x$, hence $x \in A$.

    The set $\AmbientClosure{X}{A}$ is closed, and closed subsets of metric spaces are $\Gdelta$. Also, $\bigcap_n V_n$ is
    $\Gdelta$ because each $V_n$ is open. Therefore
    $$A=\AmbientClosure{X}{A}\cap\bigcap_n V_n$$
    is $\Gdelta$ in $X$.
-/
theorem polish_subspace_isGdelta {A : Set X} [PolishSpace A] :
    IsGδ A := by
  classical
  let completeMetricOnX : UpgradedIsCompletelyMetrizableSpace X :=
    upgradeIsCompletelyMetrizable X
  letI : MetricSpace X := completeMetricOnX.toMetricSpace
  let completeMetricOnA : UpgradedIsCompletelyMetrizableSpace A :=
    upgradeIsCompletelyMetrizable A
  letI : PseudoMetricSpace A := completeMetricOnA.toPseudoMetricSpace
  letI : MetricSpace A := completeMetricOnA.toMetricSpace
  letI : UniformSpace A := completeMetricOnA.toPseudoMetricSpace.toUniformSpace
  have hA_complete : IsMetricComplete A :=
    isMetricComplete_of_upgraded A completeMetricOnA
  let bound : ℕ -> ℝ := fun n => 1 / ((n : ℝ) + 1)
  let smallTrace : Set X -> ℕ -> Prop := fun U n =>
    ∀ a b : A, (a : X) ∈ U -> (b : X) ∈ U -> dist a b < bound n
  let V : ℕ -> Set X := fun n =>
    ⋃₀ {U : Set X | IsOpen U ∧ smallTrace U n}
  have bound_pos : ∀ n, 0 < bound n := by
    intro n
    positivity
  have bound_half_pos : ∀ n, 0 < bound n / 3 := by
    intro n
    positivity
  have bound_half_add : ∀ n, bound n / 3 + bound n / 3 < bound n := by
    intro n
    have hpos := bound_pos n
    linarith
  have hVopen : ∀ n, IsOpen (V n) := by
    intro n
    exact isOpen_sUnion fun U hU => hU.1
  have hA_subset_V : A ⊆ ⋂ n, V n := by
    intro x hx
    rw [mem_iInter]
    intro n
    let a : A := ⟨x, hx⟩
    let r : ℝ := bound n / 3
    have hrpos : 0 < r := bound_half_pos n
    have hball_open : IsOpen (Metric.ball a r : Set A) := isOpen_ball
    rcases isOpen_induced_iff.mp hball_open with ⟨U, hUopen, hUpre⟩
    have hxU : x ∈ U := by
      have : a ∈ Metric.ball a r := mem_ball_self hrpos
      have : a ∈ ((↑) : A -> X) ⁻¹' U := by simpa [hUpre] using this
      exact this
    have hsmall : smallTrace U n := by
      intro b c hb hc
      have hb_ball : b ∈ Metric.ball a r := by
        have : b ∈ ((↑) : A -> X) ⁻¹' U := hb
        simpa [hUpre] using this
      have hc_ball : c ∈ Metric.ball a r := by
        have : c ∈ ((↑) : A -> X) ⁻¹' U := hc
        simpa [hUpre] using this
      have hb_dist : dist b a < r := by simpa [Metric.mem_ball] using hb_ball
      have hc_dist : dist c a < r := by simpa [Metric.mem_ball] using hc_ball
      calc
        dist b c ≤ dist b a + dist c a := dist_triangle_right _ _ _
        _ < r + r := add_lt_add hb_dist hc_dist
        _ < bound n := bound_half_add n
    exact mem_sUnion.2 ⟨U, ⟨hUopen, hsmall⟩, hxU⟩
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
      exact ⟨U, hU.1, hU.2, hxU⟩
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
        exact (hUsmall N (aSeq m) (aSeq n) hmU hnU).trans hN
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
  exact isClosed_closure.isGδ.inter (IsGδ.iInter_of_isOpen hVopen)

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
    haveI : PolishSpace A := hA
    exact polish_subspace_isGdelta
  · exact gdelta_subspace_polish

theorem irrationals_polish :
    PolishSpace ({x : ℝ | Irrational x} : Set ℝ) :=
  gdelta_subspace_polish irrationals_are_gdelta

/-! ## Fsigma and Gdelta examples in the real line -/

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: statement
  kind: claim
  title: Examples in R with the usual topology
-/
/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    The rationals $\QQ = \bigcup_{q \in \QQ} \{q\}$ are $\Fsigma$, since singletons are closed. They are not $\Gdelta$:
    $\QQ$ is meager, since each singleton is closed and nowhere dense, while a dense $\Gdelta$ subset of $\R$ is comeager
    by the \termuse{Baire category theorem} in §{sec:baire-category}. If $\QQ$ were $\Gdelta$, it would be both meager and
    comeager, so its complement $\SetDifference{\R}{\QQ}$ would also be meager. Then $\R$ would be a union of two
    \termuseas{meager set}{meager sets}, contradicting the Baire category theorem. By duality, the irrationals
    $\SetDifference{\R}{\QQ}$ are $\Gdelta$ but not $\Fsigma$.
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
  haveI : PolishSpace ℚ := hpolish
  exact (nonempty_open_not_meagre (X := ℚ) isOpen_univ univ_nonempty) rational_space_meagre

theorem rationals_not_gdelta :
    ¬ IsGδ (Set.range ((↑) : ℚ -> ℝ)) := by
  intro hG
  exact (dense_gdelta_not_meagre hG Rat.denseRange_cast) rationals_are_meagre

theorem irrationals_not_fsigma :
    ¬ IsFsigma ({x : ℝ | Irrational x} : Set ℝ) := by
  intro hF
  have hG : IsGδ (({x : ℝ | Irrational x} : Set ℝ)ᶜ) := hF.isGdelta_compl
  have h_compl :
      (({x : ℝ | Irrational x} : Set ℝ)ᶜ) = Set.range ((↑) : ℚ -> ℝ) := by
    ext x
    simp only [mem_compl_iff, mem_setOf_eq, Irrational, not_not]
  exact rationals_not_gdelta (by simpa [h_compl] using hG)

/-!
## Sequence spaces

| Book term | Lean name |
| --- | --- |
| `\termdefine{zero-dimensional}` | `IsZeroDimensional` |
| `\termdefineas{perfect space}{perfect}` | mathlib class `PerfectSpace` |
| `\termdefine{Cantor space}` | `cantor_space` |
| `\termdefine{Baire space}` | `baire_space` |
| `\termdefine{Hilbert cube}` | `hilbert_cube` |
| `\termdefine{space of real sequences}` | `real_sequence_space` |
-/

/-- Book term `\termdefine{zero-dimensional}`:
a space has a base of clopen sets. -/
abbrev IsZeroDimensional (Y : Type*) [TopologicalSpace Y] : Prop :=
  IsTopologicalBasis {s : Set Y | IsClopen s}

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    A space is \termdefine{zero-dimensional} if it has a base
    of clopen sets.
-/
theorem zero_dimensional_iff_small_inductive (Y : Type) [TopologicalSpace Y] :
    IsZeroDimensional Y ↔ HasSmallInductiveDimensionLE Y 0 :=
  (HasSmallInductiveDimensionLT_one_iff Y).symm

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
  haveI : TotallySeparatedSpace Y := totallySeparatedSpace_of_t0_of_basis_clopen h_basis
  haveI : TotallyDisconnectedSpace Y := inferInstance
  exact not_preconnected_of_totally_disconnected_nontrivial Y

theorem bool_polish :
    PolishSpace Bool := by
  infer_instance

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The \termdefine{Cantor space} $\CantorSpace$. Brouwer's characterization identifies it as the compact
        zero-dimensional \termuseas{perfect space}{perfect} model.
-/
theorem cantor_space_polish :
    PolishSpace cantor_space := by
  haveI : PolishSpace Bool := bool_polish
  exact countable_product_polish

theorem cantor_space_compact :
    CompactSpace cantor_space := by
  infer_instance

theorem cantor_space_zero_dimensional :
    IsZeroDimensional cantor_space :=
  product_discrete_zero_dimensional ℕ fun _ => Bool

theorem cantor_space_not_connected :
    ¬ ConnectedSpace cantor_space := by
  intro h_connected
  haveI : PreconnectedSpace cantor_space := h_connected.toPreconnectedSpace
  exact not_preconnected_of_totally_disconnected_nontrivial cantor_space

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The \termdefine{Baire space} $\BaireSpace$. The Alexandrov–Urysohn characterization identifies it as the
        nowhere locally compact analogue of Cantor space.
-/
/-- Book term `\termdefine{Baire space}`: `ω^ω`. -/
abbrev baire_space : Type :=
  ℕ -> ℕ

theorem baire_space_polish :
    PolishSpace baire_space := by
  haveI : PolishSpace ℕ :=
    metric_complete_separable_polish ℕ (isMetricComplete_of_mathlib ℕ)
  exact countable_product_polish

theorem baire_space_noncompact :
    NoncompactSpace baire_space := by
  rw [← not_compactSpace_iff]
  intro hcompact
  haveI : CompactSpace baire_space := hcompact
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
    ¬ ConnectedSpace baire_space := by
  intro h_connected
  haveI : PreconnectedSpace baire_space := h_connected.toPreconnectedSpace
  exact not_preconnected_of_totally_disconnected_nontrivial baire_space

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
    The \termdefine{Hilbert cube} $\HilbertCube$. The Hilbert cube is moreover compact by Tychonoff, and it is the
        universal compact target for Polish spaces: every Polish space is homeomorphic to a subspace of $\HilbertCube$.
-/
/-- Book term `\termdefine{Hilbert cube}`: `[0,1]^ω`. -/
abbrev hilbert_cube : Type :=
  ℕ -> closed_unit_interval

theorem hilbert_cube_polish :
    PolishSpace hilbert_cube := by
  haveI : PolishSpace closed_unit_interval := closed_unit_interval_polish
  exact countable_product_polish

theorem hilbert_cube_compact :
    CompactSpace hilbert_cube := by
  infer_instance

theorem hilbert_cube_connected :
    ConnectedSpace hilbert_cube := by
  exact { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }

theorem hilbert_cube_not_zero_dimensional :
    ¬ IsZeroDimensional hilbert_cube :=
  not_zeroDimensional_of_preconnected_nontrivial hilbert_cube

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The \termdefine{space of real sequences} $\RealSequenceSpace$. Anderson's theorem gives a homeomorphism
        $\RealSequenceSpace\cong \ell^2$, and Anderson--Kadec says that every infinite-dimensional separable Fréchet
        space, hence every infinite-dimensional separable Banach space, is homeomorphic to $\ell^2$; see
        [@BessagaPelczynski1975] for the infinite-dimensional topology behind these statements. Thus every
        infinite-dimensional separable Banach space from §{sec:polish-examples} is homeomorphic to
        $\RealSequenceSpace$.
-/
/-- Book term `\termdefine{space of real sequences}`: `ℝ^ω`. -/
abbrev real_sequence_space : Type :=
  ℕ -> ℝ

theorem real_sequence_space_polish :
    PolishSpace real_sequence_space := by
  haveI : PolishSpace ℝ := real_polish
  exact countable_product_polish

theorem real_sequence_space_noncompact :
    NoncompactSpace real_sequence_space := by
  rw [← not_compactSpace_iff]
  intro hcompact
  haveI : CompactSpace real_sequence_space := hcompact
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

theorem baire_space_surjects [Nonempty X] :
    ∃ f : (Nat -> Nat) -> X, Continuous f ∧ Function.Surjective f :=
  PolishSpace.exists_nat_nat_continuous_surjective X

end PolishSpaceBook

end
