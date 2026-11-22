module

public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# Closed-set regularity and Ulam's compact approximation

The proofs follow the book's sigma-algebra of two-sided approximations and
its intersection of finite covers by closures of small balls.
-/

namespace PolishSpaceBook
namespace BorelMeasureRegularity

noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- A countable measurable union has a finite initial union with arbitrarily
small remainder. This is continuity from above applied to the remainders. -/
lemma exists_finite_union_remainder (A : ℕ → Set X)
    (hA : ∀ n, MeasurableSet (A n)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, μ ((⋃ n, A n) \ ⋃ n ≤ N, A n) < ε := by
  have hem : (⋂ n, (⋃ j, A j) \ A n) = ∅ := by
    ext x
    simp only [mem_iInter, Set.mem_sdiff, mem_iUnion, mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨n, hn⟩ := (h 0).1
    exact (h n).2 hn
  obtain ⟨N, hN⟩ := exists_measure_iInter_lt
    (fun n => ((MeasurableSet.iUnion hA).diff (hA n)).nullMeasurableSet)
    hε ⟨0, measure_ne_top μ _⟩ hem
  refine ⟨N, lt_of_le_of_lt (measure_mono ?_) hN⟩
  intro x hx
  exact mem_iInter₂.mpr (fun n hn => ⟨hx.1,
    fun hxn => hx.2 (mem_iUnion₂.mpr ⟨n, hn, hxn⟩)⟩)

variable [TopologicalSpace X] [BorelSpace X]

/-- The two-sided approximation property used to generate the Borel sigma-algebra. -/
def Approximable (A : Set X) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ F U : Set X,
    IsClosed F ∧ IsOpen U ∧ F ⊆ A ∧ A ⊆ U ∧ μ (U \ F) < ε

omit [IsFiniteMeasure μ] [BorelSpace X] in
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Taking complements exchanges
    the inner and outer approximants: if $F\IncludedIn B\IncludedIn U$, then
    $$U^c\IncludedIn B^c\IncludedIn F^c,
    \qquad \SetDifference{F^c}{U^c}=\SetDifference{U}{F}.$$
    Thus $\mathcal R$ is closed under complements.
-/
lemma approximable_compl {A : Set X} (hA : Approximable μ A) :
    Approximable μ Aᶜ := by
  intro ε hε
  obtain ⟨F, U, hF, hU, hFA, hAU, h⟩ := hA ε hε
  refine ⟨Uᶜ, Fᶜ, hU.isClosed_compl, hF.isOpen_compl,
    compl_subset_compl.mpr hAU, compl_subset_compl.mpr hFA, ?_⟩
  have heq : Fᶜ \ Uᶜ = U \ F := by ext x; simp; tauto
  rwa [heq]

omit [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] in
/-- Taking the finite union of inner approximants and the full union of outer
approximants controls their gap by all individual gaps and the finite tail. -/
lemma union_gap_subset (A F U : ℕ → Set X)
    (hFA : ∀ n, F n ⊆ A n) (hAU : ∀ n, A n ⊆ U n) (N : ℕ) :
    (⋃ n, U n) \ (⋃ n ≤ N, F n) ⊆
      (⋃ n, U n \ F n) ∪ ((⋃ n, A n) \ ⋃ n ≤ N, A n) := by
  intro x hx
  simp only [Set.mem_sdiff, mem_iUnion, mem_union] at hx ⊢
  by_cases hg : ∃ n, x ∈ U n ∧ x ∉ F n
  · exact Or.inl hg
  · right
    obtain ⟨n, hn⟩ := hx.1
    have hfn : x ∈ F n := by by_contra h; exact hg ⟨n, hn, h⟩
    refine ⟨⟨n, hFA n hfn⟩, ?_⟩
    rintro ⟨j, hj, hxj⟩
    apply hg
    exact ⟨j, hAU j hxj, fun hf => hx.2 ⟨j, hj, hf⟩⟩

omit [IsFiniteMeasure μ] [TopologicalSpace X] [BorelSpace X] in
/-- The common numerical bound for finite inner and countable outer unions. -/
lemma measure_union_gap_le (A F U : ℕ → Set X)
    (hFA : ∀ n, F n ⊆ A n) (hAU : ∀ n, A n ⊆ U n) (N : ℕ) :
    μ ((⋃ n, U n) \ ⋃ n ≤ N, F n) ≤
      (∑' n, μ (U n \ F n)) + μ ((⋃ n, A n) \ ⋃ n ≤ N, A n) := by
  calc
    μ ((⋃ n, U n) \ ⋃ n ≤ N, F n) ≤
        μ ((⋃ n, U n \ F n) ∪ ((⋃ n, A n) \ ⋃ n ≤ N, A n)) :=
      measure_mono (union_gap_subset A F U hFA hAU N)
    _ ≤ μ (⋃ n, U n \ F n) + μ ((⋃ n, A n) \ ⋃ n ≤ N, A n) :=
      measure_union_le _ _
    _ ≤ (∑' n, μ (U n \ F n)) + μ ((⋃ n, A n) \ ⋃ n ≤ N, A n) := by
      gcongr
      exact measure_iUnion_le _

omit [BorelSpace X] in
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    For countable unions, let $A=\bigcup_n A_n$ with $A_n\in\mathcal R$. Choose closed $F_n$ and open $U_n$ with
    $$F_n\IncludedIn A_n\IncludedIn U_n,
    \qquad \mu(\SetDifference{U_n}{F_n})<\varepsilon 2^{-(n+2)}.$$
    Continuity from below gives $N$ such that, writing $A_N^*=\bigcup_{n\le N}A_n$,
    $$\mu(\SetDifference{A}{A_N^*})<\varepsilon/2.$$
    The set $F=\bigcup_{n\le N}F_n$ is closed, $U=\bigcup_n U_n$ is open, and $F\IncludedIn A\IncludedIn U$.
    Moreover,
    $$\SetDifference{U}{F}
    \IncludedIn\bigcup_n\SetDifference{U_n}{F_n}\;\cup\;\SetDifference{A}{A_N^*}.$$
    To check this inclusion, a point of $U$ outside all the gaps $\SetDifference{U_n}{F_n}$ lies in some $F_n$, hence in
    $A$. If it also lies in $A_N^*$, it belongs to some $U_j$ with $j\le N$, hence to $F_j$ and therefore to $F$.
    Consequently,
    $$\mu(\SetDifference{U}{F})
    \le\sum_{n=0}^{\infty}\mu(\SetDifference{U_n}{F_n})+\mu(\SetDifference{A}{A_N^*})
    <\varepsilon/2+\varepsilon/2=\varepsilon.$$
-/
lemma approximable_iUnion (A : ℕ → Set X)
    (hA : ∀ n, MeasurableSet (A n)) (h : ∀ n, Approximable μ (A n)) :
    Approximable μ (⋃ n, A n) := by
  intro ε hε
  by_cases htop : ε = ∞
  · subst ε
    exact ⟨∅, univ, isClosed_empty, isOpen_univ, empty_subset _, subset_univ _,
      by simp⟩
  let δ : ℕ → ℝ≥0∞ := fun n => ε / 2 * (2⁻¹ : ℝ≥0∞) ^ (n + 1)
  have hδpos (n : ℕ) : 0 < δ n := by
    dsimp [δ]
    exact ENNReal.mul_pos (ENNReal.half_pos hε.ne').ne'
      (pow_ne_zero _ (by simp))
  have hδsum : ∑' n, δ n = ε / 2 := by
    simp only [δ, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
    norm_num only [ENNReal.one_sub_inv_two, inv_inv]
    rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  choose F U hF hU hFA hAU hgap using fun n => h n (δ n) (hδpos n)
  obtain ⟨N, hN⟩ := exists_finite_union_remainder μ A hA
    (ENNReal.half_pos hε.ne')
  refine ⟨⋃ n ≤ N, F n, ⋃ n, U n, ?_, isOpen_iUnion hU,
    ?_, iUnion_mono hAU, ?_⟩
  · exact (finite_le_nat N).isClosed_biUnion (fun n _ => hF n)
  · exact iUnion₂_subset fun n _ => (hFA n).trans (subset_iUnion A n)
  · calc
      μ ((⋃ n, U n) \ ⋃ n ≤ N, F n) ≤
          (∑' n, μ (U n \ F n)) + μ ((⋃ n, A n) \ ⋃ n ≤ N, A n) :=
        measure_union_gap_le μ A F U hFA hAU N
      _ ≤ ε / 2 + μ ((⋃ n, A n) \ ⋃ n ≤ N, A n) := by
        gcongr
        rw [← hδsum]
        exact ENNReal.tsum_le_tsum (fun n => (hgap n).le)
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add_left (by finiteness) hN
      _ = ε := ENNReal.add_halves ε

variable [MetrizableSpace X]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Every open set belongs
    to $\mathcal R$: it is an increasing union of closed sets in a metric space, so continuity from below and finite total
    mass give the inner approximation, while the set itself gives the outer approximation.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Let $\mathcal R$ consist of the Borel sets with the displayed two-sided approximation property.
-/
lemma approximable_open {U : Set X} (hU : IsOpen U) : Approximable μ U := by
  let := TopologicalSpace.metrizableSpaceMetric X
  intro ε hε
  obtain ⟨F, hF, hFU, hUnion, hMono⟩ := hU.exists_iUnion_isClosed
  obtain ⟨N, hN⟩ := exists_finite_union_remainder μ F
    (fun n => (hF n).measurableSet) hε
  refine ⟨⋃ n ≤ N, F n, U,
    (finite_le_nat N).isClosed_biUnion (fun n _ => hF n), hU,
    iUnion₂_subset (fun n _ => hFU n), Subset.rfl, ?_⟩
  simpa only [hUnion] using hN

/-- Closed-set regularity proved by the sigma-algebra argument, with no
regularity theorem used as a black box. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Thus $\mathcal R$ is a $\sigma$-algebra containing the open sets, so it contains every Borel set.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: lemma
  title: Closed-set regularity
-/
theorem closed_open_approximation {A : Set X} (hA : MeasurableSet A)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F U : Set X, IsClosed F ∧ IsOpen U ∧ F ⊆ A ∧ A ⊆ U ∧ μ (U \ F) < ε := by
  have happ : ∀ S : Set X, MeasurableSet S → Approximable μ S :=
    MeasurableSet.induction_on_open
      (fun _ hU => approximable_open μ hU)
      (fun _ _ ih => approximable_compl μ ih)
      (fun A _ hA ih => approximable_iUnion μ A hA ih)
  exact happ A hA ε hε

end

noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

variable {X : Type*} [MetricSpace X]

/-- At scale `k + 1`, retain the first `N + 1` ball closures of the dense cover.
We use closures of open balls, as in the book; they need not equal closed balls. -/
def finiteBallClosureCover (q : ℕ → X) (k N : ℕ) : Set X :=
  ⋃ n ≤ N, closure (Metric.ball (q n) (1 / ((k : ℝ) + 1)))

lemma finiteBallClosureCover_closed (q : ℕ → X) (k N : ℕ) :
    IsClosed (finiteBallClosureCover q k N) :=
  (finite_le_nat N).isClosed_biUnion (fun _ _ => isClosed_closure)

lemma dense_ball_closures_cover (q : ℕ → X) (hq : DenseRange q) (k : ℕ) :
    (⋃ n, closure (Metric.ball (q n) (1 / ((k : ℝ) + 1)))) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := hq.exists_dist_lt x (show 0 < 1 / ((k : ℝ) + 1) by positivity)
  exact mem_iUnion.mpr ⟨n, subset_closure (by simpa [Metric.mem_ball, dist_comm] using hn)⟩

/-- The intersection of these finite covers is totally bounded, regardless
of how many balls have been retained at each scale. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    The set $K$ is totally bounded: for any $r>0$, choose $k$ with $2/k<r$. Then
    $$K\IncludedIn C_k\IncludedIn\bigcup_{n\le N_k}\Ball{q_n}{2/k}
    \IncludedIn\bigcup_{n\le N_k}\Ball{q_n}{r}.$$
-/
lemma covers_totallyBounded (q : ℕ → X) (N : ℕ → ℕ) :
    TotallyBounded (⋂ k, finiteBallClosureCover q k (N k)) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
  refine ⟨q '' Set.Iic (N k), (finite_le_nat _).image q, ?_⟩
  intro x hx
  obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp (mem_iInter.mp hx k)
  refine mem_iUnion₂.mpr ⟨q n, ⟨n, hn, rfl⟩, ?_⟩
  have hd := Metric.mem_closedBall.mp (Metric.closure_ball_subset_closedBall hxn)
  apply Metric.mem_ball.mpr
  exact hd.trans_lt (hk.trans (half_lt_self hε))

variable [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ] [CompleteSpace X]

/-- Ulam's compact set is the intersection of finite closed-ball covers.
The error at the first scale remains strict when the errors are summed. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    If $X=\emptyset$, take $K=\emptyset$. Otherwise, fix a complete compatible metric $d$ and a countable dense set
    $\IndexedFamily{q_n}{n\in\omega}$. For each $k\ge1$, the closures of the balls $\Ball{q_n}{1/k}$ cover $X$.
    Continuity from below therefore gives $N_k$ such that
    $$C_k:=\bigcup_{n\le N_k}\Closure{\Ball{q_n}{1/k}},
    \qquad \mu(\SetDifference{X}{C_k})<\varepsilon 2^{-k}.$$
    Set $K:=\bigcap_{k\ge1}C_k$. Each $C_k$ is closed, so $K$ is closed, and
    $$\mu(\SetDifference{X}{K})
    \le\sum_{k=1}^{\infty}\mu(\SetDifference{X}{C_k})
    <\sum_{k=1}^{\infty}\varepsilon 2^{-k}=\varepsilon.$$
    The strict inequality follows by retaining the strict bound for $k=1$ and using the non-strict bounds for $k\ge2$;
    the geometric series is finite.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    A closed totally bounded subset of a complete metric space is compact. Indeed, total boundedness produces a Cauchy
    subsequence of every sequence, completeness supplies its limit, and closedness keeps that limit in the set.
-/
theorem compact_concentration_of_dense (q : ℕ → X) (hq : DenseRange q)
    {ε : ℝ≥0∞} (hε : 0 < ε) (hεtop : ε ≠ ∞) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε := by
  let δ : ℕ → ℝ≥0∞ := fun k => ε * (2⁻¹ : ℝ≥0∞) ^ (k + 1)
  have hδpos (k : ℕ) : 0 < δ k :=
    ENNReal.mul_pos hε.ne' (pow_ne_zero _ (by simp))
  have hδsum : ∑' k, δ k = ε := by
    simp only [δ, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one,
      ENNReal.one_sub_inv_two, inv_inv]
    rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  have hex (k : ℕ) : ∃ N, μ (finiteBallClosureCover q k N)ᶜ < δ k := by
    obtain ⟨N, hN⟩ := exists_finite_union_remainder μ
      (fun n => closure (Metric.ball (q n) (1 / ((k : ℝ) + 1))))
      (fun _ => isClosed_closure.measurableSet) (hδpos k)
    refine ⟨N, ?_⟩
    simpa only [dense_ball_closures_cover q hq k, ← compl_eq_univ_sdiff, finiteBallClosureCover] using hN
  choose N hN using hex
  let K := ⋂ k, finiteBallClosureCover q k (N k)
  have hclosed : IsClosed K := isClosed_iInter (fun k => finiteBallClosureCover_closed q k (N k))
  refine ⟨K, (covers_totallyBounded q N).isCompact_of_isClosed hclosed, ?_⟩
  have hsumle : (∑' k, μ (finiteBallClosureCover q k (N k))ᶜ) ≤ ε := by
    rw [← hδsum]
    exact ENNReal.tsum_le_tsum (fun k => (hN k).le)
  calc
    μ Kᶜ = μ (⋃ k, (finiteBallClosureCover q k (N k))ᶜ) := by
      change μ (⋂ k, finiteBallClosureCover q k (N k))ᶜ = _
      rw [compl_iInter]
    _ ≤ ∑' k, μ (finiteBallClosureCover q k (N k))ᶜ := measure_iUnion_le _
    _ < ∑' k, δ k := ENNReal.tsum_lt_tsum
      (ne_top_of_le_ne_top hεtop hsumle) (fun k => (hN k).le) (hN 0)
    _ = ε := hδsum

end

noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- Compact concentration for every positive error, including the empty space. -/
theorem compact_concentration {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε := by
  by_cases htop : ε = ∞
  · exact ⟨∅, isCompact_empty, by simp [htop]⟩
  by_cases hX : Nonempty X
  · let := hX
    let := upgradeIsCompletelyMetrizable X
    exact compact_concentration_of_dense μ (denseSeq X) (denseRange_denseSeq X) hε htop
  · have : IsEmpty X := not_nonempty_iff.mp hX
    have hem : (univ : Set X) = ∅ := by ext x; exact isEmptyElim x
    exact ⟨∅, isCompact_empty, by simpa only [compl_empty, hem, measure_empty] using hε⟩

/-- Intersect the closed inner approximation with Ulam's compact concentration
set. The two discarded pieces each have measure below half the error. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    It suffices to find compact $K \IncludedIn X$ with $\mu(\SetDifference{X}{K}) < \varepsilon$ for
    every
    $\varepsilon > 0$. Indeed, apply closed-set regularity inside a given Borel set with error $\varepsilon/2$, apply this
    compact-concentration claim with the same error, and intersect the two approximants.
-/
theorem compact_inner_approximation {A : Set X} (hA : MeasurableSet A)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set X, K ⊆ A ∧ IsCompact K ∧ μ (A \ K) < ε := by
  by_cases htop : ε = ∞
  · exact ⟨∅, empty_subset _, isCompact_empty, by simp [htop]⟩
  obtain ⟨F, U, hF, _, hFA, hAU, hgap⟩ :=
    closed_open_approximation μ hA (ENNReal.half_pos hε.ne')
  obtain ⟨C, hC, herror⟩ := compact_concentration μ (ENNReal.half_pos hε.ne')
  refine ⟨C ∩ F, inter_subset_right.trans hFA, hC.inter_right hF, ?_⟩
  calc
    μ (A \ (C ∩ F)) ≤ μ ((U \ F) ∪ Cᶜ) := by
      apply measure_mono
      intro x hx
      by_cases hf : x ∈ F
      · exact Or.inr (fun hc => hx.2 ⟨hc, hf⟩)
      · exact Or.inl ⟨hAU hx.1, hf⟩
    _ ≤ μ (U \ F) + μ Cᶜ := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hgap herror
    _ = ε := ENNReal.add_halves ε

/-- The canonical inner-regularity statement obtained from the explicit
compact approximants, rather than from a library regularity instance. -/
theorem innerRegular_compact :
    μ.InnerRegularWRT (fun K => IsCompact K ∧ IsClosed K) MeasurableSet := by
  intro A hA r hr
  obtain ⟨K, hKA, hK, herror⟩ := compact_inner_approximation μ hA (tsub_pos_of_lt hr)
  exact ⟨K, hKA, ⟨hK, hK.isClosed⟩,
    lt_of_tsub_lt_tsub_left (le_measure_sdiff.trans_lt herror)⟩

end
end BorelMeasureRegularity
end PolishSpaceBook
