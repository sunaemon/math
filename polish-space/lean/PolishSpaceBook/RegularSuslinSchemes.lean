module

public import PolishSpaceBook.AnalyticSetsSuslinSchemes

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Regular Suslin schemes from continuous images

The construction partitions the source into clopen pieces that are small both
in the source metric and after applying the continuous map. Children are formed
by removing the finitely many preceding pieces of a countable cover.
-/

namespace PolishSpaceBook
namespace RegularSuslin

open Set TopologicalSpace Topology Filter

noncomputable section

variable {Y X : Type*} [MetricSpace Y] [SecondCountableTopology Y] [MetricSpace X]

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    Suppose $P_s$ is given, and put $\epsilon:=2^{-(|s|+1)}$. For each $u\in P_s$, continuity of $f$ and the relative
    clopen basis of $P$ give a relatively clopen neighborhood $V$ of $u$ such that
    $$
    V\IncludedIn P_s\cap\MetricBall{\SeqMetricName}{u}{\epsilon/2}
    \cap f^{-1}(\MetricBall{d}{f(u)}{\epsilon/2}).
    $$
    The triangle inequality gives both $\MetricDiameter{\SeqMetricName}{V}\le\epsilon$ and
    $\MetricDiameter{d}{f(V)}\le\epsilon$. These neighborhoods cover $P_s$. By second countability, choose a countable
    subcover $\Sequence{B_k}{k\in\omega}$; if $P_s=\emptyset$, take every $B_k$ empty.
-/
/-- Simultaneously shrink a clopen cover in the source and in its continuous image. -/
theorem small_cover (hzero : IsZeroDimensional Y) {f : Y → X} (hf : Continuous f)
    {U : Set Y} (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℕ → {V : Set Y // IsClopen V ∧ V ⊆ U ∧
      (∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε) ∧
      (∀ x ∈ V, ∀ y ∈ V, dist (f x) (f y) ≤ ε)}, U ⊆ ⋃ n, (B n).val := by
  let Small := {V : Set Y // IsClopen V ∧ V ⊆ U ∧
    (∀ x ∈ V, ∀ y ∈ V, dist x y ≤ ε) ∧
    (∀ x ∈ V, ∀ y ∈ V, dist (f x) (f y) ≤ ε)}
  let : Nonempty Small := ⟨⟨∅, isClopen_empty, by simp, by simp, by simp⟩⟩
  have hcover : U ⊆ ⋃ V : Small, V.val := by
    intro x hx
    let O := U ∩ Metric.ball x (ε / 2) ∩ f ⁻¹' Metric.ball (f x) (ε / 2)
    have hO : IsOpen O := (hU.inter Metric.isOpen_ball).inter (Metric.isOpen_ball.preimage hf)
    have hxO : x ∈ O := ⟨⟨hx, Metric.mem_ball_self (half_pos hε)⟩,
      Metric.mem_ball_self (half_pos hε)⟩
    obtain ⟨V, hV, hxV, hVO⟩ := hzero.exists_subset_of_mem_open hxO hO
    have hsmall : ∀ y ∈ V, ∀ z ∈ V, dist y z ≤ ε := by
      intro y hy z hz
      have hy' := (hVO hy).1.2
      have hz' := (hVO hz).1.2
      change dist y x < ε / 2 at hy'
      change dist z x < ε / 2 at hz'
      have := dist_triangle_right y z x
      linarith
    have himage : ∀ y ∈ V, ∀ z ∈ V, dist (f y) (f z) ≤ ε := by
      intro y hy z hz
      have hy' := (hVO hy).2
      have hz' := (hVO hz).2
      change dist (f y) (f x) < ε / 2 at hy'
      change dist (f z) (f x) < ε / 2 at hz'
      have := dist_triangle_right (f y) (f z) (f x)
      linarith
    exact mem_iUnion.mpr ⟨⟨V, hV, fun y hy => (hVO hy).1.1, hsmall, himage⟩, hxV⟩
  exact (HereditarilyLindelofSpace.isLindelof U).indexed_countable_subcover
    (fun V : Small => V.val) (fun V => V.property.1.isOpen) hcover

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    Define the children directly by
    $$
    P_{s\concat(k)}:=\SetDifference{B_k}{\bigcup_{j<k}B_j}.
    $$
    Each child is relatively clopen because only finitely many earlier clopen sets are removed. The children are pairwise
    disjoint, and they cover $P_s$: a point belongs to the child with the least index of a covering set containing it.
    Empty children remain in the indexing. Since $P_{s\concat(k)}\IncludedIn B_k$, both diameter bounds pass to each
    child. Taking closures of their images gives $F_{s\concat(k)}$. The containment
    $P_{s\concat(k)}\IncludedIn P_s$ makes these closures subsets of $F_s$, and closure does not increase metric diameter.
-/
/-- The empty source piece needs no separate enumeration: disjointification
retains empty children and gives a partition indexed by all natural numbers. -/
theorem small_partition (hzero : IsZeroDimensional Y) {f : Y → X} (hf : Continuous f)
    {U : Set Y} (hU : IsOpen U) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : ℕ → Set Y,
      (∀ n, IsClopen (V n) ∧ V n ⊆ U ∧
        (∀ x ∈ V n, ∀ y ∈ V n, dist x y ≤ ε) ∧
        (∀ x ∈ V n, ∀ y ∈ V n, dist (f x) (f y) ≤ ε)) ∧
      Pairwise (fun m n => Disjoint (V m) (V n)) ∧ U = ⋃ n, V n := by
  obtain ⟨B, hB⟩ := small_cover hzero hf hU hε
  let C : ℕ → Set Y := fun n => (B n).val
  refine ⟨disjointSeq C, ?_, disjointSeq_pairwiseDisjoint C, ?_⟩
  · intro n
    exact ⟨disjointSeq_isClopen (fun n => (B n).property.1) n,
      (disjointSeq_subset C n).trans (B n).property.2.1,
      fun x hx y hy => (B n).property.2.2.1 x hx.1 y hy.1,
      fun x hx y hy => (B n).property.2.2.2 x hx.1 y hy.1⟩
  · rw [iUnion_disjointSeq_eq_iUnion]
    exact subset_antisymm hB (iUnion_subset fun n => (B n).property.2.1)

/-- A successor partition at the precision prescribed by the parent length. -/
def children (hzero : IsZeroDimensional Y) {f : Y → X} (hf : Continuous f)
    (U : Clopens Y) (n : ℕ) : ℕ → Set Y :=
  Classical.choose (small_partition hzero hf U.isOpen
    (by positivity : 0 < (1 / 2 : ℝ) ^ (n + 1)))

theorem children_spec (hzero : IsZeroDimensional Y) {f : Y → X} (hf : Continuous f)
    (U : Clopens Y) (n : ℕ) :
    (∀ k, IsClopen (children hzero hf U n k) ∧ children hzero hf U n k ⊆ U ∧
      (∀ x ∈ children hzero hf U n k, ∀ y ∈ children hzero hf U n k,
        dist x y ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
      (∀ x ∈ children hzero hf U n k, ∀ y ∈ children hzero hf U n k,
        dist (f x) (f y) ≤ (1 / 2 : ℝ) ^ (n + 1))) ∧
    Pairwise (fun k l => Disjoint (children hzero hf U n k) (children hzero hf U n l)) ∧
    (U : Set Y) = ⋃ k, children hzero hf U n k :=
  Classical.choose_spec (small_partition hzero hf U.isOpen (by positivity))

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    We recursively build relatively clopen pieces $P_s\IncludedIn P$ and closed sets
    $$F_s:=\Closure{f(P_s)}$$
    so that:
-/
/-- Recursion on the last letter keeps the parent-child orientation visible. -/
def piece (hzero : IsZeroDimensional Y) {f : Y → X} (hf : Continuous f) : finseq ℕ → Clopens Y :=
  fun s => s.reverseRecOn (motive := fun _ => Clopens Y) ⊤
    (fun t k U => ⟨children hzero hf U t.length k, (children_spec hzero hf U t.length).1 k |>.1⟩)

@[simp] theorem piece_nil (hzero : IsZeroDimensional Y) {f : Y → X} (hf : Continuous f) :
    piece hzero hf [] = ⊤ := by simp [piece]

theorem piece_child (hzero : IsZeroDimensional Y) {f : Y → X} (hf : Continuous f)
    (s : finseq ℕ) (k : ℕ) :
    (piece hzero hf (s ++ [k]) : Set Y) = children hzero hf (piece hzero hf s) s.length k := by
  simp [piece]


@[simp] theorem mem_piece_child (hzero : IsZeroDimensional Y) {f : Y → X} (hf : Continuous f)
    (s : finseq ℕ) (k : ℕ) (x : Y) :
    x ∈ piece hzero hf (s ++ [k]) ↔ x ∈ children hzero hf (piece hzero hf s) s.length k := by
  change x ∈ (piece hzero hf (s ++ [k]) : Set Y) ↔ _
  rw [piece_child]

variable (hzero : IsZeroDimensional Y) {f : Y → X} (hf : Continuous f)

/-- The source pieces decrease along arbitrary finite extensions. -/
theorem piece_subset {s t : finseq ℕ} (hst : prefixOf s t) :
    (piece hzero hf t : Set Y) ⊆ piece hzero hf s := by
  obtain ⟨r, rfl⟩ := hst
  induction r using List.reverseRecOn with
  | nil => simp
  | append_singleton r a ih =>
      rw [← List.append_assoc, piece_child]
      exact ((children_spec hzero hf (piece hzero hf (s ++ r)) (s ++ r).length).1 a).2.1.trans ih

theorem piece_dist_bound (hbounded : ∀ x y : Y, dist x y ≤ 1) (s : finseq ℕ) :
    ∀ x ∈ piece hzero hf s, ∀ y ∈ piece hzero hf s, dist x y ≤ (1 / 2 : ℝ) ^ s.length := by
  induction s using List.reverseRecOn with
  | nil => simpa using fun x (_ : x ∈ (⊤ : Clopens Y)) y (_ : y ∈ (⊤ : Clopens Y)) => hbounded x y
  | append_singleton s k _ =>
      simpa only [mem_piece_child, List.length_append, List.length_singleton] using
        ((children_spec hzero hf (piece hzero hf s) s.length).1 k).2.2.1

theorem piece_image_dist_bound (hbounded : ∀ x y : X, dist x y ≤ 1) (s : finseq ℕ) :
    ∀ x ∈ piece hzero hf s, ∀ y ∈ piece hzero hf s, dist (f x) (f y) ≤ (1 / 2 : ℝ) ^ s.length := by
  induction s using List.reverseRecOn with
  | nil => simpa using fun x (_ : x ∈ (⊤ : Clopens Y)) y (_ : y ∈ (⊤ : Clopens Y)) => hbounded (f x) (f y)
  | append_singleton s k _ =>
      simpa only [mem_piece_child, List.length_append, List.length_singleton] using
        ((children_spec hzero hf (piece hzero hf s) s.length).1 k).2.2.2

/-- Only nonempty pieces are retained in the branch tree. -/
def pieceTree : Set (finseq ℕ) := {s | (piece hzero hf s : Set Y).Nonempty}

theorem pieceTree_subtree : IsSubtree (pieceTree hzero hf) :=
  fun _ _ ht hst => ht.mono (piece_subset hzero hf hst)

/-- The generic clopen-scheme infrastructure now applies to the constructed pieces. -/
theorem sourceCore [Nonempty Y] : ClopenSchemeCore (pieceTree hzero hf)
    (fun s => (piece hzero hf s : Set Y)) where
  root_mem := by simp [pieceTree]
  root_eq := by simp
  nonempty := fun _ hs => hs
  clopen := fun _ _ => (piece hzero hf _).isClopen
  children_cover := by
    intro s _
    rw [(children_spec hzero hf (piece hzero hf s) s.length).2.2]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨k, hx⟩
      have hx' : x ∈ piece hzero hf (concat s [k]) := by simpa [concat] using hx
      exact ⟨⟨k, ⟨x, hx'⟩⟩, hx'⟩
    · rintro ⟨k, hx⟩
      exact ⟨k.val, by simpa [concat] using hx⟩
  children_disjoint := by
    intro s _ i j hij
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    simpa only [concat, piece_child] using (children_spec hzero hf (piece hzero hf s) s.length).2.1 hne

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    \begin{enumerate}
    \item $P_\emptyset=P$;
    \item $P_{s\concat(k)}\IncludedIn P_s$;
    \item $P_s=\bigcup_k P_{s\concat(k)}$;
    \item $\MetricDiameter{\SeqMetricName}{P_s}\le 2^{-|s|}$ whenever $s\ne\emptyset$;
    \item $\MetricDiameter{d}{F_\emptyset}\le1$, and $\MetricDiameter{d}{F_s}\le 2^{-|s|}$ whenever
          $s\ne\emptyset$.
    \end{enumerate}
-/
theorem sourceMetricCore [Nonempty Y] (hbounded : ∀ x y : Y, dist x y ≤ 1) :
    ClopenSchemeMetricCore (pieceTree hzero hf) (fun s => (piece hzero hf s : Set Y)) where
  toClopenSchemeCore := sourceCore hzero hf
  dist_bound := fun _ _ => piece_dist_bound hzero hf hbounded _

/-- Closed image approximations; closures preserve the geometric diameter bound. -/
def imageScheme (s : finseq ℕ) : Set X := closure (f '' (piece hzero hf s : Set Y))

theorem imageScheme_regular (hbounded : ∀ x y : X, dist x y ≤ 1) :
    IsRegularSuslinScheme (imageScheme hzero hf) := by
  refine ⟨?_, fun _ => isClosed_closure, ?_⟩
  · intro s k
    exact closure_mono (image_mono (piece_subset hzero hf (List.prefix_append s [k])))
  · intro s
    rw [imageScheme, Metric.ediam_closure]
    apply Metric.ediam_le_of_forall_dist_le
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact piece_image_dist_bound hzero hf hbounded s x hx y hy


/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    Conversely, suppose $x\in\mathcal A(F_s)$, witnessed by $p$. For each $n$, choose $u_n\in P_{\restrict{p}{n}}$ with
    $$d(f(u_n),x)\le 2^{-n};$$
    this is possible because $x\in\Closure{f(P_{\restrict{p}{n}})}$. For $m,\ell\ge n\ge1$, nesting and the diameter bound
    give
    $$\SeqMetric{u_m}{u_\ell}\le2^{-n}.$$
    Thus $\Sequence{u_n}{n\in\omega}$ is Cauchy in the complete space $P$. Let $u$ be its limit. For each $n$, all
    sufficiently late terms lie
    in the relatively closed set $P_{\restrict{p}{n}}$, so
    $$u\in\bigcap_n P_{\restrict{p}{n}}\IncludedIn P.$$
    The shrinking diameters make this intersection contain at most one point. Continuity gives $f(u_n)\to f(u)$, whereas
    the approximation estimate gives $f(u_n)\to x$. Uniqueness of limits yields $f(u)=x$, so $x\in f(P)=A$.
    \end{proof}
-/
/-- A point in the Suslin operation is approximated by a Cauchy sequence of
source points in nested clopen pieces. Its limit stays in every piece. -/
theorem source_limit [Nonempty Y] (hcomplete : IsMetricComplete Y)
    (hbounded : ∀ x y : Y, dist x y ≤ 1) {x : X} {p : baire_space}
    (hx : ∀ n, x ∈ imageScheme hzero hf (seqPrefix p n)) :
    ∃ u : Y, (∀ n, u ∈ piece hzero hf (seqPrefix p n)) ∧ f u = x := by
  have happ (n : ℕ) : ∃ u ∈ piece hzero hf (seqPrefix p n),
      dist (f u) x ≤ (1 / 2 : ℝ) ^ n := by
    obtain ⟨y, ⟨u, hu, rfl⟩, hy⟩ :=
      Metric.mem_closure_iff.mp (hx n) ((1 / 2 : ℝ) ^ n) (by positivity)
    exact ⟨u, hu, by simpa only [dist_comm] using hy.le⟩
  choose a ha hnear using happ
  let H := sourceMetricCore hzero hf hbounded
  have hp : p ∈ treeBody (pieceTree hzero hf) := fun n => ⟨a n, ha n⟩
  have hc := clopenSchemeMetricCore_branch_sample_cauchy (pieceTree_subtree hzero hf) H hp ha
  obtain ⟨u, hu⟩ := hcomplete a hc
  have hmem (n : ℕ) : u ∈ piece hzero hf (seqPrefix p n) := by
    apply (piece hzero hf (seqPrefix p n)).isClosed.mem_of_tendsto hu
    exact (eventually_ge_atTop n).mono fun m hm =>
      clopenSchemeCore_branch_subset (pieceTree_subtree hzero hf) H.toClopenSchemeCore hp hm (ha m)
  have hfu : Tendsto (fun n => f (a n)) atTop (𝓝 (f u)) := (hf.tendsto u).comp hu
  have hfx : Tendsto (fun n => f (a n)) atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) hnear
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  exact ⟨u, hmem, tendsto_nhds_unique hfu hfx⟩

/-- Shrinking source diameters also make the recovered source point unique. -/
theorem source_limit_unique [Nonempty Y] (hcomplete : IsMetricComplete Y)
    (hbounded : ∀ x y : Y, dist x y ≤ 1) {x : X} {p : baire_space}
    (hx : ∀ n, x ∈ imageScheme hzero hf (seqPrefix p n)) :
    ∃! u : Y, (∀ n, u ∈ piece hzero hf (seqPrefix p n)) ∧ f u = x := by
  obtain ⟨u, hu, hfu⟩ := source_limit hzero hf hcomplete hbounded hx
  refine ⟨u, ⟨hu, hfu⟩, fun v hv => ?_⟩
  exact clopenSchemeMetricCore_branch_points_eq (sourceMetricCore hzero hf hbounded)
    (fun n => ⟨u, hu n⟩) hv.1 hu

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    Now show $A=\mathcal A(F_s)$. If $x=f(u)$ for some $u\in P$, then at each level choose the unique child containing $u$.
    This gives a branch $p\in\BaireSpace$ with $u\in P_{\restrict{p}{n}}$ for all $n$, hence
    $$x=f(u)\in F_{\restrict{p}{n}}\qquad(n\in\omega),$$
    so $x\in\mathcal A(F_s)$.
-/
/-- Follow the unique child containing a source point in one direction; in
the other, recover a source point by the preceding convergence construction. -/
theorem imageScheme_represents [Nonempty Y] (hcomplete : IsMetricComplete Y)
    (hbounded : ∀ x y : Y, dist x y ≤ 1) :
    suslinOperation (imageScheme hzero hf) = range f := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := mem_suslinOperation.mp hx
    obtain ⟨u, _, hu⟩ := source_limit hzero hf hcomplete hbounded hp
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    let H := sourceCore hzero hf
    apply mem_suslinOperation.mpr
    refine ⟨clopenSchemeCore_pointBranch H u, fun n => ?_⟩
    exact subset_closure ⟨u, clopenSchemeCore_pointBranch_point_mem H u n, rfl⟩

end
end RegularSuslin

open Set TopologicalSpace Topology MeasureTheory

/-- The empty scheme handles the empty analytic set; otherwise use the continuous
Baire-space parametrization and the recursive source partitions. -/
theorem analyticSet_exists_regular_suslinScheme {X : Type*} [MetricSpace X]
    (hbounded : ∀ x y : X, dist x y ≤ 1) {A : Set X} (hA : AnalyticSet A) :
    ∃ F : finseq ℕ → Set X, IsRegularSuslinScheme F ∧ suslinOperation F = A := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · refine ⟨fun _ => ∅, ?_, ?_⟩
    · refine ⟨fun _ _ => subset_rfl, fun _ => isClosed_empty, fun _ => ?_⟩
      simp
    · ext x
      simp [mem_suslinOperation]
  · let : MetricSpace baire_space := PiNat.metricSpaceNatNat
    have hb : ∀ x y : baire_space, dist x y ≤ 1 := by
      intro x y
      change @dist (sequence_metric_space ℕ) _ x y ≤ 1
      rw [← seqMetric_eq_sequenceMetricSpace_dist]
      exact seqMetric_le_one x y
    refine ⟨RegularSuslin.imageScheme baire_space_zero_dimensional hf,
      RegularSuslin.imageScheme_regular baire_space_zero_dimensional hf hbounded, ?_⟩
    exact RegularSuslin.imageScheme_represents baire_space_zero_dimensional hf
      ((isMetricComplete_iff_completeSpace baire_space).mpr inferInstance) hb

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    For (1) $\Rightarrow$ (3), the definition of analytic and the universal continuous-surjection theorem of
    §{sec:universal-continuous-surjection} give a closed set $P\IncludedIn\BaireSpace$ and a continuous map $f:P\to X$ with
    $A=f(P)$. For $A=\emptyset$, take $P=\emptyset$; otherwise one may take $P=\BaireSpace$. Fix a complete compatible
    metric $d$ on $X$ bounded by $1$, using the bounded-metric construction of §{sec:polish-proof-tools}.
-/
/-- A complete bounded compatible metric and a regular representing scheme are
chosen together. No effectiveness of the choices is asserted. -/
theorem analyticSet_exists_compatible_regular_suslinScheme {X : Type*}
    [t : TopologicalSpace X] [PolishSpace X] {A : Set X} (hA : AnalyticSet A) :
    ∃ d : MetricSpace X, d.toUniformSpace.toTopologicalSpace = t ∧
      @IsMetricComplete X d ∧ (∀ x y : X, @dist X d.toDist x y ≤ 1) ∧
      ∃ F : finseq ℕ → Set X, @IsRegularSuslinScheme X d F ∧ suslinOperation F = A := by
  let := upgradeIsCompletelyMetrizable X
  obtain ⟨d, ht, hc, _, hb⟩ := complete_compatible_metric_bounded_by_one X
    ((isMetricComplete_iff_completeSpace X).mpr inferInstance)
  refine ⟨d, ht, hc, hb, ?_⟩
  have hA' : @AnalyticSet X d.toUniformSpace.toTopologicalSpace A := by
    rw [ht]
    exact hA
  exact @analyticSet_exists_regular_suslinScheme X d hb A hA'

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    \begin{proof}[Proof] The implication (3) $\Rightarrow$ (2) is immediate, and (2) $\Rightarrow$ (1) is the proposition
    that closed schemes produce analytic sets.
-/
/-- The closed-scheme and regular-scheme descriptions recover exactly the analytic sets. -/
theorem analyticSet_iff_closed_suslinScheme {X : Type*} [TopologicalSpace X] [PolishSpace X]
    (A : Set X) : AnalyticSet A ↔
      ∃ F : finseq ℕ → Set X, (∀ s, IsClosed (F s)) ∧ suslinOperation F = A := by
  constructor
  · intro hA
    obtain ⟨d, ht, _, _, F, hF, heq⟩ := analyticSet_exists_compatible_regular_suslinScheme hA
    refine ⟨F, ?_, heq⟩
    have hclosed : ∀ s, @IsClosed X d.toUniformSpace.toTopologicalSpace (F s) := hF.2.1
    rwa [ht] at hclosed
  · rintro ⟨F, hF, rfl⟩
    exact analyticSet_suslinOperation_of_isClosed hF

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: statement
  kind: theorem
  title: Suslin-scheme representation
-/
/-- Full regular-scheme equivalence, with compatibility and completeness of the
bounded metric included in the statement. -/
theorem analyticSet_iff_compatible_regular_suslinScheme {X : Type*}
    [t : TopologicalSpace X] [PolishSpace X] (A : Set X) :
    AnalyticSet A ↔ ∃ d : MetricSpace X, d.toUniformSpace.toTopologicalSpace = t ∧
      @IsMetricComplete X d ∧ (∀ x y : X, @dist X d.toDist x y ≤ 1) ∧
      ∃ F : finseq ℕ → Set X, @IsRegularSuslinScheme X d F ∧ suslinOperation F = A := by
  constructor
  · exact analyticSet_exists_compatible_regular_suslinScheme
  · rintro ⟨d, ht, _, _, F, hF, heq⟩
    apply (analyticSet_iff_closed_suslinScheme A).mpr
    refine ⟨F, ?_, heq⟩
    have hclosed : ∀ s, @IsClosed X d.toUniformSpace.toTopologicalSpace (F s) := hF.2.1
    rwa [ht] at hclosed

end PolishSpaceBook
