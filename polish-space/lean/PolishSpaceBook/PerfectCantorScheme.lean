module

public import PolishSpaceBook.CantorBaireSpace

@[expose] public section

/-! # The open-ball Cantor scheme for the perfect set theorem

Children are open balls with disjoint closures inside their parent. Their
closure diameters tend to zero. Branch samples are Cauchy, and their limits
give the continuous injection written in Chapter 6.
-/
namespace PolishSpaceBook.PerfectCantorScheme
open Set Metric Filter TopologicalSpace
open scoped Topology

variable {X : Type*} [MetricSpace X]

/-- The closure of a ball retains the same two-radius distance bound. -/
theorem closure_ball_dist_le {c x y : X} {r : ℝ}
    (hx : x ∈ closure (ball c r)) (hy : y ∈ closure (ball c r)) :
    dist x y ≤ 2 * r := by
  have hx' := mem_closedBall.mp (closure_ball_subset_closedBall hx)
  have hy' := mem_closedBall.mp (closure_ball_subset_closedBall hy)
  have h := dist_triangle x c y
  rw [dist_comm c y] at h
  linarith

/-- A single common radius simultaneously controls containment, separation and diameter. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    Choose $r_0,r_1>0$ with $\Ball{x_i}{r_i}\IncludedIn U_s$ for $i=0,1$, and set
    $$\epsilon:=\min\left\{\frac{r_0}{2},\frac{r_1}{2},\frac{d(x_0,x_1)}{3},2^{-(|s|+2)}\right\}>0.$$
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Suppose $U_s$ has been chosen.
    Since $U_s$ is nonempty open and $X$ has no isolated points, choose distinct points $x_0,x_1 \in U_s$.
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    The closures of the open balls
    $$\Closure{\Ball{x_0}{\epsilon}},\qquad \Closure{\Ball{x_1}{\epsilon}}$$
    lie in $U_s$, since $\epsilon<r_i$. They are disjoint, since $2\epsilon<d(x_0,x_1)$.
-/
theorem split_balls [PerfectSpace X] {U : Set X} (hU : IsOpen U) (hne : U.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c₀ c₁ : X, ∃ r : ℝ, 0 < r ∧ c₀ ∈ U ∧ c₁ ∈ U ∧
      closure (ball c₀ r) ⊆ U ∧ closure (ball c₁ r) ⊆ U ∧
      Disjoint (closure (ball c₀ r)) (closure (ball c₁ r)) ∧ 2 * r ≤ δ := by
  obtain ⟨c₀, hc₀⟩ := hne
  obtain ⟨c₁, ⟨hc₁, _⟩, hne₁⟩ :=
    preperfect_iff_nhds.mp hU.preperfect c₀ hc₀ U (hU.mem_nhds hc₀)
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp hU c₀ hc₀
  obtain ⟨r₁, hr₁, hball₁⟩ := Metric.isOpen_iff.mp hU c₁ hc₁
  let r := min (min (r₀ / 2) (r₁ / 2)) (min (dist c₀ c₁ / 3) (δ / 2))
  have hd : 0 < dist c₀ c₁ := dist_pos.mpr hne₁.symm
  have hr : 0 < r := by dsimp [r]; positivity
  have h₀ : r ≤ r₀ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have h₁ : r ≤ r₁ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hsep : r ≤ dist c₀ c₁ / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hsize : r ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c₀, c₁, r, hr, hc₀, hc₁, ?_, ?_, ?_, by linarith⟩
  · intro x hx
    apply hball₀
    have hx' := mem_closedBall.mp (closure_ball_subset_closedBall hx)
    exact mem_ball.mpr (by linarith)
  · intro x hx
    apply hball₁
    have hx' := mem_closedBall.mp (closure_ball_subset_closedBall hx)
    exact mem_ball.mpr (by linarith)
  · apply Set.disjoint_left.mpr
    intro x hx₀ hx₁
    have hx₀' := mem_closedBall.mp (closure_ball_subset_closedBall hx₀)
    have hx₁' := mem_closedBall.mp (closure_ball_subset_closedBall hx₁)
    have ht := dist_triangle c₀ x c₁
    rw [dist_comm c₀ x] at ht
    linarith

/-- Nonempty open nodes, before a diameter bound is imposed. -/
structure Node (X : Type*) [TopologicalSpace X] where
  carrier : Set X
  isOpen : IsOpen carrier
  nonempty : carrier.Nonempty

/-- A perfect subset has no isolated points in its subspace topology. -/
theorem perfect_subtype {C : Set X} (hC : Perfect C) : PerfectSpace C := by
  constructor
  rw [preperfect_iff_nhds]
  intro x _ V hV
  obtain ⟨W, hW, hWV⟩ := (mem_nhds_subtype C x V).mp hV
  obtain ⟨y, ⟨hyW, hyC⟩, hyx⟩ :=
    preperfect_iff_nhds.mp hC.acc x.val x.property W hW
  refine ⟨⟨y, hyC⟩, ⟨hWV hyW, mem_univ _⟩, ?_⟩
  exact fun h => hyx (congrArg Subtype.val h)

variable [PerfectSpace X]

noncomputable def centers (N : Node X) (n : ℕ) : X × X × ℝ :=
  let h := split_balls N.isOpen N.nonempty (pow_pos (by norm_num : 0 < (1 / 2 : ℝ)) (n + 1))
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose⟩

theorem centers_spec (N : Node X) (n : ℕ) :
    let c := centers N n
    0 < c.2.2 ∧ closure (ball c.1 c.2.2) ⊆ N.carrier ∧
      closure (ball c.2.1 c.2.2) ⊆ N.carrier ∧
      Disjoint (closure (ball c.1 c.2.2)) (closure (ball c.2.1 c.2.2)) ∧
      2 * c.2.2 ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  dsimp [centers]
  have h := (split_balls N.isOpen N.nonempty
    (pow_pos (by norm_num : 0 < (1 / 2 : ℝ)) (n + 1))).choose_spec.choose_spec.choose_spec
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

noncomputable def child (N : Node X) (n : ℕ) (i : Bool) : Node X where
  carrier := ball (if i then (centers N n).2.1 else (centers N n).1) (centers N n).2.2
  isOpen := isOpen_ball
  nonempty := ⟨_, mem_ball_self (centers_spec N n).1⟩

theorem child_subset (N : Node X) (n : ℕ) (i : Bool) :
    closure (child N n i).carrier ⊆ N.carrier := by
  cases i
  · exact (centers_spec N n).2.1
  · exact (centers_spec N n).2.2.1

theorem child_disjoint (N : Node X) (n : ℕ) :
    Disjoint (closure (child N n false).carrier) (closure (child N n true).carrier) :=
  (centers_spec N n).2.2.2.1

theorem child_dist (N : Node X) (n : ℕ) (i : Bool) {x y : X}
    (hx : x ∈ closure (child N n i).carrier) (hy : y ∈ closure (child N n i).carrier) :
    dist x y ≤ (1 / 2 : ℝ) ^ (n + 1) :=
  (closure_ball_dist_le hx hy).trans (centers_spec N n).2.2.2.2

variable [Nonempty X]

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    Start with an open ball $U_\emptyset$ of radius $1/2$ around any point of $X$.
    Its closure has diameter at most $1$.
-/
noncomputable def root : Node X where
  carrier := ball (Classical.arbitrary X) (1 / 2)
  isOpen := isOpen_ball
  nonempty := ⟨_, mem_ball_self (by norm_num)⟩

/-- Recursion appends bits, matching finite prefixes in the book. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    Define
    $$U_{s \concat (i)} := \Ball{x_i}{\epsilon} \qquad (i=0,1).$$
    This completes the induction. In particular, the diameter bound holds for the closures as well.
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    Let $(X,d)$ be a nonempty perfect Polish space, with $d$ complete and compatible. We build a
    \termdefine{Cantor scheme} of nonempty open sets $\{U_s : s \in \finseq{2}\}$ satisfying:
-/
noncomputable def node (s : List Bool) : Node X :=
  s.reverseRecOn root (fun t i N => child N t.length i)

theorem node_nil : (node ([] : List Bool) : Node X) = root := by simp [node]

theorem node_append (s : List Bool) (i : Bool) :
    (node (s ++ [i]) : Node X) = child (node s) s.length i := by simp [node]

def U (s : List Bool) : Set X := (node s).carrier

theorem U_nonempty (s : List Bool) : (U s : Set X).Nonempty := (node s).nonempty

theorem U_open (s : List Bool) : IsOpen (U s : Set X) := (node s).isOpen

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    \item $\Closure{U_{s \concat (i)}} \IncludedIn U_s$ for $i \in 2$;
-/
theorem U_child_subset (s : List Bool) (i : Bool) :
    closure (U (s ++ [i]) : Set X) ⊆ U s := by
  unfold U
  rw [node_append]
  exact child_subset _ _ _

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    \item $\Closure{U_{s \concat (0)}} \cap \Closure{U_{s \concat (1)}} = \emptyset$;
-/
theorem U_child_disjoint (s : List Bool) :
    Disjoint (closure (U (s ++ [false]) : Set X)) (closure (U (s ++ [true]))) := by
  unfold U
  rw [node_append, node_append]
  exact child_disjoint _ _

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    Each closure has diameter at most $2\epsilon\le 2^{-(|s|+1)}$ by the triangle inequality.
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    \item $\MetricDiameter{d}{U_s} \le 2^{-|s|}$.
    \end{enumerate}
-/
theorem U_dist (s : List Bool) {x y : X}
    (hx : x ∈ closure (U s)) (hy : y ∈ closure (U s)) :
    dist x y ≤ (1 / 2 : ℝ) ^ s.length := by
  induction s using List.reverseRecOn with
  | nil =>
    simp only [U, node_nil, root] at hx hy
    have h := closure_ball_dist_le hx hy
    norm_num at h ⊢
    exact h
  | append_singleton s i ih =>
    simp only [U, node_append] at hx hy
    simpa using child_dist (node s) s.length i hx hy

/-- Closed sets along a branch are nested. -/
theorem branch_antitone (a : ℕ → Bool) :
    Antitone (fun n => closure (U (seqPrefix a n) : Set X)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [seqPrefix_succ_eq_concat]
  exact (U_child_subset _ _).trans subset_closure

noncomputable def sample (a : ℕ → Bool) (n : ℕ) : X :=
  (U_nonempty (X := X) (seqPrefix a n)).choose

theorem sample_mem (a : ℕ → Bool) (n : ℕ) :
    sample (X := X) a n ∈ closure (U (seqPrefix a n)) :=
  subset_closure (U_nonempty (seqPrefix a n)).choose_spec

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    For $m,n\ge N$, both points belong to $\Closure{U_{\restrict{a}{N}}}$, so
    $$d(x_m,x_n)\le 2^{-N}.$$
    Thus $\Sequence{x_n}{n\in\omega}$ is Cauchy and converges to some point $h(a) \in X$ by completeness.
-/
theorem sample_cauchy (a : ℕ → Bool) : CauchySeq (sample (X := X) a) := by
  refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => (1 / 2 : ℝ) ^ N) ?_ ?_
  · intro n m N hNn hNm
    have hn := branch_antitone (X := X) a hNn (sample_mem a n)
    have hm := branch_antitone (X := X) a hNm (sample_mem a m)
    simpa [seqPrefix_length] using U_dist (seqPrefix a N) hn hm
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

variable [CompleteSpace X]

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    Since each $\Closure{U_{\restrict{a}{n}}}$ is closed and eventually contains the tail of the sequence,
    $h(a)$ lies in every $\Closure{U_{\restrict{a}{n}}}$.
-/
theorem exists_branch_limit (a : ℕ → Bool) : ∃ x : X,
    Tendsto (sample a) atTop (𝓝 x) ∧ ∀ n, x ∈ closure (U (seqPrefix a n)) := by
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (sample_cauchy (X := X) a)
  refine ⟨x, hx, fun n => isClosed_closure.mem_of_tendsto hx ?_⟩
  exact (eventually_ge_atTop n).mono fun m hm => branch_antitone a hm (sample_mem a m)

noncomputable def point (a : ℕ → Bool) : X := (exists_branch_limit a).choose

theorem point_mem (a : ℕ → Bool) (n : ℕ) :
    point (X := X) a ∈ closure (U (seqPrefix a n)) :=
  (exists_branch_limit a).choose_spec.2 n

theorem sample_tendsto (a : ℕ → Bool) :
    Tendsto (sample (X := X) a) atTop (𝓝 (point a)) := (exists_branch_limit a).choose_spec.1

omit [CompleteSpace X] in
theorem branch_unique (a : ℕ → Bool) {x y : X}
    (hx : ∀ n, x ∈ closure (U (seqPrefix a n)))
    (hy : ∀ n, y ∈ closure (U (seqPrefix a n))) : x = y := by
  by_contra hne
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (dist_pos.mpr hne)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hle : dist x y ≤ (1 / 2 : ℝ) ^ n := by
    simpa [seqPrefix_length] using U_dist (seqPrefix a n) (hx n) (hy n)
  exact not_lt_of_ge hle hn

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    The intersection contains only this one point,
    because its diameter is bounded by $2^{-n}$ for every $n$. Thus $h(a)$ is uniquely determined by
    $$\{h(a)\}=\bigcap_{n \in \omega} \Closure{U_{\restrict{a}{n}}}.$$
-/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    For each $a \in \CantorSpace$, the closed sets
    $$\Closure{U_{\restrict{a}{0}}} \supseteq \Closure{U_{\restrict{a}{1}}} \supseteq \Closure{U_{\restrict{a}{2}}}
    \supseteq \cdots$$
    are nested, nonempty, and have diameters tending to $0$. Choose $x_n \in \Closure{U_{\restrict{a}{n}}}$.
-/
theorem branch_intersection (a : ℕ → Bool) :
    (⋂ n, closure (U (seqPrefix a n) : Set X)) = {point a} := by
  ext x
  constructor
  · intro hx
    exact branch_unique a (mem_iInter.mp hx) (point_mem a)
  · rintro rfl
    exact mem_iInter.mpr (point_mem a)

/-- Agreement on a prefix gives the quantitative continuity estimate. -/
theorem point_dist_of_prefix {a b : ℕ → Bool} {n : ℕ}
    (hprefix : seqPrefix a n = seqPrefix b n) :
    dist (point (X := X) a) (point b) ≤ (1 / 2 : ℝ) ^ n := by
  have ha := point_mem (X := X) a n
  rw [hprefix] at ha
  simpa [seqPrefix_length] using U_dist (seqPrefix b n) ha (point_mem b n)

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    It is continuous: if $a$ and $b$ agree on the first $n$ coordinates, then $h(a),h(b) \in \Closure{U_{\restrict{a}{n}}}$,
    whose diameter is at most $2^{-n}$. Consequently,
    $$d(h(a),h(b))\le 2^{-n}.$$
    Agreement on a long enough prefix therefore forces the images to be arbitrarily close.
-/
theorem continuous_point : Continuous (point (X := X)) := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hnhds := (isOpen_cyl (seqPrefix a n)).mem_nhds (mem_cyl_seqPrefix a n)
  refine Filter.mem_of_superset hnhds ?_
  intro b hb
  have hp : seqPrefix b n = seqPrefix a n := by
    simpa [seqPrefix_length] using seqPrefix_eq_of_mem_cyl hb
  exact (point_dist_of_prefix (X := X) hp).trans_lt hn

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: proof
  excerpt: |
    The map $h : \CantorSpace \to X$ is injective. If $a \ne b$, let $n$ be the first coordinate where they differ. Then
    $h(a)$ and $h(b)$ lie in the disjoint closed sets $\Closure{U_{\restrict{a}{n+1}}}$ and
    $\Closure{U_{\restrict{b}{n+1}}}$.
-/
theorem point_injective : Function.Injective (point (X := X)) := by
  intro a b heq
  by_contra hne
  let n := firstDiffIndex a b
  have hdiff : a n ≠ b n := firstDiffIndex_spec hne
  have hagree := agreeOnPrefix_of_le_firstDiffIndex hne (le_refl n)
  have hp : seqPrefix a n = seqPrefix b n := by
    unfold seqPrefix
    rw [List.ofFn_inj]
    funext i
    exact hagree i i.2
  have ha := point_mem (X := X) a (n + 1)
  have hb := point_mem (X := X) b (n + 1)
  rw [seqPrefix_succ_eq_concat, heq] at ha
  rw [seqPrefix_succ_eq_concat, ← hp] at hb
  have hdisj : Disjoint (closure (U (seqPrefix a n ++ [a n]) : Set X))
      (closure (U (seqPrefix a n ++ [b n]))) := by
    cases ha' : a n <;> cases hb' : b n
    · exact False.elim (hdiff (ha'.trans hb'.symm))
    · exact U_child_disjoint _
    · exact (U_child_disjoint _).symm
    · exact False.elim (hdiff (ha'.trans hb'.symm))
  exact Set.disjoint_left.mp hdisj ha hb

theorem point_closedEmbedding : Topology.IsClosedEmbedding (point (X := X)) :=
  continuous_point.isClosedEmbedding point_injective

omit [PerfectSpace X] [Nonempty X] in
/-- Apply the same open-ball construction in the closed perfect subspace. -/
theorem exists_injection_perfect {C : Set X} (hC : Perfect C) (hne : C.Nonempty) :
    ∃ f : (ℕ → Bool) → X, range f ⊆ C ∧ Continuous f ∧ Function.Injective f := by
  let : PerfectSpace C := perfect_subtype hC
  let : Nonempty C := hne.to_subtype
  let : CompleteSpace C := hC.closed.isComplete.completeSpace_coe
  refine ⟨fun a => (point (X := C) a).val, ?_,
    continuous_subtype_val.comp continuous_point, Subtype.val_injective.comp point_injective⟩
  rintro _ ⟨a, rfl⟩
  exact (point (X := C) a).property

end PolishSpaceBook.PerfectCantorScheme
