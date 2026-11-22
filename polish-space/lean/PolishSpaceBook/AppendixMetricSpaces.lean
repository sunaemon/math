module

/-
The explicit dyadic refinement proof below is adapted from
Mathlib/Topology/EMetricSpace/Paracompact.lean.
Copyright (c) 2021 Yury Kudryashov. Released under Apache 2.0 license.
-/
public import PolishSpaceBook.PolishSpaces
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# Appendix: metric spaces

The dyadic open-ball construction below supplies the book's paracompactness
proof, including the exclusion of later levels and uniqueness at each earlier
level. The star-refinement construction is treated separately below.
-/

namespace PolishSpaceBook

open ENNReal Topology Set Metric

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: statement
  kind: theorem
  title: Metric paracompactness
-/
/-- The explicit recursive dyadic refinement of an arbitrary open cover. -/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: proof
  excerpt: |
    For each $m<N$, at most one $D_{m,j}$ meets $B$.
    Suppose two distinct labels $j<\ell$ occurred, with points $y,z$ in the respective intersections and defining centers
    $y',z'$.
    Then
    $$d(z',y')<2(r_m+r_N)\le 2(r_m+r_{m+1})=3r_m.$$
    Consequently $z'\in U_j$, contradicting the minimality of $i(z')=\ell$.
    The neighborhood $B$ therefore meets at most $N$ members of the refinement. This proves local finiteness.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: proof
  excerpt: |
    To prove local finiteness, choose $x\in D_{n,i}$ and then $k$ with $\Ball{x}{r_k}\IncludedIn D_{n,i}$.
    Put $N=n+k+1$ and $B=\Ball{x}{r_N}$. No $D_{m,j}$ with $m\ge N$ meets $B$.
    Indeed, if $y$ belonged to their intersection, its defining center $z$ would satisfy
    $$d(z,x)<r_m+r_N\le 2r_{k+1}=r_k.$$
    This puts $z$ in the earlier set $D_{n,i}$, contrary to its eligibility at level $m$.
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: proof
  excerpt: |
    \begin{proof}
    Let $(U_i)_{i\in I}$ be an open cover of $(X,d)$, and well-order $I$.
    For each $x$, let $i(x)$ be the least index with $x\in U_{i(x)}$, and put $r_n=2^{-n}$ for $n\in\NN$.
    Recursively define the open sets
    $$D_{n,i}=\bigcup\left\{\Ball{x}{r_n}:i(x)=i,\quad
    \Ball{x}{3r_n}\IncludedIn U_i,\quad
    x\notin\bigcup_{m<n}\bigcup_{j\in I}D_{m,j}\right\}.$$
    Thus centers at a new level must avoid all earlier sets. Every $D_{n,i}$ is contained in $U_i$.
    These sets cover $X$: given $x$, choose $n$ so large that $\Ball{x}{3r_n}\IncludedIn U_{i(x)}$.
    Either an earlier set already contains $x$, or $x$ is an allowed center at level $n$ and belongs to $D_{n,i(x)}$.
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    An open cover $\mathcal V$ is an \termdefine{open refinement} of an open cover $\mathcal U$ if each member of
    $\mathcal V$ is contained in some member of $\mathcal U$. Both families must cover the whole space.
-/
theorem metric_locallyFinite_open_refinement {α : Type u} [PseudoEMetricSpace α]
    (ι : Type u) (s : ι → Set α) (ho : ∀ i, IsOpen (s i))
    (hcov : ⋃ i, s i = univ) :
    ∃ (β : Type u) (t : β → Set α),
      (∀ b, IsOpen (t b)) ∧ (⋃ b, t b = univ) ∧ LocallyFinite t ∧
        ∀ b, ∃ i, t b ⊆ s i := by
  /- We start with trivial observations about `1 / 2 ^ k`. Here and below we use `1 / 2 ^ k` in
    the comments and `2⁻¹ ^ k` in the code. -/
  have pow_pos : ∀ k : ℕ, (0 : ℝ≥0∞) < 2⁻¹ ^ k := fun k =>
    ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _
  have hpow_le : ∀ {m n : ℕ}, m ≤ n → (2⁻¹ : ℝ≥0∞) ^ n ≤ 2⁻¹ ^ m := @fun m n h =>
    pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 ENNReal.one_lt_two.le) h
  have h2pow : ∀ n : ℕ, 2 * (2⁻¹ : ℝ≥0∞) ^ (n + 1) = 2⁻¹ ^ n := fun n => by
    simp [pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ofNat_ne_top]
  -- Consider an open covering `S : Set (Set α)`
  simp only [iUnion_eq_univ_iff] at hcov
  -- choose a well-founded order on `S`
  obtain ⟨_, wf⟩ := exists_wellFoundedLT ι
  -- Let `ind x` be the minimal index `s : S` such that `x ∈ s`.
  let ind (x : α) : ι := wellFounded_lt.min { i : ι | x ∈ s i } (hcov x)
  have mem_ind (x) : x ∈ s (ind x) := wellFounded_lt.min_mem _ (hcov x)
  have notMem_of_lt_ind {x i} (hlt : i < ind x) (hxi : x ∈ s i) : False :=
    wellFounded_lt.not_lt_min {i | x ∈ s i} hxi hlt
  /- The refinement `D : ℕ → ι → Set α` is defined recursively. For each `n` and `i`, `D n i`
    is the union of balls `ball x (1 / 2 ^ n)` over all points `x` such that

    * `ind x = i`;
    * `x` does not belong to any `D m j`, `m < n`;
    * `ball x (3 / 2 ^ n) ⊆ s i`;

    We define this sequence using `Nat.strongRec`, then restate it as `Dn` and `memD`.
  -/
  set D : ℕ → ι → Set α :=
    Nat.strongRec fun n D' i ↦
      ⋃ (x : α) (hxs : ind x = i) (hb : eball x (3 * 2⁻¹ ^ n) ⊆ s i) (hlt :
        ∀ (m : ℕ) (H : m < n), ∀ (j : ι), x ∉ D' m H j), eball x (2⁻¹ ^ n) with hD
  have Dn (n i) : D n i = ⋃ (x : α) (hxs : ind x = i) (hb : eball x (3 * 2⁻¹ ^ n) ⊆ s i)
      (hlt : ∀ m < n, ∀ (j : ι), x ∉ D m j), eball x (2⁻¹ ^ n) := by
    simp only [hD]
    rw [Nat.strongRec_eq]
  have memD {n i y} :
      y ∈ D n i ↔ ∃ x : α, ind x = i ∧ eball x (3 * 2⁻¹ ^ n) ⊆ s i ∧
        (∀ m < n, ∀ (j : ι), x ∉ D m j) ∧ edist y x < 2⁻¹ ^ n := by
    rw [Dn n i]
    simp only [mem_iUnion, mem_eball, exists_prop]
  -- The sets `D n i` cover the whole space. Indeed, for each `x` we can choose `n` such that
  -- `ball x (3 / 2 ^ n) ⊆ s (ind x)`, then either `x ∈ D n i`, or `x ∈ D m i` for some `m < n`.
  have Dcov (x) : ∃ n i, x ∈ D n i := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, eball x (3 * 2⁻¹ ^ n) ⊆ s (ind x) := by
      -- This proof takes 5 lines because we can't import `specific_limits` here
      rcases EMetric.isOpen_iff.1 (ho <| ind x) x (mem_ind x) with ⟨ε, ε0, hε⟩
      have : 0 < ε / 3 := ENNReal.div_pos_iff.2 ⟨ε0.lt.ne', ENNReal.coe_ne_top⟩
      rcases ENNReal.exists_inv_two_pow_lt this.ne' with ⟨n, hn⟩
      refine ⟨n, Subset.trans (eball_subset_eball ?_) hε⟩
      simpa only [div_eq_mul_inv, mul_comm] using (ENNReal.mul_lt_of_lt_div hn).le
    by_contra! h
    apply h n (ind x)
    exact memD.2 ⟨x, rfl, hn, fun _ _ _ => h _ _, mem_eball_self (pow_pos _)⟩
  -- Each `D n i` is a union of open balls, hence it is an open set
  have Dopen (n i) : IsOpen (D n i) := by
    rw [Dn]
    iterate 4 refine isOpen_iUnion fun _ => ?_
    exact isOpen_eball
  -- the covering `D n i` is a refinement of the original covering: `D n i ⊆ s i`
  have HDS (n i) : D n i ⊆ s i := fun x => by
    rw [memD]
    rintro ⟨y, rfl, hsub, -, hyx⟩
    refine hsub (hyx.trans_le <| le_mul_of_one_le_left' ?_)
    norm_num1
  -- Let us show the rest of the properties. Since the definition expects a family indexed
  -- by a single parameter, we use `ℕ × ι` as the domain.
  refine ⟨ℕ × ι, fun ni => D ni.1 ni.2, fun _ => Dopen _ _, ?_, ?_, fun ni => ⟨ni.2, HDS _ _⟩⟩
  -- The sets `D n i` cover the whole space as we proved earlier
  · refine iUnion_eq_univ_iff.2 fun x ↦ ?_
    rcases Dcov x with ⟨n, i, h⟩
    exact ⟨⟨n, i⟩, h⟩
  /- Let us prove that the covering `D n i` is locally finite. Take a point `x` and choose
    `n`, `i` so that `x ∈ D n i`. Since `D n i` is an open set, we can choose `k` so that
    `B = ball x (1 / 2 ^ (n + k + 1)) ⊆ D n i`. -/
  · intro x
    rcases Dcov x with ⟨n, i, hn⟩
    have : D n i ∈ 𝓝 x := IsOpen.mem_nhds (Dopen _ _) hn
    rcases (nhds_basis_uniformity uniformity_basis_edist_inv_two_pow).mem_iff.1 this with
      ⟨k, -, hsub : eball x (2⁻¹ ^ k) ⊆ D n i⟩
    set B := eball x (2⁻¹ ^ (n + k + 1))
    refine ⟨B, eball_mem_nhds _ (pow_pos _), ?_⟩
    -- The sets `D m i`, `m > n + k`, are disjoint with `B`
    have Hgt (m) (hm : n + k + 1 ≤ m) (i : ι) : Disjoint (D m i) B := by
      rw [disjoint_iff_inf_le]
      rintro y ⟨hym, hyx⟩
      rcases memD.1 hym with ⟨z, rfl, _hzi, H, hz⟩
      have : z ∉ eball x (2⁻¹ ^ k) := fun hz' => H n (by lia) i (hsub hz')
      apply this
      calc
        edist z x ≤ edist y z + edist y x := edist_triangle_left _ _ _
        _ < 2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1) := ENNReal.add_lt_add hz hyx
        _ ≤ 2⁻¹ ^ (k + 1) + 2⁻¹ ^ (k + 1) :=
          (add_le_add (hpow_le <| by lia) (hpow_le <| by lia))
        _ = 2⁻¹ ^ k := by rw [← two_mul, h2pow]
    -- For each `m ≤ n + k` there is at most one `j` such that `D m j ∩ B` is nonempty.
    have Hle (m) (hm : m ≤ n + k) : Set.Subsingleton { j | (D m j ∩ B).Nonempty } := by
      rintro j₁ ⟨y, hyD, hyB⟩ j₂ ⟨z, hzD, hzB⟩
      by_contra h' : j₁ ≠ j₂
      wlog h : j₁ < j₂ generalizing j₁ j₂ y z
      · exact this z hzD hzB y hyD hyB h'.symm (h'.lt_or_gt.resolve_left h)
      rcases memD.1 hyD with ⟨y', rfl, hsuby, -, hdisty⟩
      rcases memD.1 hzD with ⟨z', rfl, -, -, hdistz⟩
      suffices edist z' y' < 3 * 2⁻¹ ^ m from notMem_of_lt_ind h (hsuby this)
      calc
        edist z' y' ≤ edist z' x + edist x y' := edist_triangle _ _ _
        _ ≤ edist z z' + edist z x + (edist y x + edist y y') :=
          (add_le_add (edist_triangle_left _ _ _) (edist_triangle_left _ _ _))
        _ < 2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1) + (2⁻¹ ^ (n + k + 1) + 2⁻¹ ^ m) := by
          apply_rules [ENNReal.add_lt_add]
        _ = 2 * (2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1)) := by simp only [two_mul, add_comm]
        _ ≤ 2 * (2⁻¹ ^ m + 2⁻¹ ^ (m + 1)) := by
          gcongr 2 * (_ + ?_); exact hpow_le (add_le_add hm le_rfl)
        _ = 3 * 2⁻¹ ^ m := by
          rw [mul_add, h2pow, ← two_add_one_eq_three, add_mul, one_mul]
    -- Finally, we glue `Hgt` and `Hle`
    have : (⋃ (m ≤ n + k) (i ∈ { i : ι | (D m i ∩ B).Nonempty }), {(m, i)}).Finite :=
      (finite_le_nat _).biUnion' fun i hi =>
        (Hle i hi).finite.biUnion' fun _ _ => finite_singleton _
    refine this.subset fun I hI => ?_
    simp only [mem_iUnion]
    refine ⟨I.1, ?_, I.2, hI, rfl⟩
    exact not_lt.1 fun hlt => (Hgt I.1 hlt I.2).le_bot hI.choose_spec

open Set Metric Topology
/-- The numerical estimate behind the star-refinement construction. -/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: proof
  excerpt: |
    Apply §{sec:appendix-metric-paracompactness} to the cover $\{\Ball{x}{\delta(x)/16}:x\in X\}$.
    Let $\mathcal V$ be a locally finite open refinement of this cover. For each $V\in\mathcal V$, choose $c(V)$ with
    $V\IncludedIn\Ball{c(V)}{\delta(c(V))/16}$.
    If $V'\cap V\ne\emptyset$, put $a=\delta(c(V))$, $b=\delta(c(V'))$, and $t=d(c(V'),c(V))$.
    An intersection point and the Lipschitz estimate give
    $$t<(a+b)/16,\qquad b\le a+t.$$
    Hence $b<17a/15<2a$. Every $y\in V'$ consequently satisfies
    $$d(y,c(V))<b/16+t<(a+2b)/16<5a/16<a.$$
    It follows that $\operatorname{St}(V,\mathcal V)\IncludedIn\Ball{c(V)}{\delta(c(V))}$, and this ball is contained in a
    member of $\mathcal U$.
    Thus $\mathcal V$ is the required star-refinement.
    \end{proof}
-/
theorem small_ball_star_subset {α : Type*} [PseudoMetricSpace α]
    (δ : α → ℝ) (hpos : ∀ x, 0 < δ x) (hlip : LipschitzWith 1 δ)
    {c c' : α} {V V' : Set α}
    (hV : V ⊆ ball c (δ c / 16)) (hV' : V' ⊆ ball c' (δ c' / 16))
    (hint : (V' ∩ V).Nonempty) : V' ⊆ ball c (δ c) := by
  obtain ⟨z, hz', hz⟩ := hint
  have hz1 := hV hz
  have hz2 := hV' hz'
  rw [mem_ball] at hz1 hz2
  have ht : dist c' c < (δ c + δ c') / 16 := by
    have := dist_triangle_left c' c z
    linarith
  have hb : δ c' ≤ δ c + dist c' c := by
    have h := hlip.dist_le_mul c' c
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
    have := (abs_le.mp h).2
    linarith
  intro y hy
  have hy' := hV' hy
  rw [mem_ball] at hy' ⊢
  have := dist_triangle y c' c
  have := hpos c
  linarith

/-- A positive Lipschitz subordinate radius produces the required refinement. -/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: proof
  excerpt: |
    Apply §{sec:appendix-metric-paracompactness} to the cover $\{\Ball{x}{\delta(x)/16}:x\in X\}$.
    Let $\mathcal V$ be a locally finite open refinement of this cover. For each $V\in\mathcal V$, choose $c(V)$ with
    $V\IncludedIn\Ball{c(V)}{\delta(c(V))/16}$.
    If $V'\cap V\ne\emptyset$, put $a=\delta(c(V))$, $b=\delta(c(V'))$, and $t=d(c(V'),c(V))$.
    An intersection point and the Lipschitz estimate give
    $$t<(a+b)/16,\qquad b\le a+t.$$
    Hence $b<17a/15<2a$. Every $y\in V'$ consequently satisfies
    $$d(y,c(V))<b/16+t<(a+2b)/16<5a/16<a.$$
    It follows that $\operatorname{St}(V,\mathcal V)\IncludedIn\Ball{c(V)}{\delta(c(V))}$, and this ball is contained in a
    member of $\mathcal U$.
    Thus $\mathcal V$ is the required star-refinement.
    \end{proof}
-/
theorem metric_star_refinement_of_radius {α : Type u} [PseudoMetricSpace α]
    {ι : Type u} (s : ι → Set α) (δ : α → ℝ)
    (hpos : ∀ x, 0 < δ x) (hlip : LipschitzWith 1 δ)
    (hsub : ∀ x, ∃ i, ball x (δ x) ⊆ s i) :
    ∃ (β : Type u) (t : β → Set α),
      (∀ b, IsOpen (t b)) ∧ (⋃ b, t b = univ) ∧ LocallyFinite t ∧
        ∀ b, ∃ i, ∀ b', (t b' ∩ t b).Nonempty → t b' ⊆ s i := by
  have hcov : ⋃ x : α, ball x (δ x / 16) = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    exact ⟨x, mem_ball_self (div_pos (hpos x) (by norm_num))⟩
  obtain ⟨β, t, ho, hc, hf, hr⟩ := metric_locallyFinite_open_refinement
    α (fun x => ball x (δ x / 16)) (fun _ => isOpen_ball) hcov
  choose c hct using hr
  refine ⟨β, t, ho, hc, hf, ?_⟩
  intro b
  obtain ⟨i, hi⟩ := hsub (c b)
  refine ⟨i, fun b' hint => ?_⟩
  exact (small_ball_star_subset δ hpos hlip (hct b) (hct b') hint).trans hi
/-- The capped-distance supremum supplies a positive subordinate radius. -/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: proof
  excerpt: |
    \begin{proof}
    The case of the empty space is immediate. If $X\in\mathcal U$, the one-element cover $\{X\}$ suffices, so assume every
    member of
    $\mathcal U$ is proper.
    Put
    $$\rho_U(x)=\min\{1,d(x,\SetDifference{X}{U})\},\qquad
    \rho(x)=\sup_{U\in\mathcal U}\rho_U(x),\qquad \delta(x)=\rho(x)/2.$$
    Each distance is now to a nonempty closed set. The functions $\rho_U$ take values in $[0,1]$ and are $1$-Lipschitz.
    Taking their supremum preserves the Lipschitz bound: for every $U$,
    $$\rho_U(x)\le\rho_U(y)+d(x,y)\le\rho(y)+d(x,y),$$
    and then interchange $x,y$. Since the cover is open, $\rho(x)>0$.
    Choose $U$ with $\rho_U(x)>\delta(x)$; then $\Ball{x}{\delta(x)}\IncludedIn U$.
    Thus $\delta$ is positive and $1$-Lipschitz, and each of its radius balls refines the original cover.
-/
theorem metric_subordinate_lipschitz_radius {α : Type u} [PseudoMetricSpace α]
    {ι : Type u} [Nonempty ι] (s : ι → Set α) (ho : ∀ i, IsOpen (s i))
    (hc : ∀ x, ∃ i, x ∈ s i) (hproper : ∀ i, (s i)ᶜ.Nonempty) :
    ∃ δ : α → ℝ, (∀ x, 0 < δ x) ∧ LipschitzWith 1 δ ∧
      ∀ x, ∃ i, ball x (δ x) ⊆ s i := by
  let r : ι → α → ℝ := fun i x => min 1 (infDist x (s i)ᶜ)
  let R : α → ℝ := fun x => ⨆ i, r i x
  have hr : ∀ i, LipschitzWith 1 (r i) := by
    intro i
    simpa only [max_eq_right zero_le_one] using
      (LipschitzWith.const (1 : ℝ)).min (lipschitz_infDist_pt (s i)ᶜ)
  have hbounded (x) : BddAbove (range (fun i => r i x)) :=
    ⟨1, by rintro _ ⟨i, rfl⟩; exact min_le_left _ _⟩
  have hle (x y) : R x ≤ R y + dist x y := by
    apply ciSup_le
    intro i
    have h := (hr i).dist_le_mul x y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
    have h' := (abs_le.mp h).2
    have h'' := le_ciSup (hbounded y) i
    change r i y ≤ R y at h''
    linarith
  have hRpos (x) : 0 < R x := by
    obtain ⟨i, hi⟩ := hc x
    have hd : 0 < infDist x (s i)ᶜ := by
      apply (infDist_pos_iff_notMem_closure (hproper i)).mp
      rw [(ho i).isClosed_compl.closure_eq]
      simpa using hi
    exact lt_of_lt_of_le (lt_min zero_lt_one hd) (le_ciSup (hbounded x) i)
  refine ⟨fun x => R x / 2, fun x => div_pos (hRpos x) (by norm_num), ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, abs_le]
    have hxy := hle x y
    have hyx := hle y x
    rw [dist_comm y x] at hyx
    have := dist_nonneg (x := x) (y := y)
    constructor <;> linarith
  · intro x
    have hhalf : R x / 2 < R x := by linarith [hRpos x]
    obtain ⟨i, hi⟩ := (lt_ciSup_iff (hbounded x)).mp hhalf
    refine ⟨i, ?_⟩
    intro y hy
    by_contra hy'
    have hd := infDist_le_dist_of_mem (x := x) (show y ∈ (s i)ᶜ from hy')
    have hri : r i x ≤ infDist x (s i)ᶜ := min_le_right _ _
    rw [mem_ball, dist_comm] at hy
    linarith

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: statement
  kind: theorem
  title: Metric star-refinement
-/
/-- Locally finite open star-refinement, by the book's explicit radius argument. -/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  target: proof
  excerpt: |
    \begin{proof}
    The case of the empty space is immediate. If $X\in\mathcal U$, the one-element cover $\{X\}$ suffices, so assume every
    member of
    $\mathcal U$ is proper.
    Put
    $$\rho_U(x)=\min\{1,d(x,\SetDifference{X}{U})\},\qquad
    \rho(x)=\sup_{U\in\mathcal U}\rho_U(x),\qquad \delta(x)=\rho(x)/2.$$
    Each distance is now to a nonempty closed set. The functions $\rho_U$ take values in $[0,1]$ and are $1$-Lipschitz.
    Taking their supremum preserves the Lipschitz bound: for every $U$,
    $$\rho_U(x)\le\rho_U(y)+d(x,y)\le\rho(y)+d(x,y),$$
    and then interchange $x,y$. Since the cover is open, $\rho(x)>0$.
    Choose $U$ with $\rho_U(x)>\delta(x)$; then $\Ball{x}{\delta(x)}\IncludedIn U$.
    Thus $\delta$ is positive and $1$-Lipschitz, and each of its radius balls refines the original cover.
-/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    If $\mathcal V$ is an open cover and $V\in\mathcal V$, write
    $$\operatorname{St}(V,\mathcal V):=\bigcup\{V'\in\mathcal V:V'\cap V\ne\emptyset\}.$$
    An open cover $\mathcal V$ \termdefineas{star-refinement}{star-refines} an open cover $\mathcal U$ if for every
    $V\in\mathcal V$ there is $U\in\mathcal U$ such that $\operatorname{St}(V,\mathcal V)\IncludedIn U$.
-/
theorem metric_locallyFinite_open_star_refinement {α : Type u} [PseudoMetricSpace α]
    (ι : Type u) (s : ι → Set α) (ho : ∀ i, IsOpen (s i))
    (hcov : ⋃ i, s i = univ) :
    ∃ (β : Type u) (t : β → Set α),
      (∀ b, IsOpen (t b)) ∧ (⋃ b, t b = univ) ∧ LocallyFinite t ∧
        ∀ b, ∃ i, ∀ b', (t b' ∩ t b).Nonempty → t b' ⊆ s i := by
  classical
  by_cases hα : Nonempty α
  · let := hα
    have hc := iUnion_eq_univ_iff.mp hcov
    obtain ⟨i₀, _⟩ := hc (Classical.arbitrary α)
    let : Nonempty ι := ⟨i₀⟩
    by_cases hfull : ∃ i, s i = univ
    · obtain ⟨i, hi⟩ := hfull
      refine ⟨PUnit, fun _ => univ, fun _ => isOpen_univ, ?_,
        locallyFinite_of_finite _, fun _ => ⟨i, fun _ _ => (by rw [hi])⟩⟩
      exact iUnion_eq_univ_iff.mpr (fun x => ⟨PUnit.unit, mem_univ x⟩)
    · have hproper : ∀ i, (s i)ᶜ.Nonempty := by
        intro i
        apply nonempty_compl.mpr
        intro hi
        exact hfull ⟨i, hi⟩
      obtain ⟨δ, hp, hl, hs⟩ := metric_subordinate_lipschitz_radius s ho hc hproper
      exact metric_star_refinement_of_radius s δ hp hl hs
  · let : IsEmpty α := not_nonempty_iff.mp hα
    obtain ⟨β, t, ht, hc, hf, hs⟩ := metric_locallyFinite_open_refinement ι s ho hcov
    refine ⟨β, t, ht, hc, hf, ?_⟩
    intro b
    obtain ⟨i, _⟩ := hs b
    exact ⟨i, fun _ h => isEmptyElim h.choose⟩
/-- The boundary formulas and the open-set criterion used in the dimension definitions. -/
/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $A\IncludedIn X$, its \termdefine{boundary} in $X$ is
    $$\AmbientBoundary{X}{A}:=\AmbientClosure{X}{A}\cap\AmbientClosure{X}{\SetDifference{X}{A}}.$$
    For an open set $V$, this becomes
    $$\AmbientBoundary{X}{V}=\SetDifference{\AmbientClosure{X}{V}}{V}.$$
    Thus an open set has empty boundary exactly when it is also closed.
-/
theorem open_boundary_formulas {X : Type*} [TopologicalSpace X] (V : Set X)
    (hV : IsOpen V) :
    frontier V = closure V ∩ closure Vᶜ ∧
      frontier V = closure V \ V ∧ (frontier V = ∅ ↔ IsClosed V) := by
  refine ⟨frontier_eq_closure_inter_closure, hV.frontier_eq, ?_⟩
  rw [hV.frontier_eq, sdiff_eq_empty, closure_subset_iff_isClosed]

end PolishSpaceBook
