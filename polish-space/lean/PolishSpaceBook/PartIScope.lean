module

public import PolishSpaceBook.PartIProse
public import PolishSpaceBook.FiniteBorelNormalForm

@[expose] public section

namespace PolishSpaceBook
open Set Filter Topology TopologicalSpace

/-- The coordinate projection detects the necessary countability of a discrete alphabet. -/
theorem countable_discrete_alphabet {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    [SeparableSpace (ℕ → A)] : Countable A := by
  have hsur : Function.Surjective (fun x : ℕ → A ↦ x 0) := fun a ↦ ⟨fun _ ↦ a, rfl⟩
  let : SeparableSpace A := hsur.denseRange.separableSpace (continuous_apply 0)
  exact (separableSpace_iff_countable).mp inferInstance

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    This chapter focuses on Polish sequence spaces $A^\omega$ whose alphabet $A$ is discrete. To be Polish, the discrete
    alphabet must be \termuse{countable}: if $A$ were uncountable, then the
    first-coordinate projection $\pi_0 : A^\omega \to A$ would split the space as
    $A^\omega = \InternalDisjointUnion_{a \in A} \pi_0^{-1}(\{a\})$ into uncountably many pairwise disjoint nonempty open
    sets, so $A^\omega$ would not be separable. Thus $A^\omega$ is Polish exactly when the alphabet $A$ is countable.
-/
theorem polish_discrete_sequences_iff_countable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] :
    PolishSpace (ℕ → A) ↔ Countable A := by
  constructor
  · intro h
    let : PolishSpace (ℕ → A) := h
    exact countable_discrete_alphabet
  · intro h
    let : Countable A := h
    obtain ⟨f, hf⟩ := Countable.exists_injective_nat A
    have he : Topology.IsClosedEmbedding f :=
      Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
        continuous_of_discreteTopology hf (fun _ _ ↦ isClosed_discrete _)
    let : PolishSpace A := he.polishSpace
    infer_instance

/-- The prefixes below a word are indexed by their lengths, including the word itself. -/
def prefixDownsetEquiv {A : Type*} (t : List A) : {s : List A // s.IsPrefix t} ≃ Fin (t.length + 1) where
  toFun s := ⟨s.val.length, Nat.lt_succ_iff.mpr s.property.length_le⟩
  invFun n := ⟨t.take n, List.take_prefix _ _⟩
  left_inv s := Subtype.ext (List.prefix_iff_eq_take.mp s.property).symm
  right_inv n := Fin.ext (by simp [List.length_take, Nat.min_eq_left (by omega : n.val ≤ t.length)])

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    A \termdefine{tree} is a partially ordered set in which, for each element $t$, the set $\{s:s\le t\}$ is well-ordered
    by the inherited order.
    For $A=2$ or $A=\omega$, the full prefix \termuse{tree} is $(\finseq{A},\prefixOf)$.
    For $t\in\finseq{A}$, the non-strict down-set of $t$ in the full prefix \termuse{tree} is exactly the set of initial
    segments of $t$:
    $$
    \RestrictedSet{\finseq{A}}{\prefixOf t}
    =
    \{\restrict{t}{n}:n\le |t|\}
    \cong |t|+1
    \quad\text{as posets},
    $$
    so it is well-ordered.
    Thus $(\finseq{A},\prefixOf)$ is a tree.
-/
theorem prefixDownset_order {A : Type*} (t : List A)
    (s u : {s : List A // s.IsPrefix t}) :
    s.val.IsPrefix u.val ↔ prefixDownsetEquiv t s ≤ prefixDownsetEquiv t u := by
  change s.val.IsPrefix u.val ↔ s.val.length ≤ u.val.length
  rw [List.prefix_iff_eq_take.mp u.property, List.prefix_take_iff]
  simpa only [List.length_take, Nat.min_eq_left u.property.length_le] using
    (and_iff_right s.property : s.val.IsPrefix t ∧ s.val.length ≤ u.val.length ↔ s.val.length ≤ u.val.length)

theorem prefixDownset_wellFounded {A : Type*} (t : List A) :
    WellFounded (fun s u : {s : List A // s.IsPrefix t} ↦ s.val.length < u.val.length) :=
  InvImage.wf (fun s : {s : List A // s.IsPrefix t} ↦ s.val.length) Nat.lt_wfRel.wf

/-- The book's clopen example uses the first coordinate to decide how far to read. -/
def variablePrefixClopen : Set baire_space := {x | x (x 0 + 1) = 0}

theorem continuous_variablePrefix : Continuous (fun x : baire_space ↦ x (x 0 + 1)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hsingleton : ∀ᶠ n : ℕ in 𝓝 (x 0), n = x 0 := by simp [nhds_discrete]
  have hfirst : ∀ᶠ y in 𝓝 x, y 0 = x 0 := (continuousAt_apply 0 x).eventually hsingleton
  apply ContinuousAt.congr_of_eventuallyEq (continuousAt_apply (x 0 + 1) x)
  filter_upwards [hfirst] with y hy
  simp [hy]

theorem variablePrefixClopen_isClopen : IsClopen variablePrefixClopen :=
  (isClopen_discrete {0}).preimage continuous_variablePrefix

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    The boundedness of $\bDelta^0_1$ is the substantive difference. For example,
    $$
    C:=\{x\in\BaireSpace:x(x(0)+1)=0\}
    $$
    is clopen: membership and nonmembership are decided by the prefix of length $x(0)+2$, but no single prefix length works
    uniformly for every $x$. In Cantor space König's lemma forces a uniform bound. From level $2$ upward the structural form
    is identical to Baire space, with binary tree bodies replacing $\omega$-branching ones.
-/
theorem variablePrefixClopen_no_uniform_bound (N : ℕ) :
    ∃ x y : baire_space, (∀ n < N, x n = y n) ∧
      x ∈ variablePrefixClopen ∧ y ∉ variablePrefixClopen := by
  let x : baire_space := fun n ↦ if n = 0 then N else 0
  let y : baire_space := fun n ↦ if n = N + 1 then 1 else x n
  refine ⟨x, y, ?_, ?_, ?_⟩
  · intro n hn
    simp [y, show n ≠ N + 1 by omega]
  · simp [variablePrefixClopen, x]
  · simp [variablePrefixClopen, x, y]

theorem variablePrefixClopen_decided (x y : baire_space)
    (h : ∀ n < x 0 + 2, x n = y n) : x ∈ variablePrefixClopen ↔ y ∈ variablePrefixClopen := by
  have h₀ := h 0 (by omega)
  have h₁ := h (x 0 + 1) (by omega)
  change (x (x 0 + 1) = 0) ↔ y (y 0 + 1) = 0
  rw [← h₀, ← h₁]

/-@ booklink:
  source: polish-space-book/polish-spaces.md
  target: prose
  excerpt: |
    The irrationals also illustrate that subspaces need not preserve completeness of the inherited metric: the Euclidean
    metric inherited from $\R$ is not complete on $\SetDifference{\R}{\QQ}$, since Cauchy sequences of irrationals can
    converge to rationals. Yet a different complete metric induces the
    same topology. So a non-closed Polish subspace of a Polish space
    may require a metric different from the inherited one; §{sec:alexandrov-theorem} gives the
    general criterion for which subspaces are Polish.
-/
theorem irrationals_inherited_metric_incomplete :
    ¬ CompleteSpace {x : ℝ // Irrational x} := by
  intro h
  let : CompleteSpace {x : ℝ // Irrational x} := h
  have hc : IsClosed {x : ℝ | Irrational x} := by
    simpa only [Subtype.range_coe_subtype] using
      (isUniformEmbedding_subtype_val (p := Irrational)).isClosedEmbedding.isClosed_range
  have hzero : (0 : ℝ) ∈ closure {x : ℝ | Irrational x} := by
    rw [dense_irrational.closure_eq]
    trivial
  rw [hc.closure_eq] at hzero
  exact not_irrational_zero hzero

/-- A compact set of irrationals cannot contain a relative neighborhood. -/

theorem irrationals_no_compact_neighborhoods (x : {x : ℝ // Irrational x}) :
    ¬ ∃ K : Set {x : ℝ // Irrational x}, IsCompact K ∧ K ∈ 𝓝 x := by
  rintro ⟨K, hK, hKn⟩
  obtain ⟨V, hVn, hVK⟩ := (mem_nhds_subtype _ x K).mp hKn
  obtain ⟨U, hUV, hU, hxU⟩ := mem_nhds_iff.mp hVn
  let C : Set ℝ := Subtype.val '' K
  have hC : IsClosed C := (hK.image continuous_subtype_val).isClosed
  obtain ⟨r, hrU⟩ := Rat.denseRange_cast.exists_mem_open hU ⟨x.val, hxU⟩
  have hrC : (r : ℝ) ∈ C := by
    rw [← hC.closure_eq]
    apply mem_closure_iff.mpr
    intro O hO hrO
    obtain ⟨z, hzIrr, hzU, hzO⟩ := dense_irrational.exists_mem_open (hU.inter hO) ⟨r, hrU, hrO⟩
    exact ⟨z, hzO, ⟨⟨z, hzIrr⟩, hVK (hUV hzU), rfl⟩⟩
  obtain ⟨y, _, hyr⟩ := hrC
  exact (Rat.not_irrational r) (hyr ▸ y.property)

/-- A rational endpoint is absent from the irrational subspace, so relative
open and closed intervals with these endpoints coincide. -/
theorem irrational_rational_interval_clopen (q r : ℚ) :
    IsClopen {x : {x : ℝ // Irrational x} | (q : ℝ) < x.1 ∧ x.1 < (r : ℝ)} := by
  have heq : {x : {x : ℝ // Irrational x} | (q : ℝ) < x.1 ∧ x.1 < (r : ℝ)} =
      Subtype.val ⁻¹' Icc (q : ℝ) (r : ℝ) := by
    ext x
    constructor
    · exact fun h => ⟨h.1.le, h.2.le⟩
    · exact fun h => ⟨lt_of_le_of_ne h.1 (Ne.symm (x.2.ne_rat q)),
        lt_of_le_of_ne h.2 (x.2.ne_rat r)⟩
  refine ⟨?_, isOpen_Ioo.preimage continuous_subtype_val⟩
  rw [heq]
  exact isClosed_Icc.preimage continuous_subtype_val

/-- The rational-endpoint intervals form the clopen base used in the
non-arithmetic application of Alexandrov--Urysohn. -/
theorem irrational_rational_interval_basis :
    IsTopologicalBasis {U : Set {x : ℝ // Irrational x} |
      ∃ q r : ℚ, q < r ∧ U = {x | (q : ℝ) < x.1 ∧ x.1 < (r : ℝ)}} := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨q, r, _, rfl⟩
    exact (irrational_rational_interval_clopen q r).isOpen
  · intro x U hx hU
    obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
    obtain ⟨W, hW, hxW, hWV⟩ := Real.isTopologicalBasis_Ioo_rat.exists_subset_of_mem_open hx hV
    simp only [mem_iUnion, mem_singleton_iff] at hW
    obtain ⟨q, r, hqr, rfl⟩ := hW
    exact ⟨Subtype.val ⁻¹' Ioo (q : ℝ) (r : ℝ), ⟨q, r, hqr, rfl⟩,
      hxW, preimage_mono hWV⟩

theorem irrational_zeroDimensional_via_rational_intervals :
    IsZeroDimensional {x : ℝ // Irrational x} := by
  apply irrational_rational_interval_basis.of_isOpen_of_subset
    (fun _ h => h.isOpen)
  rintro U ⟨q, r, _, rfl⟩
  exact irrational_rational_interval_clopen q r

/-@ booklink:
  source: polish-space-book/cantor-baire-space.md
  target: prose
  excerpt: |
    The Alexandrov–Urysohn theorem yields a non-arithmetic proof that the irrationals in $\R$ are homeomorphic to
    $\BaireSpace$. The irrationals form a nonempty Polish space by \termuse{Alexandrov's theorem} in
    §{sec:alexandrov-theorem}. The relative intervals $(q,r)\cap\SetDifference{\R}{\QQ}$, where $q<r$ are rational, form a
    clopen base, verifying zero-dimensionality. It remains to show that no point has a compact neighborhood. If a compact
    set $K\IncludedIn\SetDifference{\R}{\QQ}$ contained a relative
    open neighborhood of an
    irrational,
    then that neighborhood would contain a sequence of irrationals converging in $\R$ to a rational. The sequence would lie
    in $K$, but compactness of $K$ as a subspace of $\SetDifference{\R}{\QQ}$ would force a subsequential limit in
    $\SetDifference{\R}{\QQ}$,
    contradicting uniqueness of limits in $\R$. Thus no irrational has a compact neighborhood. This complements the
    continued-fraction homeomorphism in §{sec:simple-continued-fractions}.
-/
/-- Apply the book's clopen-scheme construction using a bounded complete
compatible metric, rather than the incomplete inherited Euclidean metric. -/
theorem irrationals_baire_homeomorphism_via_alexandrov_urysohn :
    Nonempty ({x : ℝ // Irrational x} ≃ₜ baire_space) := by
  let I := {x : ℝ // Irrational x}
  let : PolishSpace I := gdelta_subspace_polish IsGδ.setOfPred_irrational
  let : Nonempty I := ⟨⟨Real.sqrt 2, irrational_sqrt_two⟩⟩
  let completeMetric : UpgradedIsCompletelyMetrizableSpace I := upgradeIsCompletelyMetrizable I
  let : MetricSpace I := completeMetric.toMetricSpace
  obtain ⟨m, htop, hcomplete, _, hbound⟩ := complete_compatible_metric_bounded_by_one I
    ((isMetricComplete_iff_completeSpace I).mpr completeMetric.toCompleteSpace)
  have hz : @IsZeroDimensional I m.toUniformSpace.toTopologicalSpace := by
    rw [htop]
    exact irrational_zeroDimensional_via_rational_intervals
  have hn : @NoCompactNeighborhoods I m.toUniformSpace.toTopologicalSpace := by
    rw [htop]
    exact irrationals_no_compact_neighborhoods
  have : @SecondCountableTopology I m.toUniformSpace.toTopologicalSpace := by
    rw [htop]
    infer_instance
  have h := @exists_alexandrov_urysohn_baire_homeomorph I m inferInstance inferInstance
    hcomplete hz hn hbound
  rw [htop] at h
  exact h.map Homeomorph.symm

/-- The convergent reciprocal sequence together with its limit. -/
def reciprocalSequenceSet : Set ℝ :=
  insert 0 (range (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹))

theorem reciprocalSequenceSet_closed : IsClosed reciprocalSequenceSet := by
  have h : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact h.isCompact_insert_range.isClosed

/-- Inversion carries a neighborhood of `1/(n+1)` to an interval containing
just the integer `n+1` among the positive integers. -/
theorem reciprocalSequenceSet_isolated (n : ℕ) :
    ∃ U ∈ 𝓝 (((n + 1 : ℕ) : ℝ)⁻¹),
      U ∩ reciprocalSequenceSet = {((n + 1 : ℕ) : ℝ)⁻¹} := by
  let V := Ioo (((n + 1 : ℕ) : ℝ) - 1 / 2) (((n + 1 : ℕ) : ℝ) + 1 / 2)
  let U : Set ℝ := Inv.inv ⁻¹' V
  have hn : (((n + 1 : ℕ) : ℝ)⁻¹) ≠ 0 := by positivity
  have hU : U ∈ 𝓝 (((n + 1 : ℕ) : ℝ)⁻¹) :=
    (continuousAt_inv₀ hn).preimage_mem_nhds (by
      simp only [inv_inv]
      exact Ioo_mem_nhds (by linarith) (by linarith))
  refine ⟨U, hU, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hxS⟩
    rcases hxS with rfl | ⟨m, rfl⟩
    · have hlow := hx.1
      change (((n + 1 : ℕ) : ℝ) - 1 / 2) < (0 : ℝ)⁻¹ at hlow
      simp only [inv_zero, Nat.cast_add, Nat.cast_one] at hlow
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · change (((n + 1 : ℕ) : ℝ) - 1 / 2) < (((m + 1 : ℕ) : ℝ)⁻¹)⁻¹ ∧
        (((m + 1 : ℕ) : ℝ)⁻¹)⁻¹ < (((n + 1 : ℕ) : ℝ) + 1 / 2) at hx
      simp only [inv_inv, Nat.cast_add, Nat.cast_one] at hx
      have hmn : m < n + 1 := by exact_mod_cast (show (m : ℝ) < (n : ℝ) + 1 by linarith)
      have hnm : n < m + 1 := by exact_mod_cast (show (n : ℝ) < (m : ℝ) + 1 by linarith)
      have : m = n := by omega
      simp [this]
  · rintro rfl
    refine ⟨?_, Or.inr ⟨n, rfl⟩⟩
    change _ ∈ V
    simp only [inv_inv, V, mem_Ioo]
    constructor <;> linarith

theorem not_perfect_of_isolated_neighborhood {Y : Type*} [TopologicalSpace Y]
    {S U : Set Y} {x : Y} (hx : x ∈ S) (hU : U ∈ 𝓝 x)
    (hUS : U ∩ S = {x}) : ¬ Perfect S := by
  intro h
  obtain ⟨y, hy, hyx⟩ := accPt_iff_nhds.mp (h.acc x hx) U hU
  rw [hUS] at hy
  exact hyx hy

theorem reciprocalSequenceSet_not_perfect : ¬ Perfect reciprocalSequenceSet := by
  obtain ⟨U, hU, heq⟩ := reciprocalSequenceSet_isolated 0
  exact not_perfect_of_isolated_neighborhood (Or.inr ⟨0, rfl⟩) hU heq

theorem integerSet_closed : IsClosed (range ((↑) : ℤ → ℝ)) :=
  Int.isClosedEmbedding_coe_real.isClosed_range

theorem integerSet_isolated (n : ℤ) :
    ∃ U ∈ 𝓝 (n : ℝ), U ∩ range ((↑) : ℤ → ℝ) = {(n : ℝ)} := by
  refine ⟨Ioo ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2),
    Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  ext x
  constructor
  · rintro ⟨hx, m, rfl⟩
    have hmn : m < n + 1 := by exact_mod_cast (show (m : ℝ) < (n : ℝ) + 1 by linarith [hx.2])
    have hnm : n < m + 1 := by exact_mod_cast (show (n : ℝ) < (m : ℝ) + 1 by linarith [hx.1])
    have : m = n := by omega
    simp [this]
  · rintro rfl
    exact ⟨⟨by linarith, by linarith⟩, ⟨n, rfl⟩⟩

theorem integerSet_not_perfect : ¬ Perfect (range ((↑) : ℤ → ℝ)) := by
  obtain ⟨U, hU, heq⟩ := integerSet_isolated 0
  exact not_perfect_of_isolated_neighborhood ⟨0, rfl⟩ hU heq

theorem reciprocalSequenceSet_eq_book :
    reciprocalSequenceSet = {0} ∪ {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ x = 1 / (n : ℝ)} := by
  ext x
  constructor
  · rintro (rfl | ⟨n, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨n + 1, by omega, by rw [one_div]⟩
  · rintro (rfl | ⟨n, hn, rfl⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨n - 1, ?_⟩
      have : n - 1 + 1 = n := by omega
      simp only [this, one_div]

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    $\{0\} \cup \{1/n : n \in \RestrictedSet{\NN}{\ge 1}\} \IncludedIn \R$ is closed but not perfect —
    each $1/n$ is isolated.
-/
theorem reciprocalSequenceSet_example :
    IsClosed reciprocalSequenceSet ∧ ¬ Perfect reciprocalSequenceSet ∧
      ∀ n : ℕ, 1 ≤ n → ∃ U ∈ 𝓝 (1 / (n : ℝ)),
        U ∩ reciprocalSequenceSet = {1 / (n : ℝ)} := by
  refine ⟨reciprocalSequenceSet_closed, reciprocalSequenceSet_not_perfect, ?_⟩
  intro n hn
  have h := reciprocalSequenceSet_isolated (n - 1)
  have he : n - 1 + 1 = n := by omega
  simpa only [he, one_div] using h

/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    $\ZZ \IncludedIn \R$ is closed but every point is isolated, so it is not perfect.
-/
theorem integerSet_example :
    IsClosed (range ((↑) : ℤ → ℝ)) ∧ ¬ Perfect (range ((↑) : ℤ → ℝ)) ∧
      ∀ n : ℤ, ∃ U ∈ 𝓝 (n : ℝ), U ∩ range ((↑) : ℤ → ℝ) = {(n : ℝ)} :=
  ⟨integerSet_closed, integerSet_not_perfect, integerSet_isolated⟩

def binaryZeroTest (x : cantor_space) : baire_space := fun n ↦ if x n then 0 else 1

def binaryZeroIndicator (x : baire_space) : cantor_space := fun n ↦ decide (x n = 0)

theorem continuous_binaryZeroTest : Continuous binaryZeroTest :=
  continuous_pi fun n ↦
    (continuous_of_discreteTopology (f := fun b : Bool ↦ if b then (0 : ℕ) else 1)).comp
      (continuous_apply n)

theorem continuous_binaryZeroIndicator : Continuous binaryZeroIndicator :=
  continuous_pi fun n ↦
    (continuous_of_discreteTopology (f := fun m : ℕ ↦ decide (m = 0))).comp
      (continuous_apply n)

def binaryUnboundedSet : Set cantor_space := binaryZeroTest ⁻¹' FiniteBorelNormalForm.unboundedSet

theorem binaryUnboundedSet_mem_sigma_omega : binaryUnboundedSet ∈ borelSigma Ordinal.omega0 :=
  borelSigma_preimage binaryZeroTest continuous_binaryZeroTest _ FiniteBorelNormalForm.unboundedSet_mem_sigma_omega

theorem binaryZeroIndicator_preimage_unbounded :
    binaryZeroIndicator ⁻¹' binaryUnboundedSet = FiniteBorelNormalForm.unboundedSet := by
  ext x
  simp only [binaryUnboundedSet, mem_preimage, FiniteBorelNormalForm.unboundedSet, mem_iUnion,
    FiniteBorelNormalForm.completeSet, mem_ofPred_eq]
  have h (n : ℕ) :
      (fun t ↦ FiniteBorelNormalForm.slice n (binaryZeroTest (binaryZeroIndicator x)) t = 0) =
        (fun t ↦ FiniteBorelNormalForm.slice n x t = 0) := by
    funext t
    simp [FiniteBorelNormalForm.slice, binaryZeroTest, binaryZeroIndicator]
  simp_rw [h]

/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    The level-$\omega$ construction above adapts by replacing each slice
    $\funcspace{\seqPower{\omega}{k}}{\omega}$ with the binary-valued slice
    $\funcspace{\seqPower{\omega}{k}}{2}$ and defining $P_k^{(2)}$ by the same alternating condition. The reductions above
    already take only the values $0$ and $1$, and coordinate reindexing gives
    $$
    \prod_{k\geq 1}\funcspace{\seqPower{\omega}{k}}{2}
    \cong\CantorSpace,
    $$
    which yields the Cantor-space example.
-/
theorem binaryUnboundedSet_not_sigma (n : ℕ) : binaryUnboundedSet ∉ borelSigma (↑n + 1) := by
  intro h
  have := borelSigma_preimage binaryZeroIndicator continuous_binaryZeroIndicator _ h
  rw [binaryZeroIndicator_preimage_unbounded] at this
  exact FiniteBorelNormalForm.unboundedSet_not_sigma n this

theorem binaryUnboundedSet_not_pi (n : ℕ) : binaryUnboundedSet ∉ borelPi (↑n + 1) := by
  intro h
  have := borelPi_preimage binaryZeroIndicator continuous_binaryZeroIndicator _ h
  rw [binaryZeroIndicator_preimage_unbounded] at this
  exact FiniteBorelNormalForm.unboundedSet_not_pi n this

end PolishSpaceBook
