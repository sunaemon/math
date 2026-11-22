module

public import PolishSpaceBook.ConcreteCantorBaireModels
public import PolishSpaceBook.PerfectSetsStandardBorelCoding
public import PolishSpaceBook.BorelExpressionValidity

@[expose] public section

namespace PolishSpaceBook
open Set Filter Topology

/-- In a discrete product, convergence is eventual agreement of each coordinate. -/
theorem cantor_tendsto_iff_coordinates (u : ℕ → cantor_space) (x : cantor_space) :
    Tendsto u atTop (𝓝 x) ↔ ∀ n, ∃ J, ∀ j ≥ J, u j n = x n := by
  rw [tendsto_pi_nhds]
  simp only [nhds_discrete, tendsto_pure, eventually_atTop]

/-- Coordinatewise eventual agreement is equivalent to eventual agreement on
all finite initial segments. -/
theorem cantor_coordinates_iff_prefix (u : ℕ → cantor_space) (x : cantor_space) :
    (∀ n, ∃ J, ∀ j ≥ J, u j n = x n) ↔
      ∀ k, ∃ J, ∀ j ≥ J, ∀ n < k, u j n = x n := by
  constructor
  · intro h k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨J, hJ⟩ := ih
      obtain ⟨K, hK⟩ := h k
      exact ⟨max J K, fun j hj n hn ↦ by
        by_cases hnk : n < k
        · exact hJ j (le_trans (le_max_left _ _) hj) n hnk
        · have : n = k := by omega
          subst n
          exact hK j (le_trans (le_max_right _ _) hj)⟩
  · intro h n
    obtain ⟨J, hJ⟩ := h (n + 1)
    exact ⟨J, fun j hj ↦ hJ j hj n (by omega)⟩

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    \item \emph{Power set.} Give $\PowerSet{\omega}$ the topology transported from binary sequences by characteristic
    functions, as constructed below. A sequence $\Sequence{E_j}{j\in\omega}$ converges to $E$ exactly when membership of
    each fixed
    natural number eventually agrees with membership in $E$:
    $$\forall n\in\omega\;\exists J\in\omega\;\forall j\ge J,\quad (n\in E_j\Longleftrightarrow n\in E).$$
    Thus, on any fixed finite set of natural numbers, the subsets eventually agree with the limit.
-/
theorem powerset_tendsto_iff_membership (u : ℕ → powersetOmega) (E : powersetOmega) :
    Tendsto u atTop (𝓝 E) ↔ ∀ n, ∃ J, ∀ j ≥ J, (n ∈ u j ↔ n ∈ E) := by
  have hchar (A B : powersetOmega) (n : ℕ) :
      subsetCharacteristic A n = subsetCharacteristic B n ↔ (n ∈ A ↔ n ∈ B) := by
    classical
    by_cases ha : n ∈ A <;> by_cases hb : n ∈ B <;> simp [subsetCharacteristic, ha, hb]
  rw [powersetOmegaHomeomorphCantorSpace.isEmbedding.tendsto_nhds_iff]
  simpa only [Function.comp_def, powersetOmegaHomeomorphCantorSpace_apply, hchar] using
    cantor_tendsto_iff_coordinates (fun j ↦ powersetOmegaHomeomorphCantorSpace (u j))
      (powersetOmegaHomeomorphCantorSpace E)

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Give $C$ the subspace topology inherited from $\R$. For $z_j,z\in C$, convergence $z_j\to z$ means ordinary
    convergence of real numbers:
    $$\forall\varepsilon>0\;\exists J\in\omega\;\forall j\ge J,\quad |z_j-z|<\varepsilon.$$
-/
theorem middleThirds_tendsto_iff_real (u : ℕ → middleThirdsCantorSet) (z : middleThirdsCantorSet) :
    Tendsto u atTop (𝓝 z) ↔ ∀ ε > 0, ∃ J, ∀ j ≥ J, |(u j : ℝ) - z| < ε := by
  rw [Metric.tendsto_atTop]
  rfl

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    In particular, for $z_j=h(x_j)$ and $z=h(x)$, real convergence $z_j\to z$ is equivalent to eventual agreement of
    each binary coordinate. In the ternary expansions using only $0$ and $2$, each fixed digit therefore eventually
    agrees with the corresponding digit of the limit.
-/
theorem middleThirds_tendsto_iff_digits (u : ℕ → cantor_space) (x : cantor_space) :
    Tendsto (fun j ↦ middleThirdsCantorHomeomorph (u j)) atTop
      (𝓝 (middleThirdsCantorHomeomorph x)) ↔ ∀ n, ∃ J, ∀ j ≥ J, u j n = x n := by
  exact middleThirdsCantorHomeomorph.isEmbedding.tendsto_nhds_iff.symm.trans
    (cantor_tendsto_iff_coordinates u x)

/-- The canonical perfect-set definition is exactly closedness together with
accumulation in every neighborhood. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    A point $x$ is a \termdefine{limit point} (or *accumulation point*) of $A$ if every neighborhood of $x$ meets
    $\SetDifference{A}{\{x\}}$, and a point $x \in A$ is an \termuse{isolated point} of $A$ if some neighborhood of $x$
    meets $A$
    only at $x$. A subset $A$ of a topological space is \termdefineas{perfect set}{perfect} if it is closed and has no
    isolated points — equivalently, $A$ equals its set of limit points. A space is *\termuseas{perfect space}{perfect}* if
    it is perfect as a subset of itself.
-/
theorem perfect_iff_neighborhoods {X : Type*} [TopologicalSpace X] (A : Set X) :
    Perfect A ↔ IsClosed A ∧ ∀ x ∈ A, ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ A, y ≠ x := by
  rw [perfect_def, preperfect_iff_nhds]

/-- Borel isomorphisms are bijections measurable in both directions. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    A bijection between measurable spaces is a \termdefine{Borel isomorphism} if both it and its inverse are
    measurable. For topological spaces, we equip each space with its Borel $\sigma$-algebra.
-/
theorem borelIsomorphism_iff {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] :
    Nonempty (X ≃ᵐ Y) ↔ ∃ e : X ≃ Y, Measurable e ∧ Measurable e.symm := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toEquiv, e.measurable, e.symm.measurable⟩
  · rintro ⟨e, he, hi⟩
    exact ⟨⟨e, he, hi⟩⟩

/-- The sign of the first ternary digit that differs determines the strict order. -/
theorem binaryTernary_lt_of_first_difference {x y : cantor_space} {k : ℕ}
    (h : ∀ i < k, x i = y i) (hx : x k = false) (hy : y k = true) :
    Real.ofDigits (binaryTernaryDigits x) < Real.ofDigits (binaryTernaryDigits y) := by
  rw [Real.ofDigits_eq_sum_add_ofDigits (binaryTernaryDigits x) (k + 1),
    Real.ofDigits_eq_sum_add_ofDigits (binaryTernaryDigits y) (k + 1),
    Finset.sum_range_succ, Finset.sum_range_succ, binaryTernary_prefix_sum_eq h]
  have hx₁ := Real.ofDigits_le_one (fun i => binaryTernaryDigits x (i + (k + 1)))
  have hy₀ := Real.ofDigits_nonneg (fun i => binaryTernaryDigits y (i + (k + 1)))
  have hp : 0 < ((3 : ℝ) ^ (k + 1))⁻¹ := by positivity
  simp only [Real.ofDigitsTerm, binaryTernaryDigits, hx, hy, Bool.false_eq_true,
    ↓reduceIte, Fin.coe_ofNat_eq_mod, Nat.zero_mod, CharP.cast_eq_zero,
    Nat.cast_ofNat, zero_mul, Nat.mod_succ]
  dsimp only [binaryTernaryDigits] at hx₁ hy₀
  nlinarith

noncomputable def ternaryPrefixSum (y : cantor_space) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, Real.ofDigitsTerm (binaryTernaryDigits y) i

def padBinaryPrefix (y : cantor_space) (k : ℕ) (bit : Bool) : cantor_space :=
  fun n ↦ if n < k then y n else bit

theorem paddedTernary_value (y : cantor_space) (k : ℕ) (bit : Bool) :
    Real.ofDigits (binaryTernaryDigits (padBinaryPrefix y k bit)) =
      ternaryPrefixSum y k + (if bit then 1 else 0) * ((3 : ℝ) ^ k)⁻¹ := by
  rw [Real.ofDigits_eq_sum_add_ofDigits (binaryTernaryDigits (padBinaryPrefix y k bit)) k,
    binaryTernary_prefix_sum_eq (y := y) (fun i hi ↦ by simp [padBinaryPrefix, hi])]
  have htail : (fun i ↦ binaryTernaryDigits (padBinaryPrefix y k bit) (i + k)) =
      fun _ ↦ (if bit then (2 : Fin 3) else 0) := by
    funext i
    simp [binaryTernaryDigits, padBinaryPrefix, Nat.not_lt.mpr (Nat.le_add_left k i)]
  rw [htail]
  cases bit
  · simp [ternaryPrefixSum, Real.ofDigits, Real.ofDigitsTerm]
  · have h : Real.ofDigits (fun _ : ℕ ↦ (2 : Fin 3)) = 1 :=
      Real.ofDigits_const_last_eq_one 2
    simp [h, ternaryPrefixSum]

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    For a word $s$ of length $k$, put
    $$t_s:=\sum_{i<k}\frac{2s_i}{3^{i+1}},\qquad I_s:=[t_s,t_s+3^{-k}].$$
-/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Indeed, the remaining ternary digits contribute a number between $0$ and $3^{-k}$, and the stage-$k$
    intervals for distinct words are disjoint.
-/
theorem ternary_mem_prefix_interval_iff (x y : cantor_space) (k : ℕ) :
    Real.ofDigits (binaryTernaryDigits x) ∈
      Icc (ternaryPrefixSum y k) (ternaryPrefixSum y k + ((3 : ℝ) ^ k)⁻¹) ↔
      ∀ i < k, x i = y i := by
  constructor
  · intro hx
    by_contra hne
    push Not at hne
    let j := Nat.find hne
    have hj : j < k ∧ x j ≠ y j := Nat.find_spec hne
    have hbefore : ∀ i < j, x i = y i := by
      intro i hi
      have := Nat.find_min hne hi
      simpa [show i < k from lt_trans hi hj.1] using this
    cases hbit : x j
    · have hy : y j = true := by cases h : y j <;> simp_all
      have hlt := binaryTernary_lt_of_first_difference
        (y := padBinaryPrefix y k false)
        (fun i hi ↦ (hbefore i hi).trans (by simp [padBinaryPrefix, lt_trans hi hj.1]))
        hbit (by simpa [padBinaryPrefix, hj.1] using hy)
      rw [paddedTernary_value] at hlt
      simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero] at hlt
      exact (not_lt_of_ge hx.1) hlt
    · have hy : y j = false := by cases h : y j <;> simp_all
      have hlt := binaryTernary_lt_of_first_difference
        (x := padBinaryPrefix y k true) (y := x)
        (fun i hi ↦ (by simp [padBinaryPrefix, lt_trans hi hj.1] :
          padBinaryPrefix y k true i = y i).trans (hbefore i hi).symm)
        (by simpa [padBinaryPrefix, hj.1] using hy) hbit
      rw [paddedTernary_value] at hlt
      simp only [↓reduceIte, one_mul] at hlt
      exact (not_lt_of_ge hx.2) hlt
  · intro h
    rw [Real.ofDigits_eq_sum_add_ofDigits (binaryTernaryDigits x) k,
      binaryTernary_prefix_sum_eq h]
    have h₀ := Real.ofDigits_nonneg (fun i ↦ binaryTernaryDigits x (i + k))
    have h₁ := Real.ofDigits_le_one (fun i ↦ binaryTernaryDigits x (i + k))
    have hp : 0 ≤ ((3 : ℝ) ^ k)⁻¹ := by positivity
    norm_num only [Nat.cast_ofNat]
    dsimp [ternaryPrefixSum]
    constructor <;> nlinarith

/-- Cylinder neighborhoods give exactly the same convergence test as coordinates. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    A sequence converges to a point exactly when it eventually belongs to every cylinder containing that point.
    This is the finite-prefix criterion above; it is equivalent to coordinatewise eventual agreement because one can
    take the maximum of the finitely many indices needed for a given prefix.
-/
theorem cantor_tendsto_iff_cylinders (u : ℕ → cantor_space) (x : cantor_space) :
    Tendsto u atTop (𝓝 x) ↔
      ∀ s : finseq Bool, x ∈ cyl s → ∀ᶠ j in atTop, u j ∈ cyl s := by
  constructor
  · intro hu s hs
    exact hu.eventually ((cantor_cyl_clopen s).isOpen.mem_nhds hs)
  · intro h
    apply (cantor_tendsto_iff_coordinates u x).mpr
    intro n
    have hn := h (seqPrefix x (n + 1)) (mem_cyl_seqPrefix x (n + 1))
    obtain ⟨J, hJ⟩ := eventually_atTop.mp hn
    exact ⟨J, fun j hj ↦ (hJ j hj n (by simp)).trans (seqPrefix_get x (by simp))⟩

/-- The first prefix decisions are exactly the positive/negative finite sets. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The inverse image $\chi^{-1}(\cyl{s})$ is $[F_s;G_s]$, where
    $F_s=\{n<|s|:s(n)=1\}$ and $G_s=\{n<|s|:s(n)=0\}$.
-/
theorem characteristic_cylinder_eq_decisions (s : finseq Bool) :
    subsetCharacteristic ⁻¹' (cyl s : Set cantor_space) =
      membershipDecisionSet
        ((Finset.range s.length).filter (fun n ↦ s[n]?.getD false = true))
        ((Finset.range s.length).filter (fun n ↦ s[n]?.getD false = false)) := by
  classical
  rw [subsetCharacteristic_preimage_cyl]
  ext E
  simp only [mem_ofPred_eq, membershipDecisionSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    constructor
    · intro n
      rintro ⟨hn, hb⟩
      exact (h n hn).mpr (by simpa [List.getElem?_eq_getElem, hn] using hb)
    · intro n
      rintro ⟨hn, hb⟩ hmem
      have := (h n hn).mp hmem
      have hb' : s.get ⟨n, hn⟩ = false := by
        simpa [List.getElem?_eq_getElem, hn] using hb
      rw [this] at hb'
      cases hb'
  · intro h n hn
    cases hb : s.get ⟨n, hn⟩
    · simp only [Bool.false_eq_true, iff_false]
      exact h.2 n ⟨hn, by simpa [List.getElem?_eq_getElem, hn] using hb⟩
    · simp only [iff_true]
      exact h.1 n ⟨hn, by simpa [List.getElem?_eq_getElem, hn] using hb⟩

/-- Both formulations of the binary convergence criterion. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    \item \emph{Binary sequences.} In $\CantorSpace$, a sequence $\Sequence{x_j}{j\in\omega}$ converges to $x$ exactly when
    each
    coordinate eventually agrees with that of $x$:
    $$\forall n\in\omega\;\exists J\in\omega\;\forall j\ge J,\quad x_j(n)=x(n).$$
    The index $J$ may depend on $n$. Equivalently, any fixed finite initial segment eventually agrees with that of the
    limit; the whole infinite sequence need not agree at any one stage.
-/
theorem cantor_convergence_criteria (u : ℕ → cantor_space) (x : cantor_space) :
    (Tendsto u atTop (𝓝 x) ↔ ∀ n, ∃ J, ∀ j ≥ J, u j n = x n) ∧
      (Tendsto u atTop (𝓝 x) ↔ ∀ k, ∃ J, ∀ j ≥ J, ∀ n < k, u j n = x n) :=
  ⟨cantor_tendsto_iff_coordinates u x,
    (cantor_tendsto_iff_coordinates u x).trans (cantor_coordinates_iff_prefix u x)⟩

/-- The two sequence spaces agree measurably but differ topologically. -/
/-@ booklink:
  source: polish-space-book/perfect-sets-standard-borel-coding.md
  target: prose
  excerpt: |
    The model example is the Borel equivalence of Cantor space and Baire space. They cannot be homeomorphic: Cantor space is
    compact, while Baire space is nowhere locally compact. But they have the same \termdefine{Borel structure}.
-/
theorem cantor_baire_borel_not_homeomorphic :
    Nonempty (cantor_space ≃ᵐ baire_space) ∧ ¬ Nonempty (cantor_space ≃ₜ baire_space) :=
  ⟨⟨CantorBaireBorel.cantorBaireEquiv⟩, no_cantor_space_homeomorph_baire_space⟩

/-- The first Borel level has finite evidence on each side of a clopen set. -/
/-@ booklink:
  source: polish-space-book/borel-structure.md
  target: prose
  excerpt: |
    In Baire space the abstract hierarchy has a concrete location in the cylinder/tree picture.
    The first levels say which kind of finite evidence decides the question.
    By §{sec:closed-sets-trees}, open sets are coded by saturated up-sets of prefixes. For an open set $A$, membership
    $x\in A$ is confirmed by finding a prefix $s$ of $x$ with $\cyl{s}\IncludedIn A$.
    The same section codes a closed set $F$ as the body of a pruned subtree. Nonmembership $x\notin F$ is confirmed by
    finding a prefix of $x$ that falls out of that tree.
-/
theorem baire_finite_evidence (A : Set baire_space) :
    (IsOpen A → ∀ x ∈ A, ∃ s : finseq ℕ, x ∈ cyl s ∧ cyl s ⊆ A) ∧
      (IsClosed A ↔ ∃ T : Set (finseq ℕ), IsSubtree T ∧ IsPruned T ∧ A = treeBody T) ∧
      (IsClopen A → ∀ x, (∃ s : finseq ℕ, x ∈ cyl s ∧ cyl s ⊆ A) ∨
        ∃ s : finseq ℕ, x ∈ cyl s ∧ cyl s ⊆ Aᶜ) := by
  refine ⟨fun h x hx ↦ exists_cyl_subset_of_mem_open hx h,
    baire_closed_iff_exists_pruned_tree_body A, ?_⟩
  intro h x
  by_cases hx : x ∈ A
  · exact Or.inl (exists_cyl_subset_of_mem_open hx h.isOpen)
  · exact Or.inr (exists_cyl_subset_of_mem_open hx h.isClosed.isOpen_compl)

end PolishSpaceBook
