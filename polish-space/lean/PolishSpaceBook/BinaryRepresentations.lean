module

public import PolishSpaceBook.CauchyNamesPolishRepresentations

@[expose] public section
/-!
# Binary names and Cauchy names

The book's real-valued formula for binary expansion has range exactly `[0,1]`.
The greedy recursion, finite-sum Cauchy translator, and dyadic first-digit
obstruction are proved explicitly. Interval values are viewed in `ℝ`; the
Cauchy estimates use its inherited distance. `EnumeratesUnitDyadics` records
exactly the dyadic enumeration property required by these constructions.
-/

namespace PolishSpaceBook
open Set Filter Function Topology

/-- Keep a constant initial name, then switch permanently to a nearby point. -/
def switchedCauchyName (i j N : ℕ) : baire_space := fun n => if n < N then i else j

theorem switchedCauchyName_isCauchy {X : Type*} [MetricSpace X] (q : ℕ → X)
    {i j N : ℕ} (hclose : dist (q i) (q j) ≤ (1 / 2 : ℝ) ^ N) :
    IsCauchyName q (switchedCauchyName i j N) := by
  intro n m hnm
  by_cases hn : n < N
  · by_cases hm : m < N
    · simp [switchedCauchyName, hn, hm]
    · simp only [switchedCauchyName, ite_eq_left hn, ite_eq_right hm]
      exact hclose.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn.le)
  · have hm : ¬ m < N := by omega
    simp [switchedCauchyName, hn, hm]

theorem switchedCauchyName_limit {X : Type*} [MetricSpace X] [CompleteSpace X]
    (q : ℕ → X) {i j N : ℕ} (hclose : dist (q i) (q j) ≤ (1 / 2 : ℝ) ^ N) :
    cauchyRepresentation q ⟨switchedCauchyName i j N, switchedCauchyName_isCauchy q hclose⟩ = q j := by
  have hlim : Tendsto (fun n => q (switchedCauchyName i j N n)) atTop (𝓝 (q j)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [switchedCauchyName, not_lt.mpr hn]
  exact tendsto_nhds_unique (tendsto_cauchyRepresentation q _) hlim

/-- No continuous leading-digit decision can separate names on both sides
of a point whose constant name can be extended to names on either side. -/
theorem no_continuous_cauchy_boundary_decision (q : ℕ → ℝ) (i : ℕ)
    (hboth : ∀ N : ℕ, ∃ j k,
      q j < q i ∧ q i < q k ∧
      dist (q i) (q j) ≤ (1 / 2 : ℝ) ^ N ∧
      dist (q i) (q k) ≤ (1 / 2 : ℝ) ^ N) :
    ¬ ∃ f : cauchyNameDomain q → Bool, Continuous f ∧
      (∀ p, cauchyRepresentation q p < q i → f p = false) ∧
      (∀ p, q i < cauchyRepresentation q p → f p = true) := by
  rintro ⟨f, hf, hleft, hright⟩
  have hi : IsCauchyName q (fun _ => i) := by
    intro n m hnm
    simp
  let p : cauchyNameDomain q := ⟨fun _ => i, hi⟩
  let U : Set (cauchyNameDomain q) := f ⁻¹' {f p}
  have hU : IsOpen U := (isOpen_discrete _).preimage hf
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hU
  have hpO : p.val ∈ O := by
    change p ∈ Subtype.val ⁻¹' O
    rw [hOU]
    exact rfl
  obtain ⟨s, hps, hsO⟩ := exists_cyl_subset_of_mem_open hpO hO
  obtain ⟨j, k, hj, hk, hdj, hdk⟩ := hboth s.length
  let pm : cauchyNameDomain q :=
    ⟨switchedCauchyName i j s.length, switchedCauchyName_isCauchy q hdj⟩
  let pp : cauchyNameDomain q :=
    ⟨switchedCauchyName i k s.length, switchedCauchyName_isCauchy q hdk⟩
  have hsame (l : ℕ) : switchedCauchyName i l s.length ∈ cyl s := by
    intro n hn
    simpa only [switchedCauchyName, ite_eq_left hn] using hps n hn
  have hmU : pm ∈ U := by rw [← hOU]; exact hsO (hsame j)
  have hpU : pp ∈ U := by rw [← hOU]; exact hsO (hsame k)
  have hm : f pm = false := hleft pm (by simpa [pm, switchedCauchyName_limit q hdj] using hj)
  have hp : f pp = true := hright pp (by simpa [pp, switchedCauchyName_limit q hdk] using hk)
  have heq : f pm = f pp := hmU.trans hpU.symm
  rw [hm, hp] at heq
  exact Bool.noConfusion heq
/-- Every dyadic point of the unit interval occurs in the dense enumeration. -/
def EnumeratesUnitDyadics (q : ℕ → ℝ) : Prop :=
  ∀ m n : ℕ, m ≤ 2 ^ n → ∃ i, q i = (m : ℝ) / (2 : ℝ) ^ n

/-- The two specific dyadic extensions used at the boundary one half. -/
theorem unitDyadics_half_extensions (q : ℕ → ℝ) (hq : EnumeratesUnitDyadics q)
    (N : ℕ) : ∃ j k,
      q j = 1 / 2 - (1 / 2 : ℝ) ^ (N + 3) ∧
      q k = 1 / 2 + (1 / 2 : ℝ) ^ (N + 3) := by
  have hpos : 0 < (2 : ℕ) ^ (N + 2) := pow_pos (by omega) _
  have hpow : (2 : ℕ) ^ (N + 3) = 2 ^ (N + 2) * 2 := pow_succ _ _
  obtain ⟨j, hj⟩ := hq (2 ^ (N + 2) - 1) (N + 3) (by omega)
  obtain ⟨k, hk⟩ := hq (2 ^ (N + 2) + 1) (N + 3) (by omega)
  have hden : (2 : ℝ) ^ (N + 2) ≠ 0 := by positivity
  refine ⟨j, k, ?_, ?_⟩
  · rw [hj, Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [show N + 3 = (N + 2) + 1 by omega, pow_succ, one_div_pow]
    field_simp
    ring
  · rw [hk, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [show N + 3 = (N + 2) + 1 by omega, pow_succ, one_div_pow]
    field_simp
    ring

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Let $p^*$ be the constant Cauchy name of $1/2$. Since $f(\cdot)(0)$ maps into the discrete space $\{0,1\}$ and is
    continuous at $p^*$, some finite prefix $s=\restrict{p^*}{N}$ decides the value of $f(p)(0)$ for every Cauchy name $p$
    extending $s$. Choose the dyadic rationals
    $$x^\pm=\frac12\pm2^{-(N+3)}.$$
    Extend $s$ to $p^\pm$ by using a fixed index of $x^\pm$ at every position from $N$ onwards.
    For $m\ge n$, the distance between the two approximations is zero if both positions precede $N$ or both are at
    least $N$. If $n<N\le m$, it is
    $$|x^\pm-1/2|=2^{-(N+3)}\le2^{-n}.$$
-/
theorem no_continuous_dyadic_cauchy_half_decision (q : ℕ → ℝ)
    (hq : EnumeratesUnitDyadics q) :
    ¬ ∃ f : cauchyNameDomain q → Bool, Continuous f ∧
      (∀ p, cauchyRepresentation q p < 1 / 2 → f p = false) ∧
      (∀ p, 1 / 2 < cauchyRepresentation q p → f p = true) := by
  obtain ⟨i, hi⟩ := hq 1 1 (by norm_num)
  norm_num at hi
  have hb : ∀ N : ℕ, ∃ j k,
      q j < q i ∧ q i < q k ∧
      dist (q i) (q j) ≤ (1 / 2 : ℝ) ^ N ∧
      dist (q i) (q k) ≤ (1 / 2 : ℝ) ^ N := by
    intro N
    obtain ⟨j, k, hj, hk⟩ := unitDyadics_half_extensions q hq N
    have hε : 0 < (1 / 2 : ℝ) ^ (N + 3) := by positivity
    have hsmall : (1 / 2 : ℝ) ^ (N + 3) ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    refine ⟨j, k, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · rw [Real.dist_eq, hi, hj]
      simpa [abs_of_nonneg hε.le] using hsmall
    · rw [Real.dist_eq, hi, hk]
      simpa [abs_of_nonneg hε.le, abs_neg] using hsmall
  simpa only [hi] using no_continuous_cauchy_boundary_decision q i hb

/-- Any binary value map with the usual leading-digit bounds has no
continuous translator from dyadic Cauchy names. -/
theorem no_continuous_binary_translator (q : ℕ → ℝ)
    (hq : EnumeratesUnitDyadics q)
    (b : cantor_space → ℝ)
    (hzero : ∀ a, a 0 = false → b a ≤ 1 / 2)
    (hone : ∀ a, a 0 = true → 1 / 2 ≤ b a) :
    ¬ ∃ f : cauchyNameDomain q → cantor_space,
      Continuous f ∧ ∀ p, b (f p) = cauchyRepresentation q p := by
  rintro ⟨f, hf, hcomm⟩
  apply no_continuous_dyadic_cauchy_half_decision q hq
  refine ⟨fun p => f p 0, (continuous_apply 0).comp hf, ?_, ?_⟩
  · intro p hp
    cases hd : f p 0 with
    | false => exact hd
    | true => have := hone (f p) hd; rw [hcomm] at this; linarith
  · intro p hp
    cases hd : f p 0 with
    | false => have := hzero (f p) hd; rw [hcomm] at this; linarith
    | true => exact hd
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    The \termdefine{binary expansion} is the representation of $[0, 1]$
    $$\rho_{\mathrm{bin}} : \CantorSpace \to [0, 1], \qquad \rho_{\mathrm{bin}}(p) \;=\; \sum_{n \in \omega} p(n) \cdot
    2^{-(n+1)}.$$
-/
/-- The real-valued binary expansion from the book. -/
noncomputable def binaryExpansionValue (a : cantor_space) : ℝ :=
  ∑' n : ℕ, (if a n then (1 : ℝ) else 0) * (1 / 2 : ℝ) ^ (n + 1)

theorem hasSum_binaryWeights : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1 := by
  convert! (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 2) using 1 <;>
    norm_num [pow_succ, mul_comm]

theorem binaryTerm_bounds (a : cantor_space) (n : ℕ) :
    0 ≤ (if a n then (1 : ℝ) else 0) * (1 / 2 : ℝ) ^ (n + 1) ∧
    (if a n then (1 : ℝ) else 0) * (1 / 2 : ℝ) ^ (n + 1) ≤
      (1 / 2 : ℝ) ^ (n + 1) := by
  cases a n <;> simp

theorem summable_binaryTerms (a : cantor_space) :
    Summable (fun n : ℕ => (if a n then (1 : ℝ) else 0) * (1 / 2 : ℝ) ^ (n + 1)) :=
  Summable.of_nonneg_of_le (fun n => (binaryTerm_bounds a n).1)
    (fun n => (binaryTerm_bounds a n).2) hasSum_binaryWeights.summable

theorem binaryExpansionValue_bounds (a : cantor_space) :
    0 ≤ binaryExpansionValue a ∧ binaryExpansionValue a ≤ 1 := by
  refine ⟨tsum_nonneg (fun n => (binaryTerm_bounds a n).1), ?_⟩
  simpa only [binaryExpansionValue, hasSum_binaryWeights.tsum_eq] using
    Summable.tsum_le_tsum (fun n => (binaryTerm_bounds a n).2)
      (summable_binaryTerms a) hasSum_binaryWeights.summable

theorem binaryExpansionValue_tail (a : cantor_space) :
    binaryExpansionValue a = (if a 0 then (1 : ℝ) else 0) / 2 +
      binaryExpansionValue (fun n => a (n + 1)) / 2 := by
  rw [binaryExpansionValue, (summable_binaryTerms a).tsum_eq_zero_add]
  have heq : (fun n : ℕ => (if a (n + 1) then (1 : ℝ) else 0) * (1 / 2 : ℝ) ^ (n + 1 + 1)) =
      fun n => (1 / 2 : ℝ) * ((if a (n + 1) then (1 : ℝ) else 0) * (1 / 2 : ℝ) ^ (n + 1)) := by
    funext n
    rw [pow_succ]
    ring
  rw [heq, tsum_mul_left]
  simp only [binaryExpansionValue]
  ring

theorem continuous_binaryExpansionValue : Continuous binaryExpansionValue := by
  have hc (n : ℕ) : Continuous (fun a : cantor_space =>
      (if a n then (1 : ℝ) else 0) * (1 / 2 : ℝ) ^ (n + 1)) := by
    exact ((continuous_of_discreteTopology : Continuous (fun b : Bool => if b then (1 : ℝ) else 0)).comp
      (continuous_apply n : Continuous (fun a : cantor_space => a n))).mul_const _
  apply continuous_tsum hc hasSum_binaryWeights.summable
  intro n a
  rw [Real.norm_eq_abs, abs_of_nonneg (binaryTerm_bounds a n).1]
  exact (binaryTerm_bounds a n).2

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Thus $p^\pm$ are Cauchy names of $x^\pm$. The prefix decision gives
    $f(p^-)(0)=f(p^+)(0)$. Correctness of the translator gives $f(p^-)(0)=0$ because $x^-<1/2$, and $f(p^+)(0)=1$ because
    $x^+>1/2$, a contradiction.
-/

theorem no_continuous_binaryExpansion_translator (q : ℕ → ℝ)
    (hq : EnumeratesUnitDyadics q) :
    ¬ ∃ f : cauchyNameDomain q → cantor_space,
      Continuous f ∧ ∀ p, binaryExpansionValue (f p) = cauchyRepresentation q p := by
  apply no_continuous_binary_translator q hq binaryExpansionValue
  · intro a ha
    rw [binaryExpansionValue_tail, ha]
    have := (binaryExpansionValue_bounds (fun n => a (n + 1))).2
    norm_num at *
    linarith
  · intro a ha
    rw [binaryExpansionValue_tail, ha]
    have := (binaryExpansionValue_bounds (fun n => a (n + 1))).1
    norm_num at *
    linarith
/-- The greedy finite approximation used to produce a binary name. -/
noncomputable def binaryGreedySum (x : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => if binaryGreedySum x n + (1 / 2 : ℝ) ^ (n + 1) ≤ x
      then binaryGreedySum x n + (1 / 2 : ℝ) ^ (n + 1) else binaryGreedySum x n

noncomputable def binaryGreedyDigits (x : ℝ) : cantor_space :=
  fun n => decide (binaryGreedySum x n + (1 / 2 : ℝ) ^ (n + 1) ≤ x)

theorem binaryGreedySum_error {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    0 ≤ x - binaryGreedySum x n ∧ x - binaryGreedySum x n ≤ (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simpa [binaryGreedySum] using hx
  | succ n ih =>
    rw [binaryGreedySum]
    split_ifs with h
    · rw [pow_succ] at h ⊢
      constructor <;> linarith
    · rw [pow_succ] at h ⊢
      constructor <;> linarith

theorem binaryGreedySum_eq_sum (x : ℝ) (n : ℕ) :
    binaryGreedySum x n = ∑ k ∈ Finset.range n,
      (if binaryGreedyDigits x k then (1 : ℝ) else 0) * (1 / 2 : ℝ) ^ (k + 1) := by
  induction n with
  | zero => simp [binaryGreedySum]
  | succ n ih =>
    rw [binaryGreedySum, Finset.sum_range_succ, ← ih]
    simp only [binaryGreedyDigits, decide_eq_true_eq]
    split_ifs <;> ring

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Every $x\in[0,1]$ has a binary name. Starting with $s_0=0$, choose $p(n)=1$ exactly when
    $s_n+2^{-(n+1)}\le x$, and put $s_{n+1}=s_n+p(n)2^{-(n+1)}$. Inductively $0\le x-s_n\le2^{-n}$, so $s_n\to x$.
-/
theorem binaryExpansionValue_greedy {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    binaryExpansionValue (binaryGreedyDigits x) = x := by
  have hlim : Tendsto (binaryGreedySum x) atTop (𝓝 x) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < ε :=
      exists_pow_lt_of_lt_one hε (by norm_num)
    refine ⟨N, fun n hn => ?_⟩
    have he := binaryGreedySum_error hx n
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg he.1]
    exact (he.2.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn)).trans_lt hN
  have hseries := (summable_binaryTerms (binaryGreedyDigits x)).hasSum.tendsto_sum_nat
  have heq : (fun n => ∑ k ∈ Finset.range n,
      (if binaryGreedyDigits x k then (1 : ℝ) else 0) * (1 / 2 : ℝ) ^ (k + 1)) =
        binaryGreedySum x := funext (fun n => (binaryGreedySum_eq_sum x n).symm)
  rw [heq] at hseries
  exact tendsto_nhds_unique hseries hlim

theorem range_binaryExpansionValue : range binaryExpansionValue = Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact binaryExpansionValue_bounds a
  · intro hx
    exact ⟨binaryGreedyDigits x, binaryExpansionValue_greedy hx⟩
noncomputable def binaryPartialSum (a : cantor_space) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (if a k then (1 : ℝ) else 0) * (1 / 2 : ℝ) ^ (k + 1)

theorem sum_binaryWeights (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ (k + 1) = 1 - (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem binaryPartialSum_dyadic (a : cantor_space) (N : ℕ) :
    ∃ m : ℕ, m ≤ 2 ^ N ∧ binaryPartialSum a N = (m : ℝ) / (2 : ℝ) ^ N := by
  induction N with
  | zero => exact ⟨0, by norm_num, by simp [binaryPartialSum]⟩
  | succ N ih =>
    obtain ⟨m, hm, heq⟩ := ih
    have hden : (2 : ℝ) ^ N ≠ 0 := by positivity
    rw [binaryPartialSum, Finset.sum_range_succ,
      ← show binaryPartialSum a N = ∑ k ∈ Finset.range N,
        (if a k then (1 : ℝ) else 0) * (1 / 2 : ℝ) ^ (k + 1) from rfl, heq]
    cases hd : a N with
    | false =>
      refine ⟨2 * m, ?_, ?_⟩
      · rw [pow_succ]; omega
      · simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero,
          Nat.cast_mul, Nat.cast_ofNat, pow_succ]
        field_simp
    | true =>
      have hm' : m < 2 ^ N := by
        -- The largest finite sum is strictly below one.
        have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range N) => (binaryTerm_bounds a k).2)
        rw [sum_binaryWeights] at hs
        change binaryPartialSum a N ≤ _ at hs
        rw [heq] at hs
        have hpos : 0 < (1 / 2 : ℝ) ^ N := by positivity
        have hlt : (m : ℝ) / (2 : ℝ) ^ N < 1 := by linarith
        have : (m : ℝ) < (2 : ℝ) ^ N := (div_lt_one (by positivity)).mp hlt
        exact_mod_cast this
      refine ⟨2 * m + 1, ?_, ?_⟩
      · rw [pow_succ]; omega
      · simp only [↓reduceIte, one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          Nat.cast_one, one_div_pow, pow_succ]
        field_simp

theorem binaryPartialSum_mono (a : cantor_space) : Monotone (binaryPartialSum a) := by
  intro n m hnm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
    (fun k _ _ => (binaryTerm_bounds a k).1)

theorem binaryPartialSum_tail_bound (a : cantor_space) (N : ℕ) :
    binaryExpansionValue a - binaryPartialSum a N ≤ (1 / 2 : ℝ) ^ N := by
  have hg : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ (k + N + 1)) ((1 / 2 : ℝ) ^ N) := by
    convert! hasSum_binaryWeights.mul_left ((1 / 2 : ℝ) ^ N) using 1
    · funext k
      rw [show k + N + 1 = N + (k + 1) by omega, pow_add]
    · ring
  have hs := (summable_binaryTerms a).sum_add_tsum_nat_add N
  have htail := Summable.tsum_le_tsum (fun k => (binaryTerm_bounds a (k + N)).2)
    ((summable_binaryTerms a).comp_injective (add_left_injective N)) hg.summable
  rw [hg.tsum_eq] at htail
  change binaryPartialSum a N + _ = binaryExpansionValue a at hs
  linarith

theorem binaryPartialSum_le_value (a : cantor_space) (N : ℕ) :
    binaryPartialSum a N ≤ binaryExpansionValue a :=
  (summable_binaryTerms a).sum_le_tsum (Finset.range N) (fun k _ => (binaryTerm_bounds a k).1)

theorem binaryPartialSum_dist_le (a : cantor_space) {n m : ℕ} (hnm : n ≤ m) :
    dist (binaryPartialSum a n) (binaryPartialSum a m) ≤ (1 / 2 : ℝ) ^ n := by
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (binaryPartialSum_mono a hnm))]
  have := binaryPartialSum_le_value a m
  have := binaryPartialSum_tail_bound a n
  linarith

noncomputable def binaryCauchyIndices (q : ℕ → ℝ) (a : cantor_space) : baire_space :=
  fun n => Function.invFun q (binaryPartialSum a n)

theorem binaryCauchyIndices_value (q : ℕ → ℝ) (hq : EnumeratesUnitDyadics q)
    (a : cantor_space) (n : ℕ) : q (binaryCauchyIndices q a n) = binaryPartialSum a n := by
  obtain ⟨m, hm, hs⟩ := binaryPartialSum_dyadic a n
  obtain ⟨i, hi⟩ := hq m n hm
  change q (Function.invFun q (binaryPartialSum a n)) = binaryPartialSum a n
  rw [← hi.trans hs.symm]
  exact Function.apply_invFun_apply

theorem continuous_binaryCauchyIndices (q : ℕ → ℝ) : Continuous (binaryCauchyIndices q) := by
  apply continuous_pi
  intro n
  apply continuous_def.mpr
  intro U _hU
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  apply Filter.mem_of_superset ((cantor_cyl_clopen (seqPrefix a n)).isOpen.mem_nhds
    (mem_cyl_seqPrefix a n))
  intro b hb
  have hsum : binaryPartialSum b n = binaryPartialSum a n := by
    apply Finset.sum_congr rfl
    intro k hk
    have hlen : k < (seqPrefix a n).length := by simpa using Finset.mem_range.mp hk
    have heq : b k = a k := (hb k hlen).trans (seqPrefix_get a hlen)
    rw [heq]
  change Function.invFun q (binaryPartialSum b n) ∈ U
  rw [hsum]
  exact ha

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Thus the partial sums form a Cauchy name. The map $f$ is continuous, and
    $\rho_{[0,1]} \circ f = \rho_{\mathrm{bin}}$. Hence
    $$\rho_{\mathrm{bin}} \ContinuouslyReducesTo \rho_{[0,1]}.$$
-/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    **Factoring through Cauchy.** Fix an enumeration $D = \IndexedFamily{q_n}{n\in\omega}$ of the dyadic rationals in $[0,
    1]$, and
    define $f : \CantorSpace \to \DomainOf{\rho_{[0,1]}}$ by sending $p$ to the sequence of indices for the partial sums
    $\sum_{k < n} p(k) \cdot 2^{-(k+1)}$. For $m\ge n$, the digits added between the two truncation stages satisfy
    $$
    \left|\sum_{k<m}p(k)2^{-(k+1)}-\sum_{k<n}p(k)2^{-(k+1)}\right|
    \le \sum_{n\le k<m}2^{-(k+1)}
    =2^{-n}-2^{-m}
    \le 2^{-n}.
    $$
-/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    This is exactly the formal sense in which "the binary expansion gives a Cauchy approximation by truncation" — truncation
    is the translation map.
-/
theorem binaryExpansion_factors_cauchy (q : ℕ → ℝ) (hq : EnumeratesUnitDyadics q) :
    ∃ f : cantor_space → cauchyNameDomain q,
      Continuous f ∧ ∀ a, cauchyRepresentation q (f a) = binaryExpansionValue a := by
  have hfast (a : cantor_space) : IsCauchyName q (binaryCauchyIndices q a) := by
    intro n m hnm
    rw [binaryCauchyIndices_value q hq, binaryCauchyIndices_value q hq]
    exact binaryPartialSum_dist_le a hnm
  let f : cantor_space → cauchyNameDomain q := fun a => ⟨binaryCauchyIndices q a, hfast a⟩
  refine ⟨f, (continuous_binaryCauchyIndices q).subtype_mk _, ?_⟩
  intro a
  have hlim : Tendsto (fun n => q (binaryCauchyIndices q a n)) atTop (𝓝 (binaryExpansionValue a)) := by
    simp_rw [binaryCauchyIndices_value q hq]
    exact (summable_binaryTerms a).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique (tendsto_cauchyRepresentation q (f a)) hlim
end PolishSpaceBook
