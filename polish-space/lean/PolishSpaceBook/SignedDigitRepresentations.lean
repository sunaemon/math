module

public import PolishSpaceBook.BinaryRepresentations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
/-!
# Signed-digit names

The digits `0, 1, 2` code the signed digits `-1, 0, 1`. The proofs follow
finite partial sums and the book's redundant-digit selection algorithm.
The range, both continuous translators, and admissibility are proved. The
representation object uses the closed set of Baire names with all entries below
three. `signedDigitRepresentation_equivalent_cauchy` packages the explicit
translators for a dense interval sequence enumerating its dyadics. The final
unconditional admissibility theorem applies Cauchy lifting to real-valued maps
and then the same digit-selection translator.
-/

namespace PolishSpaceBook
open Set Filter Function Topology

abbrev signedDigitSpace := ℕ → Fin 3

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Signed digits avoid this obstruction. Encode the signed digits $-1,0,1$ by $0,1,2$, respectively,
    and use the same dyadic enumeration $\nu$.
-/
def signedDigitValue (d : Fin 3) : ℝ := (d.val : ℝ) - 1

theorem signedDigitValue_abs_le (d : Fin 3) : |signedDigitValue d| ≤ 1 := by
  fin_cases d <;> norm_num [signedDigitValue]

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    The standard repair is the **\termdefine{signed-digit representation}**
    $$\rho_{\mathrm{sd}} : \funcspace{\omega}{\{-1,0,1\}} \to [0,1], \qquad
    \rho_{\mathrm{sd}}(a)
    = \frac12 + \sum_{n \in \omega} a(n)\,2^{-(n+2)}.$$
-/
noncomputable def signedDigitExpansionValue (a : signedDigitSpace) : ℝ :=
  1 / 2 + ∑' n : ℕ, signedDigitValue (a n) * (1 / 2 : ℝ) ^ (n + 2)

noncomputable def signedDigitPartialSum (a : signedDigitSpace) (N : ℕ) : ℝ :=
  1 / 2 + ∑ n ∈ Finset.range N, signedDigitValue (a n) * (1 / 2 : ℝ) ^ (n + 2)

theorem hasSum_signedDigitWeights :
    HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 2)) (1 / 2) := by
  convert! hasSum_binaryWeights.mul_left (1 / 2) using 1
  · funext n
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    ring
  · ring

theorem signedDigitTerm_norm_le (a : signedDigitSpace) (n : ℕ) :
    ‖signedDigitValue (a n) * (1 / 2 : ℝ) ^ (n + 2)‖ ≤ (1 / 2 : ℝ) ^ (n + 2) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (n + 2))]
  exact mul_le_of_le_one_left (by positivity) (signedDigitValue_abs_le _)

theorem summable_signedDigitTerms (a : signedDigitSpace) :
    Summable (fun n : ℕ => signedDigitValue (a n) * (1 / 2 : ℝ) ^ (n + 2)) :=
  Summable.of_norm_bounded hasSum_signedDigitWeights.summable (signedDigitTerm_norm_le a)

theorem signedDigitExpansionValue_bounds (a : signedDigitSpace) :
    0 ≤ signedDigitExpansionValue a ∧ signedDigitExpansionValue a ≤ 1 := by
  have h := norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (signedDigitTerm_norm_le a) hasSum_signedDigitWeights.summable)
  have h' := Summable.tsum_le_tsum (signedDigitTerm_norm_le a)
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (signedDigitTerm_norm_le a) hasSum_signedDigitWeights.summable) hasSum_signedDigitWeights.summable
  rw [hasSum_signedDigitWeights.tsum_eq] at h'
  rw [Real.norm_eq_abs] at h
  have := abs_le.mp (h.trans h')
  dsimp [signedDigitExpansionValue]
  constructor <;> linarith

theorem continuous_signedDigitExpansionValue : Continuous signedDigitExpansionValue := by
  apply continuous_const.add
  have hc (n : ℕ) : Continuous (fun a : signedDigitSpace =>
      signedDigitValue (a n) * (1 / 2 : ℝ) ^ (n + 2)) :=
    ((continuous_of_discreteTopology : Continuous signedDigitValue).comp
      (continuous_apply n)).mul_const _
  exact continuous_tsum hc hasSum_signedDigitWeights.summable (fun n a => signedDigitTerm_norm_le a n)

noncomputable def selectSignedDigit (h r : ℝ) : Fin 3 :=
  if r < -h / 2 then 0 else if h / 2 < r then 2 else 1

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    If $a(n)=-1$, then $x-c_n < -h/4$, while the induction hypothesis gives $x-c_n \ge -2h$, so
    $$|x-(c_n-h)| \le h.$$
    The case $a(n)=1$ is symmetric. If $a(n)=0$, then $|x-c_n| \le 3h/4 < h$. Thus in every case
    $$|x-c_{n+1}| \le R_{n+1}, \qquad c_{n+1}=c_n+a(n)2^{-(n+2)}.$$
    Therefore $c_n \to x$, and the produced signed-digit sequence names $x$.
-/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Set $h:=2^{-(n+2)}$, so $R_n=2h$ and $R_{n+1}=h$. The workhorse bound gives
    $$|q_{p(n+4)}-x| \le 2^{-(n+4)} = h/4.$$
    Let $r:=q_{p(n+4)}-c_n$, and choose
    $$
    a(n)=
    \begin{cases}
    -1, & r < -h/2,\\
    1, & r > h/2,\\
    0, & |r| \le h/2.
    \end{cases}
    $$
-/
theorem selectSignedDigit_error {h x c t : ℝ} (_hh : 0 ≤ h)
    (hx : |x - c| ≤ 2 * h) (ht : |t - x| ≤ h / 4) :
    |x - (c + signedDigitValue (selectSignedDigit h (t - c)) * h)| ≤ h := by
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  obtain ⟨ht₁, ht₂⟩ := abs_le.mp ht
  unfold selectSignedDigit
  split_ifs with hneg hpos
  · norm_num [signedDigitValue]
    apply abs_le.mpr
    constructor <;> linarith
  · norm_num [signedDigitValue]
    apply abs_le.mpr
    constructor <;> linarith
  · norm_num [signedDigitValue]
    apply abs_le.mpr
    constructor <;> linarith

noncomputable def signedDigitCenter (t : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1 / 2
  | n + 1 => signedDigitCenter t n +
      signedDigitValue (selectSignedDigit ((1 / 2 : ℝ) ^ (n + 2))
        (t n - signedDigitCenter t n)) * (1 / 2 : ℝ) ^ (n + 2)

noncomputable def signedDigitsFromApproximations (t : ℕ → ℝ) : signedDigitSpace :=
  fun n => selectSignedDigit ((1 / 2 : ℝ) ^ (n + 2)) (t n - signedDigitCenter t n)

theorem signedDigitCenter_eq_partial (t : ℕ → ℝ) (n : ℕ) :
    signedDigitCenter t n = signedDigitPartialSum (signedDigitsFromApproximations t) n := by
  induction n with
  | zero => simp [signedDigitCenter, signedDigitPartialSum]
  | succ n ih =>
    simp only [signedDigitCenter, signedDigitPartialSum, Finset.sum_range_succ]
    simp only [signedDigitsFromApproximations]
    rw [ih]
    simp only [signedDigitPartialSum, signedDigitsFromApproximations]
    ring

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Conversely, $\rho_{[0,1]} \ContinuouslyReducesTo \rho_{\mathrm{sd}}$. Let $p$ be a Cauchy name for $x \in [0,1]$. We
    recursively choose signed digits $a(0),a(1),\ldots$. After $n$ digits, put
    $$c_n := \frac12 + \sum_{k<n} a(k)\,2^{-(k+2)}, \qquad R_n := 2^{-(n+1)},$$
    and maintain the invariant $|x-c_n| \le R_n$. It holds at $n=0$ because $c_0=1/2$ and $x \in [0,1]$.
-/
theorem signedDigitCenter_error {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (t : ℕ → ℝ) (ht : ∀ n, |t n - x| ≤ (1 / 2 : ℝ) ^ (n + 4)) (n : ℕ) :
    |x - signedDigitCenter t n| ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  induction n with
  | zero =>
    simp only [signedDigitCenter, zero_add, pow_one]
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  | succ n ih =>
    have heq : (1 / 2 : ℝ) ^ (n + 1) = 2 * (1 / 2 : ℝ) ^ (n + 2) := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]; ring
    have heq' : (1 / 2 : ℝ) ^ (n + 4) = (1 / 2 : ℝ) ^ (n + 2) / 4 := by
      rw [show n + 4 = (n + 2) + 2 by omega, pow_add]; ring
    have ht' := ht n
    rw [heq'] at ht'
    rw [heq] at ih
    exact selectSignedDigit_error (by positivity) ih ht'

theorem tendsto_signedDigitPartialSum (a : signedDigitSpace) :
    Tendsto (signedDigitPartialSum a) atTop (𝓝 (signedDigitExpansionValue a)) :=
  tendsto_const_nhds.add (summable_signedDigitTerms a).hasSum.tendsto_sum_nat

theorem signedDigitsFromApproximations_value {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (t : ℕ → ℝ) (ht : ∀ n, |t n - x| ≤ (1 / 2 : ℝ) ^ (n + 4)) :
    signedDigitExpansionValue (signedDigitsFromApproximations t) = x := by
  have hlim := (tendsto_signedDigitPartialSum (signedDigitsFromApproximations t)).const_sub x
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2)
  have hbound : |x - signedDigitExpansionValue (signedDigitsFromApproximations t)| ≤ 0 := by
    apply le_of_tendsto_of_tendsto hlim.abs hpow
    exact Filter.Eventually.of_forall (fun n => by
      dsimp only
      rw [← signedDigitCenter_eq_partial]
      exact signedDigitCenter_error hx t ht n)
  exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _)))).symm

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    The centering at $1/2$ ensures that every value lies in $[0,1]$, since
    $$\sum_{n \in \omega}2^{-(n+2)}=\frac12$$
    is the maximum displacement in either direction. The converse translation below constructs a signed-digit name for
    every $x\in[0,1]$, so the range is exactly $[0,1]$.
-/
theorem range_signedDigitExpansionValue : range signedDigitExpansionValue = Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro x ⟨a, rfl⟩
    exact signedDigitExpansionValue_bounds a
  · intro x hx
    exact ⟨signedDigitsFromApproximations (fun _ => x),
      signedDigitsFromApproximations_value hx _ (fun n => by simp)⟩

theorem signedDigitCenter_congr {t u : ℕ → ℝ} {N : ℕ} (h : ∀ n < N, t n = u n) :
    signedDigitCenter t N = signedDigitCenter u N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hc := ih (fun n hn => h n (by omega))
    simp only [signedDigitCenter, hc, h N (by omega)]

noncomputable def cauchySignedDigits (q : ℕ → ℝ) (p : baire_space) : signedDigitSpace :=
  signedDigitsFromApproximations (fun n => q (p (n + 4)))

theorem continuous_cauchySignedDigits (q : ℕ → ℝ) : Continuous (cauchySignedDigits q) := by
  apply continuous_pi
  intro n
  apply continuous_def.mpr
  intro U _
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  apply Filter.mem_of_superset ((baire_cyl_clopen (seqPrefix p (n + 5))).isOpen.mem_nhds
    (mem_cyl_seqPrefix p (n + 5)))
  intro p' hp'
  have heq (k : ℕ) (hk : k < n + 5) : p' k = p k :=
    (hp' k (by simpa using hk)).trans (seqPrefix_get p (by simpa using hk))
  have hc : signedDigitCenter (fun k => q (p' (k + 4))) n =
      signedDigitCenter (fun k => q (p (k + 4))) n :=
    signedDigitCenter_congr (fun k hk => by rw [heq (k + 4) (by omega)])
  change selectSignedDigit _ (q (p' (n + 4)) - _) ∈ U
  rw [heq (n + 4) (by omega), hc]
  exact hp

theorem cauchySignedDigits_value (q : ℕ → ℝ) (p : cauchyNameDomain q)
    (hp : cauchyRepresentation q p ∈ Icc (0 : ℝ) 1) :
    signedDigitExpansionValue (cauchySignedDigits q p.val) = cauchyRepresentation q p := by
  apply signedDigitsFromApproximations_value hp
  intro n
  exact cauchyRepresentation_dist_le q p (n + 4)

theorem signedDigitPartialSum_dyadic (a : signedDigitSpace) (N : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧ m < 2 ^ (N + 1) ∧
      signedDigitPartialSum a N = (m : ℝ) / (2 : ℝ) ^ (N + 1) := by
  induction N with
  | zero => exact ⟨1, by omega, by norm_num, by norm_num [signedDigitPartialSum]⟩
  | succ N ih =>
    obtain ⟨m, hm, hmb, heq⟩ := ih
    have hd := (a N).isLt
    have hsub : 1 ≤ 2 * m + (a N).val := by omega
    refine ⟨2 * m + (a N).val - 1, by omega, ?_, ?_⟩
    · rw [pow_succ]
      omega
    · have hs : signedDigitPartialSum a (N + 1) = signedDigitPartialSum a N +
          signedDigitValue (a N) * (1 / 2 : ℝ) ^ (N + 2) := by
        simp only [signedDigitPartialSum, Finset.sum_range_succ]
        ring
      rw [hs, heq, Nat.cast_sub hsub]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        signedDigitValue, one_div_pow]
      rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
      field_simp
      ring

theorem signedDigitPartialSum_tail_bound (a : signedDigitSpace) (N : ℕ) :
    dist (signedDigitPartialSum a N) (signedDigitExpansionValue a) ≤
      (1 / 2 : ℝ) ^ (N + 1) := by
  have hg : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ (k + N + 2)) ((1 / 2 : ℝ) ^ (N + 1)) := by
    convert! hasSum_signedDigitWeights.mul_left ((1 / 2 : ℝ) ^ N) using 1
    · funext k
      rw [show k + N + 2 = N + (k + 2) by omega, pow_add]
  have hnorm : Summable (fun k : ℕ =>
      ‖signedDigitValue (a (k + N)) * (1 / 2 : ℝ) ^ (k + N + 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => signedDigitTerm_norm_le a (k + N))
      hg.summable
  have hb := (norm_tsum_le_tsum_norm hnorm).trans
    (Summable.tsum_le_tsum (fun k => signedDigitTerm_norm_le a (k + N)) hnorm hg.summable)
  rw [hg.tsum_eq] at hb
  have hs := (summable_signedDigitTerms a).sum_add_tsum_nat_add N
  have heq : signedDigitExpansionValue a - signedDigitPartialSum a N =
      ∑' k : ℕ, signedDigitValue (a (k + N)) * (1 / 2 : ℝ) ^ (k + N + 2) := by
    dsimp only [signedDigitExpansionValue, signedDigitPartialSum]
    linarith [hs]
  rw [dist_comm, Real.dist_eq, heq]
  exact hb

theorem signedDigitPartialSum_dist_le (a : signedDigitSpace) {n m : ℕ} (hnm : n ≤ m) :
    dist (signedDigitPartialSum a n) (signedDigitPartialSum a m) ≤ (1 / 2 : ℝ) ^ n := by
  have ht := dist_triangle_right (signedDigitPartialSum a n) (signedDigitPartialSum a m)
    (signedDigitExpansionValue a)
  have hn := signedDigitPartialSum_tail_bound a n
  have hm := signedDigitPartialSum_tail_bound a m
  have hp : (1 / 2 : ℝ) ^ (m + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  simp only [pow_succ] at hn hm hp
  linarith

noncomputable def signedDigitCauchyIndices (q : ℕ → ℝ) (a : signedDigitSpace) : baire_space :=
  fun n => Function.invFun q (signedDigitPartialSum a n)

theorem signedDigitCauchyIndices_value (q : ℕ → ℝ) (hq : EnumeratesUnitDyadics q)
    (a : signedDigitSpace) (n : ℕ) : q (signedDigitCauchyIndices q a n) = signedDigitPartialSum a n := by
  obtain ⟨m, _, hm, hs⟩ := signedDigitPartialSum_dyadic a n
  obtain ⟨i, hi⟩ := hq m (n + 1) hm.le
  change q (Function.invFun q (signedDigitPartialSum a n)) = signedDigitPartialSum a n
  rw [← hi.trans hs.symm]
  exact Function.apply_invFun_apply

theorem continuous_signedDigitCauchyIndices (q : ℕ → ℝ) : Continuous (signedDigitCauchyIndices q) := by
  apply continuous_pi
  intro n
  apply continuous_def.mpr
  intro U _
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  apply Filter.mem_of_superset ((isClopen_cyl (seqPrefix a n)).isOpen.mem_nhds
    (mem_cyl_seqPrefix a n))
  intro b hb
  have hsum : signedDigitPartialSum b n = signedDigitPartialSum a n := by
    apply congrArg (fun x : ℝ => 1 / 2 + x)
    apply Finset.sum_congr rfl
    intro k hk
    have hlen : k < (seqPrefix a n).length := by simpa using Finset.mem_range.mp hk
    have heq : b k = a k := (hb k hlen).trans (seqPrefix_get a hlen)
    rw [heq]
  change Function.invFun q (signedDigitPartialSum b n) ∈ U
  rw [hsum]
  exact ha

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    **Equivalence with Cauchy.** First, $\rho_{\mathrm{sd}} \ContinuouslyReducesTo \rho_{[0,1]}$. Given a signed-digit name
    $a$, send it to the Cauchy name whose $N$-th approximation is the dyadic partial sum
    $$s_N := \frac12 + \sum_{n<N} a(n)\,2^{-(n+2)}.$$
    The omitted tail has absolute value at most $2^{-(N+1)}$, so the partial sums form a fast Cauchy sequence and converge
    to $\rho_{\mathrm{sd}}(a)$. Each $s_N$ depends only on the first $N$ digits, hence the translation from signed-digit
    names to Cauchy names is continuous.
-/
theorem signedDigitExpansion_factors_cauchy (q : ℕ → ℝ) (hq : EnumeratesUnitDyadics q) :
    ∃ f : signedDigitSpace → cauchyNameDomain q,
      Continuous f ∧ ∀ a, cauchyRepresentation q (f a) = signedDigitExpansionValue a := by
  have hfast (a : signedDigitSpace) : IsCauchyName q (signedDigitCauchyIndices q a) := by
    intro n m hnm
    rw [signedDigitCauchyIndices_value q hq, signedDigitCauchyIndices_value q hq]
    exact signedDigitPartialSum_dist_le a hnm
  let f : signedDigitSpace → cauchyNameDomain q := fun a => ⟨signedDigitCauchyIndices q a, hfast a⟩
  refine ⟨f, (continuous_signedDigitCauchyIndices q).subtype_mk _, ?_⟩
  intro a
  have hlim : Tendsto (fun n => q (signedDigitCauchyIndices q a n)) atTop
      (𝓝 (signedDigitExpansionValue a)) := by
    simp_rw [signedDigitCauchyIndices_value q hq]
    exact tendsto_signedDigitPartialSum a
  exact tendsto_nhds_unique (tendsto_cauchyRepresentation q (f a)) hlim

/-- Baire-space coding of the three-letter alphabet. -/
def signedDigitNameDomain : Set baire_space := {p | ∀ n, p n < 3}

def encodeSignedDigits (a : signedDigitSpace) : signedDigitNameDomain :=
  ⟨fun n => (a n).val, fun n => (a n).isLt⟩

def decodeSignedDigits (p : signedDigitNameDomain) : signedDigitSpace :=
  fun n => ⟨p.val n, p.property n⟩

theorem decode_encodeSignedDigits (a : signedDigitSpace) :
    decodeSignedDigits (encodeSignedDigits a) = a := rfl

theorem continuous_encodeSignedDigits : Continuous encodeSignedDigits := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun n =>
    (continuous_of_discreteTopology : Continuous (fun d : Fin 3 => d.val)).comp (continuous_apply n))

theorem continuous_decodeSignedDigits : Continuous decodeSignedDigits := by
  have h (n : ℕ) : Continuous (fun p : signedDigitNameDomain =>
      (⟨p.val n % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3)) :=
    (continuous_of_discreteTopology : Continuous (fun k : ℕ =>
      (⟨k % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3))).comp
      ((continuous_apply n).comp continuous_subtype_val)
  apply continuous_pi
  intro n
  convert h n using 1
  funext p
  apply Fin.ext
  exact (Nat.mod_eq_of_lt (p.property n)).symm

theorem isClosed_signedDigitNameDomain : IsClosed signedDigitNameDomain := by
  have heq : signedDigitNameDomain = ⋂ n : ℕ, {p : baire_space | p n < 3} := by
    ext p
    simp [signedDigitNameDomain]
  rw [heq]
  exact isClosed_iInter (fun n => (isClosed_discrete {k : ℕ | k < 3}).preimage
    (continuous_apply n : Continuous (fun p : baire_space => p n)))

/-- The finite alphabet and its closed Baire coding carry the same topology. -/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    Here $\funcspace{\omega}{\{-1,0,1\}}$ is a finite-alphabet sequence space, hence naturally homeomorphic to a closed
    subspace of $\BaireSpace$ after coding $-1,0,1$ by natural numbers.
-/
def signedDigitCoding : signedDigitSpace ≃ₜ signedDigitNameDomain where
  toFun := encodeSignedDigits
  invFun := decodeSignedDigits
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_encodeSignedDigits
  continuous_invFun := continuous_decodeSignedDigits

noncomputable def signedDigitRepresentation : Representation unitInterval where
  domain := signedDigitNameDomain
  toFun p := ⟨signedDigitExpansionValue (decodeSignedDigits p),
    signedDigitExpansionValue_bounds _⟩
  surjective := by
    intro x
    have hx : x.val ∈ range signedDigitExpansionValue := by
      rw [range_signedDigitExpansionValue]
      exact x.property
    obtain ⟨a, ha⟩ := hx
    refine ⟨encodeSignedDigits a, ?_⟩
    apply Subtype.ext
    exact ha

theorem signedDigitRepresentation_isContinuous : signedDigitRepresentation.IsContinuous :=
  (continuous_signedDigitExpansionValue.comp continuous_decodeSignedDigits).subtype_mk _

/-- Passing from the interval metric to its inherited real distance does not
change a name or the real value of its limit. -/
def intervalCauchyNameAsReal (q : ℕ → unitInterval) (p : cauchyNameDomain q) :
    cauchyNameDomain (fun n => (q n).val) := ⟨p.val, p.property⟩

theorem intervalCauchyNameAsReal_value (q : ℕ → unitInterval) (p : cauchyNameDomain q) :
    cauchyRepresentation (fun n => (q n).val) (intervalCauchyNameAsReal q p) =
      (cauchyRepresentation q p).val := by
  exact tendsto_nhds_unique (tendsto_cauchyRepresentation _ _)
    (continuous_subtype_val.tendsto _ |>.comp (tendsto_cauchyRepresentation q p))

/-- Both explicit translators, now with their Baire-space codes and the
interval-valued representation objects. -/
/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    The $n$-th output digit depends only on the finite tuple $p(0),\ldots,p(n+4)$ and the earlier output digits, so the
    translation is continuous. Hence $\rho_{\mathrm{sd}} \ContinuouslyEquivalentTo \rho_{[0,1]}$, so by the
    \termuseas{Kreitz--Weihrauch admissibility theorem}{Kreitz–Weihrauch theorem} $\rho_{\mathrm{sd}}$ is admissible.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The \termuse{signed-digit representation} from §{sec:signed-digit-representation} illustrates why admissibility
    matters. The \termuse{binary expansion} is a representation of $[0,1]$, but it is not admissible because dyadic
    rationals force discontinuous choices of tails. Signed digits add redundancy, making enough room for continuous choices
    and restoring equivalence with the Cauchy representation.
-/
theorem signedDigitRepresentation_equivalent_cauchy (q : ℕ → unitInterval) (hq : DenseRange q)
    (hdyadic : EnumeratesUnitDyadics (fun n => (q n).val)) :
    ContinuouslyEquivalent signedDigitRepresentation (cauchyRepresentationObject q hq) := by
  let qr : ℕ → ℝ := fun n => (q n).val
  obtain ⟨f, hf, hvalue⟩ := signedDigitExpansion_factors_cauchy qr hdyadic
  let F : signedDigitNameDomain → cauchyNameDomain q :=
    fun p => ⟨(f (decodeSignedDigits p)).val, (f (decodeSignedDigits p)).property⟩
  have hF : Continuous F :=
    (continuous_subtype_val.comp (hf.comp continuous_decodeSignedDigits)).subtype_mk _
  let G : cauchyNameDomain q → signedDigitNameDomain :=
    fun p => encodeSignedDigits (cauchySignedDigits qr p.val)
  have hG : Continuous G := continuous_encodeSignedDigits.comp
    ((continuous_cauchySignedDigits qr).comp continuous_subtype_val)
  constructor
  · refine ⟨F, hF, ?_⟩
    intro p
    apply Subtype.ext
    change (cauchyRepresentation q (F p)).val = signedDigitExpansionValue (decodeSignedDigits p)
    rw [← intervalCauchyNameAsReal_value]
    exact hvalue (decodeSignedDigits p)
  · refine ⟨G, hG, ?_⟩
    intro p
    apply Subtype.ext
    change signedDigitExpansionValue (cauchySignedDigits qr p.val) = (cauchyRepresentation q p).val
    have hb : cauchyRepresentation qr (intervalCauchyNameAsReal q p) ∈ Icc (0 : ℝ) 1 := by
      rw [intervalCauchyNameAsReal_value]
      exact (cauchyRepresentation q p).property
    exact (cauchySignedDigits_value qr (intervalCauchyNameAsReal q p) hb).trans
      (intervalCauchyNameAsReal_value q p)

/-- The book's admissibility conclusion from its two explicit translations. -/
theorem signedDigitRepresentation_admissible_of_dyadicEnumeration
    (q : ℕ → unitInterval) (hq : DenseRange q)
    (hdyadic : EnumeratesUnitDyadics (fun n => (q n).val)) :
    signedDigitRepresentation.IsAdmissible :=
  admissible_of_continuouslyEquivalent (cauchyRepresentationObject_isAdmissible q hq)
    (signedDigitRepresentation_equivalent_cauchy q hq hdyadic)

/-- The explicitly constructed Cauchy-to-signed-digit translator also lifts
partial maps, after applying the already proved Cauchy lifting theorem. -/
theorem signedDigitRepresentation_isAdmissible : signedDigitRepresentation.IsAdmissible := by
  apply (admissible_iff_partial_lifting _).mpr
  refine ⟨signedDigitRepresentation_isContinuous, ?_⟩
  intro E g hg
  let q : ℕ → ℝ := TopologicalSpace.denseSeq ℝ
  obtain ⟨f, hf, hvalue⟩ := cauchyRepresentation_lifts_partial q
    (TopologicalSpace.denseRange_denseSeq ℝ) (fun p => (g p).val)
    (continuous_subtype_val.comp hg)
  let h : E → signedDigitNameDomain :=
    fun p => encodeSignedDigits (cauchySignedDigits q (f p).val)
  refine ⟨h, continuous_encodeSignedDigits.comp ((continuous_cauchySignedDigits q).comp
    (continuous_subtype_val.comp hf)), ?_⟩
  intro p
  apply Subtype.ext
  change signedDigitExpansionValue (cauchySignedDigits q (f p).val) = (g p).val
  rw [cauchySignedDigits_value q (f p) (by rw [hvalue]; exact (g p).property), hvalue]

end PolishSpaceBook
