module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic

@[expose] public section

/-!
# Nested Stern--Brocot intervals

The interval construction in Chapter 3, including the determinant invariant,
the shrinking estimate after compactifying by `t ↦ t / (1 + t)`, and the unique
intersection on every infinite binary branch. `false` means L and `true` means R.
-/

namespace PolishSpaceBook

open Set

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Associate to each finite L/R word $w$ a closed interval $J_w$ in $[0,\infty]$. Start with
    $J_{\emptySeq}=[0/1,1/0]=[0,\infty]$, where $1/0$ denotes the endpoint $\infty$.
    If $J_w=[a/b,c/d]$, put $m=(a+c)/(b+d)$ and define
    $$J_{w\concat(L)}=[a/b,m],\qquad J_{w\concat(R)}=[m,c/d].$$
-/
/-- The endpoints `a/b < c/d`; `1/0` denotes the endpoint at infinity. -/
@[ext] structure MediantFrame where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  determinant : b * c = a * d + 1

namespace MediantFrame

def root : MediantFrame := ⟨0, 1, 1, 0, rfl⟩

def left (f : MediantFrame) : MediantFrame :=
  ⟨f.a, f.b, f.a + f.c, f.b + f.d, by nlinarith [f.determinant]⟩

def right (f : MediantFrame) : MediantFrame :=
  ⟨f.a + f.c, f.b + f.d, f.c, f.d, by nlinarith [f.determinant]⟩

def child (f : MediantFrame) (bit : Bool) : MediantFrame :=
  if bit then f.right else f.left

theorem left_mass_pos (f : MediantFrame) : 0 < f.a + f.b := by
  have := f.determinant
  by_contra h
  have : f.b = 0 := by omega
  simp [this] at *

theorem right_mass_pos (f : MediantFrame) : 0 < f.c + f.d := by
  have := f.determinant
  by_contra h
  have : f.c = 0 := by omega
  simp [this] at *

noncomputable def lower (f : MediantFrame) : ℝ := f.a / (f.a + f.b)
noncomputable def upper (f : MediantFrame) : ℝ := f.c / (f.c + f.d)
noncomputable def split (f : MediantFrame) : ℝ :=
  (f.a + f.c) / (f.a + f.b + (f.c + f.d))

theorem lower_nonneg (f : MediantFrame) : 0 ≤ f.lower := by
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem upper_le_one (f : MediantFrame) : f.upper ≤ 1 := by
  unfold upper
  have h : (0 : ℝ) < f.c + f.d := by exact_mod_cast f.right_mass_pos
  apply (div_le_one h).2
  linarith [Nat.cast_nonneg (α := ℝ) f.d]

theorem width (f : MediantFrame) :
    f.upper - f.lower = 1 / (((f.a + f.b : ℕ) : ℝ) * (f.c + f.d : ℕ)) := by
  have hl : (0 : ℝ) < f.a + f.b := by exact_mod_cast f.left_mass_pos
  have hr : (0 : ℝ) < f.c + f.d := by exact_mod_cast f.right_mass_pos
  have hd : (f.b : ℝ) * f.c = (f.a : ℝ) * f.d + 1 := by
    exact_mod_cast f.determinant
  unfold lower upper
  push_cast
  field_simp
  nlinarith

theorem lower_lt_upper (f : MediantFrame) : f.lower < f.upper := by
  have h := f.width
  have : (0 : ℝ) < 1 / (((f.a + f.b : ℕ) : ℝ) * (f.c + f.d : ℕ)) := by
    exact one_div_pos.mpr (mul_pos (by exact_mod_cast f.left_mass_pos)
      (by exact_mod_cast f.right_mass_pos))
  linarith

@[simp] theorem left_lower (f : MediantFrame) : f.left.lower = f.lower := rfl
@[simp] theorem right_upper (f : MediantFrame) : f.right.upper = f.upper := rfl

theorem left_upper (f : MediantFrame) : f.left.upper = f.split := by
  simp only [upper, left, split, Nat.cast_add]
  congr 1; ring

theorem right_lower (f : MediantFrame) : f.right.lower = f.split := by
  simp only [lower, right, split, Nat.cast_add]
  congr 1; ring

theorem lower_lt_split (f : MediantFrame) : f.lower < f.split := by
  simpa only [left_lower, left_upper] using f.left.lower_lt_upper

theorem split_lt_upper (f : MediantFrame) : f.split < f.upper := by
  simpa only [right_lower, right_upper] using f.right.lower_lt_upper

noncomputable def interval (f : MediantFrame) : Set ℝ := Icc f.lower f.upper

theorem child_subset (f : MediantFrame) (bit : Bool) :
    (f.child bit).interval ⊆ f.interval := by
  cases bit <;> simp only [child, Bool.false_eq_true, ↓reduceIte]
  · exact Icc_subset_Icc le_rfl (by rw [left_upper]; exact f.split_lt_upper.le)
  · exact Icc_subset_Icc (by rw [right_lower]; exact f.lower_lt_split.le) le_rfl

/-- Each endpoint fraction is reduced, by the determinant-one invariant. -/
theorem coprime_left (f : MediantFrame) : f.a.Coprime f.b := by
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_one.mp
  apply (Nat.dvd_add_iff_right
    (dvd_mul_of_dvd_left (Nat.gcd_dvd_left f.a f.b) f.d)).mpr
  rw [← f.determinant]
  exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right f.a f.b) f.c

theorem coprime_right (f : MediantFrame) : f.c.Coprime f.d := by
  rw [Nat.coprime_iff_gcd_eq_one]
  apply Nat.dvd_one.mp
  apply (Nat.dvd_add_iff_right
    (dvd_mul_of_dvd_right (Nat.gcd_dvd_right f.c f.d) f.a)).mpr
  rw [← f.determinant]
  exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left f.c f.d) f.b

/-- Repeated L moves keep the lower endpoint fixed and add its column `k` times. -/
def leftRun (f : MediantFrame) (k : ℕ) : MediantFrame :=
  ⟨f.a, f.b, f.c + k * f.a, f.d + k * f.b, by nlinarith [f.determinant]⟩

/-- Repeated R moves keep the upper endpoint fixed and add its column `k` times. -/
def rightRun (f : MediantFrame) (k : ℕ) : MediantFrame :=
  ⟨f.a + k * f.c, f.b + k * f.d, f.c, f.d, by nlinarith [f.determinant]⟩

theorem iterate_left (f : MediantFrame) (k : ℕ) : left^[k] f = f.leftRun k := by
  induction k with
  | zero => ext <;> simp [leftRun]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    ext <;> simp [left, leftRun] <;> ring

theorem iterate_right (f : MediantFrame) (k : ℕ) : right^[k] f = f.rightRun k := by
  induction k with
  | zero => ext <;> simp [rightRun]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    ext <;> simp [right, rightRun] <;> ring

end MediantFrame

/-- The frame reached after reading the first `n` letters. -/
def mediantBranchFrame (z : ℕ → Bool) : ℕ → MediantFrame
  | 0 => .root
  | n + 1 => (mediantBranchFrame z n).child (z n)

theorem mediantBranchFrame_mass (z : ℕ → Bool) (n : ℕ) :
    n + 2 ≤ (mediantBranchFrame z n).a + (mediantBranchFrame z n).b +
      ((mediantBranchFrame z n).c + (mediantBranchFrame z n).d) := by
  induction n with
  | zero => norm_num [mediantBranchFrame, MediantFrame.root]
  | succ n ih =>
    have hl := (mediantBranchFrame z n).left_mass_pos
    have hr := (mediantBranchFrame z n).right_mass_pos
    cases h : z n <;> simp only [mediantBranchFrame, MediantFrame.child, h,
      Bool.false_eq_true, ↓reduceIte, MediantFrame.left, MediantFrame.right] <;> omega

theorem mediantBranchFrame_product (z : ℕ → Bool) (n : ℕ) :
    n + 1 ≤ ((mediantBranchFrame z n).a + (mediantBranchFrame z n).b) *
      ((mediantBranchFrame z n).c + (mediantBranchFrame z n).d) := by
  have hl := (mediantBranchFrame z n).left_mass_pos
  have hr := (mediantBranchFrame z n).right_mass_pos
  have hs := mediantBranchFrame_mass z n
  nlinarith [Nat.mul_le_mul (show 1 ≤ (mediantBranchFrame z n).a +
    (mediantBranchFrame z n).b by omega)
    (show 1 ≤ (mediantBranchFrame z n).c + (mediantBranchFrame z n).d by omega)]

theorem mediantBranchFrame_width_le (z : ℕ → Bool) (n : ℕ) :
    (mediantBranchFrame z n).upper - (mediantBranchFrame z n).lower ≤
      1 / ((n : ℝ) + 1) := by
  rw [MediantFrame.width]
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast mediantBranchFrame_product z n

/-- All the compactified intervals on a branch have a unique common point. -/
theorem mediantBranchFrame_existsUnique (z : ℕ → Bool) :
    ∃! x : ℝ, ∀ n, x ∈ (mediantBranchFrame z n).interval := by
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => (mediantBranchFrame z n).interval)
    (fun n => (mediantBranchFrame z n).child_subset (z n))
    (fun n => nonempty_Icc.mpr (mediantBranchFrame z n).lower_lt_upper.le)
    isCompact_Icc (fun _ => isClosed_Icc)
  have hx' : ∀ n, x ∈ (mediantBranchFrame z n).interval := mem_iInter.mp hx
  refine ⟨x, hx', fun y hy => ?_⟩
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have hxn := hx' n
  have hyn := hy n
  have hw := mediantBranchFrame_width_le z n
  rw [Real.dist_eq, abs_le]
  exact ⟨by linarith [hxn.1, hxn.2, hyn.1, hyn.2],
    by linarith [hxn.1, hxn.2, hyn.1, hyn.2]⟩

/-- The compactifying order isomorphism sends `a/b` to `a/(a+b)`,
including the endpoint `1/0 = ∞`. -/
theorem mediantCompactify_fraction (a b : ℕ) (h : 0 < a + b) :
    (ENNReal.orderIsoUnitIntervalBirational ((a : ENNReal) / b) : ℝ) =
      (a : ℝ) / (a + b) := by
  by_cases ha : a = 0
  · subst a
    simp [ENNReal.orderIsoUnitIntervalBirational_apply_coe]
  by_cases hb : b = 0
  · subst b
    have han : (a : ENNReal) ≠ 0 := by exact_mod_cast ha
    have har : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    simp [ENNReal.div_zero han, har]
  have han : (a : ENNReal) ≠ 0 := by exact_mod_cast ha
  rw [ENNReal.orderIsoUnitIntervalBirational_apply_coe, ENNReal.toReal_inv,
    ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]
  · simp only [ENNReal.toReal_natCast, ENNReal.toReal_one]
    have har : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have hbr : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    field_simp
    ring
  · exact ENNReal.inv_ne_top.mpr
      (ENNReal.div_ne_zero.mpr ⟨han, ENNReal.natCast_ne_top b⟩)
  · simp

namespace MediantFrame

noncomputable def extendedLower (f : MediantFrame) : ENNReal := f.a / f.b
noncomputable def extendedUpper (f : MediantFrame) : ENNReal := f.c / f.d
noncomputable def extendedInterval (f : MediantFrame) : Set ENNReal :=
  Icc f.extendedLower f.extendedUpper

@[simp] theorem compactify_lower (f : MediantFrame) :
    (ENNReal.orderIsoUnitIntervalBirational f.extendedLower : ℝ) = f.lower :=
  mediantCompactify_fraction f.a f.b f.left_mass_pos

@[simp] theorem compactify_upper (f : MediantFrame) :
    (ENNReal.orderIsoUnitIntervalBirational f.extendedUpper : ℝ) = f.upper :=
  mediantCompactify_fraction f.c f.d f.right_mass_pos

theorem mem_extendedInterval_iff (f : MediantFrame) (x : ENNReal) :
    x ∈ f.extendedInterval ↔
      (ENNReal.orderIsoUnitIntervalBirational x : ℝ) ∈ f.interval := by
  change (_ ≤ x ∧ x ≤ _) ↔ (_ ≤ _ ∧ _ ≤ _)
  rw [← ENNReal.orderIsoUnitIntervalBirational.le_iff_le (x := f.extendedLower),
    ← ENNReal.orderIsoUnitIntervalBirational.le_iff_le (y := f.extendedUpper)]
  simp only [← Subtype.coe_le_coe, compactify_lower, compactify_upper]

end MediantFrame

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: proof
  excerpt: |
    The endpoint fractions satisfy $bc-ad=1$, initially and after either subdivision. In particular, they remain in
    lowest terms. The increasing homeomorphism $u(t)=t/(1+t)$, with $u(\infty)=1$, sends $J_w$ to a closed interval
    of length
    $$u(c/d)-u(a/b)=\frac{1}{(a+b)(c+d)}.$$
    This formula also holds for the endpoint $1/0$. Put $A=a+b$ and $B=c+d$. Initially $A=B=1$, and each subdivision
    replaces one of $A,B$ by $A+B$. Thus $A+B\ge |w|+2$, and
    $$AB\ge A+B-1\ge |w|+1.$$
    Along every branch, the image intervals are nonempty, nested, and have lengths tending to zero. Their intersection
    in $[0,1]$ is a singleton, and applying $u^{-1}$ proves the claim.
-/
/-- Nested mediant intervals have exactly one common point in `[0,∞]`.
The proof uses the determinant and shrinking compactified widths above. -/
/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: statement
  kind: lemma
  title: Nested mediant intervals
-/
theorem mediantBranchFrame_extended_existsUnique (z : ℕ → Bool) :
    ∃! x : ENNReal, ∀ n, x ∈ (mediantBranchFrame z n).extendedInterval := by
  obtain ⟨x, hx, huniq⟩ := mediantBranchFrame_existsUnique z
  have hx01 : x ∈ Icc (0 : ℝ) 1 := by
    simpa [mediantBranchFrame, MediantFrame.interval, MediantFrame.root,
      MediantFrame.lower, MediantFrame.upper] using hx 0
  let y := ENNReal.orderIsoUnitIntervalBirational.symm ⟨x, hx01⟩
  refine ⟨y, ?_, ?_⟩
  · intro n
    rw [MediantFrame.mem_extendedInterval_iff]
    simpa only [y, OrderIso.apply_symm_apply] using hx n
  · intro t ht
    apply ENNReal.orderIsoUnitIntervalBirational.injective
    apply Subtype.ext
    simpa only [y, OrderIso.apply_symm_apply] using
      huniq (ENNReal.orderIsoUnitIntervalBirational t)
        (fun n => ((mediantBranchFrame z n).mem_extendedInterval_iff t).mp (ht n))

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    Define the \termdefine{mediant-limit map}
    $$\MediantLimitMap : \CantorSpace \longrightarrow [0,\infty]$$
    by taking $\MediantLimitMap(z)$ to be the unique point of $\bigcap_n J_{\restrict{z}{n}}$.
-/
/-- The geometric mediant-limit map, defined on every binary branch. -/
noncomputable def mediantIntervalLimit (z : ℕ → Bool) : ENNReal :=
  (mediantBranchFrame_extended_existsUnique z).choose

theorem mediantIntervalLimit_mem (z : ℕ → Bool) (n : ℕ) :
    mediantIntervalLimit z ∈ (mediantBranchFrame z n).extendedInterval :=
  (mediantBranchFrame_extended_existsUnique z).choose_spec.1 n

theorem mediantIntervalLimit_eq_iff (z : ℕ → Bool) (x : ENNReal) :
    mediantIntervalLimit z = x ↔ ∀ n, x ∈ (mediantBranchFrame z n).extendedInterval := by
  constructor
  · rintro rfl
    exact mediantIntervalLimit_mem z
  · intro hx
    exact ((mediantBranchFrame_extended_existsUnique z).choose_spec.2 x hx).symm

theorem mediantBranchFrame_intervals_antitone (z : ℕ → Bool) :
    Antitone (fun n => (mediantBranchFrame z n).interval) :=
  antitone_nat_of_succ_le (fun n => (mediantBranchFrame z n).child_subset (z n))

theorem mediantBranchFrame_eq_of_agree {z t : ℕ → Bool} {n : ℕ}
    (h : ∀ i < n, z i = t i) : mediantBranchFrame z n = mediantBranchFrame t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [mediantBranchFrame, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Sharing `n` initial letters bounds the distance between compactified limits. -/
theorem mediantIntervalLimit_dist_le_of_agree {z t : ℕ → Bool} {n : ℕ}
    (h : ∀ i < n, z i = t i) :
    dist (ENNReal.orderIsoUnitIntervalBirational (mediantIntervalLimit z) : ℝ)
      (ENNReal.orderIsoUnitIntervalBirational (mediantIntervalLimit t) : ℝ) ≤
        1 / ((n : ℝ) + 1) := by
  have hz := ((mediantBranchFrame z n).mem_extendedInterval_iff _).mp
    (mediantIntervalLimit_mem z n)
  have ht := ((mediantBranchFrame t n).mem_extendedInterval_iff _).mp
    (mediantIntervalLimit_mem t n)
  rw [← mediantBranchFrame_eq_of_agree h] at ht
  have hw := mediantBranchFrame_width_le z n
  rw [Real.dist_eq, abs_le]
  exact ⟨by linarith [hz.1, hz.2, ht.1, ht.2],
    by linarith [hz.1, hz.2, ht.1, ht.2]⟩

theorem mediantBranchFrame_false_a (n : ℕ) :
    (mediantBranchFrame (fun _ => false) n).a = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem mediantBranchFrame_true_upper (n : ℕ) :
    (mediantBranchFrame (fun _ => true) n).extendedUpper = ⊤ := by
  have hc : ∀ n, (mediantBranchFrame (fun _ => true) n).c = 1 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => exact ih
  have hd : ∀ n, (mediantBranchFrame (fun _ => true) n).d = 0 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => exact ih
  simp [MediantFrame.extendedUpper, hc, hd]

/-@ booklink:
  source: polish-space-book/concrete-cantor-baire-models.md
  target: prose
  excerpt: |
    The constant branches satisfy $\MediantLimitMap(\wordRepeat{L}{\omega})=0$ and
    $\MediantLimitMap(\wordRepeat{R}{\omega})=\infty$, since their intervals retain the endpoint $0$ or $\infty$,
    respectively.
-/
theorem mediantIntervalLimit_allLeft : mediantIntervalLimit (fun _ => false) = 0 := by
  apply (mediantIntervalLimit_eq_iff _ _).mpr
  intro n
  constructor
  · simp [MediantFrame.extendedLower, mediantBranchFrame_false_a]
  · exact bot_le

theorem mediantIntervalLimit_allRight : mediantIntervalLimit (fun _ => true) = ⊤ := by
  apply (mediantIntervalLimit_eq_iff _ _).mpr
  intro n
  exact ⟨le_top, (mediantBranchFrame_true_upper n).ge⟩

/-- The unique limit of a branch retaining a lower endpoint forever. -/
theorem mediantIntervalLimit_of_allLeft_after {z : ℕ → Bool} (N : ℕ)
    (h : ∀ n, N ≤ n → z n = false) :
    mediantIntervalLimit z = (mediantBranchFrame z N).extendedLower := by
  apply (mediantIntervalLimit_eq_iff _ _).mpr
  have hret : ∀ k, (mediantBranchFrame z (N + k)).lower =
      (mediantBranchFrame z N).lower := by
    intro k; induction k with
    | zero => rfl
    | succ k ih =>
      change ((mediantBranchFrame z (N + k)).child (z (N + k))).lower = _
      rw [h (N + k) (by omega)]
      exact ih
  intro n
  rw [MediantFrame.mem_extendedInterval_iff, MediantFrame.compactify_lower]
  by_cases hn : N ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [← hret k]
    exact ⟨le_rfl, (mediantBranchFrame z (N + k)).lower_lt_upper.le⟩
  · exact mediantBranchFrame_intervals_antitone z (by omega : n ≤ N)
      ⟨le_rfl, (mediantBranchFrame z N).lower_lt_upper.le⟩

/-- The unique limit of a branch retaining an upper endpoint forever. -/
theorem mediantIntervalLimit_of_allRight_after {z : ℕ → Bool} (N : ℕ)
    (h : ∀ n, N ≤ n → z n = true) :
    mediantIntervalLimit z = (mediantBranchFrame z N).extendedUpper := by
  apply (mediantIntervalLimit_eq_iff _ _).mpr
  have hret : ∀ k, (mediantBranchFrame z (N + k)).upper =
      (mediantBranchFrame z N).upper := by
    intro k; induction k with
    | zero => rfl
    | succ k ih =>
      change ((mediantBranchFrame z (N + k)).child (z (N + k))).upper = _
      rw [h (N + k) (by omega)]
      exact ih
  intro n
  rw [MediantFrame.mem_extendedInterval_iff, MediantFrame.compactify_upper]
  by_cases hn : N ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [← hret k]
    exact ⟨(mediantBranchFrame z (N + k)).lower_lt_upper.le, le_rfl⟩
  · exact mediantBranchFrame_intervals_antitone z (by omega : n ≤ N)
      ⟨(mediantBranchFrame z N).lower_lt_upper.le, le_rfl⟩

/-- Retaining a lower endpoint forces every later letter to be L. -/
theorem mediantIntervalLimit_eq_lower_iff (z : ℕ → Bool) (N : ℕ) :
    mediantIntervalLimit z = (mediantBranchFrame z N).extendedLower ↔
      ∀ n, N ≤ n → z n = false := by
  refine ⟨fun heq => ?_, mediantIntervalLimit_of_allLeft_after N⟩
  have hx : (ENNReal.orderIsoUnitIntervalBirational (mediantIntervalLimit z) : ℝ) =
      (mediantBranchFrame z N).lower := by rw [heq, MediantFrame.compactify_lower]
  have hstep : ∀ k, (mediantBranchFrame z (N + k)).lower =
      (mediantBranchFrame z N).lower ∧ z (N + k) = false := by
    intro k
    have hret : (mediantBranchFrame z (N + k)).lower = (mediantBranchFrame z N).lower := by
      induction k with
      | zero => rfl
      | succ k ih =>
        have hmem := ((mediantBranchFrame z (N + k + 1)).mem_extendedInterval_iff _).mp
          (mediantIntervalLimit_mem z (N + k + 1))
        have hbit : z (N + k) = false := by
          cases hb : z (N + k)
          · rfl
          · have hl := hmem.1
            change ((mediantBranchFrame z (N + k)).child (z (N + k))).lower ≤ _ at hl
            rw [hb] at hl
            change (mediantBranchFrame z (N + k)).right.lower ≤ _ at hl
            rw [MediantFrame.right_lower, hx, ← ih] at hl
            exact False.elim ((mediantBranchFrame z (N + k)).lower_lt_split.not_ge hl)
        change ((mediantBranchFrame z (N + k)).child (z (N + k))).lower = _
        rw [hbit]
        exact ih
    refine ⟨hret, ?_⟩
    cases hb : z (N + k)
    · rfl
    · have hl := (((mediantBranchFrame z (N + k + 1)).mem_extendedInterval_iff _).mp
        (mediantIntervalLimit_mem z (N + k + 1))).1
      change ((mediantBranchFrame z (N + k)).child (z (N + k))).lower ≤ _ at hl
      rw [hb] at hl
      change (mediantBranchFrame z (N + k)).right.lower ≤ _ at hl
      rw [MediantFrame.right_lower, hx, ← hret] at hl
      exact False.elim ((mediantBranchFrame z (N + k)).lower_lt_split.not_ge hl)
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact (hstep k).2

/-- Retaining an upper endpoint forces every later letter to be R. -/
theorem mediantIntervalLimit_eq_upper_iff (z : ℕ → Bool) (N : ℕ) :
    mediantIntervalLimit z = (mediantBranchFrame z N).extendedUpper ↔
      ∀ n, N ≤ n → z n = true := by
  refine ⟨fun heq => ?_, mediantIntervalLimit_of_allRight_after N⟩
  have hx : (ENNReal.orderIsoUnitIntervalBirational (mediantIntervalLimit z) : ℝ) =
      (mediantBranchFrame z N).upper := by rw [heq, MediantFrame.compactify_upper]
  have hstep : ∀ k, (mediantBranchFrame z (N + k)).upper =
      (mediantBranchFrame z N).upper ∧ z (N + k) = true := by
    intro k
    have hret : (mediantBranchFrame z (N + k)).upper = (mediantBranchFrame z N).upper := by
      induction k with
      | zero => rfl
      | succ k ih =>
        have hmem := ((mediantBranchFrame z (N + k + 1)).mem_extendedInterval_iff _).mp
          (mediantIntervalLimit_mem z (N + k + 1))
        have hbit : z (N + k) = true := by
          cases hb : z (N + k)
          · have hu := hmem.2
            change _ ≤ ((mediantBranchFrame z (N + k)).child (z (N + k))).upper at hu
            rw [hb] at hu
            change _ ≤ (mediantBranchFrame z (N + k)).left.upper at hu
            rw [MediantFrame.left_upper, hx, ← ih] at hu
            exact False.elim ((mediantBranchFrame z (N + k)).split_lt_upper.not_ge hu)
          · rfl
        change ((mediantBranchFrame z (N + k)).child (z (N + k))).upper = _
        rw [hbit]
        exact ih
    refine ⟨hret, ?_⟩
    cases hb : z (N + k)
    · have hu := (((mediantBranchFrame z (N + k + 1)).mem_extendedInterval_iff _).mp
        (mediantIntervalLimit_mem z (N + k + 1))).2
      change _ ≤ ((mediantBranchFrame z (N + k)).child (z (N + k))).upper at hu
      rw [hb] at hu
      change _ ≤ (mediantBranchFrame z (N + k)).left.upper at hu
      rw [MediantFrame.left_upper, hx, ← hret] at hu
      exact False.elim ((mediantBranchFrame z (N + k)).split_lt_upper.not_ge hu)
    · rfl
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact (hstep k).2

/-- The mediant at a frame is shared by its two children. -/
noncomputable def MediantFrame.extendedSplit (f : MediantFrame) : ENNReal :=
  ((f.a + f.c : ℕ) : ENNReal) / (f.b + f.d : ℕ)

/-- After the split, retaining the mediant forces the opposite letter forever. -/
theorem mediantIntervalLimit_eq_split_iff (z : ℕ → Bool) (N : ℕ) :
    mediantIntervalLimit z = (mediantBranchFrame z N).extendedSplit ↔
      (z N = false ∧ ∀ n, N + 1 ≤ n → z n = true) ∨
      (z N = true ∧ ∀ n, N + 1 ≤ n → z n = false) := by
  cases hb : z N
  · have he : (mediantBranchFrame z (N + 1)).extendedUpper =
        (mediantBranchFrame z N).extendedSplit := by
      change ((mediantBranchFrame z N).child (z N)).extendedUpper = _
      rw [hb]
      rfl
    rw [← he, mediantIntervalLimit_eq_upper_iff]
    simp
  · have he : (mediantBranchFrame z (N + 1)).extendedLower =
        (mediantBranchFrame z N).extendedSplit := by
      change ((mediantBranchFrame z N).child (z N)).extendedLower = _
      rw [hb]
      rfl
    rw [← he, mediantIntervalLimit_eq_lower_iff]
    simp

theorem mediantIntervalLimit_eq_zero_iff (z : ℕ → Bool) :
    mediantIntervalLimit z = 0 ↔ z = fun _ => false := by
  have h := mediantIntervalLimit_eq_lower_iff z 0
  simpa [mediantBranchFrame, MediantFrame.extendedLower, MediantFrame.root,
    funext_iff] using h

theorem mediantIntervalLimit_eq_top_iff (z : ℕ → Bool) :
    mediantIntervalLimit z = ⊤ ↔ z = fun _ => true := by
  have h := mediantIntervalLimit_eq_upper_iff z 0
  simpa [mediantBranchFrame, MediantFrame.extendedUpper, MediantFrame.root,
    funext_iff] using h

end PolishSpaceBook
