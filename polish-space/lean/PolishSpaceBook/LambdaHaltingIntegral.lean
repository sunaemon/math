module

public import PolishSpaceBook.LambdaHaltingReal
public import PolishSpaceBook.LambdaFourierL1
public import PolishSpaceBook.LambdaRationalExponential
public import PolishSpaceBook.LambdaComputableNames
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! # A continuous integrable function whose integral encodes halting

Nonnegative differences of the finite halting approximations are the masses of
triangular bumps centered at 3s. On each bounded window the series is finite.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA MeasureTheory Set Filter Topology
open scoped FourierTransform

/-- The unit-area triangular bump. -/
noncomputable def unitTent (x : ℝ) : ℝ := max (1-|x|) 0

theorem unitTent_nonneg (x : ℝ) : 0 ≤ unitTent x := le_max_right _ _

theorem unitTent_le_one (x : ℝ) : unitTent x ≤ 1 := by
  exact max_le (by linarith [abs_nonneg x]) (by norm_num)

theorem unitTent_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : unitTent x = 0 :=
  max_eq_right (by linarith)

theorem unitTent_continuous : Continuous unitTent := by unfold unitTent; fun_prop

theorem unitTent_lipschitz (x y : ℝ) : |unitTent x-unitTent y| ≤ |x-y| := by
  calc
    _ ≤ |(1-|x|)-(1-|y|)| := abs_max_sub_max_le_abs _ _ _
    _ = abs (|x|-|y|) := by rw [sub_sub_sub_cancel_left, abs_sub_comm]
    _ ≤ _ := abs_abs_sub_abs_le_abs_sub x y

theorem unitTent_compactSupport : HasCompactSupport unitTent := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1))
  intro x hx
  by_contra h
  have : 1 ≤ |x| := by
    simp only [mem_Icc,not_and_or,not_le] at h
    rcases h with h | h
    · exact (by linarith : 1 ≤ -x).trans (neg_le_abs x)
    · exact h.le.trans (le_abs_self x)
  exact hx (unitTent_eq_zero this)

theorem unitTent_integrable : Integrable unitTent :=
  unitTent_continuous.integrable_of_hasCompactSupport unitTent_compactSupport

theorem unitTent_integral : ∫ x, unitTent x = 1 := by
  have hs : ∫ x in Ioc (-1:ℝ) 1, unitTent x = ∫ x, unitTent x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      apply unitTent_eq_zero
      simp only [mem_Ioc,not_and_or,not_lt,not_le] at hx
      rcases hx with hx | hx
      · exact (by linarith : 1 ≤ -x).trans (neg_le_abs x)
      · exact hx.le.trans (le_abs_self x))
  rw [← hs,← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (unitTent_continuous.intervalIntegrable (-1) 0)
      (unitTent_continuous.intervalIntegrable 0 1)]
  have hl : ∫ x in (-1:ℝ)..0, unitTent x = ∫ x in (-1:ℝ)..0, (1+x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1:ℝ)≤0)] at hx
    simp [unitTent,abs_of_nonpos hx.2,max_eq_left (by linarith [hx.1] : 0 ≤ 1+x)]
  have hr : ∫ x in (0:ℝ)..1, unitTent x = ∫ x in (0:ℝ)..1, (1-x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hx
    simp [unitTent,abs_of_nonneg hx.1,max_eq_left (by linarith [hx.2] : 0 ≤ 1-x)]
  rw [hl,hr,intervalIntegral.integral_add (f := fun _ : ℝ => (1:ℝ)) (g := fun x : ℝ => x)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun x : ℝ => x)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
  norm_num [integral_id]

/-- No subtraction of natural-number values is used for the rational differences. -/
@[irreducible] def haltingMassCode (s : ℕ) : ℕ :=
  if s=0 then haltingApproximation 0
  else rationalSubtractCode (haltingApproximation s) (haltingApproximation (s-1))

noncomputable def haltingMass (s : ℕ) : ℝ := rationalPoint (haltingMassCode s)

theorem haltingMass_zero : haltingMass 0 = rationalPoint (haltingApproximation 0) := by
  simp [haltingMass,haltingMassCode]

theorem haltingMass_succ (s : ℕ) :
    haltingMass (s+1) = rationalPoint (haltingApproximation (s+1))-rationalPoint (haltingApproximation s) := by
  simp [haltingMass,haltingMassCode,rationalSubtractCode_value]

theorem haltingMass_nonneg (s : ℕ) : 0 ≤ haltingMass s := by
  cases s with
  | zero => rw [haltingMass_zero,haltingApproximation_value]; exact tsum_nonneg (haltingStageDigit_nonneg 0)
  | succ s => rw [haltingMass_succ]; exact sub_nonneg.mpr (haltingApproximation_monotone (by omega))

theorem haltingMass_partial (s : ℕ) :
    ∑ i ∈ Finset.range (s+1), haltingMass i = rationalPoint (haltingApproximation s) := by
  induction s with
  | zero => simp [haltingMass_zero]
  | succ s ih => rw [Finset.sum_range_succ,ih,haltingMass_succ]; ring

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Use the increasing rational approximation $a_s\uparrow\HaltingReal$ from §{sec:tte-real-examples}. Put
    $$c_0:=a_0,\qquad c_{s+1}:=a_{s+1}-a_s\quad(s\in\NN).$$
    These are computable nonnegative rationals, and their partial sums telescope:
    $$\sum_{s=0}^{N}c_s=a_N,\qquad
     \sum_{s=0}^{\infty}c_s=\HaltingReal
     \le\sum_{e=0}^{\infty}4^{-(e+1)}=\frac13.$$
    A closed term computes a code for $c_s$: at zero use the code for $a_0$; at a positive index compute the two
    successive approximants and subtract them using rational arithmetic.
-/
theorem haltingMass_hasSum : HasSum haltingMass (haltingSetReal diagonalHalts) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg haltingMass_nonneg _).mpr
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [haltingMass_partial] using haltingApproximation_tendsto

noncomputable def haltingBump (s : ℕ) (x : ℝ) : ℝ := haltingMass s * unitTent (x-3*s)

noncomputable def haltingIntegralFunction (x : ℝ) : ℝ := ∑' s, haltingBump s x

theorem haltingBump_nonneg (s : ℕ) (x : ℝ) : 0 ≤ haltingBump s x :=
  mul_nonneg (haltingMass_nonneg s) (unitTent_nonneg _)

theorem haltingBump_continuous (s : ℕ) : Continuous (haltingBump s) := by
  unfold haltingBump
  exact continuous_const.mul (unitTent_continuous.comp (continuous_id.sub continuous_const))

theorem haltingBump_integrable (s : ℕ) : Integrable (haltingBump s) :=
  (unitTent_integrable.comp_sub_right (3*s)).const_mul _

theorem haltingBump_integral (s : ℕ) : ∫ x, haltingBump s x = haltingMass s := by
  unfold haltingBump
  rw [integral_const_mul,integral_sub_right_eq_self,unitTent_integral,mul_one]

/-- A uniform finite bound valid on the entire window, including its endpoints. -/
theorem haltingBump_zero_after (R s : ℕ) (x : ℝ) (hx : |x| ≤ R) (hs : R+1 ≤ s) :
    haltingBump s x = 0 := by
  have hsr : (R:ℝ)+1 ≤ s := by exact_mod_cast hs
  have hxr := (le_abs_self x).trans hx
  have h : 1 ≤ |x-3*s| := by
    have : 1 ≤ -(x-3*s) := by nlinarith
    exact this.trans (neg_le_abs _)
  simp [haltingBump,unitTent_eq_zero h]

theorem haltingIntegralFunction_on_window (R : ℕ) (x : ℝ) (hx : |x| ≤ R) :
    haltingIntegralFunction x = ∑ s ∈ Finset.range (R+1), haltingBump s x := by
  exact tsum_eq_sum (fun s hs => haltingBump_zero_after R s x hx (by simpa using hs))

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Define the triangular bump and the function by
    $$\tau(x):=\max(1-|x|,0),\qquad
     f(x):=\sum_{s=0}^{\infty}c_s\tau(x-3s).$$
    The function is nonnegative. For an integer $R\ge0$, if $|x|\le R$ and $s\ge R+1$, then
    $$3s-x\ge3(R+1)-R\ge1,\qquad \tau(x-3s)=0.$$
    Consequently,
    $$f(x)=\sum_{s=0}^{R}c_s\tau(x-3s)\qquad(|x|\le R).$$
    This is an exact finite description on the whole interval, including its endpoints. Each summand is continuous,
    and every point has a neighborhood in some such interval, so $f$ is continuous.
-/
theorem haltingIntegralFunction_continuous : Continuous haltingIntegralFunction := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨R,hR⟩ := exists_nat_gt (|x|+1)
  apply (Continuous.continuousAt (continuous_finsetSum (Finset.range (R+1))
    (fun s _ => haltingBump_continuous s))).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Ioo (x-1) (x+1) by constructor <;> linarith)] with y hy
  apply haltingIntegralFunction_on_window
  rw [abs_le]
  constructor <;> linarith [le_abs_self x,neg_le_abs x,hy.1,hy.2]

theorem haltingIntegralFunction_nonneg (x : ℝ) : 0 ≤ haltingIntegralFunction x :=
  tsum_nonneg (fun s => haltingBump_nonneg s x)

theorem haltingBump_summable (x : ℝ) : Summable (fun s => haltingBump s x) := by
  obtain ⟨R,hR⟩ := exists_nat_gt |x|
  exact summable_of_ne_finset_zero (s := Finset.range (R+1)) (fun s hs =>
    haltingBump_zero_after R s x hR.le (by simpa using hs))

/-- Monotone convergence for the nonnegative series controls its total mass. -/
theorem haltingIntegralFunction_lintegral :
    ∫⁻ x, ENNReal.ofReal (haltingIntegralFunction x) = ENNReal.ofReal (haltingSetReal diagonalHalts) := by
  simp_rw [haltingIntegralFunction,ENNReal.ofReal_tsum_of_nonneg (fun s => haltingBump_nonneg s _) (haltingBump_summable _)]
  rw [lintegral_tsum (fun s => (haltingBump_continuous s).measurable.ennreal_ofReal.aemeasurable)]
  simp_rw [← ofReal_integral_eq_lintegral_ofReal (haltingBump_integrable _)
    (Eventually.of_forall (haltingBump_nonneg _)),haltingBump_integral]
  rw [← ENNReal.ofReal_tsum_of_nonneg haltingMass_nonneg haltingMass_hasSum.summable,haltingMass_hasSum.tsum_eq]

theorem haltingIntegralFunction_integrable : Integrable haltingIntegralFunction := by
  refine ⟨haltingIntegralFunction_continuous.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall haltingIntegralFunction_nonneg),haltingIntegralFunction_lintegral]
  exact ENNReal.ofReal_lt_top

theorem haltingIntegralFunction_integral : ∫ x, haltingIntegralFunction x = haltingSetReal diagonalHalts := by
  have h := haltingIntegralFunction_lintegral
  rw [← ofReal_integral_eq_lintegral_ofReal haltingIntegralFunction_integrable
    (Eventually.of_forall haltingIntegralFunction_nonneg)] at h
  have ht := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg haltingIntegralFunction_nonneg),
    ENNReal.toReal_ofReal (show 0 ≤ haltingSetReal diagonalHalts from tsum_nonneg (haltingDigit_nonneg diagonalHalts))] using ht

/-- The total mass is bounded independently of any halting information. -/
theorem haltingSetReal_le_one : haltingSetReal diagonalHalts ≤ 1 := by
  have hw : ∑' e, haltingWeight e = (1/3:ℝ) := by
    simp only [haltingWeight,pow_succ]
    rw [tsum_mul_right,tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num)]
    norm_num
  exact ((haltingDigit_summable diagonalHalts).tsum_le_tsum (haltingDigit_le diagonalHalts)
    haltingWeight_summable).trans (by rw [hw]; norm_num)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    There is also a global Lipschitz bound. Taking the maximum with zero does not increase distances, and
    $\bigl||u|-|v|\bigr|\le|u-v|$, so $|\tau(u)-\tau(v)|\le|u-v|$.
    For any $x,y$, choose an integer $R$ containing both in the preceding window. Then
    $$\begin{aligned}
    |f(x)-f(y)|&\le\sum_{s=0}^{R}c_s|\tau(x-3s)-\tau(y-3s)|\\
     &\le a_R|x-y|\le|x-y|.
    \end{aligned}$$
-/
theorem haltingIntegralFunction_lipschitz (x y : ℝ) :
    |haltingIntegralFunction x-haltingIntegralFunction y| ≤ |x-y| := by
  obtain ⟨R,hR⟩ := exists_nat_gt (max |x| |y|)
  rw [haltingIntegralFunction_on_window R x ((le_max_left _ _).trans hR.le),
    haltingIntegralFunction_on_window R y ((le_max_right _ _).trans hR.le),← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ s ∈ Finset.range (R+1), |haltingBump s x-haltingBump s y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ Finset.range (R+1), haltingMass s*|x-y| := by
      apply Finset.sum_le_sum
      intro s _
      rw [haltingBump,haltingBump,← mul_sub,abs_mul,abs_of_nonneg (haltingMass_nonneg s)]
      apply mul_le_mul_of_nonneg_left _ (haltingMass_nonneg s)
      simpa only [sub_sub_sub_cancel_right] using unitTent_lipschitz (x-3*s) (y-3*s)
    _ = rationalPoint (haltingApproximation R)*|x-y| := by rw [← Finset.sum_mul,haltingMass_partial]
    _ ≤ 1*|x-y| := mul_le_mul_of_nonneg_right ((haltingApproximation_le R).trans haltingSetReal_le_one) (abs_nonneg _)
    _ = _ := one_mul _

def haltingMassProgram : AlphaTerm := numericalIfZero numericalIdentity
  (numericalCompose haltingApproximationProgram (numericalConstant 0))
  (numericalCompose rationalSubtractProgram (pairNumerical haltingApproximationProgram
    (numericalCompose haltingApproximationProgram predecessorTerm)))

theorem haltingMassProgram_computes : NumericalComputes haltingMassProgram haltingMassCode := by
  have h := numericalIfZero_computes numericalIdentity_computes
    (haltingApproximation_computes.comp (numericalConstant_computes 0))
    (rationalSubtractProgram_computes.comp (haltingApproximation_computes.pair
      (haltingApproximation_computes.comp predecessor_computes)))
  refine ⟨h.1,fun s => ?_⟩
  simpa only [haltingMassProgram,haltingMassCode,Nat.unpair_pair,id_eq] using h.2 s

/-- Select max(q,0) by the existing rational comparison program. -/
def rationalPositivePartCode (c : ℕ) : ℕ := if 0 < (RationalCode.ofNat c).value then c else 0

def rationalPositivePartProgram : AlphaTerm := numericalIfZero
  (numericalCompose rationalLessTerm (pairNumerical (numericalConstant 0) numericalIdentity))
  (numericalConstant 0) numericalIdentity

theorem rationalPositivePartProgram_computes :
    NumericalComputes rationalPositivePartProgram rationalPositivePartCode := by
  have h := numericalIfZero_computes
    (rationalLess_computes.comp ((numericalConstant_computes 0).pair numericalIdentity_computes))
    (numericalConstant_computes 0) numericalIdentity_computes
  refine ⟨h.1,fun c => ?_⟩
  have h0 : (RationalCode.ofNat 0).value = 0 := by norm_num [RationalCode.ofNat,RationalCode.value]
  by_cases hc : 0 < (RationalCode.ofNat c).value <;>
    simpa only [rationalPositivePartProgram,rationalPositivePartCode,Nat.unpair_pair,h0,hc,
      ite_true,ite_false,one_ne_zero,id_eq] using h.2 c

theorem rationalPositivePartCode_value (c : ℕ) :
    rationalPoint (rationalPositivePartCode c) = max (rationalPoint c) 0 := by
  have hc : (0:ℚ) < (RationalCode.ofNat c).value ↔ 0 < rationalPoint c := by
    unfold rationalPoint
    exact_mod_cast (Iff.rfl : (0:ℚ) < (RationalCode.ofNat c).value ↔ 0 < (RationalCode.ofNat c).value)
  unfold rationalPositivePartCode
  split_ifs with h
  · exact (max_eq_left (hc.mp h).le).symm
  · rw [max_eq_right (le_of_not_gt (mt hc.mpr h))]
    norm_num [rationalPoint,RationalCode.ofNat,RationalCode.value]

@[irreducible] def unitTentCode (c : ℕ) : ℕ :=
  rationalPositivePartCode (rationalAddCode rationalOneCode (rationalNegativeAbsCode c))

def unitTentProgram : AlphaTerm := numericalCompose rationalPositivePartProgram
  (numericalCompose rationalAddTerm (pairNumerical (numericalConstant rationalOneCode) rationalNegativeAbsProgram))

theorem unitTentProgram_computes : NumericalComputes unitTentProgram unitTentCode := by
  have h := rationalPositivePartProgram_computes.comp
    (rationalAdd_computes.comp ((numericalConstant_computes rationalOneCode).pair rationalNegativeAbsProgram_computes))
  refine ⟨h.1,fun c => ?_⟩
  simpa only [unitTentProgram,unitTentCode,rationalAddCode,Nat.unpair_pair] using h.2 c

theorem unitTentCode_value (c : ℕ) : rationalPoint (unitTentCode c) = unitTent (rationalPoint c) := by
  rw [unitTentCode,rationalPositivePartCode_value,rationalAddCode_value,rationalNegativeAbsCode_value]
  have h1 : rationalPoint rationalOneCode = 1 := by
    norm_num [rationalPoint,rationalOneCode,RationalCode.ofNat_natCode,RationalCode.value]
  rw [h1]
  rfl

def tripleCenterCode (s : ℕ) : ℕ := Nat.pair (Nat.pair (3*s) 0) 0

def tripleCenterProgram : AlphaTerm := pairNumerical
  (pairNumerical (mulNumerical (numericalConstant 3) numericalIdentity) (numericalConstant 0)) (numericalConstant 0)

theorem tripleCenterProgram_computes : NumericalComputes tripleCenterProgram tripleCenterCode :=
  (((numericalConstant_computes 3).mul numericalIdentity_computes).pair (numericalConstant_computes 0)).pair
    (numericalConstant_computes 0)

theorem tripleCenterCode_value (s : ℕ) : rationalPoint (tripleCenterCode s) = 3*s := by
  simp [tripleCenterCode,rationalPoint,RationalCode.ofNat,RationalCode.value]

/-- The input is (rational point code,bump index); the output is a real complex code. -/
@[irreducible] def haltingBumpCode (c s : ℕ) : ℕ := Nat.pair
  (rationalMultiplyCode (haltingMassCode s) (unitTentCode (rationalSubtractCode c (tripleCenterCode s)))) 0

def haltingBumpProgram : AlphaTerm :=
  let C := numericalProjectionTerm true
  let S := numericalProjectionTerm false
  pairNumerical (numericalCompose rationalMultiplyProgram
    (pairNumerical (numericalCompose haltingMassProgram S)
      (numericalCompose unitTentProgram (numericalCompose rationalSubtractProgram
        (pairNumerical C (numericalCompose tripleCenterProgram S)))))) (numericalConstant 0)

theorem haltingBumpProgram_computes : NumericalComputes haltingBumpProgram
    (fun p => haltingBumpCode p.unpair.1 p.unpair.2) := by
  have hc := projection_computes true
  have hs := projection_computes false
  have h := (rationalMultiplyProgram_computes.comp ((haltingMassProgram_computes.comp hs).pair
    (unitTentProgram_computes.comp (rationalSubtractProgram_computes.comp
      (hc.pair (tripleCenterProgram_computes.comp hs)))))).pair (numericalConstant_computes 0)
  refine ⟨h.1,fun p => ?_⟩
  simpa only [haltingBumpProgram,haltingBumpCode,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using h.2 p

theorem haltingBumpCode_value (c s : ℕ) :
    complexRationalPoint (haltingBumpCode c s) = (haltingBump s (rationalPoint c):ℂ) := by
  simp only [haltingBumpCode,complexRationalPoint,Nat.unpair_pair,rationalMultiplyCode_value,
    unitTentCode_value,rationalSubtractCode_value,tripleCenterCode_value]
  have h0 : rationalPoint 0 = 0 := by norm_num [rationalPoint,RationalCode.ofNat,RationalCode.value]
  simp only [h0,Complex.ofReal_zero,zero_mul,add_zero]
  rfl

@[irreducible] def haltingFiniteSumCode (c N : ℕ) : ℕ :=
  complexSumCode (fun p => haltingBumpCode p.unpair.1 p.unpair.2) c N

theorem haltingFiniteSumProgram_computes : NumericalComputes (complexSumProgram haltingBumpProgram)
    (fun p => haltingFiniteSumCode p.unpair.1 p.unpair.2) := by
  simpa only [haltingFiniteSumCode] using complexSumProgram_computes haltingBumpProgram_computes

theorem haltingFiniteSumCode_value (c N : ℕ) :
    complexRationalPoint (haltingFiniteSumCode c N) = ∑ s ∈ Finset.range N, (haltingBump s (rationalPoint c):ℂ) := by
  rw [haltingFiniteSumCode,complexSumCode_value]
  simp only [Nat.unpair_pair,haltingBumpCode_value]

@[irreducible] def haltingEvaluationCode (c : ℕ) : ℕ :=
  (haltingFiniteSumCode c (rationalMagnitudeBound c+1)).unpair.1

def haltingEvaluationProgram : AlphaTerm := numericalCompose (numericalProjectionTerm true)
  (numericalCompose (complexSumProgram haltingBumpProgram) (pairNumerical numericalIdentity
    (numericalCompose successorTerm rationalMagnitudeProgram)))

theorem haltingEvaluationProgram_computes : NumericalComputes haltingEvaluationProgram haltingEvaluationCode := by
  have h := (projection_computes true).comp (haltingFiniteSumProgram_computes.comp
    (numericalIdentity_computes.pair (successor_computes.comp rationalMagnitudeProgram_computes)))
  refine ⟨h.1,fun c => ?_⟩
  simpa only [haltingEvaluationProgram,haltingEvaluationCode,Nat.unpair_pair,ite_true,id_eq] using h.2 c

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    To evaluate at a rational input with code $i=\RationalCode{u}{v}{w}$, take $R=u+v$, which bounds $|q_i|$.
    For each $s\le R$, compute $c_s$, subtract $3s$ from $q_i$, take the absolute value, subtract it from one, and
    replace the result by zero if it is negative. Multiply it by $c_s$ and add the terms using a finite recursion
    that retains $i$ as its parameter. All these operations use the closed rational programs already constructed.
    Thus a closed term $E$ computes a numerical function $g$ with
    $$E\ChurchNumeral{i}\to_\beta^*\ChurchNumeral{g(i)},\qquad q_{g(i)}=f(q_i).$$
-/
theorem haltingEvaluationCode_value (c : ℕ) :
    rationalPoint (haltingEvaluationCode c) = haltingIntegralFunction (rationalPoint c) := by
  have hr := congrArg Complex.re (haltingFiniteSumCode_value c (rationalMagnitudeBound c+1))
  have hre (a : ℕ) : (complexRationalPoint a).re = rationalPoint a.unpair.1 := by
    simp [complexRationalPoint]
  simp only [hre,Complex.re_sum,Complex.ofReal_re] at hr
  rw [haltingEvaluationCode,hr,haltingIntegralFunction_on_window (rationalMagnitudeBound c)
    (rationalPoint c) (rationalPoint_abs_le_magnitude c)]

/-- Exact evaluation and the global Lipschitz estimate preserve fast Cauchy names. -/
def haltingFunctionName (p : realRepresentation.domain) : realRepresentation.domain :=
  ⟨fun n => haltingEvaluationCode (p.val n),by
    intro n m hnm
    simp only [Real.dist_eq,haltingEvaluationCode_value]
    exact (haltingIntegralFunction_lipschitz _ _).trans (p.property n m hnm)⟩

def haltingFunctionProgram : AlphaTerm := mapOutputProgram haltingEvaluationProgram
  (queryOutputProgram (liftNumericalProgram numericalIdentity))

theorem haltingFunctionProgram_computes :
    TypeTwoComputes haltingFunctionProgram (fun p => (haltingFunctionName p).val) := by
  have h := numericalIdentity_computes.uniform.query.map haltingEvaluationProgram_computes
  exact typeTwoComputes_iff_runs.mpr ⟨h.1,fun p n => h.2 p.val n⟩

theorem haltingFunctionName_realizes :
    Realizes realRepresentation realRepresentation haltingFunctionName haltingIntegralFunction := by
  intro p
  apply tendsto_nhds_unique (tendsto_cauchyRepresentation rationalPoint (haltingFunctionName p))
  have h := haltingIntegralFunction_continuous.continuousAt.tendsto.comp
    (tendsto_cauchyRepresentation rationalPoint p)
  simpa only [Function.comp_def,haltingFunctionName,haltingEvaluationCode_value,realRepresentation,cauchyRepresentationObject] using h

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    If $p$ is a Cauchy name of $x$, set $F(p)(n):=g(p(n))$. The closed term
    $$P:=\lambdaab{o}{\lambdaab{n}{E(on)}}$$
    computes this transformation by one input query followed by exact rational evaluation. For $m\ge n$,
    $$|q_{F(p)(n)}-q_{F(p)(m)}|
     =|f(q_{p(n)})-f(q_{p(m)})|\le|q_{p(n)}-q_{p(m)}|\le2^{-n}.$$
    Continuity gives $q_{F(p)(n)}\to f(x)$, so the output is a Cauchy name of $f(x)$.
    This proves that $f$ is computable as a map on represented real numbers.
-/
theorem haltingIntegralFunction_hasComputableRealizer :
    HasComputableRealizer realRepresentation realRepresentation haltingIntegralFunction :=
  ⟨haltingFunctionName,⟨haltingFunctionProgram,haltingFunctionProgram_computes⟩,haltingFunctionName_realizes⟩

noncomputable def haltingIntegralLp : ComplexL1 :=
  (memLp_one_iff_integrable.mpr haltingIntegralFunction_integrable.ofReal).toLp
    (fun x => (haltingIntegralFunction x:ℂ))

theorem haltingIntegralLp_ae : (haltingIntegralLp : ℝ → ℂ) =ᵐ[volume]
    (fun x => (haltingIntegralFunction x:ℂ)) := MemLp.coeFn_toLp _

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Finally, splitting the triangle at zero gives
    $$\int_{\R}\tau(x)\,dx
     =\int_{-1}^{0}(1+x)\,dx+\int_{0}^{1}(1-x)\,dx=1.$$
    Translation preserves the integral, so the $s$th summand has integral $c_s$. Monotone convergence for the nonnegative
    partial sums now gives
    $$\int_{\R}f(x)\,dx=\sum_{s=0}^{\infty}c_s=\HaltingReal<\infty.$$
    Thus $f$ is integrable, and the Fourier kernel at zero is identically one, giving
    $\FourierTransform{f}(0)=\HaltingReal$.
-/
theorem haltingIntegralFunction_fourier_zero :
    𝓕 (fun x => (haltingIntegralFunction x:ℂ)) 0 = (haltingSetReal diagonalHalts:ℂ) := by
  rw [fourier_eq_kernel]
  simp only [fourierKernel,fourierKernelScale,Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,one_mul]
  rw [integral_complex_ofReal,haltingIntegralFunction_integral]

theorem haltingIntegralLp_fourier_zero :
    Real.Lp.fourierTransform haltingIntegralLp 0 = (haltingSetReal diagonalHalts:ℂ) := by
  change 𝓕 (haltingIntegralLp : ℝ → ℂ) 0 = _
  rw [Real.fourier_congr_ae haltingIntegralLp_ae,haltingIntegralFunction_fourier_zero]

/-- Evaluation at zero reads precisely the constant coefficient of the polynomial code. -/
theorem complexPolynomial_eval_zero (c : ℕ) :
    (complexPolynomial c).eval 0 = complexRationalPoint ((NatListCode.decode c).getD 0 0) := by
  rw [complexPolynomial_eval]
  by_cases h : 0 < (NatListCode.decode c).length
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      simp [zero_pow hb]
    · intro h0
      exact (h0 (Finset.mem_range.mpr h)).elim
  · have hz : NatListCode.decode c = [] := List.length_eq_zero_iff.mp (by omega)
    simp [hz]

def polynomialZeroRealName (p : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((NatListCode.decode (p (Nat.pair 1 n))).getD 0 0).unpair.1

def polynomialZeroRealProgram (P : AlphaTerm) : AlphaTerm := numericalCompose (numericalProjectionTerm true)
  (numericalCompose listGetTerm (pairNumerical
    (numericalCompose P (pairNumerical (numericalConstant 1) numericalIdentity)) (numericalConstant 0)))

theorem polynomialZeroRealProgram_computes {P : AlphaTerm} {p : ℕ → ℕ} (hp : NumericalComputes P p) :
    NumericalComputes (polynomialZeroRealProgram P) (polynomialZeroRealName p) := by
  have h := (projection_computes true).comp (listGet_computes.comp
    ((hp.comp ((numericalConstant_computes 1).pair numericalIdentity_computes)).pair (numericalConstant_computes 0)))
  refine ⟨h.1,fun n => ?_⟩
  simpa only [polynomialZeroRealProgram,polynomialZeroRealName,Nat.unpair_pair,ite_true,id_eq] using h.2 n

theorem polynomialZeroRealName_error {g : C(ℝ,ℂ)} {p : ℕ → ℕ}
    (hp : IsLocallyUniformPolynomialName g p) (n : ℕ) :
    |rationalPoint (polynomialZeroRealName p n)-(g 0).re| ≤ (1/2:ℝ)^n := by
  have he := hp 1 (by omega) n 0 (by norm_num)
  rw [Complex.ofReal_zero,complexPolynomial_eval_zero] at he
  have hr := (Complex.abs_re_le_norm (g 0-complexRationalPoint ((NatListCode.decode (p (Nat.pair 1 n))).getD 0 0))).trans he
  simpa [Complex.sub_re,complexRationalPoint,polynomialZeroRealName,abs_sub_comm] using hr

theorem haltingIntegral_fourier_not_computable :
    ¬ ∃ (P : AlphaTerm) (p : ℕ → ℕ), NumericalComputes P p ∧
      IsLocallyUniformPolynomialName (Real.Lp.fourierTransform haltingIntegralLp).toContinuousMap p := by
  rintro ⟨P,p,hP,hp⟩
  apply haltingSetReal_not_approximable
  refine ⟨polynomialZeroRealProgram P,polynomialZeroRealName p,polynomialZeroRealProgram_computes hP,fun n => ?_⟩
  have h := polynomialZeroRealName_error hp n
  change |rationalPoint (polynomialZeroRealName p n)-(Real.Lp.fourierTransform haltingIntegralLp 0).re| ≤ _ at h
  simpa only [haltingIntegralLp_fourier_zero,Complex.ofReal_re] using h

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    A computable locally uniform polynomial name of the Fourier transform would give computable rational approximations
    to this value: request precision $n$ on $[-1,1]$ and read the real part of the constant coefficient. Evaluation at zero
    makes all positive powers vanish, and the uniform error bound gives error at most $2^{-n}$. This contradicts the
    noncomputability of $\HaltingReal$. A computable $L^1$-name of $f$ would produce precisely such a polynomial name under
    the preceding Fourier realizer, so no computable $L^1$-name exists either. The missing information is effective
    control of the integral in the tails.
    \end{proof}
-/
theorem haltingIntegral_no_computable_L1_name :
    ¬ ∃ (P : AlphaTerm) (p : ℕ → ℕ), NumericalComputes P p ∧ IsL1StepName haltingIntegralLp p := by
  rintro ⟨P,p,hP,hp⟩
  apply haltingIntegral_fourier_not_computable
  refine ⟨app fourierNameProgram P,fourierNameTransform p,?_,fourierNameTransform_correct _ _ hp⟩
  exact (fourierNameProgram_typeTwoComputes Set.univ).numerical_output (p := ⟨p,Set.mem_univ p⟩) hP

end PolishSpaceBook
