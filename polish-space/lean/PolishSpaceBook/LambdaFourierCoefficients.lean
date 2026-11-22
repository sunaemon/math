module

public import PolishSpaceBook.LambdaFourierBounds
public import PolishSpaceBook.LambdaPi
public import PolishSpaceBook.LambdaEulerNumber

@[expose] public section

/-! # Rational Fourier coefficients computed by numerical lambda terms -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
set_option maxRecDepth 4096

/-- Multiplication of signed-numerator rational codes, without normalization. -/
def rationalMultiplyCode (a b : ℕ) : ℕ :=
  let u := RationalCode.ofNat a
  let v := RationalCode.ofNat b
  RationalCode.natCode ((u.1.1*v.1.1+u.1.2*v.1.2,u.1.1*v.1.2+u.1.2*v.1.1),
    (u.2+1)*(v.2+1)-1)

theorem rationalMultiplyCode_value (a b : ℕ) :
    rationalPoint (rationalMultiplyCode a b) = rationalPoint a * rationalPoint b := by
  have h : 1 ≤ ((RationalCode.ofNat a).2+1)*((RationalCode.ofNat b).2+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simp only [rationalMultiplyCode,rationalPoint,RationalCode.ofNat_natCode,RationalCode.value,
    Nat.sub_add_cancel h]
  push_cast
  rw [← mul_div_mul_comm]
  congr 1
  ring

def rationalMultiplyProgram : AlphaTerm :=
  let ap := onComponent (rationalNumeratorTerm true) true
  let an := onComponent (rationalNumeratorTerm false) true
  let bp := onComponent (rationalNumeratorTerm true) false
  let bn := onComponent (rationalNumeratorTerm false) false
  pairNumerical
    (pairNumerical (addNumerical (mulNumerical ap bp) (mulNumerical an bn))
      (addNumerical (mulNumerical ap bn) (mulNumerical an bp)))
    (numericalCompose predecessorTerm
      (mulNumerical (onComponent rationalDenominatorTerm true) (onComponent rationalDenominatorTerm false)))

theorem rationalMultiplyProgram_computes : NumericalComputes rationalMultiplyProgram
    (fun p => rationalMultiplyCode p.unpair.1 p.unpair.2) := by
  have ap := (rationalNumerator_computes true).onComponent true
  have an := (rationalNumerator_computes false).onComponent true
  have bp := (rationalNumerator_computes true).onComponent false
  have bn := (rationalNumerator_computes false).onComponent false
  exact (((ap.mul bp).add (an.mul bn)).pair ((ap.mul bn).add (an.mul bp))).pair
    (predecessor_computes.comp ((rationalDenominator_computes.onComponent true).mul
      (rationalDenominator_computes.onComponent false)))

def rationalOneCode : ℕ := RationalCode.natCode ((1,0),0)

@[simp] theorem rationalOneCode_value : rationalPoint rationalOneCode = 1 := by
  simp [rationalOneCode,rationalPoint,RationalCode.value]

def rationalPowerCode (a : ℕ) : ℕ → ℕ := primitiveRec rationalOneCode (fun _ r => rationalMultiplyCode r a)

theorem rationalPowerCode_value (a j : ℕ) : rationalPoint (rationalPowerCode a j) = rationalPoint a ^ j := by
  induction j with
  | zero => simp [rationalPowerCode,primitiveRec]
  | succ j ih =>
    change rationalPoint (rationalMultiplyCode (rationalPowerCode a j) a) = _
    rw [rationalMultiplyCode_value,ih,pow_succ]

/-- Keep the base as the recursion parameter. -/
def rationalPowerProgram : AlphaTerm := numericalRecursion (numericalConstant rationalOneCode)
  (numericalCompose rationalMultiplyProgram
    (pairNumerical piState (numericalProjectionTerm true)))

theorem rationalPowerProgram_computes : NumericalComputes rationalPowerProgram
    (fun p => rationalPowerCode p.unpair.1 p.unpair.2) := by
  have h := numericalRecursion_computes (numericalConstant_computes rationalOneCode)
    (rationalMultiplyProgram_computes.comp (piState_computes.pair (projection_computes true)))
  simpa only [rationalPowerProgram,rationalPowerCode,Nat.unpair_pair,ite_true] using h

/-- A parameterized natural power is needed in the precision bound. -/
def naturalPowerProgram : AlphaTerm := numericalRecursion (numericalConstant 1)
  (mulNumerical piState (numericalProjectionTerm true))

theorem naturalPowerProgram_computes : NumericalComputes naturalPowerProgram
    (fun p => p.unpair.1 ^ p.unpair.2) := by
  have he (a j : ℕ) : primitiveRec 1 (fun _ r => r*a) j = a^j := by
    induction j with
    | zero => rfl
    | succ j ih => simpa only [primitiveRec,pow_succ] using congrArg (·*a) ih
  simpa only [naturalPowerProgram,Nat.unpair_pair,ite_true,he] using
    numericalRecursion_computes (numericalConstant_computes 1) (piState_computes.mul (projection_computes true))

def factorialReciprocalCode (j : ℕ) : ℕ := RationalCode.natCode ((1,0),j.factorial-1)

theorem factorialReciprocalCode_value (j : ℕ) :
    rationalPoint (factorialReciprocalCode j) = 1/(j.factorial:ℝ) := by
  simp [factorialReciprocalCode,rationalPoint,RationalCode.value,Nat.sub_add_cancel (Nat.factorial_pos j)]

def factorialReciprocalProgram : AlphaTerm := pairNumerical (numericalConstant (Nat.pair 1 0))
  (numericalCompose predecessorTerm eulerFactorialProgram)

theorem factorialReciprocalProgram_computes : NumericalComputes factorialReciprocalProgram factorialReciprocalCode :=
  (numericalConstant_computes (Nat.pair 1 0)).pair (predecessor_computes.comp eulerFactorial_computes)

/-- A complex rational code is a pair of rational codes. -/
def complexRationalPoint (c : ℕ) : ℂ := (rationalPoint c.unpair.1:ℂ) + (rationalPoint c.unpair.2:ℂ)*Complex.I

/-- Rotate a rational complex pair by i: (u,v) becomes (-v,u). -/
def imaginaryPowerCode : ℕ → ℕ := primitiveRec (Nat.pair rationalOneCode 0)
  (fun _ r => Nat.pair (piNegateCode r.unpair.2) r.unpair.1)

theorem imaginaryPowerCode_value (j : ℕ) : complexRationalPoint (imaginaryPowerCode j) = Complex.I^j := by
  induction j with
  | zero => simp [imaginaryPowerCode,primitiveRec,complexRationalPoint,Nat.unpair_pair,rationalOneCode,
      rationalPoint,RationalCode.value,RationalCode.ofNat,RationalCode.natCode]
  | succ j ih =>
    change complexRationalPoint (Nat.pair (piNegateCode (imaginaryPowerCode j).unpair.2)
      (imaginaryPowerCode j).unpair.1) = _
    simp only [complexRationalPoint,Nat.unpair_pair,piNegate_value,Complex.ofReal_neg]
    rw [pow_succ,← ih]
    unfold complexRationalPoint
    linear_combination (-(rationalPoint (imaginaryPowerCode j).unpair.2:ℂ)) * Complex.I_sq

def imaginaryPowerProgram : AlphaTerm := piRecursionProgram (Nat.pair rationalOneCode 0)
  (pairNumerical (numericalCompose piNegateProgram (numericalCompose (numericalProjectionTerm false) piState))
    (numericalCompose (numericalProjectionTerm true) piState))

theorem imaginaryPowerProgram_computes : NumericalComputes imaginaryPowerProgram imaginaryPowerCode :=
  piRecursion_computes (h := fun _ r => Nat.pair (piNegateCode r.unpair.2) r.unpair.1)
    ((piNegate_computes.comp ((projection_computes false).comp piState_computes)).pair
      ((projection_computes true).comp piState_computes)) (Nat.pair rationalOneCode 0)

def rationalSubtractCode (a b : ℕ) : ℕ :=
  (RationalCode.add (RationalCode.ofNat a) (RationalCode.ofNat (piNegateCode b))).natCode

theorem rationalSubtractCode_value (a b : ℕ) :
    rationalPoint (rationalSubtractCode a b) = rationalPoint a-rationalPoint b := by
  simp only [rationalSubtractCode,rationalPoint,RationalCode.ofNat_natCode,RationalCode.value_add,Rat.cast_add]
  change rationalPoint a + rationalPoint (piNegateCode b) = _
  rw [piNegate_value,sub_eq_add_neg]
  rfl

def rationalSubtractProgram : AlphaTerm := numericalCompose rationalAddTerm
  (pairNumerical (numericalProjectionTerm true) (numericalCompose piNegateProgram (numericalProjectionTerm false)))

theorem rationalSubtractProgram_computes : NumericalComputes rationalSubtractProgram
    (fun p => rationalSubtractCode p.unpair.1 p.unpair.2) := by
  have h := rationalAdd_computes.comp ((projection_computes true).pair
    (piNegate_computes.comp (projection_computes false)))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [rationalSubtractProgram,rationalSubtractCode,Nat.unpair_pair,ite_true,
    Bool.false_eq_true,ite_false] using h.2 p

/-- The real scalar multiplying i^j, with pi approximated at precision k. -/
@[irreducible] def intervalCoefficientScalar (a b k j : ℕ) : ℕ :=
  rationalMultiplyCode
    (rationalMultiplyCode (rationalPowerCode (piNegateCode (piScaleCode 2 (piName k))) j)
      (rationalSubtractCode (rationalPowerCode b (j+1)) (rationalPowerCode a (j+1))))
    (factorialReciprocalCode (j+1))

theorem intervalCoefficientScalar_value (a b k j : ℕ) :
    rationalPoint (intervalCoefficientScalar a b k j) =
      (-2*rationalPoint (piName k))^j * (rationalPoint b^(j+1)-rationalPoint a^(j+1))/((j+1).factorial:ℝ) := by
  simp only [intervalCoefficientScalar,rationalMultiplyCode_value,rationalPowerCode_value,
    piNegate_value,piScale_value,rationalSubtractCode_value,factorialReciprocalCode_value]
  push_cast
  ring

def intervalCoefficientCode (a b k j : ℕ) : ℕ :=
  let r := intervalCoefficientScalar a b k j
  let p := imaginaryPowerCode j
  Nat.pair (rationalMultiplyCode r p.unpair.1) (rationalMultiplyCode r p.unpair.2)

theorem intervalCoefficientCode_value (a b k j : ℕ) :
    complexRationalPoint (intervalCoefficientCode a b k j) =
      ((-2*(rationalPoint (piName k):ℂ)*Complex.I)^j) *
        ((rationalPoint b:ℂ)^(j+1)-(rationalPoint a:ℂ)^(j+1))/((j+1).factorial:ℂ) := by
  have he : complexRationalPoint (intervalCoefficientCode a b k j) =
      (rationalPoint (intervalCoefficientScalar a b k j):ℂ)*complexRationalPoint (imaginaryPowerCode j) := by
    simp only [intervalCoefficientCode,complexRationalPoint,Nat.unpair_pair,rationalMultiplyCode_value,
      Complex.ofReal_mul]
    ring
  rw [he,imaginaryPowerCode_value,intervalCoefficientScalar_value]
  push_cast
  rw [mul_pow]
  ring

/-- Input a paired with b paired with k paired with j. -/
def intervalCoefficientScalarProgram : AlphaTerm :=
  let A := numericalProjectionTerm true
  let T := numericalProjectionTerm false
  let B := numericalCompose (numericalProjectionTerm true) T
  let U := numericalCompose (numericalProjectionTerm false) T
  let K := numericalCompose (numericalProjectionTerm true) U
  let J := numericalCompose (numericalProjectionTerm false) U
  let S := numericalCompose successorTerm J
  let Q := numericalCompose piNegateProgram (numericalCompose (piScaleProgram 2) (numericalCompose piNameProgram K))
  let V := numericalCompose rationalPowerProgram (pairNumerical Q J)
  let W := numericalCompose rationalSubtractProgram
    (pairNumerical (numericalCompose rationalPowerProgram (pairNumerical B S))
      (numericalCompose rationalPowerProgram (pairNumerical A S)))
  numericalCompose rationalMultiplyProgram
    (pairNumerical (numericalCompose rationalMultiplyProgram (pairNumerical V W))
      (numericalCompose factorialReciprocalProgram S))

theorem intervalCoefficientScalarProgram_computes : NumericalComputes intervalCoefficientScalarProgram
    (fun p => intervalCoefficientScalar p.unpair.1 p.unpair.2.unpair.1
      p.unpair.2.unpair.2.unpair.1 p.unpair.2.unpair.2.unpair.2) := by
  have ha := projection_computes true
  have ht := projection_computes false
  have hb := (projection_computes true).comp ht
  have hu := (projection_computes false).comp ht
  have hk := (projection_computes true).comp hu
  have hj := (projection_computes false).comp hu
  have hs := successor_computes.comp hj
  have hq := piNegate_computes.comp ((piScale_computes 2).comp (piName_computes.comp hk))
  have hv := rationalPowerProgram_computes.comp (hq.pair hj)
  have hw := rationalSubtractProgram_computes.comp
    ((rationalPowerProgram_computes.comp (hb.pair hs)).pair (rationalPowerProgram_computes.comp (ha.pair hs)))
  have h := rationalMultiplyProgram_computes.comp
    ((rationalMultiplyProgram_computes.comp (hv.pair hw)).pair (factorialReciprocalProgram_computes.comp hs))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [intervalCoefficientScalarProgram,intervalCoefficientScalar,Nat.unpair_pair,Nat.succ_eq_add_one,ite_true,Bool.false_eq_true,ite_false] using h.2 p

def intervalCoefficientProgram : AlphaTerm :=
  let J := numericalCompose (numericalProjectionTerm false)
    (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))
  let P := numericalCompose imaginaryPowerProgram J
  let R := intervalCoefficientScalarProgram
  pairNumerical
    (numericalCompose rationalMultiplyProgram (pairNumerical R (numericalCompose (numericalProjectionTerm true) P)))
    (numericalCompose rationalMultiplyProgram (pairNumerical R (numericalCompose (numericalProjectionTerm false) P)))

theorem intervalCoefficientProgram_computes : NumericalComputes intervalCoefficientProgram
    (fun p => intervalCoefficientCode p.unpair.1 p.unpair.2.unpair.1
      p.unpair.2.unpair.2.unpair.1 p.unpair.2.unpair.2.unpair.2) := by
  have hj := (projection_computes false).comp ((projection_computes false).comp (projection_computes false))
  have hp := imaginaryPowerProgram_computes.comp hj
  have h := (rationalMultiplyProgram_computes.comp
    (intervalCoefficientScalarProgram_computes.pair ((projection_computes true).comp hp))).pair
      (rationalMultiplyProgram_computes.comp
        (intervalCoefficientScalarProgram_computes.pair ((projection_computes false).comp hp)))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [intervalCoefficientProgram,intervalCoefficientCode,Nat.unpair_pair,ite_true,
    Bool.false_eq_true,ite_false] using h.2 p

/-- The coefficient of frequency degree j in the interval transform polynomial. -/
noncomputable def intervalFourierCoefficient (a b : ℝ) (j : ℕ) : ℂ :=
  (-2*Real.pi*Complex.I)^j*((b:ℂ)^(j+1)-(a:ℂ)^(j+1))/((j+1).factorial:ℂ)

theorem intervalExponentialPartial_coefficients (a b ξ : ℝ) (N : ℕ) :
    intervalExponentialPartial a b (fourierKernelScale ξ) N =
      ∑ j ∈ Finset.range N, intervalFourierCoefficient a b j * (ξ:ℂ)^j := by
  unfold intervalExponentialPartial intervalFourierCoefficient fourierKernelScale
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_pow]
  ring

/-- A coarse power-difference estimate that also covers degree zero. -/
theorem power_difference_bound {x y : ℝ} (hx : |x| ≤ 10) (hy : |y| ≤ 10) (j : ℕ) :
    |x^j-y^j| ≤ j*(10:ℝ)^j*|x-y| := by
  induction j with
  | zero => simp
  | succ j ih =>
    have he : x^(j+1)-y^(j+1) = x^j*(x-y)+y*(x^j-y^j) := by ring
    rw [he]
    calc
      _ ≤ |x^j*(x-y)|+|y*(x^j-y^j)| := abs_add_le _ _
      _ = |x|^j*|x-y|+|y| * |x^j-y^j| := by rw [abs_mul,abs_pow,abs_mul]
      _ ≤ (10:ℝ)^j*|x-y|+10*(j*(10:ℝ)^j*|x-y|) := by gcongr
      _ ≤ (j+1:ℕ)*(10:ℝ)^(j+1)*|x-y| := by
        rw [pow_succ]; push_cast
        nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤10) j) (abs_nonneg (x-y))]

def intervalEndpointBound (a b : ℕ) : ℕ := rationalMagnitudeBound a+rationalMagnitudeBound b+1

theorem intervalEndpointBound_pos (a b : ℕ) : 1 ≤ intervalEndpointBound a b := by
  unfold intervalEndpointBound; omega

theorem intervalEndpointBound_values (a b : ℕ) :
    |rationalPoint a| ≤ intervalEndpointBound a b ∧ |rationalPoint b| ≤ intervalEndpointBound a b := by
  unfold intervalEndpointBound
  push_cast
  constructor
  · exact (rationalPoint_abs_le_magnitude a).trans (by
      nlinarith [Nat.cast_nonneg (α := ℝ) (rationalMagnitudeBound b)])
  · exact (rationalPoint_abs_le_magnitude b).trans (by
      nlinarith [Nat.cast_nonneg (α := ℝ) (rationalMagnitudeBound a)])

theorem piName_abs_le_five (k : ℕ) : |rationalPoint (piName k)| ≤ 5 := by
  have hp := piName_error k
  have hb : (1/2:ℝ)^(k+3) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht := abs_sub_le (rationalPoint (piName k)) Real.pi 0
  simp only [sub_zero,abs_of_pos Real.pi_pos] at ht
  linarith [Real.pi_le_four]

def fourierCoefficientSensitivity (a b j : ℕ) : ℕ :=
  4*j*10^j*(intervalEndpointBound a b)^(j+1)

theorem intervalCoefficientCode_error (a b k j : ℕ) :
    ‖complexRationalPoint (intervalCoefficientCode a b k j) -
      intervalFourierCoefficient (rationalPoint a) (rationalPoint b) j‖ ≤
        (fourierCoefficientSensitivity a b j:ℝ)*|rationalPoint (piName k)-Real.pi| := by
  have he : complexRationalPoint (intervalCoefficientCode a b k j) -
      intervalFourierCoefficient (rationalPoint a) (rationalPoint b) j =
      (((( -2*rationalPoint (piName k))^j-(-2*Real.pi)^j)*
        (rationalPoint b^(j+1)-rationalPoint a^(j+1))/((j+1).factorial:ℝ):ℝ):ℂ)*Complex.I^j := by
    rw [intervalCoefficientCode_value,intervalFourierCoefficient]
    push_cast
    simp only [mul_pow]
    ring
  rw [he,norm_mul,norm_pow,Complex.norm_I,one_pow,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have hpow := power_difference_bound
    (x := -2*rationalPoint (piName k)) (y := -2*Real.pi)
    (by simp only [abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]; linarith [piName_abs_le_five k])
    (by simp only [abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2),abs_of_pos Real.pi_pos];
        linarith [Real.pi_le_four]) j
  have hx : |-2*rationalPoint (piName k)-(-2*Real.pi)| = 2*|rationalPoint (piName k)-Real.pi| := by
    rw [show -2*rationalPoint (piName k)-(-2*Real.pi) = -2*(rationalPoint (piName k)-Real.pi) by ring]
    simp [abs_mul]
  rw [hx] at hpow
  have hab := intervalEndpointBound_values a b
  have heps : |rationalPoint b^(j+1)-rationalPoint a^(j+1)| ≤
      2*(intervalEndpointBound a b:ℝ)^(j+1) := by
    calc
      _ ≤ |rationalPoint b|^(j+1)+|rationalPoint a|^(j+1) := by
        simpa only [abs_pow] using abs_sub (rationalPoint b^(j+1)) (rationalPoint a^(j+1))
      _ ≤ (intervalEndpointBound a b:ℝ)^(j+1)+(intervalEndpointBound a b:ℝ)^(j+1) :=
        add_le_add (pow_le_pow_left₀ (abs_nonneg _) hab.2 _) (pow_le_pow_left₀ (abs_nonneg _) hab.1 _)
      _ = _ := by ring
  calc
    _ ≤ |((-2*rationalPoint (piName k))^j-(-2*Real.pi)^j)*
        (rationalPoint b^(j+1)-rationalPoint a^(j+1))| := by
      rw [abs_div,abs_of_pos (by positivity : (0:ℝ)<(j+1).factorial)]
      exact div_le_self (abs_nonneg _) (by exact_mod_cast Nat.factorial_pos (j+1))
    _ = |(-2*rationalPoint (piName k))^j-(-2*Real.pi)^j| *
        |rationalPoint b^(j+1)-rationalPoint a^(j+1)| := abs_mul _ _
    _ ≤ (j*(10:ℝ)^j*(2*|rationalPoint (piName k)-Real.pi|))*
        (2*(intervalEndpointBound a b:ℝ)^(j+1)) := by gcongr
    _ = _ := by unfold fourierCoefficientSensitivity; push_cast; ring

/-- Precision is chosen arithmetically, with no test of a real inequality. -/
def approximatedIntervalCoefficient (a b j m : ℕ) : ℕ :=
  intervalCoefficientCode a b (m+fourierCoefficientSensitivity a b j) j

theorem approximatedIntervalCoefficient_error (a b j m : ℕ) :
    ‖complexRationalPoint (approximatedIntervalCoefficient a b j m) -
      intervalFourierCoefficient (rationalPoint a) (rationalPoint b) j‖ ≤ (1/2:ℝ)^(m+3) := by
  unfold approximatedIntervalCoefficient
  apply (intervalCoefficientCode_error a b _ j).trans
  calc
    (fourierCoefficientSensitivity a b j:ℝ)*
        |rationalPoint (piName (m+fourierCoefficientSensitivity a b j))-Real.pi|
      ≤ (fourierCoefficientSensitivity a b j:ℝ)*(1/2:ℝ)^(m+fourierCoefficientSensitivity a b j+3) := by
        gcongr
        exact piName_error _
    _ ≤ (2:ℝ)^(fourierCoefficientSensitivity a b j)*(1/2:ℝ)^(m+fourierCoefficientSensitivity a b j+3) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.lt_two_pow_self (n := fourierCoefficientSensitivity a b j)).le)
        (by positivity)
    _ = _ := by
      rw [show m+fourierCoefficientSensitivity a b j+3 = fourierCoefficientSensitivity a b j+(m+3) by omega,
        pow_add,one_div_pow]
      field_simp

/-- Input a paired with b paired with degree j paired with precision m. -/
def approximatedIntervalCoefficientProgram : AlphaTerm :=
  let A := numericalProjectionTerm true
  let T := numericalProjectionTerm false
  let B := numericalCompose (numericalProjectionTerm true) T
  let U := numericalCompose (numericalProjectionTerm false) T
  let J := numericalCompose (numericalProjectionTerm true) U
  let M := numericalCompose (numericalProjectionTerm false) U
  let S := addNumerical
    (addNumerical (numericalCompose rationalMagnitudeProgram A) (numericalCompose rationalMagnitudeProgram B))
    (numericalConstant 1)
  let H := mulNumerical
    (mulNumerical (mulNumerical (numericalConstant 4) J) (numericalCompose (piPowerProgram 10) J))
    (numericalCompose naturalPowerProgram (pairNumerical S (numericalCompose successorTerm J)))
  numericalCompose intervalCoefficientProgram (pairNumerical A (pairNumerical B (pairNumerical (addNumerical M H) J)))

theorem approximatedIntervalCoefficientProgram_computes : NumericalComputes approximatedIntervalCoefficientProgram
    (fun p => approximatedIntervalCoefficient p.unpair.1 p.unpair.2.unpair.1
      p.unpair.2.unpair.2.unpair.1 p.unpair.2.unpair.2.unpair.2) := by
  have ha := projection_computes true
  have ht := projection_computes false
  have hb := (projection_computes true).comp ht
  have hu := (projection_computes false).comp ht
  have hj := (projection_computes true).comp hu
  have hm := (projection_computes false).comp hu
  have hs := ((rationalMagnitudeProgram_computes.comp ha).add (rationalMagnitudeProgram_computes.comp hb)).add
    (numericalConstant_computes 1)
  have hh := (((numericalConstant_computes 4).mul hj).mul ((piPower_computes 10).comp hj)).mul
    (naturalPowerProgram_computes.comp (hs.pair (successor_computes.comp hj)))
  have h := intervalCoefficientProgram_computes.comp (ha.pair (hb.pair ((hm.add hh).pair hj)))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [approximatedIntervalCoefficientProgram,approximatedIntervalCoefficient,fourierCoefficientSensitivity,
    intervalEndpointBound,Nat.unpair_pair,Nat.succ_eq_add_one,ite_true,Bool.false_eq_true,ite_false] using h.2 p

/-- Absorb the total coefficient weight and the polynomial-evaluation denominator. -/
theorem coefficientPrecision_bound (V Q n : ℕ) (hQ : 0 < Q) :
    (V:ℝ)*(1/2:ℝ)^(n+V+Q+3) ≤ (1/2:ℝ)^(n+2)/(Q:ℝ) := by
  apply (le_div_iff₀ (by exact_mod_cast hQ : (0:ℝ)<Q)).mpr
  calc
    (V:ℝ)*(1/2:ℝ)^(n+V+Q+3)*Q ≤ (2:ℝ)^V*(1/2:ℝ)^(n+V+Q+3)*(2:ℝ)^Q := by
      gcongr
      · exact_mod_cast (Nat.lt_two_pow_self (n := V)).le
      · exact_mod_cast (Nat.lt_two_pow_self (n := Q)).le
    _ = (1/2:ℝ)^(n+3) := by
      rw [show n+V+Q+3 = V+Q+(n+3) by omega,pow_add,pow_add]
      simp only [one_div_pow]
      field_simp
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

theorem finiteIntervalCoefficient_error (L : ℕ) (a b : ℕ → ℕ) (v : ℕ → ℂ) (V Q n j : ℕ)
    (hV : (∑ i ∈ Finset.range L, ‖v i‖) ≤ V) (hQ : 0 < Q) :
    ‖(∑ i ∈ Finset.range L, v i * complexRationalPoint (approximatedIntervalCoefficient (a i) (b i) j (n+V+Q))) -
      (∑ i ∈ Finset.range L, v i * intervalFourierCoefficient (rationalPoint (a i)) (rationalPoint (b i)) j)‖ ≤
        (1/2:ℝ)^(n+2)/(Q:ℝ) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range L,
        ‖v i*complexRationalPoint (approximatedIntervalCoefficient (a i) (b i) j (n+V+Q)) -
          v i*intervalFourierCoefficient (rationalPoint (a i)) (rationalPoint (b i)) j‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range L, ‖v i‖*(1/2:ℝ)^(n+V+Q+3) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (approximatedIntervalCoefficient_error _ _ _ _) (norm_nonneg _)
    _ = (∑ i ∈ Finset.range L, ‖v i‖)*(1/2:ℝ)^(n+V+Q+3) := by rw [Finset.sum_mul]
    _ ≤ (V:ℝ)*(1/2:ℝ)^(n+V+Q+3) := mul_le_mul_of_nonneg_right hV (by positivity)
    _ ≤ _ := coefficientPrecision_bound V Q n hQ

/-- A finite coefficientwise estimate gives a uniform estimate on the frequency window. -/
theorem complexPolynomial_coefficient_error (N R n : ℕ) (hN : 0 < N) (a b : ℕ → ℂ)
    (hab : ∀ j < N, ‖a j-b j‖ ≤ (1/2:ℝ)^(n+2)/(N*(R+1)^N:ℕ))
    (ξ : ℝ) (hξ : |ξ| ≤ R) :
    ‖(∑ j ∈ Finset.range N, a j*(ξ:ℂ)^j) - (∑ j ∈ Finset.range N, b j*(ξ:ℂ)^j)‖ ≤
      (1/2:ℝ)^(n+2) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range N, ‖a j*(ξ:ℂ)^j-b j*(ξ:ℂ)^j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ((1/2:ℝ)^(n+2)/(N*(R+1)^N:ℕ))*((R:ℝ)+1)^N := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← sub_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      apply mul_le_mul (hab j (Finset.mem_range.mp hj)) _ (by positivity) (by positivity)
      exact (pow_le_pow_left₀ (abs_nonneg ξ) (hξ.trans (by linarith)) j).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt (Finset.mem_range.mp hj)))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_mul,Nat.cast_pow,
        Nat.cast_add,Nat.cast_one]
      have hn : (N:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      have hr : (R:ℝ)+1 ≠ 0 := by positivity
      field_simp

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Computable coefficients of interval Fourier transforms
  excerpt: |
    \begin{lemma*}[\termdefineas{Computable coefficients of interval Fourier transforms}{Computable coefficients of interval
    Fourier transforms}]
    For rational endpoints $a,b$ and $j\in\NN$, let
    $$\IntervalFourierCoefficient{a}{b}{j}:=
     \frac{(-2\pi\mathrm i)^j(b^{j+1}-a^{j+1})}{(j+1)!}.$$
    One closed numerical lambda term, given codes for $a,b$ and integers $j,m\in\NN$, returns a rational complex number
    $\widetilde c_j$ satisfying
    $$|\widetilde c_j-\IntervalFourierCoefficient{a}{b}{j}|\le2^{-(m+3)}.$$
    \end{lemma*}
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Suppose the endpoint codes are $\RationalCode{p_a}{q_a}{d_a}$ and $\RationalCode{p_b}{q_b}{d_b}$. Set
    $$S:=p_a+q_a+p_b+q_b+1,\qquad
     \FourierCoefficientSensitivity{j}{S}:=4j10^jS^{j+1}.$$
    Then $S\ge1$ and $|a|,|b|\le S$. Put $k:=m+\FourierCoefficientSensitivity{j}{S}$, and compute a rational
    approximation $q$ to $\pi$ by the construction in §{sec:tte-real-examples}, so that
    $$|q-\pi|\le2^{-(k+3)}.$$
    Define
    $$\widetilde c_j:=\mathrm i^j\frac{(-2q)^j(b^{j+1}-a^{j+1})}{(j+1)!}.$$
    This is rational complex, including at degree zero.

    First check the error. Since $|q-\pi|\le1$ and $\pi\le4$, we have $|q|\le5$, and hence $|-2q|,|-2\pi|\le10$.
    Induction using
    $$u^{j+1}-v^{j+1}=u^j(u-v)+v(u^j-v^j)$$
    shows that, for $|u|,|v|\le10$,
    $$|u^j-v^j|\le j10^j|u-v|.$$
    Also $|b^{j+1}-a^{j+1}|\le2S^{j+1}$, $|\mathrm i^j|=1$, and $(j+1)!\ge1$. Therefore
    $$|\widetilde c_j-\IntervalFourierCoefficient{a}{b}{j}|
     \le\FourierCoefficientSensitivity{j}{S}|q-\pi|.$$
    Writing $H=\FourierCoefficientSensitivity{j}{S}$ and using $H\le2^H$ gives
    $$|\widetilde c_j-\IntervalFourierCoefficient{a}{b}{j}|
     \le H2^{-(m+H+3)}\le2^{-(m+3)}.$$
    There is no exception at $j=0$: both coefficients equal $b-a$ and $H=0$.

    It remains to describe the closed term producing this rational complex number. Multiplication of two rational codes
    is implemented by
    $$\begin{aligned}
    &\bigl(\RationalCode{p}{q}{d},\RationalCode{u}{v}{e}\bigr)\\
     &\longmapsto\RationalCode{pu+qv}{pv+qu}{(d+1)(e+1)-1}.
    \end{aligned}$$
    The denominator is positive, so the displayed subtraction is ordinary subtraction. The projections, natural addition
    and multiplication, predecessor, and pairing implement this formula. Swapping the two numerator components negates a
    rational code; combine this with rational addition to subtract. Starting from $\RationalCode{1}{0}{0}$ and repeatedly
    multiplying by a retained base computes its powers. The same recursion with natural multiplication computes the powers
    in $H$. Factorial recursion followed by pairing produces $\RationalCode{1}{0}{(j+1)!-1}$, the reciprocal of the positive
    factorial. These operations compute the real scalar in the formula for $\widetilde c_j$ exactly.

    Represent a rational complex number by the pair of its real and imaginary rational codes. Starting from the pair
    representing $(1,0)$ and iterating $(u,v)\mapsto(-v,u)$ computes $\mathrm i^j$. Multiply its two components by the
    real scalar just computed. All recursions have a numerical iteration count and retain the endpoint and precision
    parameters. If $c_a,c_b$ are the input endpoint codes, put
    $$z:=\NatPair{c_a}{\NatPair{c_b}{\NatPair{j}{m}}}.$$
    The resulting closed term $C$ satisfies
    $$C\ChurchNumeral{z}\to_\beta^*\ChurchNumeral{\NatPair{u}{v}},\qquad
     \widetilde c_j=\RationalValue{u}+\mathrm i\RationalValue{v}.$$
    Induction on the arithmetic recursions proves these reductions, and the preceding estimates give the required error.
    \end{proof}
-/
theorem interval_fourier_coefficients_computable :
    NumericalComputes approximatedIntervalCoefficientProgram
      (fun p => approximatedIntervalCoefficient p.unpair.1 p.unpair.2.unpair.1
        p.unpair.2.unpair.2.unpair.1 p.unpair.2.unpair.2.unpair.2) ∧
    ∀ a b j m : ℕ, ‖complexRationalPoint (approximatedIntervalCoefficient a b j m) -
      intervalFourierCoefficient (rationalPoint a) (rationalPoint b) j‖ ≤ (1/2:ℝ)^(m+3) :=
  ⟨approximatedIntervalCoefficientProgram_computes,approximatedIntervalCoefficient_error⟩

end PolishSpaceBook
