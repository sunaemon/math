module

public import PolishSpaceBook.LambdaPolynomialAlgebra
public import PolishSpaceBook.LambdaBernsteinApproximation
public import PolishSpaceBook.LambdaLaplaceExample
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

/-! # A polynomial name for the function with a noncomputable integral

Sample the function exactly at rational grid points, form rational binomial
weights, multiply the two affine factors, and sum the resulting polynomials.
The entire construction operates on the finite list codes used by the book.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open scoped unitInterval

def rationalNatCode (n : ℕ) : ℕ := Nat.pair (Nat.pair n 0) 0

def rationalNatProgram : AlphaTerm := pairNumerical
  (pairNumerical numericalIdentity (numericalConstant 0)) (numericalConstant 0)

theorem rationalNatProgram_computes : NumericalComputes rationalNatProgram rationalNatCode :=
  (numericalIdentity_computes.pair (numericalConstant_computes 0)).pair (numericalConstant_computes 0)

theorem rationalNatCode_value (n : ℕ) : rationalPoint (rationalNatCode n) = n := by
  simp [rationalNatCode,rationalPoint,RationalCode.ofNat,RationalCode.value]

@[irreducible] def bernsteinChooseCode (d j : ℕ) : ℕ :=
  rationalMultiplyCode (rationalNatCode d.factorial)
    (rationalMultiplyCode (factorialReciprocalCode j) (factorialReciprocalCode (d-j)))

def bernsteinChooseProgram : AlphaTerm :=
  let D := numericalProjectionTerm true
  let J := numericalProjectionTerm false
  numericalCompose rationalMultiplyProgram (pairNumerical
    (numericalCompose rationalNatProgram (numericalCompose eulerFactorialProgram D))
    (numericalCompose rationalMultiplyProgram (pairNumerical (numericalCompose factorialReciprocalProgram J)
      (numericalCompose factorialReciprocalProgram (numericalCombine subtractionTerm D J)))))

theorem bernsteinChooseProgram_computes : NumericalComputes bernsteinChooseProgram
    (fun p => bernsteinChooseCode p.unpair.1 p.unpair.2) := by
  have d := projection_computes true
  have j := projection_computes false
  have h := rationalMultiplyProgram_computes.comp
    ((rationalNatProgram_computes.comp (eulerFactorial_computes.comp d)).pair
      (rationalMultiplyProgram_computes.comp ((factorialReciprocalProgram_computes.comp j).pair
        (factorialReciprocalProgram_computes.comp
          (d.combine j subtractionTerm_closed (fun d j => d-j) subtractionTerm_apply)))))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [bernsteinChooseProgram,bernsteinChooseCode,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using h.2 p

theorem bernsteinChooseCode_value (d j : ℕ) (hj : j ≤ d) :
    rationalPoint (bernsteinChooseCode d j) = d.choose j := by
  rw [bernsteinChooseCode,rationalMultiplyCode_value,rationalMultiplyCode_value,
    rationalNatCode_value,factorialReciprocalCode_value,factorialReciprocalCode_value,Nat.cast_choose ℝ hj]
  ring

def bernsteinHalfCode : ℕ := rationalDivideSuccCode rationalOneCode 1

theorem bernsteinHalfCode_value : rationalPoint bernsteinHalfCode = 1/2 := by
  rw [bernsteinHalfCode,rationalDivideSuccCode_value,rationalOneCode_value]
  norm_num

def bernsteinSlopeCode (R : ℕ) : ℕ := rationalDivideSuccCode rationalOneCode (2*R-1)

def bernsteinSlopeProgram : AlphaTerm := numericalCompose rationalDivideSuccProgram
  (pairNumerical (numericalConstant rationalOneCode)
    (numericalCompose predecessorTerm (mulNumerical (numericalConstant 2) numericalIdentity)))

theorem bernsteinSlopeProgram_computes : NumericalComputes bernsteinSlopeProgram bernsteinSlopeCode := by
  have h := rationalDivideSucc_computes.comp ((numericalConstant_computes rationalOneCode).pair
    (predecessor_computes.comp ((numericalConstant_computes 2).mul numericalIdentity_computes)))
  refine ⟨h.1,fun R => ?_⟩
  simpa only [bernsteinSlopeProgram,bernsteinSlopeCode,Nat.unpair_pair,id_eq] using h.2 R

theorem bernsteinSlopeCode_value (R : ℕ) (hR : 0<R) : rationalPoint (bernsteinSlopeCode R) = 1/(2*R:ℝ) := by
  rw [bernsteinSlopeCode,rationalDivideSuccCode_value,rationalOneCode_value,Nat.sub_add_cancel (by omega)]
  push_cast
  rfl

def bernsteinAffineCoefficient (positive : Bool) (R k : ℕ) : ℕ := Nat.pair
  (if k=0 then bernsteinHalfCode else if positive then bernsteinSlopeCode R else piNegateCode (bernsteinSlopeCode R)) 0

def bernsteinAffineCoefficientProgram (positive : Bool) : AlphaTerm := pairNumerical
  (numericalIfZero (numericalProjectionTerm false) (numericalConstant bernsteinHalfCode)
    (numericalCompose (if positive then bernsteinSlopeProgram else numericalCompose piNegateProgram bernsteinSlopeProgram)
      (numericalProjectionTerm true))) (numericalConstant 0)

theorem bernsteinAffineCoefficientProgram_computes (positive : Bool) :
    NumericalComputes (bernsteinAffineCoefficientProgram positive)
      (fun p => bernsteinAffineCoefficient positive p.unpair.1 p.unpair.2) := by
  have hs : NumericalComputes
      (if positive then bernsteinSlopeProgram else numericalCompose piNegateProgram bernsteinSlopeProgram)
      (fun R => if positive then bernsteinSlopeCode R else piNegateCode (bernsteinSlopeCode R)) := by
    cases positive
    · exact piNegate_computes.comp bernsteinSlopeProgram_computes
    · exact bernsteinSlopeProgram_computes
  have h := (numericalIfZero_computes (projection_computes false) (numericalConstant_computes bernsteinHalfCode)
    (hs.comp (projection_computes true))).pair (numericalConstant_computes 0)
  refine ⟨h.1,fun p => ?_⟩
  simpa only [bernsteinAffineCoefficientProgram,bernsteinAffineCoefficient,Nat.unpair_pair,
    ite_true,Bool.false_eq_true,ite_false] using h.2 p

@[irreducible] def bernsteinAffineCode (positive : Bool) (R : ℕ) : ℕ :=
  coefficientListCode 2 (bernsteinAffineCoefficient positive R)

def bernsteinAffineProgram (positive : Bool) : AlphaTerm :=
  numericalCompose (listTabulateTerm (bernsteinAffineCoefficientProgram positive))
    (pairNumerical numericalIdentity (numericalConstant 2))

theorem bernsteinAffineProgram_computes (positive : Bool) :
    NumericalComputes (bernsteinAffineProgram positive) (bernsteinAffineCode positive) := by
  have h := (listTabulate_computes (bernsteinAffineCoefficientProgram_computes positive)).comp
    (numericalIdentity_computes.pair (numericalConstant_computes 2))
  refine ⟨h.1,fun R => ?_⟩
  simpa only [bernsteinAffineProgram,bernsteinAffineCode,coefficientListCode,Nat.unpair_pair,id_eq] using h.2 R

theorem bernsteinAffineCode_eval (positive : Bool) (R : ℕ) (hR : 0<R) (x : ℝ) :
    (complexPolynomial (bernsteinAffineCode positive R)).eval (x:ℂ) =
      ((if positive then (x+R)/(2*R) else (R-x)/(2*R):ℝ):ℂ) := by
  have hRC : (R:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have h0 : rationalPoint 0 = 0 := by norm_num [rationalPoint,RationalCode.ofNat,RationalCode.value]
  rw [bernsteinAffineCode,complexCoefficientList_eval]
  cases positive <;>
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,bernsteinAffineCoefficient,Nat.unpair_pair,
      complexRationalPoint,ite_true,show ¬ (1:ℕ)=0 from by omega,ite_false,Bool.false_eq_true,
      bernsteinHalfCode_value,piNegate_value,bernsteinSlopeCode_value R hR,h0,Complex.ofReal_zero,
      zero_mul,add_zero,pow_zero,pow_one,mul_one,zero_add] <;>
    push_cast <;> field_simp [hRC] <;> ring

/-- Exact sample times its binomial coefficient, both represented by rational codes. -/
@[irreducible] def haltingBernsteinWeightCode (R d j : ℕ) : ℕ := Nat.pair
  (rationalMultiplyCode (haltingEvaluationCode (laplaceGridCode R d j)) (bernsteinChooseCode d j)) 0

def haltingBernsteinWeightProgram : AlphaTerm :=
  let R := onComponent (numericalProjectionTerm true) true
  let D := onComponent (numericalProjectionTerm false) true
  let J := numericalProjectionTerm false
  pairNumerical (numericalCompose rationalMultiplyProgram (pairNumerical
    (numericalCompose haltingEvaluationProgram (numericalCompose laplaceGridProgram (pairNumerical R (pairNumerical D J))))
    (numericalCompose bernsteinChooseProgram (pairNumerical D J)))) (numericalConstant 0)

theorem haltingBernsteinWeightProgram_computes : NumericalComputes haltingBernsteinWeightProgram
    (fun p => haltingBernsteinWeightCode p.unpair.1.unpair.1 p.unpair.1.unpair.2 p.unpair.2) := by
  have r := (projection_computes true).onComponent true
  have d := (projection_computes false).onComponent true
  have j := projection_computes false
  have h := (rationalMultiplyProgram_computes.comp
    ((haltingEvaluationProgram_computes.comp (laplaceGridProgram_computes.comp (r.pair (d.pair j)))).pair
      (bernsteinChooseProgram_computes.comp (d.pair j)))).pair (numericalConstant_computes 0)
  refine ⟨h.1,fun p => ?_⟩
  simpa only [haltingBernsteinWeightProgram,haltingBernsteinWeightCode,Nat.unpair_pair,
    ite_true,Bool.false_eq_true,ite_false] using h.2 p

theorem haltingBernsteinWeightCode_value (R d j : ℕ) (hd : 0<d) (hj : j≤d) :
    complexRationalPoint (haltingBernsteinWeightCode R d j) =
      ((haltingIntegralFunction (-(R:ℝ)+(2*R/d)*j)*(d.choose j):ℝ):ℂ) := by
  have h0 : rationalPoint 0 = 0 := by norm_num [rationalPoint,RationalCode.ofNat,RationalCode.value]
  simp only [haltingBernsteinWeightCode,complexRationalPoint,Nat.unpair_pair,h0,Complex.ofReal_zero,
    zero_mul,add_zero,rationalMultiplyCode_value,haltingEvaluationCode_value,laplaceGridCode_value R d j hd,
    bernsteinChooseCode_value d j hj]

@[irreducible] def haltingBernsteinTermCode (R d j : ℕ) : ℕ :=
  polynomialProductCode (polynomialConstantCode (haltingBernsteinWeightCode R d j))
    (polynomialProductCode (polynomialPowerCode (bernsteinAffineCode true R) j)
      (polynomialPowerCode (bernsteinAffineCode false R) (d-j)))

def haltingBernsteinTermProgram : AlphaTerm :=
  let R := onComponent (numericalProjectionTerm true) true
  let D := onComponent (numericalProjectionTerm false) true
  let J := numericalProjectionTerm false
  numericalCompose polynomialProductProgram (pairNumerical
    (numericalCompose polynomialConstantProgram haltingBernsteinWeightProgram)
    (numericalCompose polynomialProductProgram (pairNumerical
      (numericalCompose polynomialPowerProgram (pairNumerical (numericalCompose (bernsteinAffineProgram true) R) J))
      (numericalCompose polynomialPowerProgram (pairNumerical (numericalCompose (bernsteinAffineProgram false) R)
        (numericalCombine subtractionTerm D J))))))

theorem haltingBernsteinTermProgram_computes : NumericalComputes haltingBernsteinTermProgram
    (fun p => haltingBernsteinTermCode p.unpair.1.unpair.1 p.unpair.1.unpair.2 p.unpair.2) := by
  have r := (projection_computes true).onComponent true
  have d := (projection_computes false).onComponent true
  have j := projection_computes false
  have h := polynomialProductProgram_computes.comp
    ((polynomialConstantProgram_computes.comp haltingBernsteinWeightProgram_computes).pair
      (polynomialProductProgram_computes.comp
        ((polynomialPowerProgram_computes.comp (((bernsteinAffineProgram_computes true).comp r).pair j)).pair
          (polynomialPowerProgram_computes.comp (((bernsteinAffineProgram_computes false).comp r).pair
            (d.combine j subtractionTerm_closed (fun d j => d-j) subtractionTerm_apply))))))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [haltingBernsteinTermProgram,haltingBernsteinTermCode,Nat.unpair_pair,
    ite_true,Bool.false_eq_true,ite_false] using h.2 p

@[irreducible] def haltingBernsteinCode (R d : ℕ) : ℕ :=
  polynomialSumCode (fun p => haltingBernsteinTermCode p.unpair.1.unpair.1 p.unpair.1.unpair.2 p.unpair.2)
    (Nat.pair R d) (d+1)

def haltingBernsteinProgram : AlphaTerm := numericalCompose (polynomialSumProgram haltingBernsteinTermProgram)
  (pairNumerical numericalIdentity (numericalCompose successorTerm (numericalProjectionTerm false)))

theorem haltingBernsteinProgram_computes : NumericalComputes haltingBernsteinProgram
    (fun p => haltingBernsteinCode p.unpair.1 p.unpair.2) := by
  have h := (polynomialSumProgram_computes haltingBernsteinTermProgram_computes).comp
    (numericalIdentity_computes.pair (successor_computes.comp (projection_computes false)))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [haltingBernsteinProgram,haltingBernsteinCode,Nat.unpair_pair,Nat.pair_unpair,
    id_eq,Bool.false_eq_true,ite_false] using h.2 p

def haltingBernsteinDegreeProgram : AlphaTerm :=
  let V := mulNumerical (numericalProjectionTerm true) (numericalCompose powerTwoTerm (numericalProjectionTerm false))
  mulNumerical V V

theorem haltingBernsteinDegreeProgram_computes : NumericalComputes haltingBernsteinDegreeProgram
    (fun p => haltingBernsteinDegree p.unpair.1 p.unpair.2) := by
  have h := (projection_computes true).mul (powerTwo_computes.comp (projection_computes false))
  simpa only [haltingBernsteinDegreeProgram,haltingBernsteinDegree,pow_two,ite_true,Bool.false_eq_true,ite_false] using h.mul h

@[irreducible] def haltingPolynomialName (z : ℕ) : ℕ :=
  haltingBernsteinCode z.unpair.1 (haltingBernsteinDegree z.unpair.1 z.unpair.2)

def haltingPolynomialNameProgram : AlphaTerm := numericalCompose haltingBernsteinProgram
  (pairNumerical (numericalProjectionTerm true) haltingBernsteinDegreeProgram)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Starting with the constant polynomial one, iterate multiplication to form each power of $\ell_+$ and $\ell_-$.
    Multiply their product by the constant $v_j\binom dj$, and add the resulting polynomial lists for $0\le j\le d$,
    starting with the empty list for zero. Parameterized recursion retains $R,d$ throughout. Composing these closed terms
    with the calculation of $d$ gives a closed numerical term $T$ with
    $$T\ChurchNumeral{\NatPair{R}{n}}\to_\beta^*\ChurchNumeral{q(\NatPair{R}{n})},$$
    where $q(\NatPair{R}{n})$ decodes to the coefficient list of $Q_{R,n}$. The preceding error estimate proves that
    $q$ is a computable locally uniform polynomial name of $f$. The name condition only tests $R\ge1$; at $R=0$ the
    program may return any fixed polynomial code.
-/
theorem haltingPolynomialNameProgram_computes : NumericalComputes haltingPolynomialNameProgram haltingPolynomialName := by
  have h := haltingBernsteinProgram_computes.comp ((projection_computes true).pair haltingBernsteinDegreeProgram_computes)
  refine ⟨h.1,fun z => ?_⟩
  simpa only [haltingPolynomialNameProgram,haltingPolynomialName,Nat.unpair_pair,ite_true] using h.2 z

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    The coefficient list of $Q_{R,n}$ can be generated using closed terms. For $0\le j\le d$, compute the rational sample
    $$v_j:=f(-R+2Rj/d)=g_R(j/d)$$
    by applying $E$ to the grid-point code $\RationalCode{2Rj}{Rd}{d-1}$; here $d\ge1$.
    Compute the binomial coefficient as the rational number
    $$\binom dj=\frac{d!}{j!(d-j)!},$$
    using the factorial and reciprocal-factorial programs. The natural-number differences $d-1$ and $d-j$ are nonnegative.
    The two affine polynomials
    $$\ell_+(x):=\frac12+\frac{x}{2R},\qquad
     \ell_-(x):=\frac12-\frac{x}{2R}$$
    have explicit two-entry coefficient lists. The required polynomial is
    $$Q_{R,n}(x)=\sum_{j=0}^{d}v_j\binom dj\ell_+(x)^j\ell_-(x)^{d-j}.$$
-/
theorem haltingBernsteinTermCode_eval (R d j : ℕ) (hR : 0<R) (hd : 0<d) (hj : j≤d) (x : ℝ) :
    (complexPolynomial (haltingBernsteinTermCode R d j)).eval (x:ℂ) =
      ((haltingIntegralFunction (-(R:ℝ)+(2*R/d)*j)*(d.choose j)*
        ((x+R)/(2*R))^j*((R-x)/(2*R))^(d-j):ℝ):ℂ) := by
  simp only [haltingBernsteinTermCode,polynomialProductCode_value,polynomialConstantCode_value,
    polynomialPowerCode_value,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    haltingBernsteinWeightCode_value R d j hd hj,bernsteinAffineCode_eval true R hR x,
    bernsteinAffineCode_eval false R hR x,ite_true,Bool.false_eq_true,ite_false]
  push_cast
  ring

/-- The decoded polynomial is exactly the rescaled Bernstein approximation. -/
theorem haltingBernsteinCode_eval (R d : ℕ) (hR : 0<R) (hd : 0<d) (t : I) :
    (complexPolynomial (haltingBernsteinCode R d)).eval (((2*(R:ℝ)*(t:ℝ)-R):ℝ):ℂ) =
      (bernsteinApproximation d (haltingRescaled R) t:ℂ) := by
  have hR0 : (R:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have ha : ((2*(R:ℝ)*(t:ℝ)-R)+R)/(2*R) = t := by field_simp; ring
  have hb : ((R:ℝ)-(2*R*(t:ℝ)-R))/(2*R) = 1-(t:ℝ) := by field_simp; ring
  rw [haltingBernsteinCode,polynomialSumCode_value,Polynomial.eval_finsetSum,Finset.sum_range,
    bernsteinApproximation.apply,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.unpair_pair]
  rw [haltingBernsteinTermCode_eval R d j hR hd j.is_le,ha,hb]
  apply congrArg Complex.ofReal
  simp only [smul_eq_mul,haltingRescaled,ContinuousMap.coe_mk,bernstein_apply,bernstein.z]
  have hg : -(R:ℝ)+(2*R/d)*(j:ℝ) = 2*R*((j:ℝ)/d)-R := by ring
  rw [hg]
  ring

noncomputable def haltingIntegralContinuous : C(ℝ,ℂ) where
  toFun x := (haltingIntegralFunction x:ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp haltingIntegralFunction_continuous

theorem haltingPolynomialName_isName : IsLocallyUniformPolynomialName haltingIntegralContinuous haltingPolynomialName := by
  intro R hR n x hx
  have hR0 : (0:ℝ)<R := Nat.cast_pos.mpr hR
  let t : I := ⟨(x+R)/(2*R),by
    constructor
    · exact div_nonneg (by linarith [(abs_le.mp hx).1]) (by positivity)
    · apply (div_le_one (by positivity : (0:ℝ)<2*R)).mpr
      linarith [(abs_le.mp hx).2]⟩
  have ht : 2*(R:ℝ)*(t:ℝ)-R = x := by dsimp [t]; field_simp; ring
  have he := haltingBernsteinCode_eval R (haltingBernsteinDegree R n) hR (haltingBernsteinDegree_pos hR n) t
  rw [ht] at he
  simp only [haltingPolynomialName,Nat.unpair_pair]
  rw [he]
  have h := haltingBernsteinDegree_error hR n t
  change |bernsteinApproximation (haltingBernsteinDegree R n) (haltingRescaled R) t-
    haltingIntegralFunction (2*(R:ℝ)*(t:ℝ)-R)| ≤ _ at h
  rw [ht] at h
  change ‖(haltingIntegralFunction x:ℂ)-(bernsteinApproximation
    (haltingBernsteinDegree R n) (haltingRescaled R) t:ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
  exact h

/-- A computable continuous function, with a computable locally uniform polynomial name,
whose Fourier value at zero is noncomputable and which has no computable L1 step name. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: example
  title: A computable integrable function with a noncomputable integral
-/
theorem haltingIntegral_complete_example :
    HasComputableRealizer realRepresentation realRepresentation haltingIntegralFunction ∧
    (∀ x, 0 ≤ haltingIntegralFunction x) ∧ MeasureTheory.Integrable haltingIntegralFunction ∧
    NumericalComputes haltingPolynomialNameProgram haltingPolynomialName ∧
    IsLocallyUniformPolynomialName haltingIntegralContinuous haltingPolynomialName ∧
    Real.Lp.fourierTransform haltingIntegralLp 0 = (haltingSetReal diagonalHalts:ℂ) ∧
    (¬ ∃ (P : AlphaTerm) (p : ℕ → ℕ), NumericalComputes P p ∧
      IsLocallyUniformPolynomialName (Real.Lp.fourierTransform haltingIntegralLp).toContinuousMap p) ∧
    ¬ ∃ (P : AlphaTerm) (p : ℕ → ℕ), NumericalComputes P p ∧ IsL1StepName haltingIntegralLp p :=
  ⟨haltingIntegralFunction_hasComputableRealizer,haltingIntegralFunction_nonneg,haltingIntegralFunction_integrable,
    haltingPolynomialNameProgram_computes,haltingPolynomialName_isName,haltingIntegralLp_fourier_zero,
    haltingIntegral_fourier_not_computable,haltingIntegral_no_computable_L1_name⟩

end PolishSpaceBook
