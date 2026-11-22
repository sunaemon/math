module

public import PolishSpaceBook.LambdaFourierLists

@[expose] public section

/-! # Rational exponential sums computed by closed lambda terms -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA

/-- Form a code for -|q| by comparing the two unsigned numerator parts. -/
def rationalNegativeAbsCode (c : ℕ) : ℕ :=
  RationalCode.natCode ((0,(c.unpair.1.unpair.1-c.unpair.1.unpair.2)+
    (c.unpair.1.unpair.2-c.unpair.1.unpair.1)),c.unpair.2)

theorem rationalNegativeAbsCode_value (c : ℕ) :
    rationalPoint (rationalNegativeAbsCode c) = -|rationalPoint c| := by
  simp only [rationalNegativeAbsCode,rationalPoint,RationalCode.ofNat_natCode]
  simp only [RationalCode.ofNat,RationalCode.value]
  push_cast
  rw [abs_div,abs_of_pos (by positivity : (0:ℝ)<c.unpair.2+1)]
  by_cases h : c.unpair.1.unpair.1 ≤ c.unpair.1.unpair.2
  · rw [Nat.sub_eq_zero_of_le h,Nat.cast_zero,zero_add,Nat.cast_sub h,
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · have h' := le_of_not_ge h
    rw [Nat.sub_eq_zero_of_le h',Nat.cast_zero,add_zero,Nat.cast_sub h',
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h'))]
    ring

def rationalNegativeAbsProgram : AlphaTerm :=
  let a := rationalNumeratorTerm true
  let b := rationalNumeratorTerm false
  pairNumerical (pairNumerical (numericalConstant 0)
    (addNumerical (numericalCombine subtractionTerm a b) (numericalCombine subtractionTerm b a)))
    (numericalProjectionTerm false)

theorem rationalNegativeAbsProgram_computes :
    NumericalComputes rationalNegativeAbsProgram rationalNegativeAbsCode := by
  have a := rationalNumerator_computes true
  have b := rationalNumerator_computes false
  exact ((numericalConstant_computes 0).pair
    ((a.combine b subtractionTerm_closed (fun m n => m-n) subtractionTerm_apply).add
      (b.combine a subtractionTerm_closed (fun m n => m-n) subtractionTerm_apply))).pair
    (projection_computes false)

@[irreducible] def exponentialTermCode (c j : ℕ) : ℕ :=
  Nat.pair (rationalMultiplyCode (rationalPowerCode c j) (factorialReciprocalCode j)) 0

def exponentialTermProgram : AlphaTerm := pairNumerical
  (numericalCompose rationalMultiplyProgram (pairNumerical rationalPowerProgram
    (numericalCompose factorialReciprocalProgram (numericalProjectionTerm false)))) (numericalConstant 0)

theorem exponentialTermProgram_computes : NumericalComputes exponentialTermProgram
    (fun p => exponentialTermCode p.unpair.1 p.unpair.2) := by
  have h := (rationalMultiplyProgram_computes.comp (rationalPowerProgram_computes.pair
    (factorialReciprocalProgram_computes.comp (projection_computes false)))).pair (numericalConstant_computes 0)
  refine ⟨h.1,fun p => ?_⟩
  simpa only [exponentialTermCode,exponentialTermProgram,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using h.2 p

theorem exponentialTermCode_value (c j : ℕ) :
    complexRationalPoint (exponentialTermCode c j) = (rationalPoint c:ℂ)^j/(j.factorial:ℂ) := by
  have h0 : rationalPoint 0 = 0 := by norm_num [rationalPoint,RationalCode.ofNat,RationalCode.value]
  simp only [exponentialTermCode,complexRationalPoint,Nat.unpair_pair,rationalMultiplyCode_value,
    rationalPowerCode_value,factorialReciprocalCode_value,h0,Complex.ofReal_zero,zero_mul,add_zero,
    Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_natCast,mul_one_div]

@[irreducible] def exponentialSumCode (c N : ℕ) : ℕ := complexSumCode
  (fun p => exponentialTermCode p.unpair.1 p.unpair.2) c N

def exponentialSumProgram : AlphaTerm := complexSumProgram exponentialTermProgram

theorem exponentialSumProgram_computes : NumericalComputes exponentialSumProgram
    (fun p => exponentialSumCode p.unpair.1 p.unpair.2) := by
  simpa only [exponentialSumCode,exponentialSumProgram] using
    complexSumProgram_computes exponentialTermProgram_computes

theorem exponentialSumCode_value (c N : ℕ) :
    complexRationalPoint (exponentialSumCode c N) = exponentialPartial (rationalPoint c) N := by
  simp only [exponentialSumCode,complexSumCode_value,Nat.unpair_pair,exponentialTermCode_value,exponentialPartial]

/-- Inputs are (rational code,(integer bound,precision)). -/
@[irreducible] def exponentialApproxCode (c M n : ℕ) : ℕ := exponentialSumCode c (fourierCutoff M n)

def exponentialApproxProgram : AlphaTerm := numericalCompose exponentialSumProgram
  (pairNumerical (numericalProjectionTerm true)
    (numericalCompose fourierCutoffProgram (numericalProjectionTerm false)))

theorem exponentialApproxProgram_computes : NumericalComputes exponentialApproxProgram
    (fun p => exponentialApproxCode p.unpair.1 p.unpair.2.unpair.1 p.unpair.2.unpair.2) := by
  simpa only [exponentialApproxCode,exponentialApproxProgram,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using
    exponentialSumProgram_computes.comp ((projection_computes true).pair
      (fourierCutoffProgram_computes.comp (projection_computes false)))

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Set $K:=\FourierSeriesCutoff{R}{m}$ and take the rational values
    $$v_i:=\ExponentialPartialSum{K}{-|a_i|}
     =\sum_{j<K}\frac{(-|a_i|)^j}{j!}\qquad(i<L).$$
    Since $|a_i|\le R$, the exponential-series estimate proved in the uniform truncation lemma gives
    $$|f(a_i)-v_i|\le2^{-(m+2)}
     =2^{-(n+4)}2^{-R}\le\frac{2^{-(n+4)}}{R}=h,$$
    where the last inequality uses $R\le2^R$. These values are computed by closed terms: compare the two unsigned
    numerator parts of the rational code to form the code of $-|a_i|$, compute successive powers and factorials, and sum
    the first $K$ rational terms with an accumulator initially zero. The cutoff and every summand use only the numerical
    arithmetic and recursors already constructed.
-/
theorem exponentialApproxCode_error (c M n : ℕ) (hc : |rationalPoint c| ≤ M) :
    ‖(Real.exp (rationalPoint c):ℂ)-complexRationalPoint (exponentialApproxCode c M n)‖ ≤ (1/2:ℝ)^(n+2) := by
  rw [exponentialApproxCode,exponentialSumCode_value,Complex.ofReal_exp]
  exact exponentialPartial_cutoff_error M n (by simpa using hc)

end PolishSpaceBook
