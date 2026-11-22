module

public import PolishSpaceBook.LambdaRealRepresentation
public import PolishSpaceBook.LambdaBoundedProducts
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

/-! # The book's bisection algorithm for sqrt 2, by numerical lambda recursion -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open Filter Topology
set_option maxRecDepth 4096

/-- The interval after j steps is [k/2^j,(k+1)/2^j]. -/
def sqrtTwoLowerNumerator : ℕ → ℕ := primitiveRec 1 (fun j k =>
  2*k + if (2*k+1)^2 ≤ 2*(2^(j+1))^2 then 1 else 0)

theorem sqrtTwoLowerNumerator_succ (j : ℕ) : sqrtTwoLowerNumerator (j+1) =
    2*sqrtTwoLowerNumerator j +
      if (2*sqrtTwoLowerNumerator j+1)^2 ≤ 2*(2^(j+1))^2 then 1 else 0 := rfl

theorem sqrtTwo_midpoint_test (t j : ℕ) :
    (t : ℝ) ≤ Real.sqrt 2 * (2:ℝ)^j ↔ t^2 ≤ 2*(2^j)^2 := by
  rw [← sq_le_sq₀ (Nat.cast_nonneg t)
    (mul_nonneg (Real.sqrt_nonneg 2) (by positivity)),mul_pow,Real.sq_sqrt (by norm_num)]
  norm_cast

theorem sqrtTwoLowerNumerator_bounds (j : ℕ) :
    (sqrtTwoLowerNumerator j : ℝ) ≤ Real.sqrt 2 * (2:ℝ)^j ∧
    Real.sqrt 2 * (2:ℝ)^j ≤ sqrtTwoLowerNumerator j + 1 := by
  induction j with
  | zero =>
    simp only [sqrtTwoLowerNumerator,primitiveRec,Nat.cast_one,pow_zero,mul_one]
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2:ℝ)
    constructor <;> nlinarith
  | succ j ih =>
    rw [sqrtTwoLowerNumerator_succ]
    by_cases h : (2*sqrtTwoLowerNumerator j+1)^2 ≤ 2*(2^(j+1))^2
    · have ht := (sqrtTwo_midpoint_test (2*sqrtTwoLowerNumerator j+1) (j+1)).mpr h
      simp only [ite_eq_left h]
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,pow_succ] at ht ⊢
      constructor <;> nlinarith [ih.1,ih.2]
    · have ht : ¬ (2*sqrtTwoLowerNumerator j+1 : ℕ) ≤ Real.sqrt 2 * (2:ℝ)^(j+1) :=
        fun ht => h ((sqrtTwo_midpoint_test _ _).mp ht)
      simp only [ite_eq_right h]
      simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,
        pow_succ] at ht ⊢
      constructor <;> nlinarith [ih.1,ih.2]

/-- A code for the midpoint after n+2 bisections. -/
def sqrtTwoRationalCode (n : ℕ) : RationalCode :=
  ((2*sqrtTwoLowerNumerator (n+2)+1,0),2^(n+3)-1)

def sqrtTwoName (n : ℕ) : ℕ := (sqrtTwoRationalCode n).natCode

theorem sqrtTwoName_value (n : ℕ) : rationalPoint (sqrtTwoName n) =
    (2*(sqrtTwoLowerNumerator (n+2):ℝ)+1)/(2:ℝ)^(n+3) := by
  have hd : 1 ≤ (2:ℕ)^(n+3) := Nat.one_le_pow _ _ (by decide)
  simp [sqrtTwoName,rationalPoint,sqrtTwoRationalCode,RationalCode.value,Nat.sub_add_cancel hd]

theorem sqrtTwoName_error (n : ℕ) :
    |rationalPoint (sqrtTwoName n) - Real.sqrt 2| ≤ (1/2:ℝ)^(n+3) := by
  rw [sqrtTwoName_value]
  have hd : (0:ℝ) < 2^(n+3) := by positivity
  have hpow : (2:ℝ)^(n+3) = 2^(n+2)*2 := pow_succ _ _
  obtain ⟨hl,hu⟩ := sqrtTwoLowerNumerator_bounds (n+2)
  have habs : |2*(sqrtTwoLowerNumerator (n+2):ℝ)+1 - Real.sqrt 2 * 2^(n+3)| ≤ 1 := by
    rw [abs_le,hpow]
    constructor <;> nlinarith
  calc
    |(2*(sqrtTwoLowerNumerator (n+2):ℝ)+1)/2^(n+3) - Real.sqrt 2|
        = |2*(sqrtTwoLowerNumerator (n+2):ℝ)+1 - Real.sqrt 2 * 2^(n+3)|/2^(n+3) := by
          rw [← abs_of_pos hd,← abs_div]
          congr 1
          rw [abs_of_pos hd]
          field_simp
    _ ≤ 1/2^(n+3) := (div_le_div_iff_of_pos_right hd).mpr habs
    _ = (1/2:ℝ)^(n+3) := by rw [one_div_pow]

theorem sqrtTwoName_isCauchy : IsCauchyName rationalPoint sqrtTwoName := by
  intro n m hnm
  calc
    dist (rationalPoint (sqrtTwoName n)) (rationalPoint (sqrtTwoName m))
        ≤ dist (rationalPoint (sqrtTwoName n)) (Real.sqrt 2) +
          dist (Real.sqrt 2) (rationalPoint (sqrtTwoName m)) := dist_triangle _ _ _
    _ ≤ (1/2:ℝ)^(n+3) + (1/2:ℝ)^(m+3) := by
      rw [dist_comm (Real.sqrt 2)]
      exact add_le_add (sqrtTwoName_error n) (sqrtTwoName_error m)
    _ ≤ (1/2:ℝ)^(n+3) + (1/2:ℝ)^(n+3) := add_le_add_right
      (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
        (Nat.add_le_add_right hnm 3)) _
    _ ≤ (1/2:ℝ)^n := by
      rw [pow_add]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]

theorem sqrtTwoName_tendsto :
    Tendsto (fun n => rationalPoint (sqrtTwoName n)) atTop (𝓝 (Real.sqrt 2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2:ℝ)<1)
  refine ⟨N,fun n hn => ?_⟩
  exact lt_of_le_of_lt ((sqrtTwoName_error n).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))) hN

/-- The elementary parity argument, independent of the approximation algorithm. -/
theorem sqrtTwo_irrational_by_parity : Irrational (Real.sqrt 2) := by
  rintro ⟨q,hq⟩
  have hd : (q.den:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt q.den_pos)
  have hm : Real.sqrt 2 * (q.den:ℝ) = (q.num:ℝ) :=
    (eq_div_iff hd).mp (hq.symm.trans (Rat.cast_def q))
  have hs := congrArg (fun x : ℝ => x^2) hm
  rw [mul_pow,Real.sq_sqrt (by norm_num)] at hs
  have hi : q.num^2 = 2*(q.den:ℤ)^2 := by exact_mod_cast hs.symm
  have hn := congrArg Int.natAbs hi
  simp only [Int.natAbs_pow,Int.natAbs_mul] at hn
  norm_num at hn
  have ha : 2 ∣ q.num.natAbs := Nat.prime_two.dvd_of_dvd_pow ⟨q.den^2,hn⟩
  obtain ⟨c,hc⟩ := ha
  have hb : 2 ∣ q.den := Nat.prime_two.dvd_of_dvd_pow
    (show 2 ∣ q.den^2 from ⟨c^2,by nlinarith [hn]⟩)
  have hbad := Nat.eq_one_of_dvd_coprimes q.reduced ⟨c,hc⟩ hb
  norm_num at hbad


/-- The step receives the unused parameter, the counter j, and the lower numerator k. -/
def sqrtTwoStepProgram : AlphaTerm :=
  let J := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
  let K := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
  let twiceK := mulNumerical (numericalConstant 2) K
  let M := addNumerical twiceK (numericalConstant 1)
  let D := numericalCompose powerTwoTerm (numericalCompose successorTerm J)
  addNumerical twiceK (numericalCombine lessOrEqualTerm (mulNumerical M M)
    (mulNumerical (numericalConstant 2) (mulNumerical D D)))

theorem sqrtTwoStep_computes : NumericalComputes sqrtTwoStepProgram (fun z =>
    2*z.unpair.2.unpair.2 +
      if (2*z.unpair.2.unpair.2+1)^2 ≤ 2*(2^(z.unpair.2.unpair.1+1))^2 then 1 else 0) := by
  have hj := (projection_computes true).comp (projection_computes false)
  have hk := (projection_computes false).comp (projection_computes false)
  have ht := (numericalConstant_computes 2).mul hk
  have hm := ht.add (numericalConstant_computes 1)
  have hd := powerTwo_computes.comp (successor_computes.comp hj)
  have hc := (hm.mul hm).combine ((numericalConstant_computes 2).mul (hd.mul hd))
    lessOrEqualTerm_closed (fun a b => if a ≤ b then 1 else 0) lessOrEqualTerm_apply
  simpa only [sqrtTwoStepProgram,pow_two,Nat.succ_eq_add_one,Bool.true_eq,ite_true,
    Bool.false_eq_true,ite_false] using ht.add hc

/-- The curried step G of the displayed recursor; the extra parameter is unused. -/
def sqrtTwoCurriedStep : AlphaTerm := app (curryThird sqrtTwoStepProgram) (numeral 0)

theorem sqrtTwoCurriedStep_closed : sqrtTwoCurriedStep.Closed :=
  closed_app (curryThird_closed sqrtTwoStep_computes.1) (numeral_closed 0)

def sqrtTwoStateProgram : AlphaTerm :=
  app (app recursorTerm sqrtTwoCurriedStep) (numeral 1)

theorem sqrtTwoState_computes : NumericalComputes sqrtTwoStateProgram sqrtTwoLowerNumerator := by
  refine ⟨closed_app (closed_app recursorTerm_closed sqrtTwoCurriedStep_closed) (numeral_closed 1), ?_⟩
  intro n
  apply recursorTerm_numeral sqrtTwoCurriedStep_closed 1
    (fun j k => 2*k + if (2*k+1)^2 ≤ 2*(2^(j+1))^2 then 1 else 0)
  intro j k
  exact (curryThird_apply sqrtTwoStep_computes.1 0 j k).trans (by
    simpa only [Nat.unpair_pair] using sqrtTwoStep_computes.2 (Nat.pair 0 (Nat.pair j k)))

def sqrtTwoNameProgram : AlphaTerm :=
  let K := numericalCompose sqrtTwoStateProgram (addNumerical numericalIdentity (numericalConstant 2))
  let M := addNumerical (mulNumerical (numericalConstant 2) K) (numericalConstant 1)
  let D := numericalCompose predecessorTerm
    (numericalCompose powerTwoTerm (addNumerical numericalIdentity (numericalConstant 3)))
  pairNumerical (pairNumerical M (numericalConstant 0)) D

theorem sqrtTwoName_computes : NumericalComputes sqrtTwoNameProgram sqrtTwoName := by
  have hk := sqrtTwoState_computes.comp (numericalIdentity_computes.add (numericalConstant_computes 2))
  have hm := ((numericalConstant_computes 2).mul hk).add (numericalConstant_computes 1)
  have hd := predecessor_computes.comp
    (powerTwo_computes.comp (numericalIdentity_computes.add (numericalConstant_computes 3)))
  exact (hm.pair (numericalConstant_computes 0)).pair hd

def sqrtTwoNamePoint : realRepresentation.domain := ⟨sqrtTwoName,sqrtTwoName_isCauchy⟩

theorem sqrtTwoName_represents : realRepresentation.toFun sqrtTwoNamePoint = Real.sqrt 2 :=
  tendsto_nhds_unique (tendsto_cauchyRepresentation rationalPoint sqrtTwoNamePoint) sqrtTwoName_tendsto

/-- Irrationality and a literal finite lambda program computing a name are both supplied. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: example
  title: A computable irrational: $\sqrt2$
  excerpt: |
    \begin{example*}[A computable irrational: $\sqrt2$]
    The real number $\sqrt2$ is irrational and computable.
    \end{example*}
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Start with $I_0=[1,2]$. If $I_j=[a,b]$, compute the rational midpoint $m=(a+b)/2$. Put $I_{j+1}=[m,b]$ when $m^2\le2$,
    and $I_{j+1}=[a,m]$ otherwise. To implement this bisection with natural-number operations, write
    $$I_j=\left[\frac{k_j}{2^j},\frac{k_j+1}{2^j}\right],\qquad k_0=1.$$
    The midpoint test, after multiplication by the positive denominator squared, gives the recurrence
    $$k_{j+1}=\begin{cases}
    2k_j+1,&(2k_j+1)^2\le2(2^{j+1})^2,\\
    2k_j,&(2k_j+1)^2>2(2^{j+1})^2.
    \end{cases}$$
    These are exact integer comparisons, so no test of equality between real numbers is needed.

    Inductively,
    $$k_j\le\sqrt2\,2^j\le k_j+1.$$
    The initial case is $1\le\sqrt2\le2$. In the first branch of the recurrence the midpoint is at most $\sqrt2$,
    so the right half of $I_j$ still contains $\sqrt2$; in the second branch the left half does.
    Thus $I_j$ contains $\sqrt2$ and has length $2^{-j}$. Its midpoint at stage $n+2$ is
    $$q_n:=\frac{2k_{n+2}+1}{2^{n+3}},\qquad |q_n-\sqrt2|\le2^{-(n+3)}.$$
    Thus $q_n\to\sqrt2$, and for $m\ge n$,
    $$|q_n-q_m|\le2^{-(n+3)}+2^{-(m+3)}\le2^{-(n+2)}\le2^{-n}.$$
    This verifies the pairwise bounds required of a fast Cauchy name, as well as its limit.

    For completeness, the program can be built from the elementary lambda procedures as follows. The closed term
    $$D:=\lambdaab{u}{u\,(\LambdaMul\,\ChurchNumeral{2})\,\ChurchNumeral{1}}$$
    computes $j\mapsto2^j$. Compose it with addition, multiplication, and the numerical comparison from
    §{sec:lambda-numerical-comparisons} to obtain a closed step term $G$ computing the displayed update from $j,k_j$.
    The recursor of §{sec:lambda-primitive-recursion} gives the closed term
    $$A:=\LambdaRecursor\,G\,\ChurchNumeral{1},\qquad
    A\ChurchNumeral{j}\to_\beta^*\ChurchNumeral{k_j}.$$
    The reduction follows by induction on $j$: the initial value is $1$, and each recursion step performs precisely the
    integer test and update above.

    Use the rational codes of §{sec:lambda-rational-arithmetic}, where $\RationalCode{a}{b}{c}$ represents $(a-b)/(c+1)$.
    Compose $A,D$ with addition, multiplication, predecessor, and numerical pairing to produce the code
    $$p(n):=\RationalCode{2k_{n+2}+1}{0}{2^{n+3}-1}.$$
    Here the predecessor is applied to the positive integer $2^{n+3}$, so the displayed subtraction is ordinary subtraction.
    Every component terminates on Church numerals; their composition is a closed term $P$ satisfying
    $$P\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{p(n)}.$$
    The rational represented by $p(n)$ is exactly $q_n$. The bounds already proved show that $p$ is a computable fast
    Cauchy name of $\sqrt2$.

    Irrationality is separate: if $\sqrt2=a/b$ in lowest terms with positive integers $a,b$, then $a^2=2b^2$ forces $a$
    to be even. Writing $a=2c$ gives $b^2=2c^2$, so $b$ is also even, contradicting coprimality.
    \end{proof}
-/
theorem sqrtTwo_irrational_computable : Irrational (Real.sqrt 2) ∧
    ∃ p : realRepresentation.domain, realRepresentation.toFun p = Real.sqrt 2 ∧
      ∃ P : AlphaTerm, NumericalComputes P p.val :=
  ⟨sqrtTwo_irrational_by_parity,sqrtTwoNamePoint,sqrtTwoName_represents,sqrtTwoNameProgram,sqrtTwoName_computes⟩

end PolishSpaceBook
