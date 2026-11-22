module

public import PolishSpaceBook.LambdaRealRepresentation
public import PolishSpaceBook.LambdaBoundedProducts
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Computing e by the factorial series, with explicit lambda recursion -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open Filter Topology
set_option maxRecDepth 4096

/-- The common-denominator numerator of the partial sum through 1/j!. -/
def eulerNumerator : ℕ → ℕ := primitiveRec 1 (fun j a => (j+1)*a+1)

theorem eulerNumerator_succ (j : ℕ) :
    eulerNumerator (j+1) = (j+1)*eulerNumerator j+1 := rfl

noncomputable def eulerPartialSum (j : ℕ) : ℝ := ∑ i ∈ Finset.range (j+1), 1/(i.factorial:ℝ)

theorem eulerNumerator_value (j : ℕ) :
    (eulerNumerator j:ℝ)/(j.factorial:ℝ) = eulerPartialSum j := by
  induction j with
  | zero => norm_num [eulerNumerator,primitiveRec,eulerPartialSum]
  | succ j ih =>
    have hf : (j.factorial:ℝ) ≠ 0 := by positivity
    have hj : (j:ℝ)+1 ≠ 0 := by positivity
    rw [eulerNumerator_succ,Nat.factorial_succ]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one]
    rw [eulerPartialSum,Finset.sum_range_succ,← eulerPartialSum,← ih,Nat.factorial_succ]
    push_cast
    field_simp

/-- Every extra factorial factor is at least two. -/
theorem eulerFactorial_tail_growth (j i : ℕ) :
    (j+1).factorial * 2^i ≤ (i+(j+1)).factorial := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ,show i+1+(j+1) = (i+(j+1))+1 by omega,Nat.factorial_succ]
    calc
      (j+1).factorial * (2^i*2) = ((j+1).factorial*2^i)*2 := by ring
      _ ≤ (i+(j+1)).factorial*2 := Nat.mul_le_mul_right 2 ih
      _ ≤ (i+(j+1)+1)*(i+(j+1)).factorial := by nlinarith

theorem eulerFactorial_growth (j : ℕ) : 2^j ≤ (j+1).factorial := by
  simpa using eulerFactorial_tail_growth 0 j

theorem euler_series_hasSum : HasSum (fun i : ℕ => 1/(i.factorial:ℝ)) (Real.exp 1) := by
  simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (1:ℝ)

/-- Compare the entire tail, term by term, with a geometric series. -/
theorem euler_series_tail (j : ℕ) :
    0 ≤ Real.exp 1 - eulerPartialSum j ∧
    Real.exp 1 - eulerPartialSum j ≤ 2/((j+1).factorial:ℝ) := by
  have hsum := euler_series_hasSum.summable
  have ht := (summable_nat_add_iff (j+1)).mpr hsum
  have heq : Real.exp 1 - eulerPartialSum j =
      ∑' i, 1/((i+(j+1)).factorial:ℝ) := by
    have h := hsum.sum_add_tsum_nat_add (j+1)
    rw [euler_series_hasSum.tsum_eq] at h
    exact (eq_sub_iff_add_eq.mpr (by simpa [eulerPartialSum,add_comm] using h)).symm
  rw [heq]
  refine ⟨tsum_nonneg (fun _ => by positivity), ?_⟩
  have hg := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).mul_left
    (1/((j+1).factorial:ℝ))
  calc
    ∑' i, 1/((i+(j+1)).factorial:ℝ)
        ≤ ∑' i, (1/((j+1).factorial:ℝ))*(1/2:ℝ)^i := by
      apply ht.tsum_le_tsum _ hg
      intro i
      have hf : (0:ℝ)<(j+1).factorial*2^i := by positivity
      have hb : ((j+1).factorial:ℝ)*2^i ≤ (i+(j+1)).factorial := by
        exact_mod_cast eulerFactorial_tail_growth j i
      calc
        1/((i+(j+1)).factorial:ℝ) ≤ 1/((j+1).factorial*2^i) :=
          one_div_le_one_div_of_le hf hb
        _ = _ := by simp [one_div,mul_inv_rev,inv_pow,mul_comm]
    _ = 2/((j+1).factorial:ℝ) := by
      rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring

/-- At precision n take the partial sum through (n+4)!. -/
def eulerRationalCode (n : ℕ) : RationalCode :=
  ((eulerNumerator (n+4),0),(n+4).factorial-1)

def eulerName (n : ℕ) : ℕ := (eulerRationalCode n).natCode

theorem eulerName_value (n : ℕ) : rationalPoint (eulerName n) = eulerPartialSum (n+4) := by
  have hf : 1 ≤ (n+4).factorial := Nat.factorial_pos _
  rw [← eulerNumerator_value]
  simp [eulerName,rationalPoint,eulerRationalCode,RationalCode.value,Nat.sub_add_cancel hf]

theorem eulerName_error (n : ℕ) :
    |rationalPoint (eulerName n) - Real.exp 1| ≤ (1/2:ℝ)^(n+3) := by
  rw [eulerName_value,abs_sub_comm,abs_of_nonneg (euler_series_tail (n+4)).1]
  apply (euler_series_tail (n+4)).2.trans
  have hg : (2:ℝ)^(n+4) ≤ ((n+4+1).factorial:ℝ) := by
    exact_mod_cast eulerFactorial_growth (n+4)
  calc
    2/((n+4+1).factorial:ℝ) ≤ 2/(2:ℝ)^(n+4) := by gcongr
    _ = (1/2:ℝ)^(n+3) := by
      rw [show n+4 = (n+3)+1 by omega,pow_succ,one_div_pow]
      field_simp

/-- One closed term for the factorial update on the encoded pair (j,r). -/
def eulerFactorialStep : AlphaTerm :=
  mulNumerical (numericalCompose successorTerm (numericalProjectionTerm true))
    (numericalProjectionTerm false)

theorem eulerFactorialStep_computes :
    NumericalComputes eulerFactorialStep (fun z => (z.unpair.1+1)*z.unpair.2) := by
  simpa [eulerFactorialStep,Nat.succ_eq_add_one] using
    (successor_computes.comp (projection_computes true)).mul (projection_computes false)

def eulerFactorialProgram : AlphaTerm :=
  app (app recursorTerm (curryNumerical eulerFactorialStep)) (numeral 1)

theorem eulerFactorial_computes : NumericalComputes eulerFactorialProgram Nat.factorial := by
  have hc := curryNumerical_closed eulerFactorialStep_computes.1
  refine ⟨closed_app (closed_app recursorTerm_closed hc) (numeral_closed 1), fun n => ?_⟩
  apply recursorTerm_apply hc (fun j => numeral j.factorial) (fun j => numeral_closed _) _ n
  intro j
  exact (curryNumerical_apply eulerFactorialStep_computes.1 j j.factorial).trans (by
    simpa only [Nat.unpair_pair,Nat.factorial_succ] using
      eulerFactorialStep_computes.2 (Nat.pair j j.factorial))

def eulerNumeratorStep : AlphaTerm := addNumerical eulerFactorialStep (numericalConstant 1)

theorem eulerNumeratorStep_computes :
    NumericalComputes eulerNumeratorStep (fun z => (z.unpair.1+1)*z.unpair.2+1) :=
  eulerFactorialStep_computes.add (numericalConstant_computes 1)

def eulerNumeratorProgram : AlphaTerm :=
  app (app recursorTerm (curryNumerical eulerNumeratorStep)) (numeral 1)

theorem eulerNumerator_computes : NumericalComputes eulerNumeratorProgram eulerNumerator := by
  have hc := curryNumerical_closed eulerNumeratorStep_computes.1
  refine ⟨closed_app (closed_app recursorTerm_closed hc) (numeral_closed 1), fun n => ?_⟩
  apply recursorTerm_numeral hc 1 (fun j r => (j+1)*r+1)
  intro j r
  exact (curryNumerical_apply eulerNumeratorStep_computes.1 j r).trans (by
    simpa only [Nat.unpair_pair] using eulerNumeratorStep_computes.2 (Nat.pair j r))

def eulerNameProgram : AlphaTerm :=
  let N := addNumerical numericalIdentity (numericalConstant 4)
  let A := numericalCompose eulerNumeratorProgram N
  let F := numericalCompose eulerFactorialProgram N
  pairNumerical (pairNumerical A (numericalConstant 0)) (numericalCompose predecessorTerm F)

theorem eulerName_computes : NumericalComputes eulerNameProgram eulerName := by
  have hn := numericalIdentity_computes.add (numericalConstant_computes 4)
  exact ((eulerNumerator_computes.comp hn).pair (numericalConstant_computes 0)).pair
    (predecessor_computes.comp (eulerFactorial_computes.comp hn))

theorem eulerName_isCauchy : IsCauchyName rationalPoint eulerName := by
  intro n m hnm
  calc
    dist (rationalPoint (eulerName n)) (rationalPoint (eulerName m))
        ≤ dist (rationalPoint (eulerName n)) (Real.exp 1) +
          dist (Real.exp 1) (rationalPoint (eulerName m)) := dist_triangle _ _ _
    _ ≤ (1/2:ℝ)^(n+3) + (1/2:ℝ)^(m+3) := by
      rw [dist_comm (Real.exp 1)]
      exact add_le_add (eulerName_error n) (eulerName_error m)
    _ ≤ (1/2:ℝ)^(n+3) + (1/2:ℝ)^(n+3) := add_le_add_right
      (pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
        (Nat.add_le_add_right hnm 3)) _
    _ ≤ (1/2:ℝ)^n := by
      rw [pow_add]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]

theorem eulerName_tendsto :
    Tendsto (fun n => rationalPoint (eulerName n)) atTop (𝓝 (Real.exp 1)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2:ℝ)<1)
  refine ⟨N,fun n hn => ?_⟩
  exact lt_of_le_of_lt ((eulerName_error n).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))) hN

def eulerNamePoint : realRepresentation.domain := ⟨eulerName,eulerName_isCauchy⟩

theorem eulerName_represents : realRepresentation.toFun eulerNamePoint = Real.exp 1 :=
  tendsto_nhds_unique (tendsto_cauchyRepresentation rationalPoint eulerNamePoint) eulerName_tendsto

/-- A literal closed lambda program computes a Cauchy name of the standard real exp(1). -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: example
  title: Computing $e$ by its series
  excerpt: |
    \begin{example*}[Computing $e$ by its series]
    The real number $e=\exp(1)=\sum_{j=0}^{\infty}1/j!$ is computable.
    \end{example*}
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Put $S_J:=\sum_{j=0}^{J}1/j!$. Compute its numerator and denominator by the integer recurrences
    $$f_0=a_0=1,\qquad f_{j+1}=(j+1)f_j,\qquad a_{j+1}=(j+1)a_j+1.$$
    Induction gives $f_j=j!$ and $S_j=a_j/f_j$: adding $1/(j+1)!$ multiplies the old numerator by $j+1$ and adds $1$.
    No division of integers is needed to construct this fraction.

    For $J,r\in\NN$, each of the $r$ additional factors in $(J+1+r)!$ is at least $2$, so
    $$(J+1+r)!\ge(J+1)!\,2^r.$$
    Comparing the tail term by term with a geometric series therefore gives
    $$\begin{aligned}
    0\le e-S_J&=\sum_{r=0}^{\infty}\frac1{(J+1+r)!}\\
    &\le\frac1{(J+1)!}\sum_{r=0}^{\infty}2^{-r}=\frac2{(J+1)!}.
    \end{aligned}$$
    The same factorial inequality with initial factorial $1!$ gives $(J+1)!\ge2^J$.
    Thus the explicit choice $J=n+4$ suffices: the rational $q_n:=S_{n+4}$ satisfies
    $$|q_n-e|\le\frac2{(n+5)!}\le2^{-(n+3)}.$$
    In particular $q_n\to e$, and the triangle inequality gives
    $$|q_n-q_m|\le2^{-(n+3)}+2^{-(m+3)}\le2^{-n}\qquad(m\ge n).$$
    These estimates specify the precision in advance; they require no test on an unknown real-valued error.

    Here are closed terms for the two integer recurrences. Define
    $$\begin{aligned}
    H_f&:=\lambdaab{u}{\lambdaab{v}{\LambdaMul\,(\LambdaSucc\,u)\,v}},\\
    H_a&:=\lambdaab{u}{\lambdaab{v}{\LambdaAdd\,(H_fuv)\,\ChurchNumeral{1}}},\\
    F&:=\LambdaRecursor\,H_f\,\ChurchNumeral{1},\qquad
    A:=\LambdaRecursor\,H_a\,\ChurchNumeral{1}.
    \end{aligned}$$
    The arithmetic reductions and the recursor theorem give
    $$F\ChurchNumeral{j}\to_\beta^*\ChurchNumeral{f_j},\qquad
    A\ChurchNumeral{j}\to_\beta^*\ChurchNumeral{a_j}.$$
    Indeed, at stage $j$ the step terms return $(j+1)f_j$ and $(j+1)a_j+1$, respectively, so induction proves both
    reductions with initial value $1$.

    Compose these terms with addition, predecessor, and numerical pairing to output
    $$p(n):=\RationalCode{a_{n+4}}{0}{f_{n+4}-1}.$$
    Since $f_{n+4}>0$, the subtraction in the denominator code is ordinary subtraction.
    The resulting closed term $P$ satisfies
    $$P\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{p(n)}.$$
    This code represents $a_{n+4}/f_{n+4}=q_n$. The preceding bounds show that $p$ is a computable fast Cauchy name of $e$.
    \end{proof}
-/
theorem euler_computable :
    ∃ p : realRepresentation.domain, realRepresentation.toFun p = Real.exp 1 ∧
      ∃ P : AlphaTerm, NumericalComputes P p.val :=
  ⟨eulerNamePoint,eulerName_represents,eulerNameProgram,eulerName_computes⟩

end PolishSpaceBook
