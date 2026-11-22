module

public import PolishSpaceBook.LambdaRealRepresentation
public import PolishSpaceBook.LambdaListAccess
public import PolishSpaceBook.LambdaBoundedProducts
public import PolishSpaceBook.LambdaNumericalQueries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Data.List.GetD

@[expose] public section

/-! # Exact integration of rational polynomial codes and uniform integration on [0,1]

A polynomial code is a finite list of rational coefficient codes, in ascending
powers. The numerical program divides each coefficient by its positive exponent
successor and adds. The name transformer makes one input query at precision n+2.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open Filter Topology
set_option maxRecDepth 4096

/-- Finite coefficient lists denote ordinary mathlib polynomials over the rationals. -/
noncomputable def rationalPolynomial (c : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (NatListCode.decode c).length,
    Polynomial.monomial j (RationalCode.ofNat ((NatListCode.decode c).getD j 0)).value

noncomputable def realPolynomial (c : ℕ) : Polynomial ℝ :=
  (rationalPolynomial c).map (algebraMap ℚ ℝ)

theorem realPolynomial_eval (c : ℕ) (x : ℝ) :
    (realPolynomial c).eval x = ∑ j ∈ Finset.range (NatListCode.decode c).length,
      rationalPoint ((NatListCode.decode c).getD j 0) * x^j := by
  simp [realPolynomial,rationalPolynomial,rationalPoint]

/-- Divide a rational code by j+1 without changing its signed numerator. -/
def rationalDivideSuccCode (a j : ℕ) : ℕ :=
  RationalCode.natCode ((RationalCode.ofNat a).1,((RationalCode.ofNat a).2+1)*(j+1)-1)

theorem rationalDivideSuccCode_value (a j : ℕ) :
    rationalPoint (rationalDivideSuccCode a j) = rationalPoint a / (j+1:ℕ) := by
  have hp : 1 ≤ ((RationalCode.ofNat a).2+1)*(j+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simp only [rationalPoint,rationalDivideSuccCode,RationalCode.ofNat_natCode,RationalCode.value,
    Nat.sub_add_cancel hp]
  push_cast
  rw [div_div]

def rationalDivideSuccProgram : AlphaTerm :=
  let A := numericalProjectionTerm true
  let J := numericalProjectionTerm false
  pairNumerical (numericalCompose (numericalProjectionTerm true) A)
    (numericalCompose predecessorTerm (mulNumerical
      (numericalCompose rationalDenominatorTerm A) (numericalCompose successorTerm J)))

theorem rationalDivideSucc_computes : NumericalComputes rationalDivideSuccProgram
    (fun z => rationalDivideSuccCode z.unpair.1 z.unpair.2) := by
  have ha := projection_computes true
  have hj := projection_computes false
  have hn := (projection_computes true).comp ha
  have hd := predecessor_computes.comp ((rationalDenominator_computes.comp ha).mul (successor_computes.comp hj))
  simpa [rationalDivideSuccProgram,rationalDivideSuccCode,RationalCode.natCode,RationalCode.ofNat] using hn.pair hd

def polynomialIntegralPartial (c : ℕ) : ℕ → ℕ := primitiveRec 0 (fun j r =>
  (RationalCode.add (RationalCode.ofNat r)
    (RationalCode.ofNat (rationalDivideSuccCode ((NatListCode.decode c).getD j 0) j))).natCode)

def polynomialIntegralCode (c : ℕ) : ℕ := polynomialIntegralPartial c (NatListCode.decode c).length

def polynomialIntegralStep : AlphaTerm :=
  let C := numericalProjectionTerm true
  let J := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
  let R := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
  let A := numericalCompose listGetTerm (pairNumerical C J)
  numericalCompose rationalAddTerm (pairNumerical R
    (numericalCompose rationalDivideSuccProgram (pairNumerical A J)))

def polynomialIntegralProgram : AlphaTerm := numericalCompose
  (numericalRecursion (numericalConstant 0) polynomialIntegralStep)
  (pairNumerical numericalIdentity listLengthTerm)

theorem polynomialIntegral_computes : NumericalComputes polynomialIntegralProgram polynomialIntegralCode := by
  have hc := projection_computes true
  have hj := (projection_computes true).comp (projection_computes false)
  have hr := (projection_computes false).comp (projection_computes false)
  have ha := listGet_computes.comp (hc.pair hj)
  have hd := rationalDivideSucc_computes.comp (ha.pair hj)
  have hs := rationalAdd_computes.comp (hr.pair hd)
  have hs' : NumericalComputes polynomialIntegralStep (fun z =>
      (RationalCode.add (RationalCode.ofNat z.unpair.2.unpair.2)
        (RationalCode.ofNat (rationalDivideSuccCode
          ((NatListCode.decode z.unpair.1).getD z.unpair.2.unpair.1 0) z.unpair.2.unpair.1))).natCode) := by
    simpa [polynomialIntegralStep,Nat.unpair_pair] using hs
  have h := (numericalRecursion_computes (numericalConstant_computes 0) hs').comp
    (numericalIdentity_computes.pair listLength_computes)
  refine ⟨h.1,fun c => ?_⟩
  simpa only [polynomialIntegralProgram,polynomialIntegralCode,polynomialIntegralPartial,
    Nat.unpair_pair,id_eq] using h.2 c

theorem polynomialIntegralPartial_value (c n : ℕ) :
    rationalPoint (polynomialIntegralPartial c n) =
      ∑ j ∈ Finset.range n, rationalPoint ((NatListCode.decode c).getD j 0) / (j+1:ℕ) := by
  induction n with
  | zero => simp [polynomialIntegralPartial,primitiveRec,rationalPoint,RationalCode.ofNat,RationalCode.value]
  | succ n ih =>
    change rationalPoint (RationalCode.add (RationalCode.ofNat (polynomialIntegralPartial c n))
      (RationalCode.ofNat (rationalDivideSuccCode ((NatListCode.decode c).getD n 0) n))).natCode = _
    rw [Finset.sum_range_succ]
    simp only [rationalPoint,RationalCode.ofNat_natCode,RationalCode.value_add,Rat.cast_add]
    change rationalPoint (polynomialIntegralPartial c n) + rationalPoint (rationalDivideSuccCode _ n) = _
    rw [ih,rationalDivideSuccCode_value]
    rfl

theorem polynomialIntegralCode_value (c : ℕ) :
    rationalPoint (polynomialIntegralCode c) = ∫ x in (0:ℝ)..1, (realPolynomial c).eval x := by
  simp_rw [realPolynomial_eval]
  rw [intervalIntegral.integral_finsetSum (f := fun j x =>
    rationalPoint ((NatListCode.decode c).getD j 0) * x^j) (fun j _ =>
    (continuous_const.mul (continuous_id.pow j)).intervalIntegrable 0 1)]
  rw [polynomialIntegralCode,polynomialIntegralPartial_value]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul,integral_pow]
  simp [div_eq_mul_inv]

/-- Error-bound names by rational polynomials on the unit interval. -/
def IsPolynomialName (f : ℝ → ℝ) (p : ℕ → ℕ) : Prop :=
  ∀ n x, x ∈ Set.Icc (0:ℝ) 1 → |f x - (realPolynomial (p n)).eval x| ≤ (1/2:ℝ)^n

theorem polynomialIntegral_error {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0:ℝ) 1))
    {p : ℕ → ℕ} (hp : IsPolynomialName f p) (n : ℕ) :
    |rationalPoint (polynomialIntegralCode (p n)) - ∫ x in (0:ℝ)..1, f x| ≤ (1/2:ℝ)^n := by
  rw [polynomialIntegralCode_value,abs_sub_comm,← intervalIntegral.integral_sub
    (hf.intervalIntegrable_of_Icc (by norm_num))
      ((realPolynomial (p n)).continuous.intervalIntegrable 0 1)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := (1/2:ℝ)^n) (f := fun x => f x - (realPolynomial (p n)).eval x)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      exact hp n x ⟨(by simpa using hx.1 : (0:ℝ)<x).le,by simpa using hx.2⟩)
  simpa [Real.norm_eq_abs] using h

/-- Shift by two to obtain the pairwise Cauchy bound required by the real representation. -/
def integrationName (p : ℕ → ℕ) (n : ℕ) : ℕ := polynomialIntegralCode (p (n+2))

def integrationShiftProgram : AlphaTerm := addNumerical numericalIdentity (numericalConstant 2)

theorem integrationShift_computes : NumericalComputes integrationShiftProgram (fun n => n+2) :=
  numericalIdentity_computes.add (numericalConstant_computes 2)

/-- Integrate the polynomial returned by the input query at the shifted coordinate. -/
def integrationProgram : AlphaTerm := lam 1 (lam 2
  (app polynomialIntegralProgram (app (var 1) (app integrationShiftProgram (var 2)))))

theorem integrationProgram_closed : integrationProgram.Closed := by
  unfold integrationProgram Closed
  simp only [fv_lam,fv_app,fv_var]
  rw [polynomialIntegral_computes.1,integrationShift_computes.1]
  decide

theorem integrationProgram_runs (p : ℕ → ℕ) (n : ℕ) :
    OracleRuns p integrationProgram n (integrationName p n) := by
  have h₁ : Beta (app integrationProgram (var 0))
      (lam 2 (app polynomialIntegralProgram (app (var 0) (app integrationShiftProgram (var 2))))) := by
    simpa only [integrationProgram,subst_lam_fresh _ _ 2 1 (by decide)
      (show (2:ℕ) ∉ (var 0).fv by rw [fv_var]; decide),
      subst_app,subst_var,ite_true,ite_false,show (2:ℕ)≠1 from by decide,
      subst_closed _ _ _ polynomialIntegral_computes.1,subst_closed _ _ _ integrationShift_computes.1]
      using Beta.contract 1 (lam 2
        (app polynomialIntegralProgram (app (var 1) (app integrationShiftProgram (var 2))))) (var 0)
  have h₂ : Beta (app (lam 2
      (app polynomialIntegralProgram (app (var 0) (app integrationShiftProgram (var 2))))) (numeral n))
      (app polynomialIntegralProgram (app (var 0) (app integrationShiftProgram (numeral n)))) := by
    simpa only [subst_app,subst_var,ite_true,ite_false,show (0:ℕ)≠2 from by decide,
      subst_closed _ _ _ polynomialIntegral_computes.1,subst_closed _ _ _ integrationShift_computes.1]
      using Beta.contract 2
        (app polynomialIntegralProgram (app (var 0) (app integrationShiftProgram (var 2)))) (numeral n)
  apply (beta_steps_oracle ((Relation.ReflTransGen.single (.app_left _ h₁)).tail h₂)).trans
  apply (oracle_steps_app_right polynomialIntegralProgram
    (oracle_steps_app_right (var 0) (beta_steps_oracle (integrationShift_computes.2 n)))).trans
  exact (Relation.ReflTransGen.single (.app_right _ (.query (n+2)))).trans
    (beta_steps_oracle (polynomialIntegral_computes.2 (p (n+2))))

theorem integrationProgram_computes : UniformNumericalComputes integrationProgram integrationName :=
  ⟨integrationProgram_closed,integrationProgram_runs⟩

theorem integrationProgram_typeTwoComputes (D : Set (ℕ → ℕ)) :
    TypeTwoComputes integrationProgram (fun p : D => integrationName p.val) :=
  typeTwoComputes_iff_runs.mpr ⟨integrationProgram_closed,fun p n => integrationProgram_runs p.val n⟩

theorem integrationName_isCauchy {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0:ℝ) 1))
    {p : ℕ → ℕ} (hp : IsPolynomialName f p) : IsCauchyName rationalPoint (integrationName p) := by
  intro n m hnm
  rw [Real.dist_eq]
  have hn := polynomialIntegral_error hf hp (n+2)
  have hm := polynomialIntegral_error hf hp (m+2)
  have hb := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Nat.add_le_add_right hnm 2)
  have ht := abs_sub_le (rationalPoint (integrationName p n)) (∫ x in (0:ℝ)..1, f x)
    (rationalPoint (integrationName p m))
  rw [abs_sub_comm (∫ x in (0:ℝ)..1, f x)] at ht
  dsimp [integrationName] at ht ⊢
  simp only [pow_add] at hn hm hb
  norm_num at hn hm hb
  nlinarith [pow_pos (by norm_num : (0:ℝ)<1/2) n]

theorem integrationName_tendsto {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0:ℝ) 1))
    {p : ℕ → ℕ} (hp : IsPolynomialName f p) :
    Tendsto (fun n => rationalPoint (integrationName p n)) atTop (𝓝 (∫ x in (0:ℝ)..1, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2:ℝ)<1)
  refine ⟨N,fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact lt_of_le_of_lt ((polynomialIntegral_error hf hp (n+2)).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))) hN

def integrationNamePoint {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0:ℝ) 1))
    {p : ℕ → ℕ} (hp : IsPolynomialName f p) : realRepresentation.domain :=
  ⟨integrationName p,integrationName_isCauchy hf hp⟩

theorem integrationName_represents {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0:ℝ) 1))
    {p : ℕ → ℕ} (hp : IsPolynomialName f p) :
    realRepresentation.toFun (integrationNamePoint hf hp) = ∫ x in (0:ℝ)..1, f x :=
  tendsto_nhds_unique (f := fun n => rationalPoint (integrationName p n))
    (tendsto_cauchyRepresentation rationalPoint (integrationNamePoint hf hp)) (integrationName_tendsto hf hp)


/-- Encode any finite initial segment of coefficient codes. -/
def coefficientListCode (N : ℕ) (a : ℕ → ℕ) : ℕ := NatListCode.encode ((List.range N).map a)

theorem coefficientListCode_eval (N : ℕ) (a : ℕ → ℕ) (x : ℝ) :
    (realPolynomial (coefficientListCode N a)).eval x =
      ∑ j ∈ Finset.range N, rationalPoint (a j) * x^j := by
  rw [realPolynomial_eval]
  simp only [coefficientListCode,NatListCode.decode_encode,List.length_map,List.length_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < ((List.range N).map a).length := by simpa using Finset.mem_range.mp hj
  rw [List.getD_eq_getElem _ _ hj']
  simp

/-- Weierstrass approximation followed by a finite rational approximation of coefficients. -/
theorem exists_rationalPolynomial_near {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0:ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ x ∈ Set.Icc (0:ℝ) 1, |(realPolynomial c).eval x - f x| < ε := by
  classical
  obtain ⟨P,hP⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf (ε/2) (by positivity)
  let N := P.natDegree+1
  have hN : (0:ℝ)<N := by dsimp [N]; positivity
  let δ := ε/(2*N)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  choose a ha using (fun j : ℕ => rationalPoint_dense.exists_dist_lt (P.coeff j) hδ)
  refine ⟨coefficientListCode N a,fun x hx => ?_⟩
  have he : P.eval x = ∑ j ∈ Finset.range N, P.coeff j * x^j := by
    conv_lhs => rw [P.as_sum_range]
    simp [N,Polynomial.eval_finsetSum]
  have hb : |(realPolynomial (coefficientListCode N a)).eval x - P.eval x| ≤ ε/2 := by
    rw [coefficientListCode_eval,he,← Finset.sum_sub_distrib]
    calc
      |∑ j ∈ Finset.range N, (rationalPoint (a j)*x^j-P.coeff j*x^j)|
          ≤ ∑ j ∈ Finset.range N, |rationalPoint (a j)*x^j-P.coeff j*x^j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range N, δ := by
        apply Finset.sum_le_sum
        intro j _
        rw [← sub_mul,abs_mul]
        have ha' : |rationalPoint (a j)-P.coeff j| ≤ δ := by
          simpa only [Real.dist_eq,abs_sub_comm] using (ha j).le
        have hx' : |x^j| ≤ 1 := by
          rw [abs_of_nonneg (pow_nonneg hx.1 _)]
          exact pow_le_one₀ hx.1 hx.2
        nlinarith [abs_nonneg (rationalPoint (a j)-P.coeff j),abs_nonneg (x^j)]
      _ = ε/2 := by simp [δ]; field_simp
  exact lt_of_le_of_lt (abs_sub_le _ (P.eval x) _) (by linarith [hP x hx])

theorem exists_polynomialName {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0:ℝ) 1)) :
    ∃ p, IsPolynomialName f p := by
  classical
  choose p hp using (fun n : ℕ => exists_rationalPolynomial_near hf
    (pow_pos (by norm_num : (0:ℝ)<1/2) n))
  refine ⟨p,fun n x hx => ?_⟩
  simpa only [abs_sub_comm] using (hp n x hx).le

/-- One closed program works for every name, including noncomputable input names. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: example
  title: Integration on a compact interval
  excerpt: |
    \begin{example*}[Integration on a compact interval]
    Name $f\in C(\ClosedInterval{0}{1},\R)$ by rational polynomials $p_n$ satisfying
    $$\sup_{x\in\ClosedInterval{0}{1}}\Abs{f(x)-p_n(x)}\le2^{-n}.$$
    With this representation, $f\mapsto\int_0^1f(x)\,dx$ is computable.
    \end{example*}
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Encode a rational polynomial by $c=\LambdaListCode{\ell}$, where $\ell$ is a finite list of rational coefficient codes.
    If its length is $L$ and its entry at $j<L$ is $\gamma_j$, the polynomial is
    $$q_c(x):=\sum_{j<L}\RationalValue{\gamma_j}x^j.$$
    The empty list represents zero, and trailing zero coefficients are allowed. To integrate one monomial, divide its
    coefficient by $j+1$. On rational codes this is the operation
    $$\RationalCode{a}{b}{d}\longmapsto\RationalCode{a}{b}{(d+1)(j+1)-1}.$$
    The new denominator is positive, so the subtraction is ordinary subtraction. The numerical projections, successor,
    multiplication, predecessor, and pairing give a closed term for this operation. Starting with the rational-zero code,
    use $\LambdaListLength$ to bound a recursion, $\LambdaListGet$ to read coefficient $j$, and $\LambdaRationalAdd$ to add
    the divided coefficient to the accumulator. The coefficient list is retained as the recursion parameter. This gives a
    closed term $\LambdaTermName{integratePoly}$ computing a code $I(c)$, with
    $$\begin{aligned}
    \LambdaTermName{integratePoly}\ChurchNumeral{c}&\to_\beta^*\ChurchNumeral{I(c)},\\
    \RationalValue{I(c)}&=\sum_{j<L}\frac{\RationalValue{\gamma_j}}{j+1}=\int_0^1q_c(x)\,dx.
    \end{aligned}$$
    Induction on the number of processed coefficients proves the sum identity, and integration of the finite monomial sum
    proves the last equality. For the empty list the recursion returns zero. Every natural input decodes as a finite list,
    and every coefficient code denotes a rational, so this numerical program is total.

    Write $u(n)$ for the code of the input polynomial $p_n=q_{u(n)}$. Exact polynomial integration gives the estimate
    $$\Abs{\int_0^1f(x)\,dx-\RationalValue{I(u(n))}}
     \le\int_0^1\Abs{f(x)-p_n(x)}\,dx\le2^{-n}.$$
    To obtain the pairwise bound required of a Cauchy name, use
    $$r_u(n):=I(u(n+2)).$$
    For $n\le m$, the triangle inequality gives
    $$\Abs{\RationalValue{r_u(n)}-\RationalValue{r_u(m)}}
     \le2^{-(n+2)}+2^{-(m+2)}\le2^{-(n+1)}\le2^{-n}.$$
    The approximation error tends to zero, so this name represents the integral.

    Let $\LambdaTermName{shift}$ be a closed numerical term computing $n\mapsto n+2$. The single closed term
    $$\LambdaTermName{integrate}:= \lambdaab{o}{ \lambdaab{n}{ \LambdaTermName{integratePoly}\,(o\,(
    \LambdaTermName{shift}\,n))}}$$
    realizes the integral operator. Two beta steps expose the query, the numerical computation of
    $\LambdaTermName{shift}$ gives $n+2$, one
    input query returns $\ChurchNumeral{u(n+2)}$, and the computation of $\LambdaTermName{integratePoly}$ returns
    the integral code. Hence
    $$\LambdaInputSteps{u}{\LambdaTermName{integrate}\,o\,\ChurchNumeral{n}}{\ChurchNumeral{r_u(n)}}.$$
    This works for every valid input name, including names that are not themselves computable. Confluence excludes other
    numeral outputs, and the preceding error bounds establish correctness in the real Cauchy representation.

    Finally, such names exist for every continuous function. For any $\varepsilon>0$, the Weierstrass approximation
    theorem gives a real polynomial $P$ approximating $f$ within $\varepsilon/2$ on $\ClosedInterval{0}{1}$. Take $L\ge1$
    large enough to
    include all its coefficients. Approximate each of them by a rational within
    $\delta:=\varepsilon/(2L)$. For the resulting rational polynomial $q$ and $0\le x\le1$,
    $$\Abs{q(x)-P(x)}\le\sum_{j<L}\delta\Abs{x}^j\le L\delta=\varepsilon/2.$$
    Together with the first approximation this gives the requested accuracy. Taking $\varepsilon=2^{-n}$ for each $n$
    produces a polynomial name. Its uniform error bound is supplied by the name; values at finitely many sample points
    alone do not provide that information.
    \end{proof}
-/
theorem compactIntegration_computable :
    UniformNumericalComputes integrationProgram integrationName ∧
    ∀ (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (0:ℝ) 1)),
      (∃ p, IsPolynomialName f p) ∧
      ∀ (p : ℕ → ℕ) (hp : IsPolynomialName f p),
        realRepresentation.toFun (integrationNamePoint hf hp) = ∫ x in (0:ℝ)..1, f x :=
  ⟨integrationProgram_computes,fun _ hf => ⟨exists_polynomialName hf,fun _ hp => integrationName_represents hf hp⟩⟩

end PolishSpaceBook
