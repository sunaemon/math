module

public import PolishSpaceBook.LambdaL1StepDensity
public import PolishSpaceBook.LambdaRationalExponential
public import PolishSpaceBook.LambdaComputableNames
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-! # The integrable exponential profile and its computable step names

Split at zero for the Fourier integral and at the two window endpoints for the
L1 tail. Rational exponential sums supply the values on a uniform grid.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA MeasureTheory Set
open scoped FourierTransform

noncomputable def laplaceProfile (x : ℝ) : ℂ := (Real.exp (-|x|) : ℝ)

theorem laplaceProfile_norm (x : ℝ) : ‖laplaceProfile x‖ = Real.exp (-|x|) := by
  simp only [laplaceProfile,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

theorem laplaceProfile_continuous : Continuous laplaceProfile := by
  unfold laplaceProfile
  fun_prop

theorem laplaceProfile_integrable : Integrable laplaceProfile := by
  rw [← integrableOn_univ,← Iic_union_Ioi (a := (0:ℝ)),integrableOn_union]
  constructor
  · exact (show IntegrableOn (fun x : ℝ => (Real.exp x : ℂ)) (Iic 0) volume from (integrableOn_exp_Iic 0).ofReal).congr_fun
      (fun x hx => by simp [laplaceProfile,abs_of_nonpos (show x ≤ 0 from hx)]) measurableSet_Iic
  · exact (show IntegrableOn (fun x : ℝ => (Real.exp (-x) : ℂ)) (Ioi 0) volume from (integrableOn_exp_neg_Ioi 0).ofReal).congr_fun
      (fun x hx => by simp [laplaceProfile,abs_of_pos (show 0 < x from hx)]) measurableSet_Ioi

theorem exp_neg_difference {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-a)-Real.exp (-b) ≤ b-a := by
  have hpos : 0 ≤ 1-Real.exp (a-b) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hle : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have ht : 1-Real.exp (a-b) ≤ b-a := by linarith [Real.add_one_le_exp (a-b)]
  calc
    _ = Real.exp (-a)*(1-Real.exp (a-b)) := by rw [mul_sub,mul_one,← Real.exp_add]; ring_nf
    _ ≤ 1-Real.exp (a-b) := by nlinarith
    _ ≤ _ := ht

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    The function is Lipschitz with constant one. Indeed, if $0\le a\le b$, then
    $$0\le e^{-a}-e^{-b}=e^{-a}(1-e^{a-b})\le b-a,$$
    using $e^{-a}\le1$ and $e^{a-b}\ge1+a-b$. Apply this estimate to $|x|,|y|$ in increasing order and use
    $\bigl||x|-|y|\bigr|\le|x-y|$ to obtain $|f(x)-f(y)|\le|x-y|$.
-/
theorem laplaceProfile_lipschitz (x y : ℝ) : ‖laplaceProfile x-laplaceProfile y‖ ≤ |x-y| := by
  wlog h : |x| ≤ |y| generalizing x y
  · simpa only [norm_sub_rev,abs_sub_comm] using this y x (le_of_not_ge h)
  rw [laplaceProfile,laplaceProfile,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg h)))]
  exact (exp_neg_difference (abs_nonneg x) h).trans (by
    have := abs_abs_sub_abs_le_abs_sub y x
    simpa [abs_of_nonneg (sub_nonneg.mpr h),abs_sub_comm] using this)

theorem laplaceProfile_tail (R : ℝ) (hR : 0 ≤ R) :
    (∫ x in (Ioc (-R) R)ᶜ, ‖laplaceProfile x‖) = 2*Real.exp (-R) := by
  have hs : (Ioc (-R) R)ᶜ = Iic (-R) ∪ Ioi R := by
    ext x
    by_cases hx : -R < x <;> simp_all
  rw [hs,setIntegral_union (Iic_disjoint_Ioi (by linarith)) measurableSet_Ioi
    laplaceProfile_integrable.norm.integrableOn laplaceProfile_integrable.norm.integrableOn]
  have hl : (∫ x in Iic (-R), ‖laplaceProfile x‖) = Real.exp (-R) := by
    rw [← integral_exp_Iic (-R)]
    apply setIntegral_congr_fun measurableSet_Iic
    intro x hx
    change ‖laplaceProfile x‖ = Real.exp x
    rw [laplaceProfile_norm,abs_of_nonpos (by linarith [show x ≤ -R from hx])]
    simp
  have hr : (∫ x in Ioi R, ‖laplaceProfile x‖) = Real.exp (-R) := by
    rw [← integral_exp_neg_Ioi R]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change ‖laplaceProfile x‖ = Real.exp (-x)
    rw [laplaceProfile_norm,abs_of_nonneg (by linarith [show R < x from hx])]
  rw [hl,hr]
  ring

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Put $f(x):=e^{-|x|}$. On the negative half-line it equals $e^x$, and on the positive half-line it equals $e^{-x}$.
    The two improper integrals converge, so $f\in L^1(\R,\C)$. For every positive integer $R$,
    $$\int_{\SetDifference{\R}{(-R,R]}}|f(x)|\,dx
     =\int_{-\infty}^{-R}e^x\,dx+\int_R^\infty e^{-x}\,dx
     =2e^{-R}\le2\cdot2^{-R}.$$
    The last inequality follows from $e\ge2$.
-/
theorem laplaceProfile_tail_dyadic (R : ℕ) :
    (∫ x in (Ioc (-(R:ℝ)) R)ᶜ, ‖laplaceProfile x‖) ≤ 2*(1/2:ℝ)^R := by
  rw [laplaceProfile_tail _ (by positivity)]
  have h : Real.exp (-1) ≤ (1/2:ℝ) := by
    rw [Real.exp_neg]
    have he := Real.add_one_le_exp 1
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) (by linarith : (2:ℝ) ≤ Real.exp 1)
  have he : Real.exp (-(R:ℝ)) = Real.exp (-1)^R := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  gcongr

/-- Split the kernel integral at zero, evaluating the two decaying exponentials. -/
theorem laplaceProfile_fourier (ξ : ℝ) :
    𝓕 laplaceProfile ξ = (2:ℂ)/(1+4*(Real.pi:ℂ)^2*(ξ:ℂ)^2) := by
  let k := fourierKernelScale ξ
  have hk : k.re = 0 := by simp [k,fourierKernelScale]
  have hl : (∫ x in Iic (0:ℝ), fourierKernel ξ x*laplaceProfile x) = 1/(k+1) := by
    calc
      _ = ∫ x in Iic (0:ℝ), Complex.exp ((k+1)*(x:ℂ)) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x hx
        simp only [fourierKernel,laplaceProfile,abs_of_nonpos (show x ≤ 0 from hx),neg_neg,Complex.ofReal_exp]
        rw [← Complex.exp_add]
        congr 1
        dsimp [k]
        ring
      _ = _ := by rw [integral_exp_mul_complex_Iic (by simp [hk])]; simp
  have hr : (∫ x in Ioi (0:ℝ), fourierKernel ξ x*laplaceProfile x) = -1/(k-1) := by
    calc
      _ = ∫ x in Ioi (0:ℝ), Complex.exp ((k-1)*(x:ℂ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp only [fourierKernel,laplaceProfile,abs_of_pos (show 0 < x from hx),Complex.ofReal_exp,Complex.ofReal_neg]
        rw [← Complex.exp_add]
        congr 1
        dsimp [k]
        ring
      _ = _ := by rw [integral_exp_mul_complex_Ioi (by simp [hk])]; simp
  rw [fourier_eq_kernel,← intervalIntegral.integral_Iic_add_Ioi
    (fourier_integrand_integrable laplaceProfile_integrable ξ).integrableOn
    (fourier_integrand_integrable laplaceProfile_integrable ξ).integrableOn,hl,hr]
  have h1 : k+1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hk] at this
  have h2 : k-1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hk] at this
  have hden : (1+4*(Real.pi:ℂ)^2*(ξ:ℂ)^2) ≠ 0 := by
    have h : (0:ℝ) < 1+4*Real.pi^2*ξ^2 := by positivity
    exact_mod_cast ne_of_gt h
  have hk2 : k^2 = -4*(Real.pi:ℂ)^2*(ξ:ℂ)^2 := by
    dsimp [k,fourierKernelScale]
    ring_nf
    simp [Complex.I_sq]
  field_simp
  linear_combination -2*hk2

/-- A window approximation separates the tail integral from the error on each cell. -/
theorem laplaceProfile_step_error (R : ℝ) (hR : 0 ≤ R) (a : ℕ → ℝ) (ha : Monotone a)
    (N : ℕ) (ha0 : a 0 = -R) (haN : a N = R) (v : ℕ → ℂ) (h η : ℝ)
    (hmesh : ∀ i < N, a (i+1)-a i ≤ h)
    (hvalue : ∀ i < N, ‖laplaceProfile (a i)-v i‖ ≤ η) :
    (∫ x, ‖laplaceProfile x-intervalStep a v N x‖) ≤ 2*Real.exp (-R)+2*R*(h+η) := by
  classical
  let g := (Ioc (-R) R).indicator laplaceProfile
  have hg : Integrable g := laplaceProfile_integrable.indicator measurableSet_Ioc
  have hin : ∀ x ∈ Ioc (a 0) (a N), ‖g x-intervalStep a v N x‖ ≤ h+η := by
    intro x hx
    have hxR : x ∈ Ioc (-R) R := by simpa only [ha0,haN] using hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (Ioc_subset_biUnion_Ioc N a hx)
    obtain ⟨hi,hxi⟩ := mem_iUnion.mp hi
    have hiN := Finset.mem_range.mp hi
    rw [intervalStep_on_cell a ha v N i hiN x hxi]
    change ‖(Ioc (-R) R).indicator laplaceProfile x-v i‖ ≤ _
    rw [indicator_of_mem hxR]
    calc
      _ ≤ ‖laplaceProfile x-laplaceProfile (a i)‖+‖laplaceProfile (a i)-v i‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ |x-a i|+η := add_le_add (laplaceProfile_lipschitz x (a i)) (hvalue i hiN)
      _ ≤ h+η := by
        rw [abs_of_pos (sub_pos.mpr hxi.1)]
        linarith [hxi.2,hmesh i hiN]
  have hout : ∀ x ∉ Ioc (a 0) (a N), g x = 0 := by
    intro x hx
    have hxR : x ∉ Ioc (-R) R := by simpa only [ha0,haN] using hx
    exact indicator_of_notMem hxR _
  have he : (∫ x, ‖laplaceProfile x-g x‖) = 2*Real.exp (-R) := by
    have hf : (fun x => ‖laplaceProfile x-g x‖) =
        (Ioc (-R) R)ᶜ.indicator (fun x => ‖laplaceProfile x‖) := by
      funext x
      by_cases hx : x ∈ Ioc (-R) R <;> simp [g,hx]
    rw [hf,integral_indicator measurableSet_Ioc.compl,laplaceProfile_tail R hR]
  have hbound := intervalStep_error_integral hg a ha v N (h+η) hin hout
  rw [ha0,haN] at hbound
  calc
    _ ≤ ∫ x, (‖laplaceProfile x-g x‖+‖g x-intervalStep a v N x‖) := by
      apply integral_mono (laplaceProfile_integrable.sub (intervalStep_integrable a v N)).norm
        ((laplaceProfile_integrable.sub hg).norm.add (hg.sub (intervalStep_integrable a v N)).norm)
      exact fun x => norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = (∫ x, ‖laplaceProfile x-g x‖)+(∫ x, ‖g x-intervalStep a v N x‖) :=
      integral_add (laplaceProfile_integrable.sub hg).norm (hg.sub (intervalStep_integrable a v N)).norm
    _ ≤ _ := by rw [he]; linarith

noncomputable def laplaceProfileLp : ComplexL1 :=
  (memLp_one_iff_integrable.mpr laplaceProfile_integrable).toLp laplaceProfile

theorem laplaceProfileLp_ae : (laplaceProfileLp : ℝ → ℂ) =ᵐ[volume] laplaceProfile := MemLp.coeFn_toLp _

theorem laplaceProfileLp_error (s : ℕ) :
    ‖laplaceProfileLp-stepFunctionLp s‖ = ∫ x, ‖laplaceProfile x-stepFunction s x‖ := by
  rw [L1_norm_sub_eq_integral]
  apply integral_congr_ae
  filter_upwards [laplaceProfileLp_ae,stepFunctionLp_ae s] with x hx hs
  rw [hx,hs]

/-- A common rational denominator for the uniform partition of [-R,R]. -/
def laplaceGridCode (R N i : ℕ) : ℕ := RationalCode.natCode ((2*R*i,R*N),N-1)

theorem laplaceGridCode_value (R N i : ℕ) (hN : 0 < N) :
    rationalPoint (laplaceGridCode R N i) = -(R:ℝ)+(2*(R:ℝ)/N)*i := by
  simp only [laplaceGridCode,rationalPoint,RationalCode.ofNat_natCode,RationalCode.value]
  rw [Nat.sub_add_cancel hN]
  push_cast
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hN
  field_simp
  ring

theorem laplaceGridCode_monotone (R N : ℕ) (hN : 0 < N) :
    Monotone (fun i => rationalPoint (laplaceGridCode R N i)) := by
  intro i j hij
  simp only [laplaceGridCode_value _ _ _ hN]
  gcongr

theorem laplaceGridCode_zero (R N : ℕ) (hN : 0 < N) :
    rationalPoint (laplaceGridCode R N 0) = -(R:ℝ) := by simp [laplaceGridCode_value _ _ _ hN]

theorem laplaceGridCode_last (R N : ℕ) (hN : 0 < N) :
    rationalPoint (laplaceGridCode R N N) = R := by
  rw [laplaceGridCode_value _ _ _ hN,div_mul_cancel₀ _ (by exact_mod_cast Nat.ne_zero_of_lt hN)]
  ring

theorem laplaceGridCode_mesh (R N i : ℕ) (hN : 0 < N) :
    rationalPoint (laplaceGridCode R N (i+1))-rationalPoint (laplaceGridCode R N i) = 2*(R:ℝ)/N := by
  simp only [laplaceGridCode_value _ _ _ hN,Nat.cast_add,Nat.cast_one]
  ring

theorem laplaceGridCode_bound (R N i : ℕ) (hN : 0 < N) (hi : i ≤ N) :
    |rationalPoint (laplaceGridCode R N i)| ≤ R := by
  apply abs_le.mpr
  constructor
  · rw [← laplaceGridCode_zero R N hN]
    exact laplaceGridCode_monotone R N hN (Nat.zero_le i)
  · rw [← laplaceGridCode_last R N hN]
    exact laplaceGridCode_monotone R N hN hi

@[irreducible] def laplaceHeightCode (R N m i : ℕ) : ℕ :=
  exponentialApproxCode (rationalNegativeAbsCode (laplaceGridCode R N i)) R m

theorem laplaceHeightCode_error (R N m i : ℕ) (hN : 0 < N) (hi : i ≤ N) :
    ‖laplaceProfile (rationalPoint (laplaceGridCode R N i))-
      complexRationalPoint (laplaceHeightCode R N m i)‖ ≤ (1/2:ℝ)^(m+2) := by
  have h := exponentialApproxCode_error (rationalNegativeAbsCode (laplaceGridCode R N i)) R m
    (by simpa only [rationalNegativeAbsCode_value,abs_neg,abs_abs] using laplaceGridCode_bound R N i hN hi)
  simpa only [laplaceHeightCode,rationalNegativeAbsCode_value,laplaceProfile] using h

@[irreducible] def laplaceRowCode (R N m i : ℕ) : ℕ := Nat.pair (laplaceGridCode R N i)
  (Nat.pair (laplaceGridCode R N (i+1)) (laplaceHeightCode R N m i))

@[irreducible] def laplaceStepCode (R N m : ℕ) : ℕ := NatListCode.encode ((List.range N).map (laplaceRowCode R N m))

theorem laplaceStepCode_length (R N m : ℕ) : (NatListCode.decode (laplaceStepCode R N m)).length = N := by
  simp [laplaceStepCode]

theorem laplaceStepCode_row (R N m i : ℕ) (hi : i < N) :
    stepRow (laplaceStepCode R N m) i = laplaceRowCode R N m i := by
  simp only [stepRow,laplaceStepCode,NatListCode.decode_encode]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem laplaceStepCode_valid (R N m : ℕ) (hN : 0 < N) : ValidStepCode (laplaceStepCode R N m) := by
  intro i hi
  rw [laplaceStepCode_length] at hi
  simp only [laplaceStepCode_row _ _ _ _ hi,laplaceRowCode,Nat.unpair_pair]
  exact laplaceGridCode_monotone R N hN (Nat.le_succ i)

theorem laplaceStepCode_function (R N m : ℕ) : stepFunction (laplaceStepCode R N m) =
    intervalStep (fun i => rationalPoint (laplaceGridCode R N i))
      (fun i => complexRationalPoint (laplaceHeightCode R N m i)) N := by
  funext x
  simp only [stepFunction,intervalStep,laplaceStepCode_length]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [laplaceStepCode_row _ _ _ _ (Finset.mem_range.mp hi),stepRowFunction,laplaceRowCode,Nat.unpair_pair]

theorem laplaceStepCode_error (R N m : ℕ) (hN : 0 < N) :
    ‖laplaceProfileLp-stepFunctionLp (laplaceStepCode R N m)‖ ≤
      2*(1/2:ℝ)^R+2*(R:ℝ)*(2*(R:ℝ)/N+(1/2:ℝ)^(m+2)) := by
  rw [laplaceProfileLp_error,laplaceStepCode_function]
  have h := laplaceProfile_step_error R (by positivity) _ (laplaceGridCode_monotone R N hN) N
    (laplaceGridCode_zero R N hN) (laplaceGridCode_last R N hN) _ (2*(R:ℝ)/N) ((1/2:ℝ)^(m+2))
    (fun i _ => (laplaceGridCode_mesh R N i hN).le)
    (fun i hi => laplaceHeightCode_error R N m i hN hi.le)
  have ht := laplaceProfile_tail_dyadic R
  rw [laplaceProfile_tail _ (by positivity)] at ht
  linarith

def laplaceName (n : ℕ) : ℕ := laplaceStepCode (n+3) (2*(n+3)^2*2^(n+4)) (n+(n+3)+2)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Let $s_n$ take value $v_i$ on $(a_i,a_{i+1}]$ and zero outside $(-R,R]$. For $x$ in its $i$th interval,
    $$|f(x)-s_n(x)|\le|f(x)-f(a_i)|+|f(a_i)-v_i|\le h+h=2h.$$
    Integrating over the window and adding the tail gives
    $$\begin{aligned}
    \LpNorm{1}{f-s_n}&\le2\cdot2^{-R}+2R\cdot2h\\
     &=2^{-(n+2)}+2^{-(n+2)}=2^{-(n+1)}\le2^{-n}.
    \end{aligned}$$
    Thus the sequence satisfies the required $L^1$ error bound.
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    For precision $n$, choose the integer parameters and grid
    $$\begin{aligned}
    R&:=n+3,& L&:=2R^2\cdot2^{n+4},& m&:=n+R+2,\\
    a_i&:=-R+\frac{2Ri}{L}\quad(0\le i\le L),&
    h&:=\frac{2R}{L}=\frac{2^{-(n+4)}}{R}.
    \end{aligned}$$
    The intervals $(a_i,a_{i+1}]$ for $i<L$ partition $(-R,R]$.
-/
theorem laplaceName_error (n : ℕ) :
    ‖laplaceProfileLp-stepFunctionLp (laplaceName n)‖ ≤ (1/2:ℝ)^(n+1) := by
  have hN : 0 < 2*(n+3)^2*2^(n+4) := by positivity
  apply (laplaceStepCode_error _ _ _ hN).trans
  have hR : (0:ℝ)<n+3 := by positivity
  have hp : (n+3:ℝ) ≤ 2^(n+3) := by exact_mod_cast (Nat.lt_two_pow_self (n := n+3)).le
  have hval : (1/2:ℝ)^(n+(n+3)+2+2) ≤ (1/2:ℝ)^(n+4)/(n+3) := by
    rw [show n+(n+3)+2+2 = (n+4)+(n+3) by omega,pow_add]
    have hdiv : (1/2:ℝ)^(n+3) ≤ 1/(n+3:ℝ) := by
      rw [one_div_pow]
      exact one_div_le_one_div_of_le hR hp
    calc
      _ ≤ (1/2:ℝ)^(n+4)*(1/(n+3)) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  have hmesh : 2*(n+3:ℝ)/(2*(n+3)^2*2^(n+4)) = (1/2:ℝ)^(n+4)/(n+3) := by
    rw [one_div_pow]
    field_simp
  push_cast
  rw [hmesh]
  calc
    _ ≤ 2*(1/2:ℝ)^(n+3)+2*(n+3)*((1/2:ℝ)^(n+4)/(n+3)+(1/2:ℝ)^(n+4)/(n+3)) := by gcongr
    _ = (1/2:ℝ)^(n+1) := by
      simp only [pow_add]
      norm_num
      field_simp
      norm_num

theorem laplaceName_isName : IsL1StepName laplaceProfileLp laplaceName := by
  intro n
  refine ⟨laplaceStepCode_valid _ _ _ (by positivity),?_⟩
  apply (laplaceName_error n).trans
  rw [pow_succ]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]

/-- Compute the grid point from (R,(N,i)). -/
def laplaceGridProgram : AlphaTerm :=
  let R := numericalProjectionTerm true
  let N := onComponent (numericalProjectionTerm true) false
  let i := onComponent (numericalProjectionTerm false) false
  pairNumerical (pairNumerical (mulNumerical (mulNumerical (numericalConstant 2) R) i) (mulNumerical R N))
    (numericalCompose predecessorTerm N)

theorem laplaceGridProgram_computes : NumericalComputes laplaceGridProgram
    (fun z => laplaceGridCode z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2) := by
  have R := projection_computes true
  have N := (projection_computes true).onComponent false
  have i := (projection_computes false).onComponent false
  exact ((((numericalConstant_computes 2).mul R).mul i).pair (R.mul N)).pair (predecessor_computes.comp N)

/-- A row retains the parameter (R,(N,m)), with the cell index as the second component. -/
def laplaceRowProgram : AlphaTerm :=
  let R := onComponent (numericalProjectionTerm true) true
  let N := onComponent (onComponent (numericalProjectionTerm true) false) true
  let m := onComponent (onComponent (numericalProjectionTerm false) false) true
  let i := numericalProjectionTerm false
  let left := numericalCompose laplaceGridProgram (pairNumerical R (pairNumerical N i))
  let right := numericalCompose laplaceGridProgram
    (pairNumerical R (pairNumerical N (numericalCompose successorTerm i)))
  let value := numericalCompose exponentialApproxProgram
    (pairNumerical (numericalCompose rationalNegativeAbsProgram left) (pairNumerical R m))
  pairNumerical left (pairNumerical right value)

theorem laplaceRowProgram_computes : NumericalComputes laplaceRowProgram
    (fun z => laplaceRowCode z.unpair.1.unpair.1 z.unpair.1.unpair.2.unpair.1
      z.unpair.1.unpair.2.unpair.2 z.unpair.2) := by
  have R := (projection_computes true).onComponent true
  have N := ((projection_computes true).onComponent false).onComponent true
  have m := ((projection_computes false).onComponent false).onComponent true
  have i := projection_computes false
  have left := laplaceGridProgram_computes.comp (R.pair (N.pair i))
  have right := laplaceGridProgram_computes.comp (R.pair (N.pair (successor_computes.comp i)))
  have value := exponentialApproxProgram_computes.comp
    ((rationalNegativeAbsProgram_computes.comp left).pair (R.pair m))
  have h := left.pair (right.pair value)
  refine ⟨h.1,fun z => ?_⟩
  simpa only [laplaceRowProgram,laplaceRowCode,laplaceHeightCode,Nat.unpair_pair,
    ite_true,Bool.false_eq_true,ite_false,Nat.succ_eq_add_one] using h.2 z

/-- Tabulate exactly N rows with a fixed parameter. -/
def laplaceStepProgram : AlphaTerm := numericalCompose (listTabulateTerm laplaceRowProgram)
  (pairNumerical numericalIdentity (onComponent (numericalProjectionTerm true) false))

theorem laplaceStepProgram_computes : NumericalComputes laplaceStepProgram
    (fun z => laplaceStepCode z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2) := by
  have h := (listTabulate_computes laplaceRowProgram_computes).comp
    (numericalIdentity_computes.pair ((projection_computes true).onComponent false))
  simpa only [laplaceStepProgram,laplaceStepCode,Nat.unpair_pair,id_eq,
    ite_true,Bool.false_eq_true,ite_false] using h

/-- All integer control parameters are computed from the precision n. -/
def laplacePlanProgram : AlphaTerm :=
  let R := addNumerical numericalIdentity (numericalConstant 3)
  let power := numericalCompose naturalPowerProgram
    (pairNumerical (numericalConstant 2) (addNumerical numericalIdentity (numericalConstant 4)))
  let N := mulNumerical (mulNumerical (mulNumerical (numericalConstant 2) R) R) power
  let m := addNumerical (addNumerical numericalIdentity R) (numericalConstant 2)
  pairNumerical R (pairNumerical N m)

theorem laplacePlanProgram_computes : NumericalComputes laplacePlanProgram
    (fun n => Nat.pair (n+3) (Nat.pair (2*(n+3)^2*2^(n+4)) (n+(n+3)+2))) := by
  have R := numericalIdentity_computes.add (numericalConstant_computes 3)
  have power := naturalPowerProgram_computes.comp ((numericalConstant_computes 2).pair
    (numericalIdentity_computes.add (numericalConstant_computes 4)))
  have N := (((numericalConstant_computes 2).mul R).mul R).mul power
  have m := (numericalIdentity_computes.add R).add (numericalConstant_computes 2)
  have h := R.pair (N.pair m)
  simpa only [laplacePlanProgram,Nat.unpair_pair,id_eq,pow_two,mul_assoc] using h

def laplaceNameProgram : AlphaTerm := numericalCompose laplaceStepProgram laplacePlanProgram

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    To produce the name as a finite list, use the endpoint codes
    $$c_i:=\RationalCode{2Ri}{RL}{L-1}\qquad(0\le i\le L),$$
    where $L\ge1$ ensures that $L-1$ is defined. Let $w_i$ be the rational complex code for $\nu_i$ returned by the series
    computation. Retain $\NatPair{R}{\NatPair{L}{m}}$ as a parameter. A closed row term $G$ takes this parameter and $i$
    and returns
    $$d_i:=\NatPair{c_i}{\NatPair{c_{i+1}}{w_i}}.$$
    The finite tabulation term $\LambdaListTabulate{G}$ lists these rows for $i<L$. Composing it with the calculation
    of $R,L,m$ gives a closed term $A$ satisfying
    $$A\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{\LambdaListCode{[d_i]_{i<L}}}.$$
    The decoded step function is exactly $s_n$, so this is a computable $L^1$-name, with no unspecified choices.
-/
theorem laplaceNameProgram_computes : NumericalComputes laplaceNameProgram laplaceName := by
  unfold laplaceNameProgram laplaceName
  simpa only [Nat.unpair_pair] using laplaceStepProgram_computes.comp laplacePlanProgram_computes

/-- The Fourier program applied to this closed name is an ordinary closed numerical program. -/
theorem laplaceFourierName_computes : NumericalComputes (app fourierNameProgram laplaceNameProgram)
    (fourierNameTransform laplaceName) := by
  exact (fourierNameProgram_typeTwoComputes Set.univ).numerical_output
    ⟨laplaceName,Set.mem_univ _⟩ laplaceNameProgram_computes

theorem laplaceFourierName_isName : IsLocallyUniformPolynomialName
    (Real.Lp.fourierTransform laplaceProfileLp).toContinuousMap (fourierNameTransform laplaceName) :=
  fourierNameTransform_correct _ _ laplaceName_isName

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Finally, split the Fourier integral at zero. On each half-line, multiply the exponential kernel by the corresponding
    expression for $f$ and integrate the resulting decaying exponential. This gives
    $$\FourierTransform{f}(\xi)=\frac{1}{1+2\pi\mathrm i\xi}+\frac{1}{1-2\pi\mathrm i\xi}
    =\frac{2}{1+4\pi^2\xi^2}.$$
    The real denominator is at least one. To compute a locally uniform name of the entire transform, apply the closed
    name transformer $\Phi$ from the preceding proposition to $A$. Substitution of a computable input name, proved in
    §{sec:lambda-input-composition}, replaces each query by an ordinary beta computation. Thus $\Phi A$ is a closed
    numerical term computing the output polynomial codes, and the proposition proves that
    they approximate this Fourier transform.
    \end{proof}
-/
theorem laplaceProfileLp_fourier (ξ : ℝ) :
    Real.Lp.fourierTransform laplaceProfileLp ξ = (2:ℂ)/(1+4*(Real.pi:ℂ)^2*(ξ:ℂ)^2) := by
  change 𝓕 (laplaceProfileLp : ℝ → ℂ) ξ = _
  rw [Real.fourier_congr_ae laplaceProfileLp_ae,laplaceProfile_fourier]

/-- Both names are computed by explicit closed terms and denote the canonical L1/Fourier objects. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: example
  title: An explicit Fourier transform
-/
theorem laplace_example_computable :
    NumericalComputes laplaceNameProgram laplaceName ∧ IsL1StepName laplaceProfileLp laplaceName ∧
    NumericalComputes (app fourierNameProgram laplaceNameProgram) (fourierNameTransform laplaceName) ∧
    IsLocallyUniformPolynomialName (Real.Lp.fourierTransform laplaceProfileLp).toContinuousMap
      (fourierNameTransform laplaceName) ∧
    ∀ ξ : ℝ, Real.Lp.fourierTransform laplaceProfileLp ξ = (2:ℂ)/(1+4*(Real.pi:ℂ)^2*(ξ:ℂ)^2) :=
  ⟨laplaceNameProgram_computes,laplaceName_isName,laplaceFourierName_computes,
    laplaceFourierName_isName,laplaceProfileLp_fourier⟩

end PolishSpaceBook
