module

public import PolishSpaceBook.LambdaFourierLists
public import Mathlib.Analysis.Fourier.FourierTransform

@[expose] public section

/-! # The lambda name transformer realizes the canonical L1 Fourier integral

Finite rows denote sums of half-open interval indicators. We identify their
Fourier integrals with the interval computations, prove the L1 error estimate
by integrating the pointwise norm, and apply the constructed name program.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA MeasureTheory
open scoped FourierTransform

/-- The same exponential kernel as in the interval computations. -/
noncomputable def fourierKernel (ξ x : ℝ) : ℂ := Complex.exp (fourierKernelScale ξ*(x:ℂ))

theorem fourierKernel_norm (ξ x : ℝ) : ‖fourierKernel ξ x‖ = 1 := by
  simp [fourierKernel,fourierKernelScale,Complex.norm_exp,Complex.mul_re,Complex.mul_im]

theorem fourierKernel_continuous (ξ : ℝ) : Continuous (fourierKernel ξ) := by
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    For functions on the whole real line, specify how the input controls the integral. Let $L^1(\R,\C)$ consist of
    integrable functions modulo equality almost everywhere, with norm $\LpNorm{1}{f}:=\int_{\R}|f(x)|\,dx$. Use finite sums
    of interval indicators with rational endpoints and coefficients in $\QQ+\mathrm i\QQ$ as dense approximants; each such
    step function vanishes outside a bounded interval. An input name supplies such functions $s_n$ with
    $\LpNorm{1}{f-s_n}\le2^{-n}$. Define
    $$\FourierTransform{f}(\xi):=\int_{\R}f(x)e^{-2\pi\mathrm i x\xi}\,dx.$$
    For the output in $C(\R,\C)$, a name supplies, for each positive integer $R$ and precision $n$, a polynomial with
    rational complex coefficients approximating the function uniformly on $[-R,R]$ within $2^{-n}$. This is the locally
    uniform representation.
-/
theorem fourier_eq_kernel (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 f ξ = ∫ x, fourierKernel ξ x * f x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1
  funext x
  simp only [smul_eq_mul,fourierKernel,fourierKernelScale]
  congr 2
  push_cast
  ring

theorem fourier_integrand_integrable {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    Integrable (fun x => fourierKernel ξ x * f x) :=
  hf.bdd_mul (fourierKernel_continuous ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => (fourierKernel_norm ξ x).le))

/-- Dominated convergence proves continuity, with the integrable bound |f|. -/
theorem fourier_continuous_from_kernel {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) := by
  simp_rw [show 𝓕 f = (fun ξ => ∫ x, fourierKernel ξ x * f x) from funext (fourier_eq_kernel f)]
  apply continuous_of_dominated (bound := fun x => ‖f x‖)
  · exact fun ξ => (fourier_integrand_integrable hf ξ).aestronglyMeasurable
  · exact fun ξ => Filter.Eventually.of_forall (fun x => by rw [norm_mul,fourierKernel_norm,one_mul])
  · exact hf.norm
  · filter_upwards [] with x
    unfold fourierKernel fourierKernelScale
    fun_prop

/-- Take the norm inside the integral, as in the book proof. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Since $|e^{-2\pi\mathrm i x\xi}|=1$, multiplying an integrable function by this kernel preserves integrability.
    Linearity and the norm inequality for the integral therefore give
    $$\begin{aligned}
    |\FourierTransform{f}(\xi)-\FourierTransform{g}(\xi)|
     &=\left|\int_{\R}(f(x)-g(x))e^{-2\pi\mathrm i x\xi}\,dx\right|\\
     &\le\int_{\R}|f(x)-g(x)|\,dx=\LpNorm{1}{f-g}.
    \end{aligned}$$
    The bound is independent of the frequency. Almost-everywhere equal representatives have the same integral, so this
    estimate is well defined on $L^1$. Dominated convergence, with integrable majorant $|f|$, also proves that
    $\FourierTransform{f}$ is continuous.
-/
theorem fourier_difference_le_L1_integral {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    ‖𝓕 f ξ - 𝓕 g ξ‖ ≤ ∫ x, ‖f x-g x‖ := by
  rw [fourier_eq_kernel,fourier_eq_kernel,← integral_sub
    (fourier_integrand_integrable hf ξ) (fourier_integrand_integrable hg ξ)]
  calc
    _ ≤ ∫ x, ‖fourierKernel ξ x * f x-fourierKernel ξ x * g x‖ := norm_integral_le_integral_norm _
    _ = _ := by
      congr 1
      funext x
      rw [← mul_sub,norm_mul,fourierKernel_norm,one_mul]

/-- A row denotes an ordinary Lebesgue-integrable step function. -/
noncomputable def stepRowFunction (row : ℕ) : ℝ → ℂ :=
  (Set.Ioc (rationalPoint row.unpair.1) (rationalPoint row.unpair.2.unpair.1)).indicator
    (fun _ => complexRationalPoint row.unpair.2.unpair.2)

theorem stepRowFunction_integrable (row : ℕ) : Integrable (stepRowFunction row) := by
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

noncomputable def stepFunction (s : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (NatListCode.decode s).length, stepRowFunction (stepRow s i) x

theorem stepFunction_integrable (s : ℕ) : Integrable (stepFunction s) :=
  integrable_finsetSum _ (fun i _ => stepRowFunction_integrable (stepRow s i))

def ValidStepCode (s : ℕ) : Prop := ∀ i < (NatListCode.decode s).length,
  rationalPoint (stepRow s i).unpair.1 ≤ rationalPoint (stepRow s i).unpair.2.unpair.1

theorem stepRowFunction_fourier (row : ℕ)
    (hab : rationalPoint row.unpair.1 ≤ rationalPoint row.unpair.2.unpair.1) (ξ : ℝ) :
    𝓕 (stepRowFunction row) ξ = complexRationalPoint row.unpair.2.unpair.2 *
      (∫ x in (rationalPoint row.unpair.1)..(rationalPoint row.unpair.2.unpair.1), fourierKernel ξ x) := by
  rw [fourier_eq_kernel]
  have he : (fun x => fourierKernel ξ x * stepRowFunction row x) =
      (Set.Ioc (rationalPoint row.unpair.1) (rationalPoint row.unpair.2.unpair.1)).indicator
        (fun x => fourierKernel ξ x * complexRationalPoint row.unpair.2.unpair.2) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (rationalPoint row.unpair.1) (rationalPoint row.unpair.2.unpair.1)
    · simp [stepRowFunction,hx]
    · simp [stepRowFunction,hx]
  rw [he,integral_indicator measurableSet_Ioc,← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_mul_const,mul_comm]

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Fix an output window $[-R,R]$ and precision $n$, and take the input approximant $s_{n+2}$. Write it as a finite sum
    of interval indicators with rational complex coefficients $v_\ell$ and rational endpoints $a_\ell\le b_\ell$, for
    $\ell<L$. Every summand is integrable, since its support is bounded and its value is constant on the interval.
    Multiplication by the kernel commutes with the finite sum. Integrating each indicator over the real line restricts
    the integral to its interval, so
    $$\FourierTransform{s_{n+2}}(\xi)=\sum_{\ell<L}v_\ell
     \int_{a_\ell}^{b_\ell}e^{-2\pi\mathrm i x\xi}\,dx.$$
    This identity connects the finite interval computations to the Fourier transform of the supplied step function.
-/
theorem stepFunction_fourier (s : ℕ) (hs : ValidStepCode s) (ξ : ℝ) :
    𝓕 (stepFunction s) ξ = stepFourierValue s ξ := by
  rw [fourier_eq_kernel]
  simp only [stepFunction,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => fourier_integrand_integrable
    (stepRowFunction_integrable (stepRow s i)) ξ)]
  unfold stepFourierValue
  apply Finset.sum_congr rfl
  intro i hi
  rw [← fourier_eq_kernel,stepRowFunction_fourier _ (hs i (Finset.mem_range.mp hi))]
  rfl

/-- Use mathlib's L1 space, so equality is already almost-everywhere equality. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    For functions on the whole real line, specify how the input controls the integral. Let $L^1(\R,\C)$ consist of
    integrable functions modulo equality almost everywhere, with norm $\LpNorm{1}{f}:=\int_{\R}|f(x)|\,dx$. Use finite sums
    of interval indicators with rational endpoints and coefficients in $\QQ+\mathrm i\QQ$ as dense approximants; each such
    step function vanishes outside a bounded interval. An input name supplies such functions $s_n$ with
    $\LpNorm{1}{f-s_n}\le2^{-n}$. Define
    $$\FourierTransform{f}(\xi):=\int_{\R}f(x)e^{-2\pi\mathrm i x\xi}\,dx.$$
    For the output in $C(\R,\C)$, a name supplies, for each positive integer $R$ and precision $n$, a polynomial with
    rational complex coefficients approximating the function uniformly on $[-R,R]$ within $2^{-n}$. This is the locally
    uniform representation.
-/
noncomputable abbrev ComplexL1 := Lp ℂ 1 (volume : Measure ℝ)

noncomputable def stepFunctionLp (s : ℕ) : ComplexL1 :=
  (memLp_one_iff_integrable.mpr (stepFunction_integrable s)).toLp (stepFunction s)

theorem stepFunctionLp_ae (s : ℕ) : (stepFunctionLp s : ℝ → ℂ) =ᵐ[volume] stepFunction s :=
  MemLp.coeFn_toLp _

theorem L1_norm_sub_eq_integral (f g : ComplexL1) :
    ‖f-g‖ = ∫ x, ‖f x-g x‖ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with x hx
  rw [hx]
  rfl

theorem L1_fourier_difference (f g : ComplexL1) (ξ : ℝ) :
    ‖Real.Lp.fourierTransform f ξ-Real.Lp.fourierTransform g ξ‖ ≤ ‖f-g‖ := by
  rw [L1_norm_sub_eq_integral]
  exact fourier_difference_le_L1_integral (L1.integrable_coeFn f) (L1.integrable_coeFn g) ξ

theorem stepFunctionLp_fourier (s : ℕ) (hs : ValidStepCode s) (ξ : ℝ) :
    Real.Lp.fourierTransform (stepFunctionLp s) ξ = stepFourierValue s ξ := by
  change 𝓕 (stepFunctionLp s : ℝ → ℂ) ξ = _
  rw [Real.fourier_congr_ae (stepFunctionLp_ae s),stepFunction_fourier s hs]

/-- Names by rational interval step functions, with the book's L1 error bound. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    For functions on the whole real line, specify how the input controls the integral. Let $L^1(\R,\C)$ consist of
    integrable functions modulo equality almost everywhere, with norm $\LpNorm{1}{f}:=\int_{\R}|f(x)|\,dx$. Use finite sums
    of interval indicators with rational endpoints and coefficients in $\QQ+\mathrm i\QQ$ as dense approximants; each such
    step function vanishes outside a bounded interval. An input name supplies such functions $s_n$ with
    $\LpNorm{1}{f-s_n}\le2^{-n}$. Define
    $$\FourierTransform{f}(\xi):=\int_{\R}f(x)e^{-2\pi\mathrm i x\xi}\,dx.$$
    For the output in $C(\R,\C)$, a name supplies, for each positive integer $R$ and precision $n$, a polynomial with
    rational complex coefficients approximating the function uniformly on $[-R,R]$ within $2^{-n}$. This is the locally
    uniform representation.
-/
def IsL1StepName (f : ComplexL1) (p : ℕ → ℕ) : Prop :=
  ∀ n, ValidStepCode (p n) ∧ ‖f-stepFunctionLp (p n)‖ ≤ (1/2:ℝ)^n

/-- Polynomial names for the locally uniform representation on continuous functions. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    For functions on the whole real line, specify how the input controls the integral. Let $L^1(\R,\C)$ consist of
    integrable functions modulo equality almost everywhere, with norm $\LpNorm{1}{f}:=\int_{\R}|f(x)|\,dx$. Use finite sums
    of interval indicators with rational endpoints and coefficients in $\QQ+\mathrm i\QQ$ as dense approximants; each such
    step function vanishes outside a bounded interval. An input name supplies such functions $s_n$ with
    $\LpNorm{1}{f-s_n}\le2^{-n}$. Define
    $$\FourierTransform{f}(\xi):=\int_{\R}f(x)e^{-2\pi\mathrm i x\xi}\,dx.$$
    For the output in $C(\R,\C)$, a name supplies, for each positive integer $R$ and precision $n$, a polynomial with
    rational complex coefficients approximating the function uniformly on $[-R,R]$ within $2^{-n}$. This is the locally
    uniform representation.
-/
def IsLocallyUniformPolynomialName (g : C(ℝ,ℂ)) (q : ℕ → ℕ) : Prop :=
  ∀ R : ℕ, 0 < R → ∀ n : ℕ, ∀ ξ : ℝ, |ξ| ≤ R →
    ‖g ξ-(complexPolynomial (q (Nat.pair R n))).eval (ξ:ℂ)‖ ≤ (1/2:ℝ)^n

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Combining the input error, the series tail, and the coefficient error gives
    $$\sup_{|\xi|\le R}|\FourierTransform{f}(\xi)-P(\xi)|\le3\cdot2^{-(n+2)}<2^{-n}.
-/
theorem fourierNameTransform_correct (f : ComplexL1) (p : ℕ → ℕ) (hp : IsL1StepName f p) :
    IsLocallyUniformPolynomialName (Real.Lp.fourierTransform f).toContinuousMap (fourierNameTransform p) := by
  intro R _ n ξ hξ
  apply fourierNameTransform_error p (Real.Lp.fourierTransform f) R n (hp (n+2)).1 _ ξ hξ
  intro t
  rw [← stepFunctionLp_fourier (p (n+2)) (hp (n+2)).1]
  exact (L1_fourier_difference f (stepFunctionLp (p (n+2))) t).trans (hp (n+2)).2

/-- The one closed program works for every valid name, without requiring computable input names. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    The construction works for every valid input name, including noncomputable names. The preceding estimate proves
    that the output is a name of the Fourier transform, and confluence excludes other numeral outputs.
-/
theorem fourier_L1_name_realizer :
    UniformNumericalComputes fourierNameProgram fourierNameTransform ∧
    ∀ f : ComplexL1, ∀ p : ℕ → ℕ, IsL1StepName f p →
      IsLocallyUniformPolynomialName (Real.Lp.fourierTransform f).toContinuousMap (fourierNameTransform p) :=
  ⟨fourierNameProgram_computes,fourierNameTransform_correct⟩

/-- Rational real and imaginary parts approximate any complex number. -/
theorem complexRationalPoint_dense : DenseRange complexRationalPoint := by
  apply Metric.denseRange_iff.mpr
  intro z ε hε
  obtain ⟨u,hu⟩ := rationalPoint_dense.exists_dist_lt z.re (half_pos hε)
  obtain ⟨v,hv⟩ := rationalPoint_dense.exists_dist_lt z.im (half_pos hε)
  refine ⟨Nat.pair u v,?_⟩
  have hr : (complexRationalPoint (Nat.pair u v)).re = rationalPoint u := by
    simp [complexRationalPoint]
  have hi : (complexRationalPoint (Nat.pair u v)).im = rationalPoint v := by
    simp [complexRationalPoint]
  have h := Complex.norm_le_abs_re_add_abs_im (z-complexRationalPoint (Nat.pair u v))
  rw [Complex.sub_re,Complex.sub_im,hr,hi] at h
  rw [Real.dist_eq] at hu hv
  rw [dist_eq_norm]
  linarith

theorem complexCoefficientList_eval (N : ℕ) (a : ℕ → ℕ) (z : ℂ) :
    (complexPolynomial (coefficientListCode N a)).eval z =
      ∑ j ∈ Finset.range N, complexRationalPoint (a j)*z^j := by
  rw [complexPolynomial_eval]
  simp only [coefficientListCode,NatListCode.decode_encode,List.length_map,List.length_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < ((List.range N).map a).length := by simpa using Finset.mem_range.mp hj
  rw [List.getD_eq_getElem _ _ hj']
  simp

/-- Weierstrass on the two real components gives a complex polynomial approximation. -/
theorem exists_complex_polynomial_near (g : C(ℝ,ℂ)) (R : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, ∀ x : ℝ, |x| ≤ R → ‖P.eval (x:ℂ)-g x‖ < ε := by
  obtain ⟨P,hP⟩ := exists_polynomial_near_of_continuousOn (-(R:ℝ)) R (fun x => (g x).re)
    (Complex.continuous_re.comp g.continuous).continuousOn (ε/2) (half_pos hε)
  obtain ⟨Q,hQ⟩ := exists_polynomial_near_of_continuousOn (-(R:ℝ)) R (fun x => (g x).im)
    (Complex.continuous_im.comp g.continuous).continuousOn (ε/2) (half_pos hε)
  refine ⟨P.map Complex.ofRealHom + Polynomial.C Complex.I * Q.map Complex.ofRealHom,fun x hx => ?_⟩
  have he : (P.map Complex.ofRealHom + Polynomial.C Complex.I * Q.map Complex.ofRealHom).eval (x:ℂ) =
      Complex.ofReal (P.eval x) + Complex.I*Complex.ofReal (Q.eval x) := by
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    rw [show (x:ℂ) = Complex.ofRealHom x from rfl,Polynomial.eval_map_apply,Polynomial.eval_map_apply]
    rfl
  rw [he]
  have h := Complex.norm_le_abs_re_add_abs_im
    (Complex.ofReal (P.eval x) + Complex.I*Complex.ofReal (Q.eval x)-g x)
  simp only [Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.sub_im,Complex.add_im,Complex.mul_im,
    zero_mul,one_mul,mul_zero,add_zero,zero_add,sub_zero] at h
  have hp := hP x (abs_le.mp hx)
  have hq := hQ x (abs_le.mp hx)
  linarith

/-- Approximate the finite complex coefficients, with a window-dependent error allowance. -/
theorem exists_complexPolynomial_code_near (g : C(ℝ,ℂ)) (R : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℕ, ∀ x : ℝ, |x| ≤ R → ‖(complexPolynomial c).eval (x:ℂ)-g x‖ < ε := by
  classical
  obtain ⟨P,hP⟩ := exists_complex_polynomial_near g R (half_pos hε)
  let N := P.natDegree+1
  let B : ℝ := ((R:ℝ)+1)^N
  have hN : (0:ℝ)<N := by dsimp [N]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let δ := ε/(2*N*B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  choose a ha using (fun j : ℕ => complexRationalPoint_dense.exists_dist_lt (P.coeff j) hδ)
  refine ⟨coefficientListCode N a,fun x hx => ?_⟩
  have he : P.eval (x:ℂ) = ∑ j ∈ Finset.range N, P.coeff j*(x:ℂ)^j := by
    conv_lhs => rw [P.as_sum_range]
    simp [N,Polynomial.eval_finsetSum]
  have hb : ‖(complexPolynomial (coefficientListCode N a)).eval (x:ℂ)-P.eval (x:ℂ)‖ ≤ ε/2 := by
    rw [complexCoefficientList_eval,he,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j ∈ Finset.range N, ‖complexRationalPoint (a j)*(x:ℂ)^j-P.coeff j*(x:ℂ)^j‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range N, δ*B := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← sub_mul,norm_mul]
        have ha' : ‖complexRationalPoint (a j)-P.coeff j‖ ≤ δ := by
          simpa only [dist_eq_norm,norm_sub_rev] using (ha j).le
        apply mul_le_mul ha' _ (norm_nonneg _) (by positivity)
        rw [norm_pow,Complex.norm_real,Real.norm_eq_abs]
        exact (pow_le_pow_left₀ (abs_nonneg x) (hx.trans (by linarith)) j).trans
          (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt (Finset.mem_range.mp hj)))
      _ = ε/2 := by
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        dsimp [δ]
        field_simp
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((complexPolynomial (coefficientListCode N a)).eval (x:ℂ)) (P.eval (x:ℂ)) (g x)
  linarith [hP x hx]

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Fix $g\in C(\R,\C)$, a positive integer $R$, and $\varepsilon>0$. Apply the real Weierstrass approximation theorem
    separately to the real and imaginary parts of $g$ on $[-R,R]$, with error less than $\varepsilon/4$ for each part.
    Combining the two real polynomials gives a complex polynomial $A$ satisfying
    $$\sup_{|x|\le R}|A(x)-g(x)|<\varepsilon/2.$$
    Take $N\ge1$ large enough to include all coefficients of $A$, and approximate each coefficient by a rational complex
    number within
    $$\delta:=\frac{\varepsilon}{2N(R+1)^N}.$$
    Such approximations exist by the density of rational real and imaginary parts. For the resulting rational complex
    polynomial $P$, the triangle inequality and $|x|^j\le(R+1)^N$ for $j<N$ give
    $$\begin{aligned}
    \sup_{|x|\le R}|P(x)-A(x)|&\le N\delta(R+1)^N=\varepsilon/2,\\
    \sup_{|x|\le R}|P(x)-g(x)|&<\varepsilon.
    \end{aligned}$$
    Choosing such a polynomial with $\varepsilon=2^{-n}$ for each $R,n$ produces the required name. These choices prove
    existence; no procedure for making them is assumed.

    For uniqueness, suppose the same name represents $g$ and $h$, and fix $x\in\R$. Choose a positive integer
    $R>|x|$. If $P_{R,n}$ is the polynomial supplied by that name, then
    $$|g(x)-h(x)|\le|g(x)-P_{R,n}(x)|+|h(x)-P_{R,n}(x)|\le2\cdot2^{-n}.$$
    Letting $n\to\infty$ proves $g(x)=h(x)$. Since $x$ was arbitrary, the two functions are equal.
    \end{proof}
-/
theorem exists_locallyUniformPolynomialName (g : C(ℝ,ℂ)) : ∃ q, IsLocallyUniformPolynomialName g q := by
  classical
  choose q hq using (fun z : ℕ => exists_complexPolynomial_code_near g z.unpair.1
    (pow_pos (by norm_num : (0:ℝ)<1/2) z.unpair.2))
  refine ⟨q,fun R _ n x hx => ?_⟩
  have h := hq (Nat.pair R n) x (by simpa only [Nat.unpair_pair] using hx)
  simpa only [Nat.unpair_pair,norm_sub_rev] using h.le

/-- Error-bound names determine at most one point of a normed space. -/
theorem eq_of_common_dyadic_approximants {E : Type*} [NormedAddCommGroup E]
    (a b : E) (u : ℕ → E) (ha : ∀ n, ‖a-u n‖ ≤ (1/2:ℝ)^n)
    (hb : ∀ n, ‖b-u n‖ ≤ (1/2:ℝ)^n) : a = b := by
  by_contra hab
  have hpos : 0 < ‖a-b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (half_pos hpos) (by norm_num : (1/2:ℝ)<1)
  have ht := norm_sub_le_norm_sub_add_norm_sub a (u n) b
  rw [norm_sub_rev (u n) b] at ht
  linarith [ha n,hb n]

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Take each interval indicator to be one on $(a,b]$, with $a\le b$, and zero elsewhere. Changing either endpoint's
    value does not change its almost-everywhere class. An input name determines at most one element of $L^1$: if the same
    step functions name both $f$ and $g$, then
    $$\LpNorm{1}{f-g}\le\LpNorm{1}{f-s_n}+\LpNorm{1}{g-s_n}\le2\cdot2^{-n}$$
    for every $n$. Letting $n\to\infty$ gives $f=g$ in $L^1$.
-/
theorem IsL1StepName.unique {f g : ComplexL1} {p : ℕ → ℕ}
    (hf : IsL1StepName f p) (hg : IsL1StepName g p) : f = g :=
  eq_of_common_dyadic_approximants f g (fun n => stepFunctionLp (p n)) (fun n => (hf n).2) (fun n => (hg n).2)

theorem IsLocallyUniformPolynomialName.unique {f g : C(ℝ,ℂ)} {q : ℕ → ℕ}
    (hf : IsLocallyUniformPolynomialName f q) (hg : IsLocallyUniformPolynomialName g q) : f = g := by
  ext x
  obtain ⟨R,hR⟩ := exists_nat_gt |x|
  have hpos : 0 < R := by exact_mod_cast (lt_of_le_of_lt (abs_nonneg x) hR)
  exact eq_of_common_dyadic_approximants (f x) (g x)
    (fun n => (complexPolynomial (q (Nat.pair R n))).eval (x:ℂ))
    (fun n => hf R hpos n x hR.le) (fun n => hg R hpos n x hR.le)

/-- The polynomial names give a surjective partial representation of all continuous functions. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Locally uniform polynomial representation
  excerpt: |
    \begin{lemma*}[\termdefineas{Locally uniform polynomial representation}{Locally uniform polynomial representation}]
    Every function in $C(\R,\C)$ has a locally uniform name by rational complex polynomials. Two continuous functions
    with the same name are equal.
    \end{lemma*}
-/
noncomputable def locallyUniformPolynomialRepresentation : Representation C(ℝ,ℂ) where
  domain := {q | ∃ g : C(ℝ,ℂ), IsLocallyUniformPolynomialName g q}
  toFun q := Classical.choose q.property
  surjective g := by
    obtain ⟨q,hq⟩ := exists_locallyUniformPolynomialName g
    refine ⟨⟨q,⟨g,hq⟩⟩,?_⟩
    exact IsLocallyUniformPolynomialName.unique (Classical.choose_spec (show ∃ h, IsLocallyUniformPolynomialName h q from ⟨g,hq⟩)) hq

theorem locallyUniformPolynomialRepresentation_spec (q : locallyUniformPolynomialRepresentation.domain) :
    IsLocallyUniformPolynomialName (locallyUniformPolynomialRepresentation.toFun q) q.val :=
  Classical.choose_spec q.property

end PolishSpaceBook
