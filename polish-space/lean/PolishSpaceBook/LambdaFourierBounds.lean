module

public import PolishSpaceBook.LambdaRealRepresentation
public import PolishSpaceBook.LambdaBoundedProducts
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-! # Explicit exponential-series cutoffs for Fourier approximation -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
open Filter Topology
set_option maxRecDepth 4096

/-- The exponential polynomial with exactly N terms, including the constant term. -/
noncomputable def exponentialPartial (z : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, z^j/(j.factorial:ℂ)

/-- Once the factorial denominator grows at least twice as fast, each term halves. -/
theorem exponential_term_halves {r : ℝ} (hr : 0 ≤ r) (k : ℕ)
    (hk : 2*r ≤ k+1) :
    r^(k+1)/((k+1).factorial:ℝ) ≤ (r^k/(k.factorial:ℝ))*(1/2) := by
  have hf : (0:ℝ) < k.factorial := by positivity
  have hd : (0:ℝ) < k+1 := by positivity
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  apply (div_le_iff₀ (mul_pos hd hf)).mpr
  have he : (r^k/(k.factorial:ℝ))*(1/2)*((k+1)*k.factorial) = r^k*((k+1)/2) := by
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hr _)

theorem exponential_term_geometric {r : ℝ} (hr : 0 ≤ r) (k : ℕ)
    (hk : 2*r ≤ k+1) (i : ℕ) :
    r^(i+k)/((i+k).factorial:ℝ) ≤ (r^k/(k.factorial:ℝ))*(1/2:ℝ)^i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [show i+1+k = (i+k)+1 by omega,pow_succ]
    calc
      r^((i+k)+1)/(((i+k)+1).factorial:ℝ) ≤
          (r^(i+k)/((i+k).factorial:ℝ))*(1/2) :=
        exponential_term_halves hr (i+k) (by push_cast; linarith)
      _ ≤ (r^k/(k.factorial:ℝ))*(1/2:ℝ)^i*(1/2) :=
        mul_le_mul_of_nonneg_right ih (by norm_num)
      _ = _ := by ring

/-- Sum the geometric majorant of the tail, without dividing by z. -/
theorem exponentialPartial_tail {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (hz : ‖z‖ ≤ r)
    (N : ℕ) (hN : 2*r ≤ N+1) :
    ‖Complex.exp z - exponentialPartial z N‖ ≤ 2*(r^N/(N.factorial:ℝ)) := by
  have hs : HasSum (fun j : ℕ => z^j/(j.factorial:ℂ)) (Complex.exp z) := by
    simpa [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp z
  have ht := (summable_nat_add_iff N).mpr hs.summable
  have hn : Summable (fun i : ℕ => ‖z^(i+N)/((i+N).factorial:ℂ)‖) :=
    summable_norm_iff.mpr ht
  have he : Complex.exp z - exponentialPartial z N =
      ∑' i : ℕ, z^(i+N)/((i+N).factorial:ℂ) := by
    have h := hs.summable.sum_add_tsum_nat_add N
    rw [hs.tsum_eq] at h
    exact (eq_sub_iff_add_eq.mpr (by simpa [exponentialPartial,add_comm] using h)).symm
  rw [he]
  have hg := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left
    (r^N/(N.factorial:ℝ))
  calc
    ‖∑' i : ℕ, z^(i+N)/((i+N).factorial:ℂ)‖ ≤
        ∑' i : ℕ, ‖z^(i+N)/((i+N).factorial:ℂ)‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' i : ℕ, (r^N/(N.factorial:ℝ))*(1/2:ℝ)^i := by
      apply hn.tsum_le_tsum _ hg
      intro i
      calc
        ‖z^(i+N)/((i+N).factorial:ℂ)‖ = ‖z‖^(i+N)/((i+N).factorial:ℝ) := by simp
        _ ≤ r^(i+N)/((i+N).factorial:ℝ) := by gcongr
        _ ≤ _ := exponential_term_geometric hr N hN i
    _ = 2*(r^N/(N.factorial:ℝ)) := by
      rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring

/-- A deliberately generous cutoff, computable using only addition and multiplication. -/
def fourierCutoff (M n : ℕ) : ℕ := 2*M + 2*M*M + n + 3

theorem exponential_initial_bound (M : ℕ) :
    (M:ℝ)^(2*M)/((2*M).factorial:ℝ) ≤ (2:ℝ)^(2*M*M) := by
  calc
    (M:ℝ)^(2*M)/((2*M).factorial:ℝ) ≤ (M:ℝ)^(2*M) :=
      div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos (2*M))
    _ ≤ ((2:ℝ)^M)^(2*M) := pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast (Nat.lt_two_pow_self (n := M)).le) _
    _ = (2:ℝ)^(2*M*M) := by rw [← pow_mul]; congr 1; ring

theorem exponentialPartial_cutoff_error {z : ℂ} (M n : ℕ) (hz : ‖z‖ ≤ M) :
    ‖Complex.exp z - exponentialPartial z (fourierCutoff M n)‖ ≤ (1/2:ℝ)^(n+2) := by
  have hg := exponential_term_geometric (by positivity : (0:ℝ) ≤ M) (2*M)
    (by push_cast; linarith) (2*M*M+n+3)
  have hN : 2*(M:ℝ) ≤ (fourierCutoff M n:ℝ)+1 := by
    unfold fourierCutoff; push_cast; nlinarith
  apply (exponentialPartial_tail (by positivity) hz _ hN).trans
  have he : 2*M*M+n+3+(2*M) = fourierCutoff M n := by unfold fourierCutoff; omega
  rw [he] at hg
  calc
    2*((M:ℝ)^(fourierCutoff M n)/((fourierCutoff M n).factorial:ℝ))
        ≤ 2*(((M:ℝ)^(2*M)/((2*M).factorial:ℝ))*(1/2:ℝ)^(2*M*M+n+3)) := by linarith
    _ ≤ 2*((2:ℝ)^(2*M*M)*(1/2:ℝ)^(2*M*M+n+3)) := by
      gcongr
      exact exponential_initial_bound M
    _ = (1/2:ℝ)^(n+2) := by
      rw [show 2*M*M+n+3 = 2*M*M+(n+2)+1 by omega,pow_add,pow_add,one_div_pow]
      field_simp

/-- Integrating the exponential polynomial gives the finite interval transform. -/
noncomputable def intervalExponentialPartial (a b : ℝ) (c : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, c^j*((b:ℂ)^(j+1)-(a:ℂ)^(j+1))/((j+1).factorial:ℂ)

theorem integral_exponentialPartial (a b : ℝ) (c : ℂ) (N : ℕ) :
    (∫ x in a..b, exponentialPartial (c*(x:ℂ)) N) = intervalExponentialPartial a b c N := by
  unfold exponentialPartial intervalExponentialPartial
  rw [intervalIntegral.integral_finsetSum (f := fun j x => (c*(x:ℂ))^j/(j.factorial:ℂ)) (fun j _ =>
    (((continuous_const.mul Complex.continuous_ofReal).pow j).div_const _).intervalIntegrable a b)]
  apply Finset.sum_congr rfl
  intro j hj
  have he : (fun x : ℝ => (c*(x:ℂ))^j/(j.factorial:ℂ)) =
      (fun x : ℝ => (c^j/(j.factorial:ℂ)) * ((x^j:ℝ):ℂ)) := by
    funext x; push_cast; rw [mul_pow]; ring
  rw [he,intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal,integral_pow]
  have hf : (j.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hj : (j:ℂ)+1 ≠ 0 := by exact_mod_cast (show j+1 ≠ 0 by omega)
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- The same finite polynomial works uniformly wherever the kernel exponent is bounded. -/
theorem intervalExponentialPartial_error (a b : ℝ) (hab : a ≤ b) (c : ℂ) (M n : ℕ)
    (hc : ‖c‖ * max |a| |b| ≤ M) :
    ‖(∫ x in a..b, Complex.exp (c*(x:ℂ))) -
      intervalExponentialPartial a b c (fourierCutoff M n)‖ ≤ (b-a)*(1/2:ℝ)^(n+2) := by
  rw [← integral_exponentialPartial]
  have hf : IntervalIntegrable (fun x : ℝ => Complex.exp (c*(x:ℂ))) MeasureTheory.volume a b :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable a b
  have hp : Continuous (fun x : ℝ => exponentialPartial (c*(x:ℂ)) (fourierCutoff M n)) := by
    unfold exponentialPartial
    exact continuous_finsetSum _ (fun j _ =>
      ((continuous_const.mul Complex.continuous_ofReal).pow j).div_const _)
  rw [← intervalIntegral.integral_sub hf (hp.intervalIntegrable a b)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := (1/2:ℝ)^(n+2))
    (f := fun x => Complex.exp (c*(x:ℂ)) - exponentialPartial (c*(x:ℂ)) (fourierCutoff M n))
    (fun x hx => ?_)
  · simpa [abs_of_nonneg (sub_nonneg.mpr hab),mul_comm] using h
  rw [Set.uIoc_of_le hab] at hx
  apply exponentialPartial_cutoff_error
  calc
    ‖c*(x:ℂ)‖ = ‖c‖*|x| := by simp
    _ ≤ ‖c‖ * max |a| |b| := mul_le_mul_of_nonneg_left
      (abs_le_max_abs_abs hx.1.le hx.2) (norm_nonneg _)
    _ ≤ M := hc

noncomputable def fourierKernelScale (ξ : ℝ) : ℂ := -2*Real.pi*Complex.I*ξ

theorem fourierKernelScale_norm (ξ : ℝ) : ‖fourierKernelScale ξ‖ = 2*Real.pi*|ξ| := by
  simp [fourierKernelScale,abs_of_nonneg Real.pi_pos.le]

theorem intervalFourierPartial_error (a b : ℝ) (hab : a ≤ b) (R : ℝ) (M n : ℕ)
    (hM : 2*Real.pi*R*max |a| |b| ≤ M) (ξ : ℝ) (hξ : |ξ| ≤ R) :
    ‖(∫ x in a..b, Complex.exp (fourierKernelScale ξ*(x:ℂ))) -
      intervalExponentialPartial a b (fourierKernelScale ξ) (fourierCutoff M n)‖ ≤
        (b-a)*(1/2:ℝ)^(n+2) := by
  apply intervalExponentialPartial_error a b hab _ M n
  rw [fourierKernelScale_norm]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hξ (by positivity)) (le_max_of_le_left (abs_nonneg a))).trans hM

/-- An integer bound on the total weighted interval length absorbs all finite-sum errors. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Linearity of the integral and the triangle inequality give
    $$\begin{aligned}
    \sup_{|\xi|\le R}|\FourierTransform{s_{n+2}}(\xi)-B(\xi)|
     &\le A2^{-(n+A+2)}\\
     &\le2^{-(n+2)},
    \end{aligned}$$
    where the last inequality uses $A\le2^A$.
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Set
    $$N:=\FourierSeriesCutoff{M}{n+A},\qquad
     B(\xi):=\sum_{\ell<L}v_\ell\IntervalFourierPolynomial{a_\ell}{b_\ell}{N}{\xi}.
-/
theorem finiteFourierPartial_error (L : ℕ) (a b : ℕ → ℝ) (v : ℕ → ℂ)
    (hab : ∀ i < L, a i ≤ b i) (R : ℝ) (M A n : ℕ)
    (hM : ∀ i < L, 2*Real.pi*R*max |a i| |b i| ≤ M)
    (hA : (∑ i ∈ Finset.range L, ‖v i‖*(b i-a i)) ≤ A)
    (ξ : ℝ) (hξ : |ξ| ≤ R) :
    ‖(∑ i ∈ Finset.range L, v i * (∫ x in a i..b i, Complex.exp (fourierKernelScale ξ*(x:ℂ)))) -
      (∑ i ∈ Finset.range L, v i *
        intervalExponentialPartial (a i) (b i) (fourierKernelScale ξ) (fourierCutoff M (n+A)))‖ ≤
          (1/2:ℝ)^(n+2) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range L, ‖v i * (∫ x in a i..b i, Complex.exp (fourierKernelScale ξ*(x:ℂ))) -
      v i * intervalExponentialPartial (a i) (b i) (fourierKernelScale ξ) (fourierCutoff M (n+A))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range L, (‖v i‖*(b i-a i))*(1/2:ℝ)^(n+A+2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub,norm_mul,mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (intervalFourierPartial_error _ _ (hab i (Finset.mem_range.mp hi)) R M (n+A)
          (hM i (Finset.mem_range.mp hi)) ξ hξ) (norm_nonneg _)
    _ = (∑ i ∈ Finset.range L, ‖v i‖*(b i-a i))*(1/2:ℝ)^(n+A+2) := by rw [Finset.sum_mul]
    _ ≤ (A:ℝ)*(1/2:ℝ)^(n+A+2) := mul_le_mul_of_nonneg_right hA (by positivity)
    _ ≤ (2:ℝ)^A*(1/2:ℝ)^(n+A+2) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Nat.lt_two_pow_self (n := A)).le) (by positivity)
    _ = (1/2:ℝ)^(n+2) := by
      rw [show n+A+2 = A+(n+2) by omega,pow_add,one_div_pow]
      field_simp

/-- The input is the pair of the integer radius bound and requested precision. -/
def fourierCutoffProgram : AlphaTerm :=
  let M := numericalProjectionTerm true
  let n := numericalProjectionTerm false
  let twiceM := mulNumerical (numericalConstant 2) M
  addNumerical (addNumerical (addNumerical twiceM (mulNumerical twiceM M)) n) (numericalConstant 3)

theorem fourierCutoffProgram_computes : NumericalComputes fourierCutoffProgram
    (fun p => fourierCutoff p.unpair.1 p.unpair.2) := by
  exact ((((numericalConstant_computes 2).mul (projection_computes true)).add
    (((numericalConstant_computes 2).mul (projection_computes true)).mul (projection_computes true))).add
      (projection_computes false)).add (numericalConstant_computes 3)

/-- Discard the denominator and add the two unsigned numerator parts. -/
def rationalMagnitudeBound (c : ℕ) : ℕ := (RationalCode.ofNat c).1.1 + (RationalCode.ofNat c).1.2

theorem rationalPoint_abs_le_magnitude (c : ℕ) : |rationalPoint c| ≤ rationalMagnitudeBound c := by
  unfold rationalPoint RationalCode.value rationalMagnitudeBound
  push_cast
  rw [abs_div,abs_of_pos (by positivity : (0:ℝ) < (RationalCode.ofNat c).2+1)]
  calc
    _ ≤ |((RationalCode.ofNat c).1.1:ℝ) - (RationalCode.ofNat c).1.2| :=
      div_le_self (abs_nonneg _) (by norm_num)
    _ ≤ ((RationalCode.ofNat c).1.1:ℝ) + (RationalCode.ofNat c).1.2 := by
      exact (abs_sub _ _).trans_eq (by simp)

def rationalMagnitudeProgram : AlphaTerm :=
  addNumerical (rationalNumeratorTerm true) (rationalNumeratorTerm false)

theorem rationalMagnitudeProgram_computes : NumericalComputes rationalMagnitudeProgram rationalMagnitudeBound :=
  (rationalNumerator_computes true).add (rationalNumerator_computes false)

/-- A bound for every exponent on the frequency window [-R,R]. -/
def fourierRadiusBound (R a b : ℕ) : ℕ := 8*R*(rationalMagnitudeBound a+rationalMagnitudeBound b)

theorem fourierRadiusBound_valid (R a b : ℕ) :
    2*Real.pi*(R:ℝ)*max |rationalPoint a| |rationalPoint b| ≤ fourierRadiusBound R a b := by
  have hm : max |rationalPoint a| |rationalPoint b| ≤
      (rationalMagnitudeBound a:ℝ)+rationalMagnitudeBound b := by
    apply max_le
    · exact (rationalPoint_abs_le_magnitude a).trans (le_add_of_nonneg_right (by positivity))
    · exact (rationalPoint_abs_le_magnitude b).trans (le_add_of_nonneg_left (by positivity))
  unfold fourierRadiusBound
  push_cast
  calc
    _ ≤ 2*Real.pi*(R:ℝ)*((rationalMagnitudeBound a:ℝ)+rationalMagnitudeBound b) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ _ := by
      gcongr
      linarith [Real.pi_le_four]

/-- Input R paired with the pair of endpoint codes. -/
def fourierRadiusProgram : AlphaTerm :=
  let endpoints := numericalProjectionTerm false
  let A := numericalCompose rationalMagnitudeProgram (numericalCompose (numericalProjectionTerm true) endpoints)
  let B := numericalCompose rationalMagnitudeProgram (numericalCompose (numericalProjectionTerm false) endpoints)
  mulNumerical (mulNumerical (numericalConstant 8) (numericalProjectionTerm true)) (addNumerical A B)

theorem fourierRadiusProgram_computes : NumericalComputes fourierRadiusProgram
    (fun p => fourierRadiusBound p.unpair.1 p.unpair.2.unpair.1 p.unpair.2.unpair.2) :=
  ((numericalConstant_computes 8).mul (projection_computes true)).mul
    ((rationalMagnitudeProgram_computes.comp ((projection_computes true).comp (projection_computes false))).add
      (rationalMagnitudeProgram_computes.comp ((projection_computes false).comp (projection_computes false))))

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Uniform truncation for interval Fourier transforms
  excerpt: |
    \begin{lemma*}[\termdefineas{Uniform truncation for interval Fourier transforms}{Uniform truncation for interval
    Fourier transforms}]
    Let $a\le b$, $R>0$, and let $M,n\in\NN$ satisfy $2\pi R\max(|a|,|b|)\le M$. Set
    $$\FourierSeriesCutoff{M}{n}:=2M+2M^2+n+3$$
    and, for $N\in\NN$, put
    $$\IntervalFourierPolynomial{a}{b}{N}{\xi}:=
     \sum_{j<N}\frac{(-2\pi\mathrm i\xi)^j(b^{j+1}-a^{j+1})}{(j+1)!}.$$
    Then, with $N=\FourierSeriesCutoff{M}{n}$,
    $$\sup_{|\xi|\le R}\left|\int_a^b e^{-2\pi\mathrm i x\xi}\,dx
     -\IntervalFourierPolynomial{a}{b}{N}{\xi}\right|\le(b-a)2^{-(n+2)}.$$
    A closed numerical lambda term computes $\FourierSeriesCutoff{M}{n}$ from $M,n$. If $a,b$ are rational and $R$ is a
    positive integer, a suitable $M$ can also be computed from their codes.
    \end{lemma*}
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Write $\ExponentialPartialSum{N}{z}:=\sum_{j<N}z^j/j!$. For $r\ge0$, put $t_k=r^k/k!$. If $k+1\ge2r$, then
    $$t_{k+1}=t_k\frac{r}{k+1}\le\frac{t_k}{2}.$$
    Thus $t_{N+i}\le t_N2^{-i}$ whenever $N+1\ge2r$. Absolute convergence of the exponential series and the geometric
    sum give, for $|z|\le r$,
    $$|e^z-\ExponentialPartialSum{N}{z}|\le\sum_{i=0}^{\infty}t_{N+i}\le2t_N.$$
    To make the cutoff explicit, take $r=M\in\NN$. Since $M\le2^M$ and $(2M)!\ge1$,
    $$t_{2M}\le M^{2M}\le2^{2M^2}.$$
    Starting at $2M$, each further step halves the bound. For $N=\FourierSeriesCutoff{M}{n}$ there are $2M^2+n+3$ such
    steps, so
    $$|e^z-\ExponentialPartialSum{N}{z}|
     \le2\cdot2^{2M^2}2^{-(2M^2+n+3)}=2^{-(n+2)}.$$
    This includes $M=0$, using the usual convention $M^0=1$.

    For $x\in[a,b]$ and $|\xi|\le R$, the exponent $z=-2\pi\mathrm i x\xi$ has modulus at most $M$. Integrating the last
    bound over $[a,b]$ gives the required error. Indeed, integrating the finite sum term by term yields
    $$\int_a^b\ExponentialPartialSum{N}{-2\pi\mathrm i x\xi}\,dx
     =\IntervalFourierPolynomial{a}{b}{N}{\xi}.$$
    The construction uses no division by $\xi$ and works at $\xi=0$ as well. Its coefficients involve $\pi$; they will be
    approximated by rational complex numbers below.

    For the numerical construction, read $M,n$ by projections, compute $t=2M$, and then compute $t+tM+n+3$ using the
    addition and multiplication terms. Their composition gives a closed term $D$ with
    $$D\ChurchNumeral{\NatPair{M}{n}}\to_\beta^*\ChurchNumeral{\FourierSeriesCutoff{M}{n}}.$$
    To choose $M$, suppose the endpoint codes are $\RationalCode{p_a}{q_a}{d_a}$ and
    $\RationalCode{p_b}{q_b}{d_b}$. Their values have absolute values at most $p_a+q_a$ and $p_b+q_b$. Thus
    $$M:=8R(p_a+q_a+p_b+q_b)$$
    suffices because $\pi\le4$. The numerical projections, addition, and multiplication also compute this bound by a
    closed term. Neither construction requires a search or a test for equality of real numbers.
    \end{proof}
-/
theorem fourier_interval_truncation :
    NumericalComputes fourierCutoffProgram (fun p => fourierCutoff p.unpair.1 p.unpair.2) ∧
    NumericalComputes fourierRadiusProgram
      (fun p => fourierRadiusBound p.unpair.1 p.unpair.2.unpair.1 p.unpair.2.unpair.2) ∧
    (∀ R a b : ℕ,
      2*Real.pi*(R:ℝ)*max |rationalPoint a| |rationalPoint b| ≤ fourierRadiusBound R a b) ∧
    (∀ (a b : ℝ), a ≤ b → ∀ (R : ℝ) (M n : ℕ),
      2*Real.pi*R*max |a| |b| ≤ M → ∀ ξ : ℝ, |ξ| ≤ R →
      ‖(∫ x in a..b, Complex.exp (fourierKernelScale ξ*(x:ℂ))) -
        intervalExponentialPartial a b (fourierKernelScale ξ) (fourierCutoff M n)‖ ≤
          (b-a)*(1/2:ℝ)^(n+2)) :=
  ⟨fourierCutoffProgram_computes,fourierRadiusProgram_computes,fourierRadiusBound_valid,
    intervalFourierPartial_error⟩

end PolishSpaceBook
