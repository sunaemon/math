module

public import PolishSpaceBook.LambdaHaltingIntegral
public import Mathlib.Analysis.SpecialFunctions.Bernstein

@[expose] public section

/-! # Quantitative Bernstein approximation on a bounded real interval

The binomial variance and a finite Cauchy--Schwarz estimate give an explicit
uniform error for Lipschitz functions. The degree is then a natural number
computed from the radius and requested dyadic precision.
-/
namespace PolishSpaceBook
open scoped unitInterval

/-- The mean absolute deviation of the binomial grid is at most 1/(2 sqrt d). -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    The binomial theorem and its first two derivatives give
    $$\sum_{j=0}^{d}\BernsteinBasis{d}{j}{t}=1,\qquad
     \sum_{j=0}^{d}(t-j/d)^2\BernsteinBasis{d}{j}{t}=\frac{t(1-t)}d.$$
    The weights are nonnegative. Put
    $$D:=\sum_{j=0}^{d}|t-j/d|\BernsteinBasis{d}{j}{t}.$$
    The finite Cauchy--Schwarz inequality gives
    $$\begin{aligned}
     D^2&\le\left(\sum_{j=0}^{d}\BernsteinBasis{d}{j}{t}\right)
           \left(\sum_{j=0}^{d}(t-j/d)^2\BernsteinBasis{d}{j}{t}\right)\\
     &=\frac{t(1-t)}d\le\frac1{4d}.
    \end{aligned}$$
    Since $D\ge0$, it follows that $D\le1/(2\sqrt d)$.
-/
theorem bernstein_mean_deviation (d : ℕ) (hd : d ≠ 0) (t : I) :
    ∑ k : Fin (d+1), |(t:ℝ)-(bernstein.z k:ℝ)| *bernstein d k t ≤ 1/(2*Real.sqrt d) := by
  let D := ∑ k : Fin (d+1), |(t:ℝ)-(bernstein.z k:ℝ)| *bernstein d k t
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) bernstein_nonneg)
  have hsq : D^2 ≤ (t:ℝ)*(1-t)/d := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ)
      (r := fun k : Fin (d+1) => |(t:ℝ)-(bernstein.z k:ℝ)| *bernstein d k t)
      (f := fun k : Fin (d+1) => bernstein d k t)
      (g := fun k : Fin (d+1) => ((t:ℝ)-(bernstein.z k:ℝ))^2*bernstein d k t)
      (fun _ _ => bernstein_nonneg)
      (fun _ _ => mul_nonneg (sq_nonneg _) bernstein_nonneg)
      (fun k _ => by rw [mul_pow,sq_abs]; ring_nf; exact le_rfl)
    simpa only [bernstein.probability,one_mul,bernstein.variance hd] using h
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
  have hv : (t:ℝ)*(1-t)/d ≤ 1/(4*(d:ℝ)) := by
    apply (div_le_iff₀ hdR).mpr
    have he : (1/(4*(d:ℝ)))*(d:ℝ) = 1/4 := by field_simp
    rw [he]
    nlinarith [sq_nonneg ((t:ℝ)-1/2)]
  have hroot : Real.sqrt (1/(4*(d:ℝ))) = 1/(2*Real.sqrt d) := by
    rw [Real.sqrt_div (by norm_num),Real.sqrt_one,Real.sqrt_mul (by norm_num)]
    norm_num
  calc
    D = Real.sqrt (D^2) := (Real.sqrt_sq hD).symm
    _ ≤ Real.sqrt (1/(4*(d:ℝ))) := Real.sqrt_le_sqrt (hsq.trans hv)
    _ = _ := hroot

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Subtract $g(t)$ using the fact that the weights sum to one, and apply the Lipschitz bound:
    $$\begin{aligned}
     |\BernsteinApproximation{d}{g}{t}-g(t)|
     &\le\sum_{j=0}^{d}\BernsteinBasis{d}{j}{t}|g(j/d)-g(t)|\\
     &\le LD\le\frac{L}{2\sqrt d}.
    \end{aligned}$$
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Quantitative Bernstein approximation
-/
theorem bernstein_lipschitz_error (g : C(I,ℝ)) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ u v : I, |g u-g v| ≤ L*|(u:ℝ)-v|) (d : ℕ) (hd : d ≠ 0) (t : I) :
    |bernsteinApproximation d g t-g t| ≤ L/(2*Real.sqrt d) := by
  have he : bernsteinApproximation d g t-g t =
      ∑ k : Fin (d+1), bernstein d k t*(g (bernstein.z k)-g t) := by
    simp only [bernsteinApproximation.apply,smul_eq_mul,mul_sub,Finset.sum_sub_distrib,
      ← Finset.sum_mul,bernstein.probability,one_mul]
  rw [he]
  calc
    _ ≤ ∑ k : Fin (d+1), |bernstein d k t*(g (bernstein.z k)-g t)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin (d+1), bernstein d k t*(L*|(bernstein.z k:ℝ)-t|) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul,abs_of_nonneg bernstein_nonneg]
      exact mul_le_mul_of_nonneg_left (hg _ _) bernstein_nonneg
    _ = L*(∑ k : Fin (d+1), |(t:ℝ)-(bernstein.z k:ℝ)| *bernstein d k t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_sub_comm]
      ring
    _ ≤ L*(1/(2*Real.sqrt d)) := mul_le_mul_of_nonneg_left (bernstein_mean_deviation d hd t) hL
    _ = _ := by ring

noncomputable def haltingRescaled (R : ℕ) : C(I,ℝ) where
  toFun t := haltingIntegralFunction (2*R*(t:ℝ)-R)
  continuous_toFun := haltingIntegralFunction_continuous.comp
    ((continuous_const.mul continuous_subtype_val).sub continuous_const)

theorem haltingRescaled_lipschitz (R : ℕ) (u v : I) :
    |haltingRescaled R u-haltingRescaled R v| ≤ (2*R)*|(u:ℝ)-v| := by
  apply (haltingIntegralFunction_lipschitz _ _).trans
  change |(2*(R:ℝ)*(u:ℝ)-R)-(2*R*(v:ℝ)-R)| ≤ _
  rw [show (2*(R:ℝ)*(u:ℝ)-R)-(2*R*(v:ℝ)-R) = (2*R)*((u:ℝ)-v) by ring,
    abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤2*R)]

def haltingBernsteinDegree (R n : ℕ) : ℕ := (R*2^n)^2

theorem haltingBernsteinDegree_pos {R : ℕ} (hR : 0 < R) (n : ℕ) : 0 < haltingBernsteinDegree R n := by
  unfold haltingBernsteinDegree
  positivity

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    We now construct a locally uniform polynomial name. Given integers $R\ge1$ and $n\ge0$, put
    $$g_R(t):=f(2Rt-R),\qquad d:=(R2^n)^2.$$
    The Lipschitz constant of $g_R$ is at most $2R$.
    The \termuseas{Quantitative Bernstein approximation}{quantitative Bernstein lemma} therefore gives
    $$|\BernsteinApproximation{d}{g_R}{t}-g_R(t)|
     \le\frac{2R}{2\sqrt d}=2^{-n}\qquad(0\le t\le1).$$
    Consequently, the rational polynomial
    $$Q_{R,n}(x):=\BernsteinApproximation{d}{g_R}{(x+R)/(2R)}$$
    approximates $f$ uniformly on $[-R,R]$ with error at most $2^{-n}$.
-/
theorem haltingBernsteinDegree_error {R : ℕ} (hR : 0 < R) (n : ℕ) (t : I) :
    |bernsteinApproximation (haltingBernsteinDegree R n) (haltingRescaled R) t-haltingRescaled R t| ≤ (1/2:ℝ)^n := by
  have h := bernstein_lipschitz_error (haltingRescaled R) (2*R) (by positivity)
    (haltingRescaled_lipschitz R) _ (Nat.ne_of_gt (haltingBernsteinDegree_pos hR n)) t
  have hs : Real.sqrt (haltingBernsteinDegree R n) = (R:ℝ)*2^n := by
    simp only [haltingBernsteinDegree,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat]
    rw [Real.sqrt_sq (by positivity)]
  have hR0 : (R:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have he : (2*(R:ℝ))/(2*((R:ℝ)*2^n)) = (1/2:ℝ)^n := by
    rw [div_pow]
    field_simp
    simp
  simpa only [hs,he] using h

end PolishSpaceBook
