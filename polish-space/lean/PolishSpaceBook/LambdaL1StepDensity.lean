module

public import PolishSpaceBook.LambdaFourierL1
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Order.Interval.Set.Union

@[expose] public section

/-! # Rational interval step functions are dense in L1

Approximate a compactly supported continuous function on a rational uniform
partition, then encode the endpoints and rational complex values as finite rows.
The final existence argument uses the standard density of compactly supported
continuous functions; it does not assert a computable choice from an unnamed L1 element.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA MeasureTheory

noncomputable def intervalStep (a : ℕ → ℝ) (v : ℕ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range N, (Set.Ioc (a i) (a (i+1))).indicator (fun _ => v i) x

theorem intervalStep_integrable (a : ℕ → ℝ) (v : ℕ → ℂ) (N : ℕ) :
    Integrable (intervalStep a v N) := by
  apply integrable_finsetSum
  intro i _
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

theorem intervalStep_on_cell (a : ℕ → ℝ) (ha : Monotone a) (v : ℕ → ℂ) (N i : ℕ)
    (hi : i < N) (x : ℝ) (hx : x ∈ Set.Ioc (a i) (a (i+1))) : intervalStep a v N x = v i := by
  classical
  unfold intervalStep
  rw [Finset.sum_eq_single i]
  · simp [hx]
  · intro j _ hji
    have hjx : x ∉ Set.Ioc (a j) (a (j+1)) := by
      intro hjx
      obtain hji | hij := lt_or_gt_of_ne hji
      · have h := ha (show j+1 ≤ i by omega)
        linarith [hx.1,hjx.2]
      · have h := ha (show i+1 ≤ j by omega)
        linarith [hjx.1,hx.2]
    simp [hjx]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hi))

theorem intervalStep_off_window (a : ℕ → ℝ) (ha : Monotone a) (v : ℕ → ℂ) (N : ℕ)
    (x : ℝ) (hx : x ∉ Set.Ioc (a 0) (a N)) : intervalStep a v N x = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hix : x ∉ Set.Ioc (a i) (a (i+1)) := by
    intro hix
    apply hx
    exact ⟨(ha (Nat.zero_le i)).trans_lt hix.1,hix.2.trans (ha (by simpa using Finset.mem_range.mp hi))⟩
  simp [hix]

theorem intervalStep_error_integral {g : ℝ → ℂ} (hg : Integrable g)
    (a : ℕ → ℝ) (ha : Monotone a) (v : ℕ → ℂ) (N : ℕ) (η : ℝ)
    (hinside : ∀ x ∈ Set.Ioc (a 0) (a N), ‖g x-intervalStep a v N x‖ ≤ η)
    (houtside : ∀ x ∉ Set.Ioc (a 0) (a N), g x = 0) :
    (∫ x, ‖g x-intervalStep a v N x‖) ≤ (a N-a 0)*η := by
  have hb : Integrable ((Set.Ioc (a 0) (a N)).indicator (fun _ : ℝ => η)) := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  calc
    _ ≤ ∫ x, (Set.Ioc (a 0) (a N)).indicator (fun _ : ℝ => η) x := by
      apply integral_mono (hg.sub (intervalStep_integrable a v N)).norm hb
      intro x
      by_cases hx : x ∈ Set.Ioc (a 0) (a N)
      · simpa [hx] using hinside x hx
      · simp [hx,houtside x hx,intervalStep_off_window a ha v N x hx]
    _ = _ := by
      rw [integral_indicator measurableSet_Ioc,setIntegral_const,Real.volume_real_Ioc_of_le (ha (Nat.zero_le N))]
      rfl

/-- A compact support lies strictly inside some positive integer window. -/
theorem compactSupport_integer_window {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    ∃ R : ℕ, 0 < R ∧ ∀ x : ℝ, x ∉ Set.Ioc (-(R:ℝ)) R → g x = 0 := by
  obtain ⟨r,hr⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℝ)).mp hg.isCompact.isBounded
  obtain ⟨R,hR⟩ := exists_nat_gt (max r 0 + 1)
  have hpos : 0 < R := by exact_mod_cast (lt_of_lt_of_le (by linarith [le_max_right r 0] : (0:ℝ)<max r 0+1) hR.le)
  refine ⟨R,hpos,fun x hx => image_eq_zero_of_notMem_tsupport (fun hxt => ?_)⟩
  have hb : |x| ≤ r := by simpa [Metric.mem_closedBall,Real.dist_eq] using hr hxt
  apply hx
  have hx' : |x| < (R:ℝ) := lt_of_le_of_lt hb (by linarith [le_max_left r 0])
  exact ⟨(abs_lt.mp hx').1,(abs_lt.mp hx').2.le⟩

/-- Uniform rational grids, with arbitrarily small positive mesh. -/
theorem exists_rational_grid (R : ℕ) (hR : 0 < R) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∃ a : ℕ → ℚ,
      Monotone (fun i => (a i:ℝ)) ∧ (a 0:ℝ) = -(R:ℝ) ∧ (a N:ℝ) = R ∧
      ∀ i : ℕ, (a (i+1):ℝ)-(a i:ℝ) < δ := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((2*(R:ℝ))/δ)
  have hn : (0:ℝ)<N := (div_pos (by exact_mod_cast (show 0<2*R by omega)) hδ).trans hN
  have hn' : 0 < N := by exact_mod_cast hn
  let a : ℕ → ℚ := fun i => -(R:ℚ)+(2*R/N)*(i:ℚ)
  have he (i : ℕ) : (a i:ℝ) = -(R:ℝ)+(2*(R:ℝ)/N)*(i:ℝ) := by dsimp [a]; push_cast; rfl
  have hmesh : 0 < 2*(R:ℝ)/N := div_pos (by exact_mod_cast (show 0<2*R by omega)) hn
  refine ⟨N,hn',a,?_,?_,?_,?_⟩
  · intro i j hij
    simp only [he]
    exact add_le_add_right (mul_le_mul_of_nonneg_left (show (i:ℝ) ≤ (j:ℝ) by exact_mod_cast hij) hmesh.le) _
  · simp [he]
  · rw [he,div_mul_cancel₀ _ (ne_of_gt hn)]
    ring
  · intro i
    simp only [he,Nat.cast_add,Nat.cast_one]
    have hlt : 2*(R:ℝ)/N < δ := (div_lt_iff₀ hn).mpr (by
      have := (div_lt_iff₀ hδ).mp hN
      nlinarith)
    nlinarith

/-- Realize the finite mathematical step function by the numerical row code used by the program. -/
theorem intervalStep_has_code (a : ℕ → ℚ) (ha : Monotone (fun i => (a i:ℝ))) (u : ℕ → ℕ) (N : ℕ) :
    ∃ s : ℕ, ValidStepCode s ∧ stepFunction s = intervalStep (fun i => (a i:ℝ)) (fun i => complexRationalPoint (u i)) N := by
  classical
  choose e he using (fun i : ℕ => RationalCode.value_surjective (a i))
  let c : ℕ → ℕ := fun i => (e i).natCode
  have hc (i : ℕ) : rationalPoint (c i) = (a i:ℝ) := by simp [c,rationalPoint,he]
  let row : ℕ → ℕ := fun i => Nat.pair (c i) (Nat.pair (c (i+1)) (u i))
  let s := NatListCode.encode ((List.range N).map row)
  have hlen : (NatListCode.decode s).length = N := by simp [s]
  have hrow (i : ℕ) (hi : i < N) : stepRow s i = row i := by
    simp only [stepRow,s,NatListCode.decode_encode]
    have hi' : i < ((List.range N).map row).length := by simpa using hi
    rw [List.getD_eq_getElem _ _ hi']
    simp
  refine ⟨s,?_,?_⟩
  · intro i hi
    rw [hlen] at hi
    simp only [hrow i hi,row,Nat.unpair_pair,hc]
    exact ha (Nat.le_succ i)
  · funext x
    simp only [stepFunction,intervalStep,hlen]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [hrow i (Finset.mem_range.mp hi),stepRowFunction,row,Nat.unpair_pair,hc]

/-- Uniform continuity and rational complex approximations produce small L1 step error. -/
theorem compactContinuous_step_approximation {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgi : Integrable g) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℕ, ValidStepCode s ∧ (∫ x, ‖g x-stepFunction s x‖) ≤ ε := by
  classical
  obtain ⟨R,hR,hout⟩ := compactSupport_integer_window hgc
  have hr : (0:ℝ)<R := by exact_mod_cast hR
  let η := ε/(4*R)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Set.Icc (-(R:ℝ)) R)).uniformContinuousOn_of_continuous hg.continuousOn) η hη
  obtain ⟨N,hN,a,ha,ha0,haN,hmesh⟩ := exists_rational_grid R hR δ hδ
  choose u hu using (fun i : ℕ => complexRationalPoint_dense.exists_dist_lt (g (a i:ℝ)) hη)
  let v := fun i => complexRationalPoint (u i)
  have hin : ∀ x ∈ Set.Ioc (-(R:ℝ)) R, ‖g x-intervalStep (fun i => (a i:ℝ)) v N x‖ ≤ 2*η := by
    intro x hx
    have hx' : x ∈ Set.Ioc (a 0:ℝ) (a N:ℝ) := by simpa only [ha0,haN] using hx
    have hcover := Ioc_subset_biUnion_Ioc N (fun i => (a i:ℝ)) hx'
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hcover
    obtain ⟨hi,hxi⟩ := Set.mem_iUnion.mp hi
    have hiN : i < N := Finset.mem_range.mp hi
    rw [intervalStep_on_cell _ ha v N i hiN x hxi]
    have hai : (a i:ℝ) ∈ Set.Icc (-(R:ℝ)) R := by
      constructor
      · rw [← ha0]; exact ha (Nat.zero_le i)
      · rw [← haN]; exact ha hiN.le
    have hdist : dist x (a i:ℝ) < δ := by
      rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hxi.1)]
      exact lt_of_le_of_lt (sub_le_sub_right hxi.2 _) (hmesh i)
    have hm := hmod x ⟨hx.1.le,hx.2⟩ (a i:ℝ) hai hdist
    have hu' := hu i
    rw [dist_eq_norm] at hm hu'
    have ht := norm_sub_le_norm_sub_add_norm_sub (g x) (g (a i:ℝ)) (v i)
    dsimp [v] at ht ⊢
    linarith
  obtain ⟨s,hs,hscode⟩ := intervalStep_has_code a ha u N
  refine ⟨s,hs,?_⟩
  rw [hscode]
  have hbound := intervalStep_error_integral hgi (fun i => (a i:ℝ)) ha v N (2*η)
    (by simpa only [ha0,haN] using hin) (by simpa only [ha0,haN] using hout)
  rw [ha0,haN] at hbound
  have he : ((R:ℝ)-(-(R:ℝ)))*(2*η) = ε := by dsimp [η]; field_simp; ring
  simpa only [he] using hbound

/-- Standard continuous density followed by the explicit rational grid construction. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Fix $f\in L^1(\R,\C)$ and $\varepsilon>0$. By this density, choose a continuous function $g$ with compact support and
    $\LpNorm{1}{f-g}\le\varepsilon/2$. Take a positive integer
    $R$ such that $g(x)=0$ outside $(-R,R)$, and put $\eta:=\varepsilon/(8R)$. Uniform continuity on $[-R,R]$ gives a
    $\delta>0$ such that
    $$|g(x)-g(y)|<\eta\qquad(x,y\in[-R,R],\ |x-y|<\delta).$$
    Choose an integer $N\ge1$ with $2R/N<\delta$, and set
    $$a_i:=-R+\frac{2Ri}{N}\qquad(0\le i\le N).$$
    For each $i<N$, choose $v_i\in\QQ+\mathrm i\QQ$ with $|g(a_i)-v_i|<\eta$. Define
    $$s(x):=\begin{cases}
    v_i,&a_i<x\le a_{i+1}\text{ for some }i<N,\\
    0,&x\notin(-R,R].
    \end{cases}$$
    The intervals are disjoint and cover $(-R,R]$, so this defines a rational interval step function. On its $i$th
    interval,
    $$|g(x)-s(x)|\le|g(x)-g(a_i)|+|g(a_i)-v_i|<2\eta.$$
    Outside $(-R,R]$, both functions vanish. Hence
    $$\LpNorm{1}{g-s}\le2R\cdot2\eta=\varepsilon/2,\qquad
    \LpNorm{1}{f-s}\le\LpNorm{1}{f-g}+\LpNorm{1}{g-s}\le\varepsilon.$$
    
    Applying this construction with $\varepsilon=2^{-n}$ for each $n$ gives the required name. The rational endpoints and
    rational complex values have finite numerical codes, so each approximant has the list code used by the name
    transformer below. This proves that every $L^1$ element has a name; it does not supply a computable choice of a name
    from an element given without any representation.
    \end{proof}
-/
theorem L1_exists_step_approximation (f : ComplexL1) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℕ, ValidStepCode s ∧ ‖f-stepFunctionLp s‖ ≤ ε := by
  obtain ⟨g,hgc,hfg,hg,hgi⟩ := (L1.integrable_coeFn f).exists_hasCompactSupport_integral_sub_le
    (half_pos hε)
  obtain ⟨s,hs,hgs⟩ := compactContinuous_step_approximation hg hgc hgi (half_pos hε)
  refine ⟨s,hs,?_⟩
  rw [L1_norm_sub_eq_integral]
  have he : (∫ x, ‖f x-(stepFunctionLp s) x‖) = ∫ x, ‖f x-stepFunction s x‖ := by
    apply integral_congr_ae
    filter_upwards [stepFunctionLp_ae s] with x hx
    rw [hx]
  rw [he]
  calc
    _ ≤ ∫ x, (‖f x-g x‖ + ‖g x-stepFunction s x‖) := by
      apply integral_mono ((L1.integrable_coeFn f).sub (stepFunction_integrable s)).norm
        (((L1.integrable_coeFn f).sub hgi).norm.add (hgi.sub (stepFunction_integrable s)).norm)
      exact fun x => norm_sub_le_norm_sub_add_norm_sub (f x) (g x) (stepFunction s x)
    _ = (∫ x, ‖f x-g x‖) + ∫ x, ‖g x-stepFunction s x‖ :=
      integral_add ((L1.integrable_coeFn f).sub hgi).norm (hgi.sub (stepFunction_integrable s)).norm
    _ ≤ ε := by linarith

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Rational interval step representation
  excerpt: |
    \begin{lemma*}[\termdefineas{Rational interval step representation}{Rational interval step representation}]
    Every element of $L^1(\R,\C)$ has a name by rational interval step functions with the prescribed error bounds.
    \end{lemma*}
-/
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
theorem exists_L1StepName (f : ComplexL1) : ∃ p : ℕ → ℕ, IsL1StepName f p := by
  choose p hp using (fun n : ℕ => L1_exists_step_approximation f
    (show (0:ℝ) < (1/2:ℝ)^n by positivity))
  exact ⟨p,hp⟩

/-- All L1 elements are represented, with equality understood almost everywhere. -/
noncomputable def l1StepRepresentation : Representation ComplexL1 where
  domain := {p | ∃ f : ComplexL1, IsL1StepName f p}
  toFun p := Classical.choose p.property
  surjective f := by
    obtain ⟨p,hp⟩ := exists_L1StepName f
    refine ⟨⟨p,⟨f,hp⟩⟩,?_⟩
    exact IsL1StepName.unique
      (Classical.choose_spec (show ∃ g, IsL1StepName g p from ⟨f,hp⟩)) hp

theorem l1StepRepresentation_spec (p : l1StepRepresentation.domain) :
    IsL1StepName (l1StepRepresentation.toFun p) p.val := Classical.choose_spec p.property

/-- The already constructed closed lambda term realizes the canonical Fourier map. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Computability of the Fourier transform on $L^1$
-/
theorem fourier_hasComputableRealizer :
    HasComputableRealizer l1StepRepresentation locallyUniformPolynomialRepresentation
      (fun f : ComplexL1 => (Real.Lp.fourierTransform f).toContinuousMap) := by
  let F : l1StepRepresentation.domain → locallyUniformPolynomialRepresentation.domain :=
    fun p => ⟨fourierNameTransform p.val,⟨(Real.Lp.fourierTransform (l1StepRepresentation.toFun p)).toContinuousMap,
      fourierNameTransform_correct _ _ (l1StepRepresentation_spec p)⟩⟩
  refine ⟨F,⟨fourierNameProgram,fourierNameProgram_typeTwoComputes _⟩,?_⟩
  intro p
  exact IsLocallyUniformPolynomialName.unique (locallyUniformPolynomialRepresentation_spec (F p))
    (fourierNameTransform_correct _ _ (l1StepRepresentation_spec p))

end PolishSpaceBook
