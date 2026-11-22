module

public import PolishSpaceBook.ConditionalBorelKernel
public import PolishSpaceBook.PerfectSetsStandardBorelCoding
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

@[expose] public section

/-!
# Fiber concentration and uniqueness of disintegration

Use countably many measurable tests to choose one exceptional null set. The
conditional integral identity determines the values on these tests, and their
point-separating property then forces concentration on individual fibers.
-/

noncomputable section

namespace PolishSpaceBook.DisintegrationFibers

open Set MeasureTheory MeasurableSpace Filter
open scoped ENNReal MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) [IsProbabilityMeasure μ] (π : X → Y)
variable (p : Y → ProbabilityMeasure X) (hp : Measurable p)

include hp

lemma eval_measurable {A : Set X} (hA : MeasurableSet A) :
    Measurable (fun y => (p y : Measure X) A) :=
  (Measure.measurable_coe hA).comp (measurable_subtype_coe.comp hp)

/-- The conditional probability of an observed event is its indicator. -/
theorem observed_event (hπ : Measurable π)
    (hid : ∀ A D, MeasurableSet A → MeasurableSet D →
      ∫⁻ y in D, (p y : Measure X) A ∂μ.map π = μ (A ∩ π ⁻¹' D))
    {C : Set Y} (hC : MeasurableSet C) :
    (fun y => (p y : Measure X) (π ⁻¹' C)) =ᵐ[μ.map π]
      C.indicator (fun _ => (1 : ℝ≥0∞)) := by
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (eval_measurable p hp (hπ hC)) (measurable_const.indicator hC)
  intro D hD _
  rw [hid _ D (hπ hC) hD, lintegral_indicator hC]
  simp [Measure.restrict_apply hC, Measure.map_apply hπ (hC.inter hD), preimage_inter]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Choose a countable family $\Sequence{G_n}{n\in\omega}$ generating $\mathcal B(Y)$ and separating points.
    For each $n$ and every Borel $D\IncludedIn Y$, the extended identity gives
    $$\begin{aligned}
    \int_D\mu_y(\pi^{-1}(G_n))\,d\nu(y)
    &=\mu(\pi^{-1}(G_n)\cap\pi^{-1}(D))\\
    &=\nu(G_n\cap D)=\int_D1_{G_n}(y)\,d\nu(y).
    \end{aligned}$$
    Uniqueness of measurable densities therefore gives
    $\mu_y(\pi^{-1}(G_n))=1_{G_n}(y)$ almost everywhere. Countability lets us remove one common null set
    so that these identities hold for all $n$ simultaneously. For any remaining $y$, put
    $$V_n(y)=
    \begin{cases}
    \pi^{-1}(G_n),&y\in G_n,\\
    \SetDifference{X}{\pi^{-1}(G_n)},&y\notin G_n.
    \end{cases}$$
    Each $V_n(y)$ has $\mu_y$-measure $1$, including the second case because the excluded set has measure zero.
    Their countable intersection also has measure $1$. Moreover,
    $$\begin{aligned}
    x\in\bigcap_n V_n(y)
    &\iff \forall n\;(\pi(x)\in G_n\iff y\in G_n)\\
    &\iff \pi(x)=y,
    \end{aligned}$$
    since the family separates points. Hence $\mu_y(\pi^{-1}(\{y\}))=1$ for $\nu$-almost every $y$.
-/
/-- One common null set suffices for all tests in a countable generating
sequence. Their membership pattern determines the observed point. -/
theorem ae_fiber [CountablyGenerated Y] [SeparatesPoints Y] [MeasurableSingletonClass Y]
    (hπ : Measurable π)
    (hid : ∀ A D, MeasurableSet A → MeasurableSet D →
      ∫⁻ y in D, (p y : Measure X) A ∂μ.map π = μ (A ∩ π ⁻¹' D)) :
    ∀ᵐ y ∂μ.map π, (p y : Measure X) (π ⁻¹' {y}) = 1 := by
  classical
  have htests : ∀ᵐ y ∂μ.map π, ∀ n : ℕ,
      (p y : Measure X) (π ⁻¹' natGeneratingSequence Y n) =
        (natGeneratingSequence Y n).indicator (fun _ => (1 : ℝ≥0∞)) y :=
    ae_all_iff.mpr fun n => observed_event μ π p hp hπ hid (measurableSet_natGeneratingSequence n)
  filter_upwards [htests] with y hy
  apply (mem_ae_iff_prob_eq_one (hπ (measurableSet_singleton y))).mp
  have htests' : ∀ᵐ x ∂(p y : Measure X), ∀ n : ℕ,
      π x ∈ natGeneratingSequence Y n ↔ y ∈ natGeneratingSequence Y n := by
    refine ae_all_iff.mpr fun n => ?_
    by_cases hn : y ∈ natGeneratingSequence Y n
    · have hm : (p y : Measure X) (π ⁻¹' natGeneratingSequence Y n) = 1 := by
        simpa [hn] using hy n
      have ha := (mem_ae_iff_prob_eq_one (hπ (measurableSet_natGeneratingSequence n))).mpr hm
      filter_upwards [ha] with x hx using ⟨fun _ => hn, fun _ => hx⟩
    · have hm : (p y : Measure X) (π ⁻¹' natGeneratingSequence Y n) = 0 := by
        simpa [hn] using hy n
      have ha := (measure_eq_zero_iff_ae_notMem).mp hm
      filter_upwards [ha] with x hx using ⟨fun hx' => (hx hx').elim, fun hy' => (hn hy').elim⟩
  filter_upwards [htests'] with x hx
  change π x = y
  apply injective_mapNatBool Y
  funext n
  simp only [mapNatBool, hx n]

omit hp

/-- Finite intersections of a countable generating sequence form a countable
pi-system, with the empty intersection included. -/
def finiteTests [CountablyGenerated X] (F : Finset ℕ) : Set X :=
  ⋂ n ∈ F, natGeneratingSequence X n

lemma finiteTests_measurable [CountablyGenerated X] (F : Finset ℕ) :
    MeasurableSet (finiteTests (X := X) F) :=
  F.measurableSet_biInter fun n _ => measurableSet_natGeneratingSequence n

lemma finiteTests_pi [CountablyGenerated X] : IsPiSystem (range (finiteTests (X := X))) := by
  classical
  rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩ _
  refine ⟨F ∪ G, ?_⟩
  ext x
  simp only [finiteTests, mem_iInter, Finset.mem_union, or_imp, forall_and, mem_inter_iff]

lemma finiteTests_generate [CountablyGenerated X] :
    ‹MeasurableSpace X› = generateFrom (range (finiteTests (X := X))) := by
  classical
  apply le_antisymm
  · calc
      _ = generateFrom (range (natGeneratingSequence X)) := (generateFrom_natGeneratingSequence X).symm
      _ ≤ _ := generateFrom_mono ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨{n}, by simp [finiteTests]⟩
  · apply generateFrom_le
    rintro _ ⟨F, rfl⟩
    exact finiteTests_measurable F

include hp

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Let $(\mu_y)$ and $(\rho_y)$ be two such families. Choose a countable generating family
    $\Sequence{A_n}{n\in\omega}$ for $\mathcal B(X)$. For every finite $F\IncludedIn\omega$, set
    $$A_F=\bigcap_{n\in F}A_n,\qquad A_\emptyset=X.$$
    These sets form a countable $\pi$-system generating $\mathcal B(X)$: intersections correspond to unions of
    finite index sets, and singletons among the index sets recover the original generators.
    For each $F$, the recovered conditional identity shows that
    $$\int_D\mu_y(A_F)\,d\nu(y)=\int_D\rho_y(A_F)\,d\nu(y)$$
    for every Borel $D\IncludedIn Y$. Uniqueness of measurable densities gives
    $\mu_y(A_F)=\rho_y(A_F)$ almost everywhere. There are only countably many finite $F$, so outside one common
    null set the two probability measures agree on the whole generating $\pi$-system. Uniqueness of finite
    measures now gives $\mu_y=\rho_y$ there. Thus the exceptional null set is independent of the Borel set being
    evaluated, as required.
-/
/-- Two probability families with the full conditional integral identity
agree as measures outside one common null set. -/
theorem ae_unique_of_identity [CountablyGenerated X]
    (q : Y → ProbabilityMeasure X) (hq : Measurable q)
    (hidp : ∀ A D, MeasurableSet A → MeasurableSet D →
      ∫⁻ y in D, (p y : Measure X) A ∂μ.map π = μ (A ∩ π ⁻¹' D))
    (hidq : ∀ A D, MeasurableSet A → MeasurableSet D →
      ∫⁻ y in D, (q y : Measure X) A ∂μ.map π = μ (A ∩ π ⁻¹' D)) :
    p =ᵐ[μ.map π] q := by
  have htest (F : Finset ℕ) :
      (fun y => (p y : Measure X) (finiteTests F)) =ᵐ[μ.map π]
        (fun y => (q y : Measure X) (finiteTests F)) := by
    apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (eval_measurable p hp (finiteTests_measurable F))
      (eval_measurable q hq (finiteTests_measurable F))
    intro D hD _
    rw [hidp _ D (finiteTests_measurable F) hD, hidq _ D (finiteTests_measurable F) hD]
  filter_upwards [ae_all_iff.mpr htest] with y hy
  apply Subtype.ext
  change (p y : Measure X) = (q y : Measure X)
  apply ext_of_generate_finite (range (finiteTests (X := X))) finiteTests_generate finiteTests_pi
  · rintro _ ⟨F, rfl⟩
    exact hy F
  · simp

omit hp

/-- On a measure-one fiber, intersecting with an observed event is either
identity or zero, according to whether the observation belongs to that event. -/
lemma fiber_inter [MeasurableSingletonClass Y] (hπ : Measurable π) (y : Y)
    (hy : (p y : Measure X) (π ⁻¹' {y}) = 1) (A : Set X) (D : Set Y) :
    (p y : Measure X) (A ∩ π ⁻¹' D) = D.indicator (fun z => (p z : Measure X) A) y := by
  classical
  have hae := (mem_ae_iff_prob_eq_one (hπ (measurableSet_singleton y))).mpr hy
  by_cases hD : y ∈ D
  · rw [indicator_of_mem hD]
    apply measure_congr
    filter_upwards [hae] with x hx
    have hx' : π x = y := hx
    apply propext
    change (x ∈ A ∧ π x ∈ D) ↔ x ∈ A
    simp [hx', hD]
  · rw [indicator_of_notMem hD]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hae] with x hx
    have hx' : π x = y := hx
    simp [hx', hD]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    For uniqueness, first recover the full conditional identity from the two conditions in the theorem.
    For any probability family satisfying them, its fiber condition implies, outside one null set,
    $$\mu_y(A\cap\pi^{-1}(D))=1_D(y)\mu_y(A)$$
    for Borel $A\IncludedIn X$ and $D\IncludedIn Y$. Indeed, on the fiber over $y$, membership in
    $\pi^{-1}(D)$ is constant and equals membership of $y$ in $D$; the complement of the fiber has measure zero.
    Apply the theorem's integral formula to $A\cap\pi^{-1}(D)$ to obtain
    $$\int_D\mu_y(A)\,d\nu(y)=\mu(A\cap\pi^{-1}(D)).$$
-/
omit [IsProbabilityMeasure μ] in
/-- The theorem's fiber condition and its unconditional integral formula
recover the full conditional integral formula on each observation set. -/
theorem identity_of_fiber [MeasurableSingletonClass Y] (hπ : Measurable π)
    (hfiber : ∀ᵐ y ∂μ.map π, (p y : Measure X) (π ⁻¹' {y}) = 1)
    (hint : ∀ A, MeasurableSet A → ∫⁻ y, (p y : Measure X) A ∂μ.map π = μ A)
    (A : Set X) (D : Set Y) (hA : MeasurableSet A) (hD : MeasurableSet D) :
    ∫⁻ y in D, (p y : Measure X) A ∂μ.map π = μ (A ∩ π ⁻¹' D) := by
  rw [← lintegral_indicator hD]
  calc
    _ = ∫⁻ y, (p y : Measure X) (A ∩ π ⁻¹' D) ∂μ.map π :=
      lintegral_congr_ae (hfiber.mono fun y hy => (fiber_inter π p hπ y hy A D).symm)
    _ = _ := hint _ (hA.inter (hπ hD))

include hp

/-- Uniqueness under exactly the fiber and total-integral requirements of
the disintegration theorem. -/
theorem ae_unique [CountablyGenerated X] [MeasurableSingletonClass Y]
    (hπ : Measurable π) (q : Y → ProbabilityMeasure X) (hq : Measurable q)
    (hpfiber : ∀ᵐ y ∂μ.map π, (p y : Measure X) (π ⁻¹' {y}) = 1)
    (hqfiber : ∀ᵐ y ∂μ.map π, (q y : Measure X) (π ⁻¹' {y}) = 1)
    (hpint : ∀ A, MeasurableSet A → ∫⁻ y, (p y : Measure X) A ∂μ.map π = μ A)
    (hqint : ∀ A, MeasurableSet A → ∫⁻ y, (q y : Measure X) A ∂μ.map π = μ A) :
    p =ᵐ[μ.map π] q :=
  ae_unique_of_identity μ π p hp q hq
    (identity_of_fiber μ π p hπ hpfiber hpint)
    (identity_of_fiber μ π q hπ hqfiber hqint)

omit hp

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Use the classification theorem in §{sec:standard-borel-classification} to realize $X$ as a Borel subset of
    $\CantorSpace$. Let $\mathcal C$ be the countable Boolean algebra of clopen subsets of $\CantorSpace$.
    Since $\mu$ is a probability measure, $X$ is nonempty; fix $x_0\in X$ for the null-set modifications below.
-/
/-- Existence for arbitrary standard Borel spaces, assembled from the
book's Cantor coding, conditional clopen construction, Borel extension,
null-set modifications, and countable fiber tests. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    The most consequential measure-theoretic fact about Polish/standard Borel spaces is that conditional measures can always
    be chosen Borel-measurably:
-/
theorem exists_disintegration [StandardBorelSpace X] [StandardBorelSpace Y]
    (hπ : Measurable π) :
    ∃ p : Y → ProbabilityMeasure X, Measurable p ∧
      (∀ᵐ y ∂μ.map π, (p y : Measure X) (π ⁻¹' {y}) = 1) ∧
      ∀ A : Set X, MeasurableSet A → ∫⁻ y, (p y : Measure X) A ∂μ.map π = μ A := by
  let := upgradeStandardBorel X
  obtain ⟨U, _, hj⟩ := exists_basisCode_measurableEmbedding (X := X)
  let x₀ := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  obtain ⟨p, hp, hid⟩ := ConditionalBorelKernel.exists_original_probability
    μ π (basisCode U) hπ hj x₀
  have hid' A D hA hD := (hid A D hA hD).1
  refine ⟨p, hp, ae_fiber μ π p hp hπ hid', ?_⟩
  intro A hA
  simpa using hid' A univ hA MeasurableSet.univ

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: theorem
  title: Disintegration
-/
/-- The disintegration theorem, including uniqueness modulo one null set. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Here $\mu_y$ is a conditional law of the original point $x \in X$ given the observed value $\pi(x)=y$. The support
    condition says that, for almost every observed $y$, the conditional measure lives on the fiber above $y$; the integral
    formula says that the original measure is recovered by first choosing $y$ according to $\nu$ and then choosing $x$
    according to $\mu_y$.
-/
theorem disintegration [StandardBorelSpace X] [StandardBorelSpace Y]
    (hπ : Measurable π) :
    ∃ p : Y → ProbabilityMeasure X, Measurable p ∧
      (∀ᵐ y ∂μ.map π, (p y : Measure X) (π ⁻¹' {y}) = 1) ∧
      (∀ A : Set X, MeasurableSet A → ∫⁻ y, (p y : Measure X) A ∂μ.map π = μ A) ∧
      ∀ q : Y → ProbabilityMeasure X, Measurable q →
        (∀ᵐ y ∂μ.map π, (q y : Measure X) (π ⁻¹' {y}) = 1) →
        (∀ A : Set X, MeasurableSet A → ∫⁻ y, (q y : Measure X) A ∂μ.map π = μ A) →
        p =ᵐ[μ.map π] q := by
  obtain ⟨p, hp, hfiber, hint⟩ := exists_disintegration μ π hπ
  exact ⟨p, hp, hfiber, hint, fun q hq hqfiber hqint =>
    ae_unique μ π p hp hπ q hq hfiber hqfiber hint hqint⟩

end PolishSpaceBook.DisintegrationFibers
