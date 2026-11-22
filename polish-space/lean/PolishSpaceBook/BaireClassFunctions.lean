module

public import PolishSpaceBook.BorelStructure
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
# Baire-class functions

Formalization targets for `polish-space/src/polish-space-book/baire-class-functions.md`.

Formalized here: the genetic Baire-class hierarchy, its cumulativity, closure of
a pointwise limit at the successor level, and closure under pre- and
postcomposition by continuous maps, the inverse-image rank bound, and its
Baire-one `Fσ` and Borel-measurability corollary, the closed-set indicator
example with its explicit distance approximants, and the discrete-codomain
counterexample with the real-valued ramp comparison, the exact Baire class
of the Dirichlet function, and the difference-quotient proof for derivatives
with the explicit discontinuous derivative example.

The real-valued
Lebesgue--Hausdorff converse is an external theorem cited in the book and is
explicitly skipped there.
-/

namespace PolishSpaceBook

open Filter
open scoped Ordinal Topology

/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: prose
  excerpt: |
    Let $X$ be a topological space and let $Y$ be a metrizable space. A function $f:X\to Y$ is
    \termdefineas{Baire class 0}{Baire class $0$} if it is continuous. For a nonzero countable ordinal $\alpha$, $f$ is
    \termdefineas{Baire class alpha}{Baire class $\alpha$} if there is a sequence $\Sequence{f_n}{n\in\omega}$ of functions
    $X\to Y$
    of Baire classes
    $<\alpha$ such that
    $$
    f(x)=\lim_{n\to\infty} f_n(x)
    $$
    for every $x\in X$. At a successor stage this says "pointwise limit of functions of the preceding accumulated classes";
    at a limit stage the witness classes need not have a common bound below the limit. Only each individual term must have
    class $<\alpha$.
-/
/-- Membership in the genetic Baire hierarchy. Level zero consists of the
continuous maps. At a positive level `α`, a map is a pointwise limit of a
sequence whose `n`-th term belongs to some level strictly below `α`.

The definition makes sense for every ordinal; the book applies it only at
countable levels below `ω₁`. It also needs only the topology of the codomain,
so this formalization slightly generalizes the book's metrizable-codomain
definition. -/
inductive IsBaireClass {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    Ordinal → (X → Y) → Prop where
  | continuous {f : X → Y} (hf : Continuous f) : IsBaireClass 0 f
  | pointwiseLimit {alpha : Ordinal} (halpha : alpha ≠ 0) {f : X → Y}
      (fseq : ℕ → X → Y) (level : ℕ → Ordinal)
      (hlt : ∀ n, level n < alpha)
      (hclass : ∀ n, IsBaireClass (level n) (fseq n))
      (hlim : ∀ x, Tendsto (fun n ↦ fseq n x) atTop (nhds (f x))) :
      IsBaireClass alpha f

/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: prose
  excerpt: |
    The classes are cumulative. If $\beta<\alpha$ and $f$ belongs to Baire class $\beta$, then the constant sequence
    $f,f,\ldots$ witnesses that $f$ also belongs to Baire class $\alpha$. Thus "Baire class at most $\alpha$" means
    membership in this cumulative class; the exact Baire class, when needed, is the least such ordinal.
-/
/-- The Baire classes are cumulative. In the strict case the constant sequence
with value `f` witnesses membership at the larger level. -/
theorem IsBaireClass.mono {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {alpha beta : Ordinal} {f : X → Y} (hf : IsBaireClass alpha f) (hab : alpha ≤ beta) :
    IsBaireClass beta f := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · exact hf
  · refine .pointwiseLimit ?_ (fun _ ↦ f) (fun _ ↦ alpha) (fun _ ↦ hab) (fun _ ↦ hf) ?_
    · exact (lt_of_le_of_lt bot_le hab).ne'
    · intro x
      exact tendsto_const_nhds

/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: statement
  kind: proposition
  title: Basic closure under pointwise limits
-/
/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: proof
  excerpt: |
    \begin{proof}
    This is built into the definition: every $f_n$ has class $<\alpha+1$, and $f$ is their pointwise limit.
    \end{proof}
-/
/-- A pointwise limit of maps of Baire class at most `α` has Baire class at
most `α + 1`. -/
theorem isBaireClass_pointwiseLimit_succ
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {alpha : Ordinal} {f : X → Y} {fseq : ℕ → X → Y}
    (hclass : ∀ n, IsBaireClass alpha (fseq n))
    (hlim : ∀ x, Tendsto (fun n ↦ fseq n x) atTop (nhds (f x))) :
    IsBaireClass (alpha + 1) f := by
  have hlt : alpha < alpha + 1 := by
    rw [← Order.succ_eq_add_one]
    exact Order.lt_succ alpha
  exact .pointwiseLimit (lt_of_le_of_lt bot_le hlt).ne' fseq (fun _ ↦ alpha)
    (fun _ ↦ hlt) hclass hlim

/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: prose
  excerpt: |
    The same induction on the Baire class also gives the expected closure under composition.
-/
/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: statement
  kind: proposition
  title: Composition with continuous maps
-/
/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] For $\alpha=0$ this is ordinary closure of continuous maps under composition. For $\alpha>0$, write
    $f=\lim_n f_n$ pointwise with $f_n$ of classes $<\alpha$. Then $g\circ f=\lim_n g\circ f_n$ pointwise by continuity of
    $g$, and the induction hypothesis puts each $g\circ f_n$ below $\alpha$. Similarly, $f\circ h=\lim_n f_n\circ h$, and
    each $f_n\circ h$ has class $<\alpha$ by induction.
    \end{proof}
-/
/-- Continuous postcomposition and precomposition preserve every Baire class.
The proof simultaneously follows the two inductions in the book. -/
theorem IsBaireClass.comp_continuous
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {alpha : Ordinal} {f : X → Y} (hf : IsBaireClass alpha f)
    {g : Y → Z} (hg : Continuous g) {h : Z → X} (hh : Continuous h) :
    IsBaireClass alpha (g ∘ f) ∧ IsBaireClass alpha (f ∘ h) := by
  induction hf with
  | continuous hf => exact ⟨.continuous (hg.comp hf), .continuous (hf.comp hh)⟩
  | @pointwiseLimit alpha halpha f fseq level hlt hclass hlim ih =>
      constructor
      · refine .pointwiseLimit halpha (fun n ↦ g ∘ fseq n) level hlt (fun n ↦ (ih n).1) ?_
        intro x
        exact (hg.tendsto (f x)).comp (hlim x)
      · refine .pointwiseLimit halpha (fun n ↦ fseq n ∘ h) level hlt (fun n ↦ (ih n).2) ?_
        intro x
        exact hlim (h x)

/-- The closed inner approximations used in the book, with thresholds `2⁻ⁿ`.
The full open set is handled separately because mathlib assigns distance zero
to the empty set. Every point lies in the interior of some approximation. -/
theorem exists_closed_inner_approximation {Y : Type*} [MetricSpace Y]
    {V : Set Y} (hV : IsOpen V) :
    ∃ F : ℕ → Set Y, (∀ k, IsClosed (F k)) ∧ (∀ k, F k ⊆ V) ∧
      ∀ y ∈ V, ∃ k, F k ∈ nhds y := by
  by_cases hfull : V = Set.univ
  · subst V
    exact ⟨fun _ ↦ Set.univ, fun _ ↦ isClosed_univ, fun _ ↦ Set.Subset.rfl,
      fun _ _ ↦ ⟨0, Filter.univ_mem⟩⟩
  have hne : Vᶜ.Nonempty := Set.nonempty_iff_ne_empty.mpr (by simpa using hfull)
  let F : ℕ → Set Y := fun k ↦ {y | (1 / 2 : ℝ) ^ k ≤ Metric.infDist y Vᶜ}
  refine ⟨F, fun k ↦ isClosed_le continuous_const (Metric.continuous_infDist_pt _), ?_, ?_⟩
  · intro k y hy
    by_contra hout
    have hz := Metric.infDist_zero_of_mem (show y ∈ Vᶜ from hout)
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ k := pow_pos (by norm_num) _
    change (1 / 2 : ℝ) ^ k ≤ Metric.infDist y Vᶜ at hy
    linarith
  · intro y hy
    have hp : 0 < Metric.infDist y Vᶜ :=
      (hV.isClosed_compl.notMem_iff_infDist_pos hne).mp (by simpa using hy)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hp (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨k, Filter.mem_of_superset (x := {z | (1 / 2 : ℝ) ^ k < Metric.infDist z Vᶜ}) ?_
      (fun z hz ↦ by
        change (1 / 2 : ℝ) ^ k ≤ Metric.infDist z Vᶜ
        exact hz.le)⟩
    exact (isOpen_lt continuous_const (Metric.continuous_infDist_pt _)).mem_nhds hk

/-- The eventual-membership formula in the inverse-image proof. Closedness
retains membership at the limit; interior coverage supplies eventual membership. -/
theorem preimage_open_eq_iUnion_iInter {X Y : Type*} [TopologicalSpace Y]
    {f : X → Y} {fseq : ℕ → X → Y} {V : Set Y} {F : ℕ → Set Y}
    (hlim : ∀ x, Tendsto (fun n ↦ fseq n x) atTop (nhds (f x)))
    (hclosed : ∀ k, IsClosed (F k)) (hsub : ∀ k, F k ⊆ V)
    (hcover : ∀ y ∈ V, ∃ k, F k ∈ nhds y) :
    f ⁻¹' V = ⋃ k, ⋃ N : ℕ, ⋂ m : ℕ, fseq (N + m) ⁻¹' F k := by
  ext x
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_iInter]
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := hcover (f x) hx
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((hlim x).eventually hk)
    exact ⟨k, N, fun m ↦ hN (N + m) (Nat.le_add_right _ _)⟩
  · rintro ⟨k, N, hN⟩
    apply hsub k
    apply (hclosed k).mem_of_tendsto (hlim x)
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ by simpa [Nat.add_sub_of_le hn] using hN (n - N)⟩

/-- Countable intersections preserve a multiplicative Borel level, by taking
complements and using countable-union closure at the additive level. -/
theorem borelPi_iInter {X : Type*} [MetricSpace X] {alpha : Ordinal}
    {A : ℕ → Set X} (hA : ∀ n, A n ∈ borelPi alpha) :
    (⋂ n, A n) ∈ borelPi alpha := by
  change (⋂ n, A n)ᶜ ∈ borelSigma alpha
  rw [Set.compl_iInter]
  exact borelSigma_iUnion hA

/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: statement
  kind: theorem
  title: Inverse-image bound
-/
/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] We argue by induction on $\alpha$.

    For $\alpha=0$, the function $f$ is continuous, so $f^{-1}(V)$ is open, hence in $\bSigma^0_1(X)$.

    Assume $\alpha>0$ and the result holds for all smaller classes. Choose functions $f_n:X\to Y$ of classes
    $\alpha_n<\alpha$ with $f_n(x)\to f(x)$ for every $x$. Fix an open set $V\IncludedIn Y$.

    Because $Y$ is metric,
    $$
    V=\bigcup_{k\ge 1} F_k
    $$
    for closed sets $F_k\IncludedIn V$ chosen for instance as
    $$
    F_k=\{y\in Y:d(y,\SetDifference{Y}{V})\ge 2^{-k}\},
    $$
    with the convention that $d(y,\emptyset)=1$. These sets may be empty, but their union is $V$: if $y\in V$, openness
    gives $d(y,\SetDifference{Y}{V})>0$, so $y\in F_k$ for all sufficiently large $k$.

    We claim that
    $$
    f^{-1}(V)
    =
    \bigcup_{k\ge 1}\bigcup_{N\in\omega}\bigcap_{n\ge N} f_n^{-1}(F_k).
    $$
    If $x\in f^{-1}(V)$, choose $k$ so large that $d(f(x),\SetDifference{Y}{V})>2^{-k}$. Then $f(x)$ lies in the interior of
    $F_k$,
    and $f_n(x)\to f(x)$ gives $f_n(x)\in F_k$ for all sufficiently large $n$. This puts $x$ in the right-hand side.
    Conversely, if $x$ belongs to the right-hand side, then for some $k,N$ all $f_n(x)$ with $n\ge N$ lie in the closed set
    $F_k$. Passing to the limit gives $f(x)\in F_k\IncludedIn V$.

    By the induction hypothesis applied to the open complement $\SetDifference{Y}{F_k}$, each
    $$
    f_n^{-1}(\SetDifference{Y}{F_k})
    $$
    lies in $\bSigma^0_{\alpha_n+1}(X)$, with $\alpha_n+1\le\alpha$ because $\alpha_n<\alpha$. Therefore $f_n^{-1}(F_k)$
    lies in $\bPi^0_\alpha(X)$ by the monotonicity proved in §{sec:borel-hierarchy}. Countable intersections of
    $\bPi^0_\alpha$ sets remain in
    $\bPi^0_\alpha$: after taking complements, this is the closure of $\bSigma^0_\alpha$ under countable unions, which
    follows directly from the recursive definition for $\alpha\ge 2$, and is the ordinary closure of open sets under
    countable unions when $\alpha=1$. The displayed formula writes $f^{-1}(V)$ as a countable union of $\bPi^0_\alpha$ sets,
    hence $f^{-1}(V)\in\bSigma^0_{\alpha+1}(X)$.
    \end{proof}
-/
/-- The inverse-image bound follows the book's induction, using closed inner
approximations and the eventual-membership formula. The proof works at every
ordinal for which the genetic hierarchy is defined, hence at countable levels. -/
theorem IsBaireClass.preimage_open {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {alpha : Ordinal} {f : X → Y} (hf : IsBaireClass alpha f)
    {V : Set Y} (hV : IsOpen V) : f ⁻¹' V ∈ borelSigma (alpha + 1) := by
  induction hf generalizing V with
  | continuous hf =>
      simpa [borelSigma_one] using hV.preimage hf
  | @pointwiseLimit alpha halpha f fseq level hlt hclass hlim ih =>
      obtain ⟨F, hclosed, hsub, hcover⟩ := exists_closed_inner_approximation hV
      rw [preimage_open_eq_iUnion_iInter hlim hclosed hsub hcover]
      have hpos : 1 ≤ alpha := Order.one_le_iff_pos.mpr (bot_lt_iff_ne_bot.mpr halpha)
      apply borelSigma_iUnion
      intro k
      apply borelSigma_iUnion
      intro N
      apply borelPi_subset_borelSigma_succ hpos
      apply borelPi_iInter
      intro m
      change (fseq (N + m) ⁻¹' F k)ᶜ ∈ borelSigma alpha
      rw [← Set.preimage_compl]
      have hone : 1 ≤ level (N + m) + 1 := by
        exact le_add_left (le_refl (1 : Ordinal))
      have hlevel : level (N + m) + 1 ≤ alpha := by
        rw [← Order.succ_eq_add_one]
        exact Order.succ_le_of_lt (hlt _)
      exact borelSigma_mono hone hlevel (ih _ (hclosed k).isOpen_compl)

/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: statement
  kind: corollary
  excerpt: |
    If $X$ and $Y$ are metric spaces and $f:X\to Y$ is a pointwise limit of continuous functions, then
    $f^{-1}(V)$ is $\Fsigma$ for every open $V\IncludedIn Y$. In particular, every
    \termuseas{Baire class alpha}{Baire-one} function is \termuseas{Borel-measurable map}{Borel measurable}.
-/
/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Apply the inverse-image bound above with $\alpha=1$. The class $\bSigma^0_2$ is exactly the
    $\Fsigma$ class, and the open-set criterion in §{sec:borel-hierarchy} gives Borel measurability.
    \end{proof}
-/
/-- Specializing the inverse-image bound to Baire class one gives `Fσ`
preimages and Borel measurability, as in the book's corollary. -/
theorem IsBaireClass.one_preimage_isFsigma_and_measurable
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y}
    (hf : IsBaireClass 1 f) :
    (∀ V, IsOpen V → IsFsigma (f ⁻¹' V)) ∧ IsBorelMeasurable f := by
  have hpre : ∀ V, IsOpen V → IsFsigma (f ⁻¹' V) := by
    intro V hV
    simpa [one_add_one_eq_two, borelSigma_two] using hf.preimage_open hV
  refine ⟨hpre, isBorelMeasurable_iff_preimage_open.mpr ?_⟩
  intro V hV
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨S, hS, hclosed, heq⟩ := hpre V hV
  rw [heq]
  exact MeasurableSet.sUnion hS (fun s hs ↦ (hclosed s hs).measurableSet)

/-- The sequence formulation of the preceding corollary. -/
theorem pointwise_limit_continuous_preimage_isFsigma_and_measurable
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {f : X → Y} {fseq : ℕ → X → Y} (hseq : ∀ n, Continuous (fseq n))
    (hlim : ∀ x, Tendsto (fun n ↦ fseq n x) atTop (nhds (f x))) :
    (∀ V, IsOpen V → IsFsigma (f ⁻¹' V)) ∧ IsBorelMeasurable f := by
  have hf : IsBaireClass (1 : Ordinal.{0}) f := by
    simpa using isBaireClass_pointwiseLimit_succ (alpha := 0)
      (fun n ↦ IsBaireClass.continuous (hseq n)) hlim
  exact hf.one_preimage_isFsigma_and_measurable

/-- Level zero is exactly continuity. -/
theorem isBaireClass_zero_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} : IsBaireClass (0 : Ordinal.{0}) f ↔ Continuous f := by
  constructor
  · intro hf
    cases hf with
    | continuous h => exact h
    | pointwiseLimit h _ _ _ _ _ => exact False.elim (h rfl)
  · exact IsBaireClass.continuous

private theorem eventually_one_le_nat_mul {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ ((n : ℝ) + 1) * r := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / r)
  have hNr : 1 < (N : ℝ) * r := (div_lt_iff₀ hr).mp hN
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- The explicit distance approximants from the book converge to the indicator.
The empty set is treated separately, matching the book's distance convention. -/
theorem isBaireClass_one_closed_indicator {X : Type*} [MetricSpace X]
    {F : Set X} (hF : IsClosed F) :
    IsBaireClass (1 : Ordinal.{0}) (F.indicator (fun _ ↦ (1 : ℝ))) := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hne
  · simpa using (IsBaireClass.continuous (continuous_const (y := (0 : ℝ)))).mono
      (show (0 : Ordinal.{0}) ≤ 1 from bot_le)
  let u : ℕ → X → ℝ := fun n x ↦ max 0 (1 - ((n : ℝ) + 1) * Metric.infDist x F)
  have hu : ∀ n, Continuous (u n) := fun n ↦
    continuous_const.max (continuous_const.sub
      (continuous_const.mul (Metric.continuous_infDist_pt F)))
  have hlim : ∀ x, Tendsto (fun n ↦ u n x) atTop (nhds (F.indicator (fun _ ↦ (1 : ℝ)) x)) := by
    intro x
    by_cases hx : x ∈ F
    · simp only [Set.indicator_of_mem hx, u, Metric.infDist_zero_of_mem hx, mul_zero, sub_zero,
        max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]
      exact tendsto_const_nhds
    · rw [Set.indicator_of_notMem hx]
      have hr := (hF.notMem_iff_infDist_pos hne).mp hx
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_one_le_nat_mul hr] with n hn
      dsimp [u]
      exact (max_eq_left (by linarith)).symm
  simpa using isBaireClass_pointwiseLimit_succ (alpha := (0 : Ordinal.{0}))
    (fun n ↦ IsBaireClass.continuous (hu n)) hlim

/-- Small open intervals about one and zero recover the set and its complement. -/
theorem continuous_real_indicator_iff_isClopen {X : Type*} [TopologicalSpace X]
    (F : Set X) : Continuous (F.indicator (fun _ ↦ (1 : ℝ))) ↔ IsClopen F := by
  classical
  constructor
  · intro h
    have h1 : (F.indicator (fun _ ↦ (1 : ℝ))) ⁻¹' Set.Ioi (1 / 2) = F := by
      ext x
      by_cases hx : x ∈ F <;> norm_num [hx]
    have h0 : (F.indicator (fun _ ↦ (1 : ℝ))) ⁻¹' Set.Iio (1 / 2) = Fᶜ := by
      ext x
      by_cases hx : x ∈ F <;> norm_num [hx]
    exact ⟨isOpen_compl_iff.mp (h0 ▸ isOpen_Iio.preimage h), h1 ▸ isOpen_Ioi.preimage h⟩
  · intro h
    exact h.continuous_indicator continuous_const

/-- A closed set that is not open has an indicator of exact Baire class one. -/
theorem closed_indicator_exact_baire_one {X : Type*} [MetricSpace X]
    {F : Set X} (hF : IsClosed F) (hnot : ¬ IsOpen F) :
    IsBaireClass (1 : Ordinal.{0}) (F.indicator (fun _ ↦ (1 : ℝ))) ∧
      ¬ IsBaireClass (0 : Ordinal.{0}) (F.indicator (fun _ ↦ (1 : ℝ))) := by
  refine ⟨isBaireClass_one_closed_indicator hF, ?_⟩
  intro h
  exact hnot ((continuous_real_indicator_iff_isClopen F).mp (isBaireClass_zero_iff.mp h)).isOpen

/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: statement
  kind: example
  title: Indicators of closed sets
-/
/-- The complete closed-indicator example, including its exact class when
`F` is not open. The preceding lemmas retain the explicit approximating sequence. -/
theorem closed_indicator_example {X : Type*} [MetricSpace X]
    {F : Set X} (hF : IsClosed F) :
    IsBaireClass (1 : Ordinal.{0}) (F.indicator (fun _ ↦ (1 : ℝ))) ∧
      (Continuous (F.indicator (fun _ ↦ (1 : ℝ))) ↔ IsClopen F) ∧
      (¬ IsOpen F → ¬ IsBaireClass (0 : Ordinal.{0}) (F.indicator (fun _ ↦ (1 : ℝ)))) :=
  ⟨isBaireClass_one_closed_indicator hF, continuous_real_indicator_iff_isClopen F,
    fun hnot ↦ (closed_indicator_exact_baire_one hF hnot).2⟩

/-- Connectedness and discreteness force continuous maps to be constant;
uniqueness of limits preserves constancy at every genetic Baire level. -/
theorem IsBaireClass.eq_of_preconnected_discrete
    {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y] [T2Space Y]
    {alpha : Ordinal} {f : X → Y} (hf : IsBaireClass alpha f) (x y : X) : f x = f y := by
  induction hf with
  | continuous h =>
      exact ((IsLocallyConstant.iff_continuous _).mpr h).apply_eq_of_preconnectedSpace x y
  | @pointwiseLimit alpha hpos f fseq level hlt hclass hlim ih =>
      apply tendsto_nhds_unique (hlim x)
      convert hlim y using 1
      funext n
      exact ih n

/-- The two-valued step function, with its discrete codomain. -/
noncomputable def discreteStep (x : ℝ) : Bool := if 0 < x then true else false

/-- This discrete-valued step is nonconstant, so it belongs to no genetic
Baire class, in particular not to Baire class one. -/
theorem discreteStep_not_isBaireClass (alpha : Ordinal) : ¬ IsBaireClass alpha discreteStep := by
  intro h
  have heq := h.eq_of_preconnected_discrete 0 1
  norm_num [discreteStep] at heq

/-- All four possible preimages are `Fσ`: the two half-lines, empty, or all of ℝ. -/
theorem discreteStep_preimage_isFsigma (V : Set Bool) : IsFsigma (discreteStep ⁻¹' V) := by
  have hc : ∀ S : Set ℝ, IsClosed S → IsFsigma S := by
    intro S hS
    exact ⟨{S}, Set.countable_singleton _, by simpa, by simp⟩
  have ho : ∀ S : Set ℝ, IsOpen S → IsFsigma S := by
    intro S hS
    have hmem : S ∈ borelSigma (Y := ℝ) (1 : Ordinal.{0}) := by simpa [borelSigma_one] using hS
    have hs2 : S ∈ borelSigma (Y := ℝ) (2 : Ordinal.{0}) := borelSigma_one_subset_two hmem
    simpa [borelSigma_two] using hs2
  by_cases ht : true ∈ V <;> by_cases hf : false ∈ V
  · have heq : discreteStep ⁻¹' V = Set.univ := by
      ext x
      by_cases hx : 0 < x <;> simp [discreteStep, hx, ht, hf]
    rw [heq]; exact hc _ isClosed_univ
  · have heq : discreteStep ⁻¹' V = Set.Ioi 0 := by
      ext x
      by_cases hx : 0 < x <;> simp [discreteStep, hx, ht, hf]
    rw [heq]; exact ho _ isOpen_Ioi
  · have heq : discreteStep ⁻¹' V = Set.Iic 0 := by
      ext x
      by_cases hx : 0 < x <;> simp [discreteStep, hx, ht, hf, le_of_not_gt, not_le.mpr]
    rw [heq]; exact hc _ isClosed_Iic
  · have heq : discreteStep ⁻¹' V = ∅ := by
      ext x
      by_cases hx : 0 < x <;> simp [discreteStep, hx, ht, hf]
    rw [heq]; exact hc _ isClosed_empty

/-- With the real codomain, the book's clipped linear ramps are continuous and
converge pointwise to the same step values. -/
theorem realStep_isBaireClass_one :
    IsBaireClass (1 : Ordinal.{0}) (fun x : ℝ ↦ if 0 < x then (1 : ℝ) else 0) := by
  let g : ℕ → ℝ → ℝ := fun n x ↦ min 1 (max 0 (((n : ℝ) + 1) * x))
  have hg : ∀ n, Continuous (g n) := fun n ↦
    continuous_const.min (continuous_const.max (continuous_const.mul continuous_id))
  have hlim : ∀ x, Tendsto (fun n ↦ g n x) atTop (nhds (if 0 < x then (1 : ℝ) else 0)) := by
    intro x
    by_cases hx : 0 < x
    · simp only [ite_eq_left hx]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_one_le_nat_mul hx] with n hn
      dsimp [g]
      exact (min_eq_left (le_trans hn (le_max_right _ _))).symm
    · simp only [ite_eq_right hx]
      have hg0 : ∀ n, g n x = 0 := by
        intro n
        dsimp [g]
        rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hx))]
        norm_num
      simpa only [hg0] using (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop))
  simpa using isBaireClass_pointwiseLimit_succ (alpha := (0 : Ordinal.{0}))
    (fun n ↦ IsBaireClass.continuous (hg n)) hlim

/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: statement
  kind: example
  title: The converse depends on the codomain
-/
/-- The complete discrete-codomain counterexample, together with the real-valued
comparison. The constancy argument and the clipped approximants follow the book. -/
theorem discrete_codomain_counterexample :
    (∀ V : Set Bool, IsFsigma (discreteStep ⁻¹' V)) ∧
      ¬ IsBaireClass (1 : Ordinal.{0}) discreteStep ∧
      IsBaireClass (1 : Ordinal.{0}) (fun x : ℝ ↦ if 0 < x then (1 : ℝ) else 0) :=
  ⟨discreteStep_preimage_isFsigma, discreteStep_not_isBaireClass 1, realStep_isBaireClass_one⟩

/-- Enumerate a countable set and approximate its indicator by the indicators
of the finite initial segments, exactly as in the Dirichlet example. -/
theorem isBaireClass_two_countable_indicator {X : Type*} [MetricSpace X]
    {S : Set X} (hS : S.Countable) :
    IsBaireClass (2 : Ordinal.{0}) (S.indicator (fun _ ↦ (1 : ℝ))) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa using (IsBaireClass.continuous (continuous_const (y := (0 : ℝ)))).mono
      (show (0 : Ordinal.{0}) ≤ 2 from bot_le)
  obtain ⟨q, rfl⟩ := hS.exists_eq_range hne
  let F : ℕ → Set X := fun n ↦ q '' Set.Iic n
  have hF : ∀ n, IsClosed (F n) := fun n ↦ ((Set.finite_Iic n).image q).isClosed
  have hlim : ∀ x, Tendsto (fun n ↦ (F n).indicator (fun _ ↦ (1 : ℝ)) x)
      atTop (nhds ((Set.range q).indicator (fun _ ↦ (1 : ℝ)) x)) := by
    intro x
    by_cases hx : x ∈ Set.range q
    · rw [Set.indicator_of_mem hx]
      obtain ⟨N, rfl⟩ := hx
      apply tendsto_const_nhds.congr'
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
      exact (Set.indicator_of_mem (show q N ∈ F n from ⟨N, hn, rfl⟩) (fun _ : X ↦ (1 : ℝ))).symm
    · rw [Set.indicator_of_notMem hx]
      have hnot : ∀ n, x ∉ F n := by
        rintro n ⟨m, _, hm⟩
        exact hx ⟨m, hm⟩
      simp only [Set.indicator_of_notMem (hnot _)]
      exact tendsto_const_nhds
  simpa only [one_add_one_eq_two] using isBaireClass_pointwiseLimit_succ
    (fun n ↦ isBaireClass_one_closed_indicator (hF n)) hlim

/-- The real-valued indicator of the rationals. -/
noncomputable def dirichlet : ℝ → ℝ := (Set.range ((↑) : ℚ → ℝ)).indicator (fun _ ↦ 1)

/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: statement
  kind: example
  title: Dirichlet function
-/
/-- Finite rational initial segments give the upper bound. The inverse image
of `(-1/2, 1/2)` is the irrationals, which are not `Fσ`, giving the lower bound. -/
theorem dirichlet_exact_baire_two :
    IsBaireClass (2 : Ordinal.{0}) dirichlet ∧ ¬ IsBaireClass (1 : Ordinal.{0}) dirichlet := by
  classical
  refine ⟨isBaireClass_two_countable_indicator (Set.countable_range _), ?_⟩
  intro h
  have hpre := h.one_preimage_isFsigma_and_measurable.1 (Set.Ioo (-1 / 2) (1 / 2)) isOpen_Ioo
  have heq : dirichlet ⁻¹' Set.Ioo (-1 / 2) (1 / 2) = {x : ℝ | Irrational x} := by
    ext x
    by_cases hx : x ∈ Set.range ((↑) : ℚ → ℝ)
    · have hi : ¬ Irrational x := by simpa [Irrational, Set.mem_range] using hx
      norm_num [dirichlet, hx, hi]
    · have hi : Irrational x := by simpa [Irrational, Set.mem_range] using hx
      norm_num [dirichlet, hx, hi]
  exact irrationals_not_fsigma (heq ▸ hpre)


/-- Difference quotients with increments `1/(n+1)` give the book's pointwise
continuous approximation to a derivative. -/
theorem derivative_isBaireClass_one {u : ℝ → ℝ} (hu : Differentiable ℝ u) :
    IsBaireClass (1 : Ordinal.{0}) (deriv u) := by
  let h : ℕ → ℝ → ℝ := fun n x ↦ ((n : ℝ) + 1) * (u (x + 1 / ((n : ℝ) + 1)) - u x)
  have hc : ∀ n, Continuous (h n) := fun n ↦ continuous_const.mul
    ((hu.continuous.comp (continuous_id.add continuous_const)).sub hu.continuous)
  have hi : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhdsWithin 0 {0}ᶜ) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall (fun n ↦ by simp; positivity)⟩
  have hl : ∀ x, Tendsto (fun n ↦ h n x) atTop (nhds (deriv u x)) := by
    intro x
    simpa [h, smul_eq_mul, Function.comp_def] using
      ((hu x).hasDerivAt.tendsto_slope_zero.comp hi)
  simpa using isBaireClass_pointwiseLimit_succ (alpha := (0 : Ordinal.{0}))
    (fun n ↦ IsBaireClass.continuous (hc n)) hl

/-- The book's oscillating primitive; at zero the formula itself has value zero. -/
noncomputable def oscillatingPrimitive (x : ℝ) : ℝ := x ^ 2 * Real.sin x⁻¹

/-- The derivative is zero at zero and has the usual product-rule formula elsewhere. -/
noncomputable def oscillatingDerivative (x : ℝ) : ℝ :=
  if x = 0 then 0 else 2 * x * Real.sin x⁻¹ - Real.cos x⁻¹

theorem oscillatingPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt oscillatingPrimitive (oscillatingDerivative x) x := by
  by_cases hx : x = 0
  · subst x
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hlim : Tendsto (fun t : ℝ ↦ t * Real.sin t⁻¹) (nhds 0) (nhds 0) := by
      apply squeeze_zero_norm (fun t ↦ ?_) (show Tendsto (fun t : ℝ ↦ |t|) (nhds 0) (nhds 0) from
        by simpa using continuous_abs.tendsto (0 : ℝ))
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg t) (Real.abs_sin_le_one _)
    have heq : (fun t : ℝ ↦ t⁻¹ • (oscillatingPrimitive (0 + t) - oscillatingPrimitive 0)) =
        (fun t : ℝ ↦ t * Real.sin t⁻¹) := by
      funext t
      by_cases ht : t = 0
      · simp [ht, oscillatingPrimitive]
      · dsimp [oscillatingPrimitive]
        simp only [zero_add, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero]
        field_simp
    rw [heq]
    simpa [oscillatingDerivative] using hlim.mono_left nhdsWithin_le_nhds
  · have h := ((hasDerivAt_id x).pow 2).mul (((hasDerivAt_id x).inv hx).sin)
    apply h.congr_deriv
    simp [oscillatingDerivative, hx, pow_two]
    field_simp
    ring

theorem oscillatingPrimitive_differentiable : Differentiable ℝ oscillatingPrimitive :=
  fun x ↦ (oscillatingPrimitive_hasDerivAt x).differentiableAt

theorem deriv_oscillatingPrimitive : deriv oscillatingPrimitive = oscillatingDerivative := by
  funext x
  exact (oscillatingPrimitive_hasDerivAt x).deriv

/-- Along `1/((n+1)2π)` the derivative is constantly `-1`, although its value
at zero is zero. This makes the discontinuity in the book explicit. -/
theorem oscillatingDerivative_not_continuousAt_zero : ¬ ContinuousAt oscillatingDerivative 0 := by
  intro hc
  let x : ℕ → ℝ := fun n ↦ 1 / (((n : ℝ) + 1) * (2 * Real.pi))
  have hx : Tendsto x atTop (nhds 0) := by
    simpa only [x, div_div, zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const (2 * Real.pi)
  have hv : ∀ n, oscillatingDerivative (x n) = -1 := by
    intro n
    have hn : x n ≠ 0 := by dsimp [x]; positivity
    rw [oscillatingDerivative, ite_eq_right hn]
    simp only [x, one_div, inv_inv]
    rw [show ((n : ℝ) + 1) * (2 * Real.pi) = (↑(n + 1) : ℝ) * (2 * Real.pi) by norm_cast]
    have hs : Real.sin ((↑(n + 1) : ℝ) * (2 * Real.pi)) = 0 := by
      convert Real.sin_nat_mul_pi ((n + 1) * 2) using 1
      congr 1
      push_cast
      ring
    rw [hs, Real.cos_nat_mul_two_pi]
    ring
  have ht := hc.tendsto.comp hx
  change Tendsto (fun n ↦ oscillatingDerivative (x n)) atTop (nhds (oscillatingDerivative 0)) at ht
  simp only [hv] at ht
  norm_num [oscillatingDerivative] at ht

/-@ booklink:
  source: polish-space-book/baire-class-functions.md
  target: statement
  kind: example
  title: Derivatives are Baire one
-/
/-- Both parts of the derivative example: every derivative is Baire one, and
the explicit oscillating primitive has a discontinuous derivative of exact class one. -/
theorem derivative_baire_one_example :
    (∀ u : ℝ → ℝ, Differentiable ℝ u → IsBaireClass (1 : Ordinal.{0}) (deriv u)) ∧
      Differentiable ℝ oscillatingPrimitive ∧
      deriv oscillatingPrimitive = oscillatingDerivative ∧
      IsBaireClass (1 : Ordinal.{0}) oscillatingDerivative ∧
      ¬ ContinuousAt oscillatingDerivative 0 ∧
      ¬ IsBaireClass (0 : Ordinal.{0}) oscillatingDerivative := by
  have hb : IsBaireClass (1 : Ordinal.{0}) oscillatingDerivative := by
    rw [← deriv_oscillatingPrimitive]
    exact derivative_isBaireClass_one oscillatingPrimitive_differentiable
  refine ⟨fun u hu ↦ derivative_isBaireClass_one hu, oscillatingPrimitive_differentiable,
    deriv_oscillatingPrimitive, hb, oscillatingDerivative_not_continuousAt_zero, ?_⟩
  intro h
  exact oscillatingDerivative_not_continuousAt_zero (isBaireClass_zero_iff.mp h).continuousAt

end PolishSpaceBook
