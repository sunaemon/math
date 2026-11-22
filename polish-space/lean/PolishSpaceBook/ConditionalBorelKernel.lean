module

public import PolishSpaceBook.ConditionalClopenKernel
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Comap

@[expose] public section

/-!
# Extending the conditional integral identity to all Borel sets

For each observation set, integrate the ambient probability family to obtain a
finite measure. Agreement on the clopen algebra then determines that measure
on all Borel sets. The resulting identity forces concentration on any Borel
set containing the original space.
-/

noncomputable section

namespace PolishSpaceBook.ConditionalBorelKernel

open Set MeasureTheory MeasurableSpace Filter Topology TopologicalSpace
open scoped ENNReal NNReal MeasureTheory

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- Integrating a probability family over an observation set gives a finite
measure, including when that observation set has measure zero. -/
lemma integrated_finite (ν : Measure Y) [IsFiniteMeasure ν]
    (p : Y → ProbabilityMeasure Z)
    (hp : ∀ B : Set Z, MeasurableSet B → Measurable (fun y => (p y : Measure Z) B))
    (D : Set Y) : IsFiniteMeasure ((ν.restrict D).bind (fun y => (p y : Measure Z))) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ
    (Measure.measurable_of_measurable_coe _ hp).aemeasurable]
  simp

lemma integrated_real (ν : Measure Y) (p : Y → ProbabilityMeasure Z)
    (hp : ∀ B : Set Z, MeasurableSet B → Measurable (fun y => (p y : Measure Z) B))
    (D : Set Y) {B : Set Z} (hB : MeasurableSet B) :
    ((ν.restrict D).bind (fun y => (p y : Measure Z))).real B =
      ∫ y in D, (p y : Measure Z).real B ∂ν := by
  rw [Measure.real, Measure.bind_apply hB (Measure.measurable_of_measurable_coe _ hp).aemeasurable]
  exact (integral_toReal (hp B hB).aemeasurable
    (Eventually.of_forall fun y => measure_lt_top (p y : Measure Z) B)).symm

variable [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
  [TotallyDisconnectedSpace Z] [SecondCountableTopology Z] [BorelSpace Z]
variable (μ : Measure X) [IsProbabilityMeasure μ] (π : X → Y) (j : X → Z)

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Fix a Borel set $D\IncludedIn Y$. On the ambient Cantor space define
    $$\begin{aligned}
    Q_D(B)&=\int_D\tilde\mu_y(B)\,d\nu(y),\\
    R_D(B)&=\mu(B\cap X\cap\pi^{-1}(D)).
    \end{aligned}$$
    These are finite measures. Countable additivity of $Q_D$ follows from countable additivity of each
    $\tilde\mu_y$ and monotone convergence. The measure $R_D$ is the pushforward, under the inclusion of $X$,
    of the restriction of $\mu$ to $\pi^{-1}(D)$. Both measures have total mass $\nu(D)$, which may be zero.
    The preceding identity gives $Q_D(C)=R_D(C)$ for every $C\in\mathcal C$. Since the clopen algebra is a
    $\pi$-system generating the Borel sets, uniqueness of finite measures gives $Q_D=R_D$. Consequently,
    $$\int_D\tilde\mu_y(B)\,d\nu(y)=\mu(B\cap X\cap\pi^{-1}(D))$$
    for every Borel $B\IncludedIn\CantorSpace$ and every Borel $D\IncludedIn Y$.
-/
/-- Equality on the clopen algebra determines the two finite measures
associated with each fixed observation set. -/
theorem integrated_eq_map (hj : Measurable j)
    (p : Y → ProbabilityMeasure Z)
    (hp : ∀ B : Set Z, MeasurableSet B → Measurable (fun y => (p y : Measure Z) B))
    (hcl : ∀ (C : Clopens Z) (D : Set Y), MeasurableSet D →
      ∫ y in D, (p y : Measure Z).real C ∂μ.map π = μ.real (j ⁻¹' C ∩ π ⁻¹' D))
    {D : Set Y} (hD : MeasurableSet D) :
    ((μ.map π).restrict D).bind (fun y => (p y : Measure Z)) =
      (μ.restrict (π ⁻¹' D)).map j := by
  let := integrated_finite (μ.map π) p hp D
  have heq (C : Set Z) (hC : IsClopen C) :
      (((μ.map π).restrict D).bind (fun y => (p y : Measure Z))) C =
        (μ.restrict (π ⁻¹' D)).map j C := by
    apply ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _) |>.mp
    change (((μ.map π).restrict D).bind (fun y => (p y : Measure Z))).real C =
      ((μ.restrict (π ⁻¹' D)).map j).real C
    rw [integrated_real _ p hp D hC.isOpen.measurableSet]
    have hc : (∫ y in D, (p y : Measure Z).real C ∂μ.map π) =
        μ.real (j ⁻¹' C ∩ π ⁻¹' D) := hcl ⟨C, hC⟩ D hD
    rw [hc]
    simp only [Measure.real, Measure.map_apply hj hC.isOpen.measurableSet,
      Measure.restrict_apply (hj hC.isOpen.measurableSet)]
  apply ext_of_generate_finite {C : Set Z | IsClopen C}
    ClopenMeasureExtension.measurable_eq_generateFrom_clopens
    ClopenMeasureExtension.clopens_isPiSystem heq
  exact heq univ isClopen_univ

/-- The conditional integral formula now holds for every ambient Borel set. -/
theorem borel_lintegral_identity (hj : Measurable j)
    (p : Y → ProbabilityMeasure Z)
    (hp : ∀ B : Set Z, MeasurableSet B → Measurable (fun y => (p y : Measure Z) B))
    (hcl : ∀ (C : Clopens Z) (D : Set Y), MeasurableSet D →
      ∫ y in D, (p y : Measure Z).real C ∂μ.map π = μ.real (j ⁻¹' C ∩ π ⁻¹' D))
    {B : Set Z} (hB : MeasurableSet B) {D : Set Y} (hD : MeasurableSet D) :
    ∫⁻ y in D, (p y : Measure Z) B ∂μ.map π = μ (j ⁻¹' B ∩ π ⁻¹' D) := by
  rw [← Measure.bind_apply hB (Measure.measurable_of_measurable_coe _ hp).aemeasurable,
    integrated_eq_map μ π j hj p hp hcl hD,
    Measure.map_apply hj hB, Measure.restrict_apply (hj hB)]

/-- The real-valued version of the extended identity used in the book. -/
theorem borel_integral_identity (hj : Measurable j)
    (p : Y → ProbabilityMeasure Z)
    (hp : ∀ B : Set Z, MeasurableSet B → Measurable (fun y => (p y : Measure Z) B))
    (hcl : ∀ (C : Clopens Z) (D : Set Y), MeasurableSet D →
      ∫ y in D, (p y : Measure Z).real C ∂μ.map π = μ.real (j ⁻¹' C ∩ π ⁻¹' D))
    {B : Set Z} (hB : MeasurableSet B) {D : Set Y} (hD : MeasurableSet D) :
    ∫ y in D, (p y : Measure Z).real B ∂μ.map π = μ.real (j ⁻¹' B ∩ π ⁻¹' D) := by
  rw [← integrated_real _ p hp D hB, integrated_eq_map μ π j hj p hp hcl hD]
  simp only [Measure.real, Measure.map_apply hj hB, Measure.restrict_apply (hj hB)]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Apply this identity with $B=X^c$ and $D=Y$, where the complement is taken in the ambient Cantor space.
    Since $X^c\cap X=\emptyset$,
    $$\int_Y\tilde\mu_y(X^c)\,d\nu(y)=0.$$
    The integrand is nonnegative and Borel, so $\tilde\mu_y(X^c)=0$ almost everywhere. Equivalently,
    $\tilde\mu_y(X)=1$ almost everywhere. Thus
    $$H_X=\{y\in Y:\tilde\mu_y(X)=1\}$$
    is Borel and has $\nu$-measure $1$.
-/
/-- A Borel set containing the original space has conditional mass one
outside a single measurable null set. -/
theorem ae_concentrated (hj : Measurable j)
    (p : Y → ProbabilityMeasure Z)
    (hp : ∀ B : Set Z, MeasurableSet B → Measurable (fun y => (p y : Measure Z) B))
    (hcl : ∀ (C : Clopens Z) (D : Set Y), MeasurableSet D →
      ∫ y in D, (p y : Measure Z).real C ∂μ.map π = μ.real (j ⁻¹' C ∩ π ⁻¹' D))
    {S : Set Z} (hS : MeasurableSet S) (hjS : ∀ x, j x ∈ S) :
    ∀ᵐ y ∂μ.map π, (p y : Measure Z) S = 1 := by
  have hempty : j ⁻¹' Sᶜ = ∅ := by
    ext x
    simp [hjS x]
  have hz := borel_lintegral_identity μ π j hj p hp hcl hS.compl MeasurableSet.univ
  simp only [hempty, preimage_univ, inter_univ, measure_empty, Measure.restrict_univ] at hz
  have hae := (lintegral_eq_zero_iff (hp Sᶜ hS.compl)).mp hz
  filter_upwards [hae] with y hy
  exact (prob_compl_eq_zero_iff hS).mp hy

/-- Correct the ambient family on the Borel null set where concentration
fails. A single fixed point of the original space supplies the replacement. -/
theorem exists_concentrated_probability (hπ : Measurable π) (hj : Measurable j)
    {S : Set Z} (hS : MeasurableSet S) (hjS : ∀ x, j x ∈ S) (x₀ : X) :
    ∃ q : Y → ProbabilityMeasure Z,
      @Measurable Y (ProbabilityMeasure Z) ‹MeasurableSpace Y› (borel (ProbabilityMeasure Z)) q ∧
      (∀ B : Set Z, MeasurableSet B → Measurable (fun y => (q y : Measure Z) B)) ∧
      (∀ y, (q y : Measure Z) S = 1) ∧
      ∀ (B : Set Z) (D : Set Y), MeasurableSet B → MeasurableSet D →
        ∫⁻ y in D, (q y : Measure Z) B ∂μ.map π = μ (j ⁻¹' B ∩ π ⁻¹' D) := by
  classical
  obtain ⟨p, hp, heval, hcl⟩ :=
    ConditionalClopenKernel.exists_ambient_probability (μ := μ) j hπ hj (j x₀)
  let H : Set Y := {y | (p y : Measure Z) S = 1}
  have hH : MeasurableSet H := measurableSet_eq_fun (heval S hS) measurable_const
  have hHae : ∀ᵐ y ∂μ.map π, y ∈ H := ae_concentrated μ π j hj p heval hcl hS hjS
  let δ : ProbabilityMeasure Z := ⟨Measure.dirac (j x₀), Measure.dirac.isProbabilityMeasure⟩
  let q (y : Y) : ProbabilityMeasure Z := if y ∈ H then p y else δ
  have hq : @Measurable Y (ProbabilityMeasure Z) ‹MeasurableSpace Y›
      (borel (ProbabilityMeasure Z)) q := hp.piecewise hH measurable_const
  have hqe (B : Set Z) (hB : MeasurableSet B) : Measurable (fun y => (q y : Measure Z) B) := by
    have heq : (fun y => (q y : Measure Z) B) =
        H.piecewise (fun y => (p y : Measure Z) B) (fun _ => (δ : Measure Z) B) := by
      funext y
      by_cases hy : y ∈ H <;> simp [q, hy]
    rw [heq]
    exact (heval B hB).piecewise hH measurable_const
  have hqae : q =ᵐ[μ.map π] p := hHae.mono fun y hy => ite_eq_left hy
  refine ⟨q, hq, hqe, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ H
    · rw [show q y = p y from ite_eq_left hy]
      exact hy
    · simp [q, hy, δ, Measure.dirac_apply' _ hS, hjS x₀]
  · intro B D hB hD
    calc
      _ = ∫⁻ y in D, (p y : Measure Z) B ∂μ.map π :=
        lintegral_congr_ae (ae_restrict_of_ae (hqae.mono fun y hy => by rw [hy]))
      _ = _ := borel_lintegral_identity μ π j hj p heval hcl hB hD

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Make a second null-set modification by setting
    $$\lambda_y=
    \begin{cases}
    \tilde\mu_y,&y\in H_X,\\
    \delta_{x_0},&y\notin H_X.
    \end{cases}$$
    This remains a Borel probability family on the ambient space, and now $\lambda_y(X)=1$ for every $y$.
    Every Borel subset $A$ of $X$ is also Borel in the ambient space, since $X$ is Borel. Define
    $$\mu_y(A)=\lambda_y(A).$$
    This gives a probability measure on $X$ for every $y$, and $y\mapsto\mu_y(A)$ is Borel for every such $A$.
    The modification affects only a fixed $\nu$-null set, so for every Borel $A\IncludedIn X$ and
    $D\IncludedIn Y$,
    $$\int_D\mu_y(A)\,d\nu(y)=\mu(A\cap\pi^{-1}(D)).$$
    Taking $D=Y$ gives the integral formula in the theorem.
-/
/-- Pull the everywhere concentrated ambient measures back along the Borel
embedding. The result is a measurable probability family on the original space,
with the full conditional integral identity. Fiber concentration is a separate
step. -/
theorem exists_original_probability (hπ : Measurable π) (hj : MeasurableEmbedding j) (x₀ : X) :
    ∃ r : Y → ProbabilityMeasure X, Measurable r ∧
      ∀ (A : Set X) (D : Set Y), MeasurableSet A → MeasurableSet D →
        (∫⁻ y in D, (r y : Measure X) A ∂μ.map π = μ (A ∩ π ⁻¹' D)) ∧
        (∫ y in D, (r y : Measure X).real A ∂μ.map π = μ.real (A ∩ π ⁻¹' D)) := by
  obtain ⟨q, _, heval, hmass, hid⟩ :=
    exists_concentrated_probability μ π j hπ hj.measurable hj.measurableSet_range
      (fun x => mem_range_self x) x₀
  have hprob y : IsProbabilityMeasure ((q y : Measure Z).comap j) := by
    constructor
    rw [Measure.comap_apply j hj.injective (fun _ hA => hj.measurableSet_image' hA)
      _ MeasurableSet.univ, image_univ]
    exact hmass y
  let r (y : Y) : ProbabilityMeasure X := ⟨(q y : Measure Z).comap j, hprob y⟩
  have hr (A : Set X) (hA : MeasurableSet A) (y : Y) :
      (r y : Measure X) A = (q y : Measure Z) (j '' A) :=
    Measure.comap_apply j hj.injective (fun _ hB => hj.measurableSet_image' hB) _ hA
  have hrm : Measurable (fun y => (r y : Measure X)) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp_rw [hr A hA]
    exact heval (j '' A) (hj.measurableSet_image' hA)
  refine ⟨r, hrm.subtype_mk, ?_⟩
  intro A D hA hD
  have hlin : (∫⁻ y in D, (r y : Measure X) A ∂μ.map π) = μ (A ∩ π ⁻¹' D) := by
    simp_rw [hr A hA]
    simpa only [preimage_image_eq _ hj.injective] using
      hid (j '' A) D (hj.measurableSet_image' hA) hD
  refine ⟨hlin, ?_⟩
  change (∫ y in D, ((r y : Measure X) A).toReal ∂μ.map π) = _
  have he : Measurable (fun y => (r y : Measure X) A) := (Measure.measurable_coe hA).comp hrm
  rw [integral_toReal he.aemeasurable
    (Eventually.of_forall fun y => measure_lt_top (r y : Measure X) A), hlin]
  rfl

end PolishSpaceBook.ConditionalBorelKernel
