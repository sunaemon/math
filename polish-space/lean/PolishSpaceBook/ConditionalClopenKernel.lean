module

public import PolishSpaceBook.ClopenMeasureExtension
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Scalar conditional probabilities and simultaneous clopen normalization

The disintegration construction first factors scalar conditional expectations
through the observation map. Countably many identities are then made pointwise
on one common conull set, with a fixed point mass on its complement.
-/

noncomputable section

namespace PolishSpaceBook.ConditionalClopenKernel

open Set MeasureTheory MeasurableSpace Filter Topology TopologicalSpace
open scoped ENNReal NNReal MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (π : X → Y)

/-- A real-valued measurable representative on the observation space. -/
def scalar (A : Set X) : Y → ℝ :=
  Classical.choose (stronglyMeasurable_condExp
    (μ := μ) (m := ‹MeasurableSpace Y›.comap π)
    (f := A.indicator (fun _ => (1 : ℝ)))).exists_eq_measurable_comp

lemma scalar_stronglyMeasurable (A : Set X) : StronglyMeasurable (scalar μ π A) := by
  unfold scalar
  exact (Classical.choose_spec (stronglyMeasurable_condExp
    (μ := μ) (m := ‹MeasurableSpace Y›.comap π)
    (f := A.indicator (fun _ => (1 : ℝ)))).exists_eq_measurable_comp).1

lemma scalar_comp (A : Set X) :
    μ[A.indicator (fun _ => (1 : ℝ)) | ‹MeasurableSpace Y›.comap π] = scalar μ π A ∘ π :=
  (Classical.choose_spec (stronglyMeasurable_condExp
    (μ := μ) (m := ‹MeasurableSpace Y›.comap π)
    (f := A.indicator (fun _ => (1 : ℝ)))).exists_eq_measurable_comp).2

lemma scalar_measurable (A : Set X) : Measurable (scalar μ π A) :=
  (scalar_stronglyMeasurable μ π A).measurable

variable {μ π} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma scalar_integrable (hπ : Measurable π) (A : Set X) :
    Integrable (scalar μ π A) (μ.map π) := by
  apply (integrable_map_measure (scalar_stronglyMeasurable μ π A).aestronglyMeasurable
    hπ.aemeasurable).mpr
  rw [← scalar_comp]
  exact integrable_condExp

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    For each $C\in\mathcal C$, choose a $\pi^{-1}\mathcal B(Y)$-measurable representative of the
    conditional expectation of $1_{C\cap X}$. Measurable factorization through $\pi$ gives a Borel function
    $g_C:Y\to\mathbb R$ satisfying
    $$g_C(\pi(x))=\mathbb E_\mu(1_{C\cap X}\mid\pi^{-1}\mathcal B(Y))(x).$$
    This representative is integrable with respect to $\nu$. For every Borel $D\IncludedIn Y$, the change-of-variables
    formula and the defining property of conditional expectation give
    $$\begin{aligned}
    \int_D g_C\,d\nu
    &=\int_{\pi^{-1}(D)}g_C\circ\pi\,d\mu\\
    &=\int_{\pi^{-1}(D)}1_{C\cap X}\,d\mu\\
    &=\mu(C\cap X\cap\pi^{-1}(D)).
    \end{aligned}$$
-/
/-- The defining conditional-expectation identity descends to every measurable
set in the observation space. -/
theorem scalar_setIntegral (hπ : Measurable π) {A : Set X} (hA : MeasurableSet A)
    {D : Set Y} (hD : MeasurableSet D) :
    ∫ y in D, scalar μ π A y ∂μ.map π = μ.real (A ∩ π ⁻¹' D) := by
  rw [setIntegral_map hD (scalar_stronglyMeasurable μ π A).aestronglyMeasurable
    hπ.aemeasurable]
  change (∫ x in π ⁻¹' D, (scalar μ π A ∘ π) x ∂μ) = _
  rw [← scalar_comp, setIntegral_condExp hπ.comap_le
    ((integrable_const (1 : ℝ)).indicator hA) (show MeasurableSet[‹MeasurableSpace Y›.comap π]
      (π ⁻¹' D) from ⟨D, hD, rfl⟩), setIntegral_indicator hA]
  simp [inter_comm]

lemma scalar_bounds (hπ : Measurable π) {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ y ∂μ.map π, 0 ≤ scalar μ π A y ∧ scalar μ π A y ≤ 1 := by
  apply (ae_map_iff hπ.aemeasurable
    ((measurableSet_le measurable_const (scalar_measurable μ π A)).inter
      (measurableSet_le (scalar_measurable μ π A) measurable_const))).mpr
  have hn : ∀ᵐ x ∂μ, 0 ≤ μ[A.indicator (fun _ => (1 : ℝ)) |
      ‹MeasurableSpace Y›.comap π] x :=
    condExp_nonneg (Eventually.of_forall fun x => by classical
      by_cases hx : x ∈ A <;> simp [hx])
  have hu := condExp_mono (μ := μ) (m := ‹MeasurableSpace Y›.comap π)
    ((integrable_const (1 : ℝ)).indicator hA) (integrable_const (1 : ℝ))
    (Eventually.of_forall (show ∀ x, A.indicator (fun _ => (1 : ℝ)) x ≤ 1 from
      fun x => by classical
        by_cases hx : x ∈ A <;> simp [hx]))
  rw [condExp_const hπ.comap_le] at hu
  filter_upwards [hn, hu] with x hx hx'
  constructor
  · change 0 ≤ scalar μ π A (π x)
    simpa only [scalar_comp, Function.comp_apply] using hx
  · change scalar μ π A (π x) ≤ 1
    simpa only [scalar_comp, Function.comp_apply] using hx'

lemma scalar_empty (hπ : Measurable π) : scalar μ π ∅ =ᵐ[μ.map π] 0 := by
  apply (ae_map_iff hπ.aemeasurable
    (measurableSet_eq_fun (scalar_measurable μ π ∅) measurable_const)).mpr
  have h := scalar_comp μ π ∅
  simp only [indicator_empty, condExp_const hπ.comap_le] at h
  exact Eventually.of_forall fun x => (congrFun h x).symm

lemma scalar_univ (hπ : Measurable π) : scalar μ π univ =ᵐ[μ.map π] 1 := by
  apply (ae_map_iff hπ.aemeasurable
    (measurableSet_eq_fun (scalar_measurable μ π univ) measurable_const)).mpr
  have h := scalar_comp μ π univ
  simp only [indicator_univ, condExp_const hπ.comap_le] at h
  exact Eventually.of_forall fun x => (congrFun h x).symm

lemma scalar_union (hπ : Measurable π) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    scalar μ π (A ∪ B) =ᵐ[μ.map π] scalar μ π A + scalar μ π B := by
  apply (ae_map_iff hπ.aemeasurable
    (measurableSet_eq_fun (scalar_measurable μ π (A ∪ B))
      ((scalar_measurable μ π A).add (scalar_measurable μ π B)))).mpr
  have h := condExp_add (μ := μ) ((integrable_const (1 : ℝ)).indicator hA)
    ((integrable_const (1 : ℝ)).indicator hB) (‹MeasurableSpace Y›.comap π)
  have hi : A.indicator (fun _ => (1 : ℝ)) + B.indicator (fun _ => (1 : ℝ)) =
      (A ∪ B).indicator (fun _ => (1 : ℝ)) :=
    by
      funext x
      exact congrFun (indicator_union_of_disjoint hAB (fun _ => (1 : ℝ))).symm x
  rw [hi] at h
  filter_upwards [h] with x hx
  simpa only [scalar_comp, Function.comp_apply, Pi.add_apply] using hx

section Clopens

variable {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
  [TotallyDisconnectedSpace Z] [SecondCountableTopology Z]
  [MeasurableSpace Z] [BorelSpace Z]
variable (j : X → Z)

/-- All scalar probability identities on the countable ambient clopen algebra. -/
def good : Set Y := {y |
  (∀ C : Clopens Z, 0 ≤ scalar μ π (j ⁻¹' C) y ∧ scalar μ π (j ⁻¹' C) y ≤ 1) ∧
  scalar μ π ∅ y = 0 ∧ scalar μ π univ y = 1 ∧
  ∀ C D : Clopens Z, Disjoint (C : Set Z) D →
    scalar μ π (j ⁻¹' (C ⊔ D : Clopens Z)) y =
      scalar μ π (j ⁻¹' C) y + scalar μ π (j ⁻¹' D) y}

omit [IsProbabilityMeasure μ] [MeasurableSpace Z] [BorelSpace Z] in
lemma good_measurable : MeasurableSet (good (μ := μ) (π := π) j) := by
  let : Countable (Clopens Z) := Clopens.countable_iff_secondCountable.mpr inferInstance
  unfold good
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
  · change MeasurableSet {y | ∀ C : Clopens Z,
      0 ≤ scalar μ π (j ⁻¹' C) y ∧ scalar μ π (j ⁻¹' C) y ≤ 1}
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun C =>
      (measurableSet_le measurable_const (scalar_measurable μ π _)).inter
        (measurableSet_le (scalar_measurable μ π _) measurable_const)
  · exact measurableSet_eq_fun (scalar_measurable μ π _) measurable_const
  · exact measurableSet_eq_fun (scalar_measurable μ π _) measurable_const
  · change MeasurableSet {y | ∀ C D : Clopens Z, Disjoint (C : Set Z) D →
        scalar μ π (j ⁻¹' (C ⊔ D : Clopens Z)) y =
          scalar μ π (j ⁻¹' C) y + scalar μ π (j ⁻¹' D) y}
    simp only [ofPred_forall]
    refine MeasurableSet.iInter fun C => MeasurableSet.iInter fun D => ?_
    by_cases h : Disjoint (C : Set Z) D
    · simp only [h, iInter_true]
      exact measurableSet_eq_fun (scalar_measurable μ π _)
        ((scalar_measurable μ π _).add (scalar_measurable μ π _))
    · simp [h]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Positivity, preservation of constants, and additivity of conditional expectation imply, separately for each
    clopen or disjoint pair of clopens,
    $$\begin{gathered}
    0\le g_C(y)\le1,\qquad g_\emptyset(y)=0,\qquad g_\CantorSpace(y)=1,\\
    g_{C\internalDisjointUnion E}(y)=g_C(y)+g_E(y).
    \end{gathered}$$
    Each assertion holds for $\nu$-almost every $y$: its pullback holds $\mu$-almost everywhere, and
    $\nu=\pi_*\mu$. Let $H\IncludedIn Y$ be the set where all these assertions hold simultaneously, for all
    $C\in\mathcal C$ and all disjoint $C,E\in\mathcal C$. Each equality or inequality defines a Borel set.
    Since $\mathcal C$ and $\mathcal C\times\mathcal C$ are countable, $H$ is Borel and $\nu(H)=1$.
-/
lemma ae_good (hπ : Measurable π) (hj : Measurable j) :
    ∀ᵐ y ∂μ.map π, y ∈ good (μ := μ) (π := π) j := by
  let : Countable (Clopens Z) := Clopens.countable_iff_secondCountable.mpr inferInstance
  have hb : ∀ᵐ y ∂μ.map π, ∀ C : Clopens Z,
      0 ≤ scalar μ π (j ⁻¹' C) y ∧ scalar μ π (j ⁻¹' C) y ≤ 1 :=
    ae_all_iff.mpr fun C => scalar_bounds hπ (hj C.isClopen.isOpen.measurableSet)
  have ha : ∀ᵐ y ∂μ.map π, ∀ C D : Clopens Z, Disjoint (C : Set Z) D →
      scalar μ π (j ⁻¹' (C ⊔ D : Clopens Z)) y =
        scalar μ π (j ⁻¹' C) y + scalar μ π (j ⁻¹' D) y := by
    refine ae_all_iff.mpr fun C => ae_all_iff.mpr fun D => ?_
    by_cases h : Disjoint (C : Set Z) D
    · have hu := scalar_union (μ := μ) hπ (hj C.isClopen.isOpen.measurableSet)
        (hj D.isClopen.isOpen.measurableSet) (h.preimage j)
      filter_upwards [hu] with y hy using fun _ => hy
    · exact Eventually.of_forall fun _ hh => (h hh).elim
  filter_upwards [hb, scalar_empty hπ, scalar_univ hπ, ha] with y hb h0 h1 ha
  exact ⟨hb, h0, h1, ha⟩

open scoped Classical in
/-- On the common exceptional set use the same point mass for every clopen. -/
def normalized (z₀ : Z) (C : Clopens Z) (y : Y) : ℝ :=
  if y ∈ good (μ := μ) (π := π) j then scalar μ π (j ⁻¹' C) y
  else (C : Set Z).indicator (fun _ => (1 : ℝ)) z₀

omit [IsProbabilityMeasure μ] [MeasurableSpace Z] [BorelSpace Z] in
lemma normalized_measurable (z₀ : Z) (C : Clopens Z) :
    Measurable (normalized (μ := μ) (π := π) j z₀ C) :=
  (scalar_measurable μ π _).piecewise (good_measurable j) measurable_const

lemma normalized_ae (hπ : Measurable π) (hj : Measurable j) (z₀ : Z) (C : Clopens Z) :
    normalized (μ := μ) (π := π) j z₀ C =ᵐ[μ.map π] scalar μ π (j ⁻¹' C) := by
  filter_upwards [ae_good j hπ hj] with y hy
  simp [normalized, hy]

omit [IsProbabilityMeasure μ] [CompactSpace Z] [T2Space Z]
  [TotallyDisconnectedSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z] in
lemma normalized_bounds (z₀ : Z) (C : Clopens Z) (y : Y) :
    0 ≤ normalized (μ := μ) (π := π) j z₀ C y ∧
      normalized (μ := μ) (π := π) j z₀ C y ≤ 1 := by
  classical
  by_cases hy : y ∈ good (μ := μ) (π := π) j
  · simpa only [normalized, ite_eq_left hy] using hy.1 C
  · by_cases hz : z₀ ∈ C <;> simp [normalized, hy, hz]

omit [IsProbabilityMeasure μ] [CompactSpace Z] [T2Space Z]
  [TotallyDisconnectedSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z] in
lemma normalized_empty (z₀ : Z) (y : Y) :
    normalized (μ := μ) (π := π) j z₀ ⊥ y = 0 := by
  classical
  by_cases hy : y ∈ good (μ := μ) (π := π) j
  · simpa [normalized, hy] using hy.2.1
  · simp [normalized, hy]

omit [IsProbabilityMeasure μ] [CompactSpace Z] [T2Space Z]
  [TotallyDisconnectedSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z] in
lemma normalized_univ (z₀ : Z) (y : Y) :
    normalized (μ := μ) (π := π) j z₀ ⊤ y = 1 := by
  classical
  by_cases hy : y ∈ good (μ := μ) (π := π) j
  · simpa [normalized, hy] using hy.2.2.1
  · simp [normalized, hy]

omit [IsProbabilityMeasure μ] [CompactSpace Z] [T2Space Z]
  [TotallyDisconnectedSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z] in
lemma normalized_union (z₀ : Z) (C D : Clopens Z) (h : Disjoint (C : Set Z) D) (y : Y) :
    normalized (μ := μ) (π := π) j z₀ (C ⊔ D) y =
      normalized (μ := μ) (π := π) j z₀ C y + normalized (μ := μ) (π := π) j z₀ D y := by
  classical
  by_cases hy : y ∈ good (μ := μ) (π := π) j
  · simpa only [normalized, ite_eq_left hy] using hy.2.2.2 C D h
  · simp only [normalized, ite_eq_right hy]
    exact congrFun (indicator_union_of_disjoint h (fun _ => (1 : ℝ))) z₀

/-- Null-set normalization preserves the scalar integral identity. -/
theorem normalized_setIntegral (hπ : Measurable π) (hj : Measurable j)
    (z₀ : Z) (C : Clopens Z) {D : Set Y} (hD : MeasurableSet D) :
    ∫ y in D, normalized (μ := μ) (π := π) j z₀ C y ∂μ.map π =
      μ.real (j ⁻¹' C ∩ π ⁻¹' D) := by
  calc
    _ = ∫ y in D, scalar μ π (j ⁻¹' C) y ∂μ.map π :=
      setIntegral_congr_ae hD ((normalized_ae j hπ hj z₀ C).mono fun _ hy _ => hy)
    _ = _ := scalar_setIntegral hπ (hj C.isClopen.isOpen.measurableSet) hD

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    Define the corrected functions by
    $$\widehat g_C(y)=
    \begin{cases}
    g_C(y),&y\in H,\\
    1_C(x_0),&y\notin H.
    \end{cases}$$
    They are Borel. On $H$ the probability identities already hold; outside $H$ they are the identities for the
    point mass at $x_0$. Thus $C\mapsto\widehat g_C(y)$ is a finitely additive probability on $\mathcal C$ for
    every $y$. Also $\widehat g_C=g_C$ almost everywhere, so every integral over $D$ above is unchanged.
    By \termuse{clopen probability extension}, there is a unique probability measure $\tilde\mu_y$ on
    $\CantorSpace$ satisfying $\tilde\mu_y(C)=\widehat g_C(y)$ for all $C\in\mathcal C$.
    The map $y\mapsto\tilde\mu_y$ is Borel into $\ProbMeasures{\CantorSpace}$, and every Borel evaluation is Borel.
    In particular, this Markov kernel satisfies
    $$\int_D\tilde\mu_y(C)\,d\nu(y)=\mu(C\cap X\cap\pi^{-1}(D))$$
    for every $C\in\mathcal C$ and every Borel $D\IncludedIn Y$.
-/
/-- The simultaneous normalization supplies a Borel probability family on the
ambient compact space. Its clopen evaluations still represent the original
conditional expectations. -/
theorem exists_ambient_probability (hπ : Measurable π) (hj : Measurable j) (z₀ : Z) :
    ∃ p : Y → ProbabilityMeasure Z,
      @Measurable Y (ProbabilityMeasure Z) ‹MeasurableSpace Y› (borel (ProbabilityMeasure Z)) p ∧
      (∀ B : Set Z, MeasurableSet B → Measurable (fun y => (p y : Measure Z) B)) ∧
      ∀ (C : Clopens Z) (D : Set Y), MeasurableSet D →
        ∫ y in D, (p y : Measure Z).real C ∂μ.map π = μ.real (j ⁻¹' C ∩ π ⁻¹' D) := by
  let v y C := ENNReal.ofReal (normalized (μ := μ) (π := π) j z₀ C y)
  have h0 y : v y ⊥ = 0 := by simp [v, normalized_empty]
  have h1 y : v y ⊤ = 1 := by simp [v, normalized_univ]
  have hadd y (C E : Clopens Z) (h : Disjoint (C : Set Z) E) :
      v y (C ⊔ E) = v y C + v y E := by
    dsimp [v]
    rw [normalized_union j z₀ C E h y, ENNReal.ofReal_add
      (normalized_bounds j z₀ C y).1 (normalized_bounds j z₀ E y).1]
  have hv C : Measurable (fun y => v y C) := (normalized_measurable j z₀ C).ennreal_ofReal
  obtain ⟨p, ⟨hp, heval⟩, _⟩ :=
    ClopenMeasureExtension.existsUnique_probabilityFamily v h0 h1 hadd hv
  have hcl (C : Set Z) (hC : IsClopen C) : Measurable (fun y => (p y : Measure Z) C) := by
    change Measurable (fun y => (p y : Measure Z) (⟨C, hC⟩ : Clopens Z))
    simp_rw [heval]
    exact hv ⟨C, hC⟩
  refine ⟨p, hp, ClopenMeasureExtension.measurable_evaluation_of_clopens
    (fun y => (p y : Measure Z)) (fun y => (p y).prop) hcl, ?_⟩
  intro C D hD
  have hr y : (p y : Measure Z).real C = normalized (μ := μ) (π := π) j z₀ C y := by
    rw [Measure.real, heval]
    exact ENNReal.toReal_ofReal (normalized_bounds j z₀ C y).1
  simp_rw [hr]
  exact normalized_setIntegral j hπ hj z₀ C hD

end Clopens

end PolishSpaceBook.ConditionalClopenKernel
