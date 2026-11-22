module

public import PolishSpaceBook.BorelMeasureRegularity
public import PolishSpaceBook.PolishEmbeddingsBorelRefinements
public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.MeasureTheory.Constructions.UnitInterval

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Lusin continuity from a Polish refinement

First refine the domain topology to make the Borel map continuous. Ulam's
explicit compact approximation in that topology produces a large compact set.
On this set the identity from the finer topology to the original Hausdorff
topology is a homeomorphism. The category analogue instead opens the inverse
images of basic opens outside a countable union of meager discrepancies.
-/

namespace PolishSpaceBook
namespace LusinContinuity

noncomputable section
open Set Topology TopologicalSpace MeasureTheory Filter
open scoped ENNReal symmDiff

/-- A finer topology agrees with the Hausdorff topology on any subset compact
for the finer topology: the identity is a continuous closed embedding. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    The identity map from $(X,\tau')$ to $(X,\tau_X)$ is continuous, so $F$ is
    also $\tau_X$-compact and hence closed. Its restriction $(F,\tau')\to(F,\tau_X)$ is a continuous bijection from a
    compact space to a Hausdorff space, hence a homeomorphism. Composing its inverse with the $\tau'$-continuous
    restriction of $f$ shows that $\restrict{f}{F}$ is continuous for the original topology.
-/
lemma compact_refinement_induced_eq {X : Type*} [t : TopologicalSpace X] [T2Space X]
    (t' : TopologicalSpace X) (hle : t' ≤ t) {F : Set X}
    (hF : @IsCompact X t' F) :
    @TopologicalSpace.induced F X Subtype.val t' =
      @TopologicalSpace.induced F X Subtype.val t := by
  let : TopologicalSpace F := @TopologicalSpace.induced F X Subtype.val t'
  let : CompactSpace F := @isCompact_iff_compactSpace X t' F |>.mp hF
  let : TopologicalSpace X := t
  have hval : @Continuous F X (@TopologicalSpace.induced F X Subtype.val t') t
      (Subtype.val : F → X) := by
    exact @Continuous.comp F X X _ t' t Subtype.val id
      ((@continuous_id_iff_le X t' t).mpr hle) (@continuous_subtype_val X t' F)
  exact (hval.isClosedEmbedding Subtype.val_injective).isEmbedding.eq_induced

/-- The book's refinement proof gives a compact set, a strengthening of its
closed-set formulation. No library version of Lusin's theorem is used. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    In fact, $F$ can be chosen compact. Apply \termuse{Borel maps become continuous} in
    §{sec:polish-topology-refinement} to refine $\tau_X$ to a Polish topology $\tau'\supseteq\tau_X$ in which $f$ is
    continuous, with the same Borel $\sigma$-algebra. Thus $\mu$ is still a finite Borel measure on $(X,\tau')$.
    By \termuseas{Ulam theorem}{Ulam's theorem} applied to this topology, choose a $\tau'$-compact $F$ with
    $\mu(\SetDifference{X}{F})<\varepsilon$.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Borel measurable functions are not in general continuous, but they are continuous after removing a small set:
-/
theorem exists_compact_continuousOn
    {X Y : Type*} [tX : TopologicalSpace X] [PolishSpace X]
    [mX : MeasurableSpace X] [BorelSpace X]
    [tY : TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → Y} (hf : Measurable f)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F : Set X, IsCompact F ∧ μ Fᶜ < ε ∧ ContinuousOn f F := by
  obtain ⟨t', hle, hp, hb, hc⟩ := exists_polish_refinement_continuous hf
  have hBorel : @BorelSpace X t' mX := ⟨by
    rw [hb]
    exact BorelSpace.measurable_eq⟩
  obtain ⟨F, hF, herror⟩ :=
    @BorelMeasureRegularity.compact_concentration X t' hp mX hBorel μ _ ε hε
  have heq := @compact_refinement_induced_eq X tX _ t' hle F hF
  have hcont : @Continuous F Y (@TopologicalSpace.induced F X Subtype.val t') tY
      (fun x => f x) :=
    @Continuous.comp F X Y _ t' tY Subtype.val f hc (@continuous_subtype_val X t' F)
  rw [heq] at hcont
  have hcompact : @IsCompact X tX F := by
    simpa only [image_id] using
      @IsCompact.image X X t' tX F id hF ((@continuous_id_iff_le X t' tX).mpr hle)
  exact ⟨F, hcompact, herror, (@continuousOn_iff_continuous_domRestrict X Y tX tY f F).mpr hcont⟩

/-- Lusin's theorem in the closed-set form stated in the book. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: theorem
  title: Lusin
-/
theorem exists_closed_continuousOn
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → Y} (hf : Measurable f)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F : Set X, IsClosed F ∧ μ Fᶜ < ε ∧ ContinuousOn f F := by
  obtain ⟨F, hF, he, hc⟩ := exists_compact_continuousOn μ hf hε
  exact ⟨F, hF.isClosed, he, hc⟩


/-- Outside the union of the symmetric differences, every basic inverse
image agrees exactly with the corresponding relatively open set. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Then $M$ is meager, and for every $n$,
    $$f^{-1}(V_n)\cap\SetDifference{X}{M}=U_n\cap\SetDifference{X}{M}.$$
    These sets are relatively open in $\SetDifference{X}{M}$, so the basis criterion for continuity shows that $f$ is
    continuous on this comeager set.
-/
theorem continuousOn_compl_discrepancies
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (V : ℕ → Set Y) (hV : IsTopologicalBasis (range V))
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n)) :
    ContinuousOn f (⋃ n, (f ⁻¹' V n) ∆ U n)ᶜ := by
  let C := (⋃ n, (f ⁻¹' V n) ∆ U n)ᶜ
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hV.continuous_iff.mpr
  rintro W ⟨n, rfl⟩
  have heq : (C.domRestrict f) ⁻¹' V n = (Subtype.val : C → X) ⁻¹' U n := by
    ext x
    have hx : (x : X) ∉ (f ⁻¹' V n) ∆ U n :=
      fun hx => x.property (mem_iUnion.mpr ⟨n, hx⟩)
    simp only [mem_symmDiff, mem_preimage] at hx ⊢
    change (f x ∈ V n ↔ (x : X) ∈ U n)
    tauto
  rw [heq]
  exact (hU n).preimage continuous_subtype_val

/-- The category analogue uses only countably many Baire-property
approximations, one for each member of a basis of the target. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    For the category analogue, let $\{V_n\}$ be a countable base for $Y$. Each Borel set $f^{-1}(V_n)$ has the Baire
    property, so choose an open $U_n\IncludedIn X$ with $f^{-1}(V_n)\mathbin{\triangle}U_n$ meager. Set
    $$M:=\bigcup_n\bigl(f^{-1}(V_n)\mathbin{\triangle}U_n\bigr).$$
-/
theorem exists_meagre_continuousOn_compl
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} (hf : Measurable f) :
    ∃ M : Set X, IsMeagre M ∧ ContinuousOn f Mᶜ := by
  obtain ⟨V, hV⟩ := exists_seq_basis Y
  have hB (n : ℕ) :=
    ((hV.isOpen (mem_range_self n)).measurableSet.preimage hf).baireMeasurableSet
  choose U hU hEq using fun n => (hB n).residualEq_isOpen
  have hM (n : ℕ) : IsMeagre ((f ⁻¹' V n) ∆ U n) := by
    change ((f ⁻¹' V n) ∆ U n)ᶜ ∈ residual X
    filter_upwards [Filter.eventuallyEqSet_iff.mp (hEq n)] with x hx
    simp only [mem_compl_iff, mem_symmDiff]
    tauto
  exact ⟨⋃ n, (f ⁻¹' V n) ∆ U n, isMeagre_iUnion hM,
    continuousOn_compl_discrepancies f V hV U hU⟩

/-- Intersecting the two continuity sets removes a meager set together with
an open set of arbitrarily small measure, as in the book's final combination. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Intersecting it with the closed set $F$ in
    \termuseas{Lusin theorem}{Lusin's theorem} makes $f$ continuous outside $M\cup(\SetDifference{X}{F})$, where
    $M$ is meager and the open set $\SetDifference{X}{F}$ has measure less than $\varepsilon$.
-/
theorem exists_meagre_small_exception
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] {f : X → Y} (hf : Measurable f)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M E : Set X, IsMeagre M ∧ IsOpen E ∧ μ E < ε ∧ ContinuousOn f (M ∪ E)ᶜ := by
  obtain ⟨F, hF, herror, hc⟩ := exists_closed_continuousOn μ hf hε
  obtain ⟨M, hM, _⟩ := exists_meagre_continuousOn_compl hf
  refine ⟨M, Fᶜ, hM, hF.isOpen_compl, herror, hc.mono ?_⟩
  intro x hx
  simpa only [compl_compl] using (compl_subset_compl.mpr (subset_union_right (s := M) (t := Fᶜ))) hx


/-- A positive-measure closed nowhere dense set prevents its indicator from
being continuous on any conull set, for a measure positive on nonempty opens. -/
theorem indicator_not_continuousOn_conull
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure]
    {F C : Set X} (hF : IsClosed F) (hFn : IsNowhereDense F)
    (hpos : μ F ≠ 0) (hC : μ Cᶜ = 0) :
    ¬ ContinuousOn (F.indicator (fun _ => (1 : ℝ))) C := by
  intro hc
  have haC : ∀ᵐ x ∂μ, x ∈ C := by
    rw [ae_iff]
    exact hC
  have hdC : Dense C := μ.dense_of_ae haC
  have hdF : Dense Fᶜ := (isClosed_isNowhereDense_iff_compl.mp ⟨hF, hFn⟩).2
  have hd : Dense (C ∩ Fᶜ) := hdC.inter_of_isOpen_right hdF hF.isOpen_compl
  have hz : EqOn (F.indicator (fun _ => (1 : ℝ))) (fun _ => 0) (C ∩ Fᶜ) := by
    intro x hx
    exact indicator_of_notMem hx.2 _
  have hzC : EqOn (F.indicator (fun _ => (1 : ℝ))) (fun _ => 0) C :=
    hz.of_subset_closure hc continuousOn_const inter_subset_left (by rw [hd.closure_eq]; exact subset_univ _)
  have hFC : (F ∩ C).Nonempty := by
    by_contra h
    have hsub : F ⊆ Cᶜ := by
      intro x hx hcx
      exact h ⟨x, hx, hcx⟩
    exact hpos (measure_mono_null hsub hC)
  obtain ⟨x, hxF, hxC⟩ := hFC
  have := hzC hxC
  simp only [indicator_of_mem hxF, one_ne_zero] at this

/-- Relative nonempty open subsets of the unit interval have positive
Lebesgue measure; a small nondegenerate real interval lies in their image. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Also $C$ is dense: every nonempty relatively open subset of the interval has positive
    Lebesgue measure.
-/
lemma unitInterval_volume_openPos :
    (volume : Measure unitInterval).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  obtain ⟨x, hx⟩ := hUne
  have hxV : (x : ℝ) ∈ V := by rw [← hVU] at hx; exact hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV x hxV
  let a : ℝ := max 0 ((x : ℝ) - r / 2)
  let b : ℝ := min 1 ((x : ℝ) + r / 2)
  have hab : a < b := by
    dsimp [a, b]
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    have := x.property.1
    have := x.property.2
    constructor <;> constructor <;> linarith
  have hsub : Icc a b ⊆ Subtype.val '' U := by
    intro y hy
    have hy0 : 0 ≤ y := (le_max_left _ _).trans hy.1
    have hy1 : y ≤ 1 := hy.2.trans (min_le_left _ _)
    refine ⟨⟨y, hy0, hy1⟩, ?_, rfl⟩
    rw [← hVU]
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have hya := (le_max_right _ _).trans hy.1
    have hyb := hy.2.trans (min_le_right _ _)
    constructor <;> linarith
  rw [unitInterval.volume_apply]
  apply ne_of_gt
  apply lt_of_lt_of_le _ (measure_mono hsub)
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)

/-- A nonatomic probability measure admits a positive-measure closed nowhere
dense set: cover a dense sequence by open sets of summable small measure. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    To obtain a closed nowhere dense set of positive measure, take a dense sequence $q_n$ and use closed-set
    regularity and $\lambda(\{q_n\})=0$ to choose relatively open neighborhoods $W_n$ with
    $$q_n\in W_n,\qquad \lambda(W_n)<2^{-(n+2)}.$$
    Then $O:=\bigcup_n W_n$ is open and dense, while
    $$\lambda(O)\le\sum_{n=0}^{\infty}\lambda(W_n)\le\frac12.$$
    Thus $K:=\SetDifference{X}{O}$ is closed and nowhere dense, with $\lambda(K)\ge1/2$.
-/
theorem exists_closed_nowhereDense_measure_ge_half
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∃ F : Set X, IsClosed F ∧ IsNowhereDense F ∧ (2⁻¹ : ℝ≥0∞) ≤ μ F := by
  let q := denseSeq X
  let δ : ℕ → ℝ≥0∞ := fun n => (2⁻¹ : ℝ≥0∞) ^ (n + 2)
  have hδpos (n : ℕ) : 0 < δ n := ENNReal.pow_pos (by norm_num) _
  have hδsum : ∑' n, δ n = (2⁻¹ : ℝ≥0∞) := by
    simp only [δ, pow_add, ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
    rw [pow_two, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hex (n : ℕ) : ∃ U : Set X, IsOpen U ∧ q n ∈ U ∧ μ U < δ n := by
    obtain ⟨F, U, _, hU, hFq, hqU, hgap⟩ :=
      BorelMeasureRegularity.closed_open_approximation μ (measurableSet_singleton (q n)) (hδpos n)
    have hFzero : μ F = 0 := measure_mono_null hFq (measure_singleton (q n))
    exact ⟨U, hU, hqU (mem_singleton _), by rwa [measure_sdiff_null hFzero] at hgap⟩
  choose U hU hqU hμU using hex
  let O := ⋃ n, U n
  have hO : IsOpen O := isOpen_iUnion hU
  have hdO : Dense O := (denseRange_denseSeq X).mono (by
    rintro x ⟨n, rfl⟩
    exact mem_iUnion.mpr ⟨n, hqU n⟩)
  have hμO : μ O ≤ (2⁻¹ : ℝ≥0∞) := calc
    μ O ≤ ∑' n, μ (U n) := measure_iUnion_le _
    _ ≤ ∑' n, δ n := ENNReal.tsum_le_tsum (fun n => (hμU n).le)
    _ = 2⁻¹ := hδsum
  refine ⟨Oᶜ, hO.isClosed_compl,
    (isClosed_isNowhereDense_iff_compl.mpr (by simpa using And.intro hO hdO)).2, ?_⟩
  rw [measure_compl hO.measurableSet (measure_ne_top μ O), measure_univ]
  calc
    (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
    _ ≤ 1 - μ O := tsub_le_tsub_left hμO 1

/-- The quantitative construction has positive measure. -/
theorem exists_closed_nowhereDense_pos
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∃ F : Set X, IsClosed F ∧ IsNowhereDense F ∧ μ F ≠ 0 := by
  obtain ⟨F, hF, hFn, hhalf⟩ := exists_closed_nowhereDense_measure_ge_half μ
  exact ⟨F, hF, hFn, ne_of_gt (lt_of_lt_of_le (by norm_num) hhalf)⟩

/-- The obstruction is nonvacuous for Lebesgue measure on the unit interval. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Let $\lambda$ be Lebesgue measure on
    $X=[0,1]$.
-/
theorem unitInterval_exists_closed_nowhereDense_pos :
    ∃ F : Set unitInterval, IsClosed F ∧ IsNowhereDense F ∧ volume F ≠ 0 :=
  exists_closed_nowhereDense_pos volume

/-- The book's Lebesgue-measure counterexample, on the actual unit interval. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Since $\SetDifference{X}{K}$ is open and dense, $C\cap\SetDifference{X}{K}$ is dense in $X$, and
    hence dense in $C$. If $\restrict{g}{C}$ were continuous, its value $0$ on this dense subset would force it to be
    identically $0$ on $C$, contradicting its value $1$ at a point of $K\cap C$.
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Let $g$ be its indicator:
    $g=1$ on $K$ and $g=0$ on $\SetDifference{X}{K}$. For any conull $C\IncludedIn X$, the set $K\cap C$ is nonempty,
    because $K$ has positive measure.
-/
theorem unitInterval_indicator_not_continuousOn_conull
    {F C : Set unitInterval} (hF : IsClosed F) (hFn : IsNowhereDense F)
    (hpos : volume F ≠ 0) (hC : volume Cᶜ = 0) :
    ¬ ContinuousOn (F.indicator (fun _ => (1 : ℝ))) C := by
  let := unitInterval_volume_openPos
  exact indicator_not_continuousOn_conull volume hF hFn hpos hC


/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    The measure-small exceptional set cannot in general be replaced by a null set.
-/
/-- A Borel measurable real-valued function on the unit interval for which
no removal of a null set yields continuity. -/
theorem unitInterval_exists_measurable_no_conull_continuity :
    ∃ g : unitInterval → ℝ, Measurable g ∧
      ∀ C : Set unitInterval, volume Cᶜ = 0 → ¬ ContinuousOn g C := by
  obtain ⟨F, hF, hFn, hpos⟩ := unitInterval_exists_closed_nowhereDense_pos
  exact ⟨F.indicator (fun _ => 1), measurable_const.indicator hF.measurableSet,
    fun _ hC => unitInterval_indicator_not_continuousOn_conull hF hFn hpos hC⟩

end
end LusinContinuity
end PolishSpaceBook
