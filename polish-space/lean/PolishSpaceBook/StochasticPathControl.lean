module

public import PolishSpaceBook.LusinContinuity
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section

/-! # Uniform control of paths on a set of large probability

The existing refinement proof of Lusin continuity supplies a compact set.
Joint evaluation on its product with the time interval supplies a uniform
bound and a common modulus of continuity.
-/
namespace PolishSpaceBook.StochasticPathControl
noncomputable section
open Set MeasureTheory Topology Filter TopologicalSpace
open scoped ENNReal

abbrev RealPath := C(unitInterval, ℝ)

/-- Joint evaluation on a compact parameter set gives uniform path control. -/
theorem compact_path_control {Ω : Type*} [PseudoMetricSpace Ω]
    {K : Set Ω} (hK : IsCompact K) {F : Ω → RealPath}
    (hF : ContinuousOn F K) :
    ∃ M : ℝ, (∀ ω ∈ K, ∀ t : unitInterval, |F ω t| ≤ M) ∧
      ∀ η > 0, ∃ δ > 0, ∀ ω ∈ K, ∀ s t : unitInterval,
        dist s t ≤ δ → |F ω s - F ω t| < η := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hfK : Continuous (fun ω : K => F ω) :=
    continuousOn_iff_continuous_domRestrict.mp hF
  let H : K × unitInterval → ℝ := fun z => F z.1 z.2
  have hH : Continuous H :=
    continuous_eval.comp ((hfK.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hH.norm.continuousOn
  refine ⟨M, ?_, ?_⟩
  · intro ω hω t
    have := hM ⟨(⟨ω, hω⟩, t), mem_univ _, rfl⟩
    simpa only [H, Real.norm_eq_abs] using this
  · intro η hη
    obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous hH) η hη
    refine ⟨δ / 2, half_pos hδ, ?_⟩
    intro ω hω s t hst
    have hdist : dist ((⟨ω, hω⟩ : K), s) ((⟨ω, hω⟩ : K), t) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using
        hst.trans_lt (half_lt_self hδ)
    simpa only [H, Real.dist_eq] using hu hdist

/-- All oscillations at time separation at most `δ`, before taking a supremum. -/
def oscillationValues {Ω : Type*} (F : Ω → RealPath) (K : Set Ω) (δ : ℝ) : Set ℝ :=
  {r | ∃ ω ∈ K, ∃ s t : unitInterval, dist s t ≤ δ ∧ r = |F ω s - F ω t|}

/-- The common modulus appearing in the book's limit formula. -/
def pathModulus {Ω : Type*} (F : Ω → RealPath) (K : Set Ω) (δ : ℝ) : ℝ :=
  sSup (oscillationValues F K δ)

lemma zero_mem_oscillationValues {Ω : Type*} (F : Ω → RealPath) {K : Set Ω}
    (hK : K.Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) : 0 ∈ oscillationValues F K δ := by
  obtain ⟨ω, hω⟩ := hK
  exact ⟨ω, hω, 0, 0, by simpa using hδ, by simp⟩

lemma oscillationValues_bddAbove {Ω : Type*} {F : Ω → RealPath} {K : Set Ω}
    {M : ℝ} (hM : ∀ ω ∈ K, ∀ t : unitInterval, |F ω t| ≤ M) (δ : ℝ) :
    BddAbove (oscillationValues F K δ) := by
  refine ⟨M + M, ?_⟩
  rintro r ⟨ω, hω, s, t, _, rfl⟩
  have htri : |F ω s - F ω t| ≤ |F ω s| + |F ω t| := by
    simpa using abs_sub_le (F ω s) 0 (F ω t)
  exact htri.trans (add_le_add (hM ω hω s) (hM ω hω t))

/-- The epsilon-delta control gives the actual supremum limit as time width decreases to zero. -/
theorem pathModulus_tendsto_zero {Ω : Type*} {F : Ω → RealPath} {K : Set Ω}
    (hK : K.Nonempty) {M : ℝ} (hM : ∀ ω ∈ K, ∀ t : unitInterval, |F ω t| ≤ M)
    (hu : ∀ η > 0, ∃ δ > 0, ∀ ω ∈ K, ∀ s t : unitInterval,
      dist s t ≤ δ → |F ω s - F ω t| < η) :
    Tendsto (pathModulus F K) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨δ, hδ, hcontrol⟩ := hu (η / 2) (half_pos hη)
  filter_upwards [Ioo_mem_nhdsGT hδ] with d hd
  have hn := zero_mem_oscillationValues F hK hd.1.le
  have hnonneg : 0 ≤ pathModulus F K d :=
    le_csSup (oscillationValues_bddAbove hM d) hn
  have hupper : pathModulus F K d ≤ η / 2 := by
    apply csSup_le ⟨0, hn⟩
    rintro r ⟨ω, hω, s, t, hst, rfl⟩
    exact (hcontrol ω hω s t (hst.trans hd.2.le)).le
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
    hupper.trans_lt (half_lt_self hη)

/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: statement
  kind: example
  title: Continuous dependence of sample paths on a set of large probability
-/
/-- Probability-form compact Lusin continuity, retaining the book's path codomain. -/
theorem exists_large_compact_path_control
    {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Ω → RealPath}
    (hF : @Measurable Ω RealPath inferInstance (borel RealPath) F) {ε : ℝ≥0∞} (hε : 0 < ε) (hε₁ : ε < 1) :
    ∃ K : Set Ω, IsCompact K ∧ 1 - ε < μ K ∧ μ Kᶜ < ε ∧
      ContinuousOn F K ∧ IsCompact (F '' K) ∧
      ∃ M : ℝ, (∀ ω ∈ K, ∀ t : unitInterval, |F ω t| ≤ M) ∧
        (∀ η > 0, ∃ δ > 0, ∀ ω ∈ K, ∀ s t : unitInterval,
          dist s t ≤ δ → |F ω s - F ω t| < η) ∧
        Tendsto (pathModulus F K) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let := upgradeIsCompletelyMetrizable Ω
  let : MeasurableSpace RealPath := borel RealPath
  let : BorelSpace RealPath := ⟨rfl⟩
  obtain ⟨K, hK, he, hc⟩ := LusinContinuity.exists_compact_continuousOn μ hF hε
  have hadd := ENNReal.add_lt_add_left (measure_ne_top μ K) he
  rw [measure_add_measure_compl hK.isClosed.measurableSet, measure_univ] at hadd
  have hprob : 1 - ε < μ K :=
    (ENNReal.sub_lt_iff_lt_right (ne_of_lt (hε₁.trans (by simp))) hε₁.le).mpr hadd
  have hne : K.Nonempty := nonempty_of_measure_ne_zero
    (ne_of_gt ((show (0 : ℝ≥0∞) ≤ 1 - ε from zero_le).trans_lt hprob))
  obtain ⟨M, hM, hu⟩ := compact_path_control hK hc
  exact ⟨K, hK, hprob, he, hc, hK.image_of_continuousOn hc,
    M, hM, hu, pathModulus_tendsto_zero hne hM hu⟩

end
end PolishSpaceBook.StochasticPathControl
