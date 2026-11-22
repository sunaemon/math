module

public import PolishSpaceBook.HewittSavage
public import PolishSpaceBook.BorelReducibilitySynthesis
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Nonsmoothness of eventual equality

The book's measure argument: finite-permutation invariance, Hewitt--Savage,
a point mass for the real-valued invariant, and nullity of countable classes.
-/

namespace PolishSpaceBook
noncomputable section
open MeasureTheory ProbabilityTheory MeasurableSpace Set Function Filter Topology
open scoped NNReal ENNReal

/-- Without atoms the distribution function is continuous, by its jump formula. -/
theorem continuous_cdf_of_noAtoms (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    Continuous (cdf ν) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (cdf ν).mono.continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [(cdf ν).rightLim_eq]
  have hjump := (cdf ν).measure_singleton x
  rw [measure_cdf, measure_singleton] at hjump
  have hle := ENNReal.ofReal_eq_zero.mp hjump.symm
  have hge := (cdf ν).mono.leftLim_le (x := x) le_rfl
  linarith

/-- A zero-one probability measure on the real line has an atom of mass one.
If it had no atoms, the continuous cdf would take the value one half. -/
theorem real_zero_one_has_full_atom (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hzero : ∀ B : Set ℝ, MeasurableSet B → ν B = 0 ∨ ν B = 1) :
    ∃ c : ℝ, ν {c} = 1 := by
  by_contra! hn
  have hz : ∀ c : ℝ, ν {c} = 0 := fun c =>
    (hzero {c} (measurableSet_singleton c)).resolve_right (hn c)
  let : NullSingletonClass ν := ⟨hz⟩
  have hleft : ∃ a : ℝ, cdf ν a ≤ (1 / 2 : ℝ) := by
    obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot ν).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
    exact ⟨a, ha.le⟩
  have hright : ∃ b : ℝ, (1 / 2 : ℝ) ≤ cdf ν b := by
    obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop ν).eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).exists
    exact ⟨b, hb.le⟩
  obtain ⟨t, ht⟩ := mem_range_of_exists_le_of_exists_ge (continuous_cdf_of_noAtoms ν) hleft hright
  rw [cdf_eq_real] at ht
  rcases hzero (Iic t) measurableSet_Iic with h | h <;>
    simp [measureReal_def, h] at ht

/-- The full-atom conclusion identifies the entire probability measure with
the Dirac mass, as stated in the book before pulling it back to a fiber. -/
theorem real_zero_one_eq_dirac (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hzero : ∀ B : Set ℝ, MeasurableSet B → ν B = 0 ∨ ν B = 1) :
    ∃ c : ℝ, ν = Measure.dirac c := by
  obtain ⟨c, hc⟩ := real_zero_one_has_full_atom ν hzero
  have hnull : ν ({c} : Set ℝ)ᶜ = 0 := by
    rw [measure_compl (measurableSet_singleton c) (measure_ne_top ν _), measure_univ, hc, tsub_self]
  have hae : (id : ℝ → ℝ) =ᵐ[ν] (fun _ => c) := by
    have hmem : ∀ᵐ x ∂ν, x ∈ ({c} : Set ℝ) := ae_iff.mpr hnull
    filter_upwards [hmem] with x hx
    exact mem_singleton_iff.mp hx
  exact ⟨c, by simpa using Measure.map_congr hae⟩

/-- Fair coin distribution and its countable product. -/
def fairCoin : Measure Bool := bernoulliMeasure true false ⟨1 / 2, by constructor <;> norm_num⟩
instance : IsProbabilityMeasure fairCoin := by unfold fairCoin; infer_instance

def fairCoinProduct : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => fairCoin)
instance : IsProbabilityMeasure fairCoinProduct := by unfold fairCoinProduct; infer_instance

lemma fairCoin_singleton (b : Bool) : fairCoin {b} = (1 / 2 : ℝ≥0∞) := by
  cases b <;> norm_num [fairCoin, bernoulliMeasure_def, Measure.nnreal_smul_coe_apply, unitInterval.toNNReal, unitInterval.symm]
  all_goals
    change ((1 / 2 : ℝ≥0) : ℝ≥0∞) = 2⁻¹
    norm_num

instance fairCoinProduct_noAtoms : NullSingletonClass fairCoinProduct where
  measure_singleton x := by
    apply le_antisymm _ zero_le
    apply le_of_tendsto_of_tendsto tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0∞) < 1))
    apply Eventually.of_forall
    intro n
    have hsub : {x} ⊆ Set.pi (↑(Finset.range n) : Set ℕ) (fun i => {x i}) := by
      intro y hy
      obtain rfl := mem_singleton_iff.mp hy
      exact fun i _ => mem_singleton _
    have h := measure_mono (μ := fairCoinProduct) hsub
    have heq : fairCoinProduct (Set.pi (↑(Finset.range n) : Set ℕ) (fun i => {x i})) =
        (1 / 2 : ℝ≥0∞) ^ n := by
      rw [fairCoinProduct, Measure.infinitePi_pi _ (by measurability)]
      simp [fairCoin_singleton]
    rwa [heq] at h

/-- Every eventual-equality class is a countable union of finite classes. -/
theorem e0_class_countable (x : ℕ → Bool) : {y | E0 x y}.Countable := by
  have heq : {y | E0 x y} = ⋃ N : ℕ, {y | E0At N x y} := by
    ext y; simp [E0]
  rw [heq]
  exact Set.countable_iUnion (fun N => (e0At_class_finite N x).countable)

lemma e0_finite_permutation (σ : Equiv.Perm ℕ) (hσ : {n | σ n ≠ n}.Finite)
    (x : ℕ → Bool) : E0 x (x ∘ σ) := by
  classical
  let I := hσ.toFinset
  refine ⟨I.sup id + 1, ?_⟩
  intro n hn
  have hfix : σ n = n := by
    by_contra h
    have hnI : n ∈ I := hσ.mem_toFinset.mpr h
    have hle : n ≤ I.sup id := Finset.le_sup (f := id) hnI
    omega
  simp [Function.comp_apply, hfix]

/-- Hewitt--Savage applies to every Borel union of eventual-equality classes. -/
theorem e0_saturated_zero_one {A : Set (ℕ → Bool)} (hA : MeasurableSet A)
    (hsat : ∀ x y, E0 x y → (x ∈ A ↔ y ∈ A)) :
    fairCoinProduct A = 0 ∨ fairCoinProduct A = 1 := by
  apply hewitt_savage_zero_one fairCoin hA
  intro σ hσ x
  exact (hsat x (x ∘ σ) (e0_finite_permutation σ hσ x)).symm

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    $\EventualEqualityER$ is *not smooth*.
-/
/-- Eventual equality is nonsmooth: a Borel complete real invariant would
have a conull fiber, but each of its fibers is a countable null class. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Suppose toward a contradiction that a Borel reduction $f : \CantorSpace \to \R$
    reduced $\EventualEqualityER$ to
    equality on $\R$. Then $f$ is constant on $\EventualEqualityER$-classes. If $B \IncludedIn \R$ is Borel, the preimage
    $f^{-1}(B)$ is
    $\EventualEqualityER$-saturated: changing finitely many bits cannot change membership in it.
-/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Every $\EventualEqualityER$-saturated Borel set is invariant under finite-support permutations of coordinates, because
    such a
    permutation changes only finitely many coordinates of each binary sequence. Hence the Hewitt--Savage zero-one law of
    §{sec:zero-one-laws}, applied to the fair-coin product measure $\mu$, gives
    $$
    \mu(f^{-1}(B))\in\{0,1\}
    \qquad(B\in\mathcal B(\R)).
    $$
    Let $\nu:=f_*\mu$ be the pushforward probability measure on $\R$. The displayed equation says that every Borel subset of
    $\R$ has $\nu$-measure $0$ or $1$.
-/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Such a probability measure on $\R$ must be a point mass. Indeed, if some singleton had measure strictly between $0$ and
    $1$, the zero-one property would already fail. If every singleton had measure $0$, then the distribution function
    $F(t)=\nu((-\infty,t])$ would be continuous, with limits $0$ and $1$ at $\pm\infty$; choosing $t$ with $0<F(t)<1$ again
    contradicts the zero-one property. Therefore $\nu=\delta_c$ for some $c\in\R$, and
    $$\mu(f^{-1}(\{c\}))=1.$$
    The level set $f^{-1}(\{c\})$ is nonempty. Since a reduction identifies exactly equivalent points, it is one
    $\EventualEqualityER$-class. Every such class is countable, and the fair-coin product measure is nonatomic, so
    this level set has measure zero. This contradicts its measure being one. Hence $\EventualEqualityER$ is not smooth.
-/
theorem e0_not_smooth : ¬ Smooth E0 := by
  rintro ⟨f, hf, hclass⟩
  let ν := fairCoinProduct.map f
  have : IsProbabilityMeasure ν := inferInstance
  have hzero : ∀ B : Set ℝ, MeasurableSet B → ν B = 0 ∨ ν B = 1 := by
    intro B hB
    rw [show ν B = fairCoinProduct (f ⁻¹' B) from Measure.map_apply hf hB]
    apply e0_saturated_zero_one (hB.preimage hf)
    intro x y hxy
    change f x ∈ B ↔ f y ∈ B
    rw [(hclass x y).mp hxy]
  obtain ⟨c, hdirac⟩ := real_zero_one_eq_dirac ν hzero
  have hc : ν {c} = 1 := by rw [hdirac]; simp
  have hfiber : fairCoinProduct (f ⁻¹' {c}) = 1 := by
    rw [← Measure.map_apply hf (measurableSet_singleton c)]
    exact hc
  have hne : (f ⁻¹' {c}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, measure_empty] at hfiber
    exact zero_ne_one hfiber
  obtain ⟨x, hx⟩ := hne
  have hcount : (f ⁻¹' {c}).Countable := (e0_class_countable x).mono (by
    intro y hy
    apply (hclass x y).mpr
    exact (mem_singleton_iff.mp hx).trans (mem_singleton_iff.mp hy).symm)
  have hz := hcount.measure_zero fairCoinProduct
  rw [hfiber] at hz
  exact one_ne_zero hz

end
end PolishSpaceBook
