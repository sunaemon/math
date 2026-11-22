module

public import PolishSpaceBook.DisintegrationFibers
public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section

/-! # Conditional distributions from the book's disintegration

Disintegrate the joint law along the second projection and push the resulting
probabilities along the first projection. The eventwise identity transports
back to the original probability space.
-/
namespace PolishSpaceBook.ConditionalDistributions
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal MeasureTheory ProbabilityTheory

variable {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]

/-- Push the product-valued conditional probabilities to their first coordinate. -/
def firstMarginalKernel (p : T → ProbabilityMeasure (S × T)) (hp : Measurable p) :
    Kernel T S where
  toFun y := (p y : Measure (S × T)).map Prod.fst
  measurable' := (Measure.measurable_map Prod.fst measurable_fst).comp
    (measurable_subtype_coe.comp hp)

instance firstMarginalKernel_isMarkov (p : T → ProbabilityMeasure (S × T))
    (hp : Measurable p) : IsMarkovKernel (firstMarginalKernel p hp) where
  isProbabilityMeasure y := by
    change IsProbabilityMeasure ((p y : Measure (S × T)).map Prod.fst)
    infer_instance

/-- The joint-law construction gives the full identity for observation events. -/
theorem exists_kernel_identity [StandardBorelSpace S] [StandardBorelSpace T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) :
    ∃ κ : Kernel T S, IsMarkovKernel κ ∧
      ∀ A D, MeasurableSet A → MeasurableSet D →
        ∫⁻ y in D, κ y A ∂μ.map Y = μ (X ⁻¹' A ∩ Y ⁻¹' D) := by
  let Z : Ω → S × T := fun ω => (X ω, Y ω)
  have hZ : Measurable Z := hX.prodMk hY
  let ν := μ.map Z
  let : IsProbabilityMeasure ν := inferInstance
  obtain ⟨p, hp, hfiber, hint⟩ :=
    DisintegrationFibers.exists_disintegration ν Prod.snd measurable_snd
  let κ := firstMarginalKernel p hp
  have hνY : ν.map Prod.snd = μ.map Y := by
    rw [Measure.map_map measurable_snd hZ]
    rfl
  refine ⟨κ, inferInstance, ?_⟩
  intro A D hA hD
  have hid := DisintegrationFibers.identity_of_fiber ν Prod.snd p measurable_snd
    hfiber hint (Prod.fst ⁻¹' A) D (measurable_fst hA) hD
  rw [hνY, Measure.map_apply hZ ((measurable_fst hA).inter (measurable_snd hD))] at hid
  change (∫⁻ y in D, ((p y : Measure (S × T)).map Prod.fst) A ∂μ.map Y) = _
  simp_rw [Measure.map_apply measurable_fst hA]
  exact hid

/-- The eventwise identity identifies this constructed kernel with the canonical
conditional distribution and hence gives the usual conditional expectation. -/
theorem kernel_condExp_of_identity [StandardBorelSpace S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) (κ : Kernel T S) [IsMarkovKernel κ]
    (hid : ∀ A D, MeasurableSet A → MeasurableSet D →
      ∫⁻ y in D, κ y A ∂μ.map Y = μ (X ⁻¹' A ∩ Y ⁻¹' D))
    {f : S → ℝ} (hf : Measurable f) (hint : Integrable (fun ω => f (X ω)) μ) :
    μ[fun ω => f (X ω) | MeasurableSpace.comap Y inferInstance] =ᵐ[μ]
      fun ω => ∫ s, f s ∂κ (Y ω) := by
  let : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let : Nonempty S := Nonempty.map X inferInstance
  have heq : μ.map (fun ω => (Y ω, X ω)) = μ.map Y ⊗ₘ κ := by
    apply Measure.ext_prod
    intro D A hD hA
    rw [Measure.map_apply (hY.prodMk hX) (hD.prod hA), Measure.compProd_apply_prod hD hA]
    simpa only [mk_preimage_prod, inter_comm] using (hid A D hA hD).symm
  have hk := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hY hX heq
  have hka := ae_of_ae_map hY.aemeasurable hk
  have hce := condExp_ae_eq_integral_condDistrib hY hX.aemeasurable hf.stronglyMeasurable hint
  filter_upwards [hce, hka] with ω hω hκ
  exact hω.trans (by rw [hκ])

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: example
  title: Conditional distributions
-/
/-- The conditional distribution obtained from the joint law, including the
conditional-expectation formula for every bounded Borel function. -/
theorem exists_regular_conditional_distribution [StandardBorelSpace S] [StandardBorelSpace T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T}
    (hX : Measurable X) (hY : Measurable Y) :
    ∃ κ : Kernel T S, IsMarkovKernel κ ∧
      (∀ A D, MeasurableSet A → MeasurableSet D →
        ∫⁻ y in D, κ y A ∂μ.map Y = μ (X ⁻¹' A ∩ Y ⁻¹' D)) ∧
      ∀ f : S → ℝ, Measurable f → ∀ C : ℝ, (∀ s, ‖f s‖ ≤ C) →
        μ[fun ω => f (X ω) | MeasurableSpace.comap Y inferInstance] =ᵐ[μ]
          fun ω => ∫ s, f s ∂κ (Y ω) := by
  obtain ⟨κ, hκ, hid⟩ := exists_kernel_identity μ hX hY
  let := hκ
  refine ⟨κ, hκ, hid, ?_⟩
  intro f hf C hC
  exact kernel_condExp_of_identity μ hX hY κ hid hf
    (Integrable.of_bound (hf.comp hX).aestronglyMeasurable C
      (Eventually.of_forall fun ω => hC (X ω)))

end
end PolishSpaceBook.ConditionalDistributions
