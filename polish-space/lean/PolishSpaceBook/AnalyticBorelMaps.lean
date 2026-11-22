module

public import PolishSpaceBook.PolishEmbeddingsBorelRefinements
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-!
# Borel images through explicit Polish refinements

A single countable family contains the Borel domain and all basic-open
preimages. Refining it to clopen sets makes the domain Polish and the map
continuous without changing its image.
-/

namespace PolishSpaceBook

open Set TopologicalSpace Topology MeasureTheory

/-- Use the book's Cauchy-name surjection to convert a Polish continuous image
into the canonical Baire-parametrized analytic-set predicate. -/
theorem analyticSet_range_via_baire_surjection {Z X : Type*}
    [TopologicalSpace Z] [PolishSpace Z] [TopologicalSpace X]
    {f : Z → X} (hf : Continuous f) : AnalyticSet (range f) := by
  cases isEmpty_or_nonempty Z
  · rw [range_eq_empty]
    exact analyticSet_empty
  · obtain ⟨q, hq, hsurj⟩ := exists_baire_continuous_surjection Z
    rw [AnalyticSet]
    exact Or.inr ⟨f ∘ q, hf.comp hq, hsurj.range_comp f⟩

/-- A Borel subset and a Borel map can be handled in the same refinement:
index zero records the subset, and successor indices record basic-open preimages. -/
theorem exists_polish_refinement_clopen_and_continuous
    {Y X : Type*} [tY : TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [tX : TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {B : Set Y} {f : Y → X}
    (hB : MeasurableSet B) (hf : Measurable f) :
    ∃ t' : TopologicalSpace Y, t' ≤ tY ∧ @PolishSpace Y t' ∧
      @borel Y t' = @borel Y tY ∧ @IsClopen Y t' B ∧ @Continuous Y X t' tX f := by
  obtain ⟨V, hV⟩ := exists_seq_basis X
  let C : ℕ → Set Y
    | 0 => B
    | n + 1 => f ⁻¹' V n
  have hC : ∀ n, MeasurableSet (C n) := by
    intro n
    cases n with
    | zero => exact hB
    | succ n => exact (hV.isOpen (mem_range_self n)).measurableSet.preimage hf
  obtain ⟨t', hle, hp, hb, hc⟩ := exists_polish_refinement_clopen C hC
  refine ⟨t', hle, hp, hb, hc 0, ?_⟩
  let : TopologicalSpace Y := t'
  apply hV.continuous_iff.mpr
  rintro _ ⟨n, rfl⟩
  exact (hc (n + 1)).isOpen

/-- Clopen refinement realizes a Borel set itself as a Polish source for its
inclusion into the original topology. -/
theorem analyticSet_of_borel_via_refinement
    {X : Type*} [t : TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {A : Set X} (hA : MeasurableSet A) : AnalyticSet A := by
  obtain ⟨t', hle, hp, _, hcl⟩ := exists_polish_refinement_clopen (fun _ => A) (fun _ => hA)
  let : TopologicalSpace X := t'
  let : PolishSpace X := hp
  let : PolishSpace A := (hcl 0).isClosed.polishSpace
  have hid : @Continuous X X t' t id := continuous_iff_le_induced.mpr (by simpa only [induced_id] using hle)
  have hi : @Continuous A X (t'.induced Subtype.val) t Subtype.val :=
    @Continuous.comp A X X (t'.induced Subtype.val) t' t Subtype.val id hid
      (@continuous_subtype_val X t' A)
  have h := @analyticSet_range_via_baire_surjection A X inferInstance inferInstance t Subtype.val hi
  simpa only [Subtype.range_coe] using h

/-- Restrict the continuous map to the clopen Polish domain in the refined topology. -/
theorem analyticSet_borel_image_via_refinement
    {Y X : Type*} [tY : TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [tX : TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {B : Set Y} {f : Y → X}
    (hB : MeasurableSet B) (hf : Measurable f) : AnalyticSet (f '' B) := by
  obtain ⟨t', _, hp, _, hcl, hc⟩ := exists_polish_refinement_clopen_and_continuous hB hf
  let : TopologicalSpace Y := t'
  let : PolishSpace Y := hp
  let : PolishSpace B := hcl.isClosed.polishSpace
  have hcont : Continuous (fun y : B => f y.val) := hc.comp continuous_subtype_val
  have hr : range (fun y : B => f y.val) = f '' B := by
    ext x
    simp
  rw [← hr]
  exact analyticSet_range_via_baire_surjection hcont

/-@ booklink:
  source: polish-space-book/analytic-sets-suslin-schemes.md
  target: prose
  excerpt: |
    More generally, if $D$ is analytic in a Polish space $Y$ and $f:Y\to X$ is Borel, then $f(D)$ is analytic.
    For $D=\emptyset$ this is immediate. Otherwise, take a continuous map $h:\BaireSpace\to Y$ with $h(\BaireSpace)=D$.
    The composite $f\circ h$ is Borel, and
    $$f(D)=(f\circ h)(\BaireSpace).$$
    Applying the Borel-image characterization to the Borel domain $\BaireSpace$ proves the claim.
-/
/-- For an analytic source set, compose its continuous Baire parametrization
with the Borel map before applying the Borel-domain result. -/
theorem analyticSet_image_via_baire_parametrization
    {Y X : Type*} [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {A : Set Y} {f : Y → X}
    (hA : AnalyticSet A) (hf : Measurable f) : AnalyticSet (f '' A) := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨g, hg, rfl⟩
  · simpa using (analyticSet_empty : AnalyticSet (∅ : Set X))
  · have hc : Measurable (f ∘ g) := hf.comp hg.measurable
    have h := analyticSet_borel_image_via_refinement MeasurableSet.univ hc
    simpa only [image_univ, Set.range_comp] using h

end PolishSpaceBook
