module

public import PolishSpaceBook.LusinSuslinPrefixImage
public import PolishSpaceBook.ZeroDimensionalPolishRefinement

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # From Borel maps to the separated-prefix image construction -/

namespace PolishSpaceBook

open Set TopologicalSpace Topology MeasureTheory

/-- Make the Borel domain clopen and the map continuous, then use its closed Baire presentation. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Given $f:X\to Y$ Borel and injective on the Borel set $B\IncludedIn X$, choose a countable open base
    $\Sequence{V_n}{n\in\omega}$ of $Y$. Apply \termuse{Kuratowski's refinement theorem} to the Borel family
    $$C_0:=B,\qquad C_{n+1}:=f^{-1}(V_n)\quad(n\in\omega).$$
    In the refined Polish topology, $B$ is clopen and $f$ is continuous, because the inverse images of the basic open
    sets are open. Restricting to $B$ therefore gives a continuous injection on a Polish space.

    By \termuse{closed presentation in Baire space} in §{sec:closed-presentation-baire}, there are a closed set
    $F\IncludedIn\BaireSpace$ and a continuous Borel isomorphism $e:F\to B$. Compose the restricted map with $e$.
    Refinement preserves the Borel $\sigma$-algebra of the source, and $e$ preserves both the image and injectivity.
    It therefore suffices to prove the image assertion for a closed set $F\IncludedIn\BaireSpace$ and a continuous
    injection $f:F\to Y$.
-/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    The following changes of presentation preserve the relevant Borel structures, and Borelness of the image is
    invariant under such changes. The topology-refinement results are those developed in
    §{sec:polish-embeddings-refinements}.
-/
theorem measurableSet_image_via_prefix_refinement
    {X : Type} {Y : Type*} [tX : TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {B : Set X} {f : X → Y}
    (hB : MeasurableSet B) (hf : Measurable f) (hi : InjOn f B) : MeasurableSet (f '' B) := by
  let := metrizableSpaceMetric Y
  obtain ⟨t', _, hp, _, hcl, hfc⟩ := exists_polish_refinement_clopen_and_continuous hB hf
  let : TopologicalSpace X := t'
  let : PolishSpace X := hp
  let : PolishSpace B := hcl.isClosed.polishSpace
  let g : B → Y := fun x => f x.val
  have hg : Continuous g := hfc.comp continuous_subtype_val
  have hgi : Function.Injective g := injOn_iff_injective.mp hi
  obtain ⟨F, hF, e, he, _⟩ := exists_continuous_closed_baire_presentation B
  have hm : MeasurableSet (range (g ∘ e)) :=
    LusinSuslinPrefix.measurableSet_range hF (hg.comp he) (hgi.comp e.injective)
  rw [e.surjective.range_comp g] at hm
  have hr : range g = f '' B := by ext y; simp [g]
  rwa [hr] at hm

/-- The full Borel-map form, with Borel images supplied by the prefix construction. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Returning to the original Borel domain $B$, every Borel subset of $B$ is Borel in $X$. Apply the image conclusion
    to each such subset. Since its image is the inverse image of that subset under $(f|_B)^{-1}$, the inverse on $f(B)$
    is Borel. Thus $f|_B$ is a Borel isomorphism.
    \end{proof}
-/
theorem lusinSuslin_via_prefix_refinement
    {X : Type} {Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {B : Set X} {f : X → Y}
    (hB : MeasurableSet B) (hf : Measurable f) (hi : InjOn f B) :
    MeasurableSet (f '' B) ∧ MeasurableEmbedding (B.domRestrict f) := by
  refine ⟨measurableSet_image_via_prefix_refinement hB hf hi, injOn_iff_injective.mp hi,
    hf.comp measurable_subtype_coe, ?_⟩
  intro A hA
  have hD : MeasurableSet (Subtype.val '' A : Set X) :=
    (MeasurableEmbedding.subtype_coe hB).measurableSet_image' hA
  have hsub : Subtype.val '' A ⊆ B := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hm := measurableSet_image_via_prefix_refinement hD hf (hi.mono hsub)
  simpa only [image_image, Set.domRestrict] using hm


/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: statement
  kind: corollary
  title: Continuous form
-/
/-- The continuous case follows by applying the constructed Borel-image theorem to each Borel subset. -/
theorem continuous_injective_measurableEmbedding_via_prefix
    {X : Type} {Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {f : X → Y}
    (hf : Continuous f) (hi : Function.Injective f) :
    MeasurableSet (range f) ∧ MeasurableEmbedding f := by
  refine ⟨?_, hi, hf.measurable, ?_⟩
  · simpa only [image_univ] using
      measurableSet_image_via_prefix_refinement MeasurableSet.univ hf.measurable hi.injOn
  · intro A hA
    exact measurableSet_image_via_prefix_refinement hA hf.measurable hi.injOn

end PolishSpaceBook
