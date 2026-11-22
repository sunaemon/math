module

public import PolishSpaceBook.ProkhorovHilbert
public import PolishSpaceBook.EffrosBorelCompact
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-!
# Weak Borel structure and measurable probability families

Open evaluations are lower semicontinuous. The pi-lambda theorem extends their
measurability to all Borel sets. In the other direction, a countable determining
pi-system and Lusin--Suslin suffice on a compact metrizable ambient space. A
Hilbert-cube embedding transfers the result to an arbitrary Polish space.
No Polish-space instance for the space of probabilities on a noncompact space
is assumed.
-/

noncomputable section

namespace PolishSpaceBook.ProbabilityMeasureBorel

open Set Topology TopologicalSpace MeasureTheory MeasurableSpace Function
open scoped ENNReal

section Evaluations

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Y]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    For an open set $U\IncludedIn X$, the evaluation $\mu\mapsto\mu(U)$ is lower semicontinuous by
    the Portmanteau theorem. The Borel sets whose evaluations are Borel form a Dynkin system:
    evaluation at the whole space is constant, complements use $\mu(B^c)=1-\mu(B)$, and disjoint
    countable unions use sums of nonnegative measurable functions. Open sets form a generating
    $\pi$-system, so the $\pi$–$\lambda$ theorem makes every Borel evaluation measurable.
    This proves the forward implication.
-/
/-- The pi-lambda argument extending open evaluation measurability to Borel sets. -/
theorem borel_measurable_toMeasure :
    @Measurable (ProbabilityMeasure X) (Measure X) (borel (ProbabilityMeasure X))
      inferInstance ProbabilityMeasure.toMeasure := by
  let : MeasurableSpace (ProbabilityMeasure X) := borel (ProbabilityMeasure X)
  let : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (S := {U : Set X | IsOpen U})
  · exact BorelSpace.measurable_eq
  · intro U hU V hV _
    exact hU.inter hV
  · intro U hU
    exact (ProkhorovHilbert.open_eval_lowerSemicontinuous hU).measurable

/-- Evaluation on any Borel set is measurable for the weak topology's Borel sets. -/
theorem borel_measurable_eval {B : Set X} (hB : MeasurableSet B) :
    @Measurable (ProbabilityMeasure X) ℝ≥0∞ (borel (ProbabilityMeasure X)) inferInstance
      (fun μ => (μ : Measure X) B) :=
  (Measure.measurable_coe hB).comp borel_measurable_toMeasure

end Evaluations

section Determining

variable (X : Type*) [m : MeasurableSpace X] [CountablyGenerated X]

/-- Finite intersections of a countable generating sequence, including the empty
intersection, form a countable determining pi-system. -/
theorem exists_countable_determining_piSystem :
    ∃ S : Set (Set X), S.Countable ∧ IsPiSystem S ∧ m = MeasurableSpace.generateFrom S := by
  let A : Finset ℕ → Set X := fun s => ⋂ i ∈ s, natGeneratingSequence X i
  refine ⟨range A, countable_range A, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _
    refine ⟨s ∪ t, ?_⟩
    ext x
    simp only [A, mem_iInter, Finset.mem_union, mem_inter_iff]
    aesop
  · apply le_antisymm
    · rw [← generateFrom_natGeneratingSequence (α := X)]
      apply generateFrom_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨{i}, by simp [A]⟩
    · apply generateFrom_le
      rintro _ ⟨s, rfl⟩
      exact MeasurableSet.biInter (Finset.countable_toSet s)
        (fun i _ => measurableSet_natGeneratingSequence (α := X) i)

end Determining

section Compact

variable {H Y : Type*} [MetricSpace H] [CompactSpace H] [MeasurableSpace H]
  [BorelSpace H] [MeasurableSpace Y]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    First prove the converse for the Hilbert cube $H=\HilbertCube$. Choose a countable generating
    $\pi$-system $\Sequence{C_n}{n\in\omega}$ containing $H$, by taking finite intersections of a
    countable Borel generating family together with $H$. The evaluation map
    $$E:\ProbMeasures{H}\to\HilbertCube,\qquad E(\mu)(n)=\mu(C_n)$$
    is Borel by the preceding argument and injective by uniqueness of finite measures on a generating
    $\pi$-system. The weak space $\ProbMeasures{H}$ is compact metrizable, hence Polish.
    Lusin–Suslin therefore makes $E$ a Borel isomorphism onto its Borel image. If all evaluations of
    $k$ are measurable, then $E\circ k$ is measurable, and composing with this inverse proves that $k$ is measurable.
-/
/-- On a compact metric space, countable evaluation coordinates and
Lusin--Suslin recover the weak Borel structure. -/
theorem compact_borel_measurable_iff (p : Y → ProbabilityMeasure H) :
    @Measurable Y (ProbabilityMeasure H) ‹MeasurableSpace Y›
        (borel (ProbabilityMeasure H)) p ↔
      ∀ B : Set H, MeasurableSet B → Measurable (fun y => (p y : Measure H) B) := by
  let : MeasurableSpace (ProbabilityMeasure H) := borel (ProbabilityMeasure H)
  let : BorelSpace (ProbabilityMeasure H) := ⟨rfl⟩
  let := metrizableSpaceMetric (ProbabilityMeasure H)
  have : PolishSpace (ProbabilityMeasure H) := inferInstance
  obtain ⟨S, hSc, hSpi, hSgen⟩ := exists_countable_determining_piSystem H
  let : Countable S := hSc.to_subtype
  let E : ProbabilityMeasure H → S → ℝ≥0∞ := fun μ B => (μ : Measure H) B
  have hE : Measurable E := by
    apply Measurable.of_eval
    intro B
    exact borel_measurable_eval (hSgen ▸ measurableSet_generateFrom B.property)
  have hEi : Injective E := by
    intro μ ν h
    apply ProbabilityMeasure.toMeasure_injective
    apply ext_of_generate_finite S hSgen hSpi
    · intro B hB
      exact congrFun h ⟨B, hB⟩
    · simp
  have hEmb := hE.measurableEmbedding hEi
  constructor
  · intro hp B hB
    exact (borel_measurable_eval hB).comp hp
  · intro hp
    apply hEmb.measurable_comp_iff.mp
    exact Measurable.of_eval (fun B => hp B (hSgen ▸ measurableSet_generateFrom B.property))

end Compact

section Embedding

variable {X H : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace H] [MeasurableSpace H] [BorelSpace H] [SeparableSpace H]

/-- A Borel embedding of the underlying metric spaces induces a Borel embedding
of probability spaces equipped with their weak Borel structures. -/
theorem borel_push_measurableEmbedding (f : X → H) (hf : IsEmbedding f)
    (hR : MeasurableSet (range f)) :
    @MeasurableEmbedding (ProbabilityMeasure X) (ProbabilityMeasure H)
      (borel (ProbabilityMeasure X)) (borel (ProbabilityMeasure H))
      (ProkhorovHilbert.push f hf) := by
  let : MeasurableSpace (ProbabilityMeasure X) := borel (ProbabilityMeasure X)
  let : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
  let : MeasurableSpace (ProbabilityMeasure H) := borel (ProbabilityMeasure H)
  let : BorelSpace (ProbabilityMeasure H) := ⟨rfl⟩
  apply (ProkhorovHilbert.push_isEmbedding f hf hR).measurableEmbedding
  have heq : range (ProkhorovHilbert.push f hf) =
      {ν : ProbabilityMeasure H | (ν : Measure H) (range f) = 1} := by
    ext ν
    exact ProkhorovHilbert.mem_range_push_iff f hf hR ν
  rw [heq]
  exact borel_measurable_eval hR (measurableSet_singleton 1)

end Embedding

section Polish

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: lemma
  title: Measurable families of probability measures
-/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    For general Polish $X$, choose a topological embedding $f:X\to H$ with Borel image.
    The pushforward map $f_*:\ProbMeasures{X}\to\ProbMeasures{H}$ is a topological embedding, as in
    the Hilbert-cube argument for Prokhorov's theorem. Its image is
    $$\{\nu\in\ProbMeasures{H}:\nu(f(X))=1\},$$
    which is Borel by the first paragraph. Thus $\ProbMeasures{X}$ has a standard Borel structure.
    If every evaluation of $k$ is measurable, then every evaluation of $f_*\circ k$ is measurable,
    since $(f_*k(y))(C)=k(y)(f^{-1}(C))$. The compact case makes $f_*\circ k$ measurable, and the
    inverse of the topological embedding on its image makes $k$ measurable.
-/
/-- Weak Borel measurability of a probability family is equivalent to
measurability of every Borel evaluation, for an arbitrary measurable domain. -/
theorem borel_measurable_iff (p : Y → ProbabilityMeasure X) :
    @Measurable Y (ProbabilityMeasure X) ‹MeasurableSpace Y›
        (borel (ProbabilityMeasure X)) p ↔
      ∀ B : Set X, MeasurableSet B → Measurable (fun y => (p y : Measure X) B) := by
  let := metrizableSpaceMetric X
  let : PolishSpace hilbert_cube := hilbert_cube_polish
  let := metrizableSpaceMetric hilbert_cube
  let : MeasurableSpace (ProbabilityMeasure X) := borel (ProbabilityMeasure X)
  let : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
  let : MeasurableSpace (ProbabilityMeasure hilbert_cube) :=
    borel (ProbabilityMeasure hilbert_cube)
  let : BorelSpace (ProbabilityMeasure hilbert_cube) := ⟨rfl⟩
  obtain ⟨f, hf, hR⟩ := exists_hilbert_cube_embedding X
  have hpush := borel_push_measurableEmbedding f hf hR.measurableSet
  constructor
  · intro hp B hB
    exact (borel_measurable_eval hB).comp hp
  · intro hp
    apply hpush.measurable_comp_iff.mp
    apply (compact_borel_measurable_iff _).mpr
    intro B hB
    simpa only [Function.comp_apply, ProkhorovHilbert.push_apply f hf _ hB] using
      hp (f ⁻¹' B) (hf.continuous.measurable hB)

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: proof
  excerpt: |
    The characterization says precisely that the weak Borel structure is generated by all Borel
    evaluations. For a Borel isomorphism $g:X\to X'$, the identity
    $(g_*\mu)(B)=\mu(g^{-1}(B))$ shows that pushforward and its inverse are measurable.
    Choosing any compatible Polish topology on a standard Borel space therefore gives the same
    measurable structure on its probability measures.
-/
/-- The canonical Giry subtype structure is precisely the weak topology's
Borel sigma-algebra. This is a theorem, not an assumed instance. -/
theorem measurableSpace_eq_borel :
    (inferInstance : MeasurableSpace (ProbabilityMeasure X)) = borel (ProbabilityMeasure X) := by
  apply le_antisymm
  · have hm : @Measurable (ProbabilityMeasure X) (ProbabilityMeasure X)
        (borel (ProbabilityMeasure X)) inferInstance id := by
      let := metrizableSpaceMetric X
      exact Measurable.subtype_mk borel_measurable_toMeasure
    simpa only [measurable_iff_comap_le, MeasurableSpace.comap_id] using hm
  · have hm : @Measurable (ProbabilityMeasure X) (ProbabilityMeasure X)
        inferInstance (borel (ProbabilityMeasure X)) id := by
      apply (borel_measurable_iff id).mpr
      intro B hB
      exact (Measure.measurable_coe hB).comp measurable_subtype_coe
    simpa only [measurable_iff_comap_le, MeasurableSpace.comap_id] using hm

/-- The weak Borel space of probability measures on a Polish space is standard
Borel, by its Borel image in the compact Hilbert-cube probability space. -/
theorem weak_standardBorel :
    @StandardBorelSpace (ProbabilityMeasure X) (borel (ProbabilityMeasure X)) := by
  let := metrizableSpaceMetric X
  let : PolishSpace hilbert_cube := hilbert_cube_polish
  let := metrizableSpaceMetric hilbert_cube
  let : MeasurableSpace (ProbabilityMeasure X) := borel (ProbabilityMeasure X)
  let : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
  let : MeasurableSpace (ProbabilityMeasure hilbert_cube) :=
    borel (ProbabilityMeasure hilbert_cube)
  let : BorelSpace (ProbabilityMeasure hilbert_cube) := ⟨rfl⟩
  let := metrizableSpaceMetric (ProbabilityMeasure hilbert_cube)
  have : PolishSpace (ProbabilityMeasure hilbert_cube) := inferInstance
  obtain ⟨f, hf, hR⟩ := exists_hilbert_cube_embedding X
  have he := borel_push_measurableEmbedding f hf hR.measurableSet
  have : StandardBorelSpace (range (ProkhorovHilbert.push f hf)) :=
    he.measurableSet_range.standardBorel
  exact standardBorel_of_measurableEquiv he.equivRange

end Polish

section StandardBorel

variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y]

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    Equivalently, after identifying $\ProbMeasures{X}$ with its standard Borel structure from §{sec:prob-measure-space}, a
    kernel is a Borel map
    $$Y \to \ProbMeasures{X}, \qquad y \mapsto K_y.$$
-/
/-- Transport to a standard Borel space by choosing a compatible Polish topology.
The right side only uses its original measurable structure. -/
theorem standardBorel_measurable_iff (p : Y → ProbabilityMeasure X) :
    letI := upgradeStandardBorel X
    @Measurable Y (ProbabilityMeasure X) ‹MeasurableSpace Y›
        (borel (ProbabilityMeasure X)) p ↔
      ∀ B : Set X, MeasurableSet B → Measurable (fun y => (p y : Measure X) B) := by
  let := upgradeStandardBorel X
  exact borel_measurable_iff p

/-- The canonical probability-measure measurable space over a standard Borel
space is itself standard Borel. -/
theorem probability_standardBorel : StandardBorelSpace (ProbabilityMeasure X) := by
  let := upgradeStandardBorel X
  have h := weak_standardBorel (X := X)
  rwa [← measurableSpace_eq_borel (X := X)] at h

end StandardBorel

section Transport

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

/-- Pushforward along a measurable map is measurable for the canonical
evaluation structures. -/
theorem measurable_probability_map {f : X → Z} (hf : Measurable f) :
    Measurable (fun μ : ProbabilityMeasure X => μ.map f) :=
  Measurable.subtype_mk ((Measure.measurable_map f hf).comp measurable_subtype_coe)

/-- A Borel isomorphism transports probability measures by pushforward. When
compatible Polish topologies are present, `measurableSpace_eq_borel` identifies
both sides here with the Borel structures of their weak topologies. -/
def probabilityMapEquiv (e : X ≃ᵐ Z) : ProbabilityMeasure X ≃ᵐ ProbabilityMeasure Z where
  toFun μ := μ.map e
  invFun ν := ν.map e.symm
  left_inv μ := by
    apply ProbabilityMeasure.toMeasure_injective
    ext B hB
    rw [ProbabilityMeasure.map_apply' _ e.symm.measurable.aemeasurable hB,
      ProbabilityMeasure.map_apply' _ e.measurable.aemeasurable (e.symm.measurable hB)]
    congr 1
    ext x
    simp
  right_inv ν := by
    apply ProbabilityMeasure.toMeasure_injective
    ext B hB
    rw [ProbabilityMeasure.map_apply' _ e.measurable.aemeasurable hB,
      ProbabilityMeasure.map_apply' _ e.symm.measurable.aemeasurable (e.measurable hB)]
    congr 1
    ext x
    simp
  measurable_toFun := measurable_probability_map e.measurable
  measurable_invFun := measurable_probability_map e.symm.measurable

end Transport

section WeakTransport

variable {X Z : Type*} [TopologicalSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Z] [PolishSpace Z]
  [MeasurableSpace Z] [BorelSpace Z]

/-- Pushforward along a Borel isomorphism is a measurable equivalence for the
weak Borel structures, even when the isomorphism is not continuous. -/
def weakProbabilityMapEquiv (e : X ≃ᵐ Z) :
    @MeasurableEquiv (ProbabilityMeasure X) (ProbabilityMeasure Z)
      (borel (ProbabilityMeasure X)) (borel (ProbabilityMeasure Z)) := by
  rw [← measurableSpace_eq_borel (X := X), ← measurableSpace_eq_borel (X := Z)]
  exact probabilityMapEquiv e

end WeakTransport

end PolishSpaceBook.ProbabilityMeasureBorel
