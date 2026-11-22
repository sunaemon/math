module

public import PolishSpaceBook.AnalyticSetsSuslinSchemes
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Baire.BaireMeasurable

@[expose] public section

/-!
# Separation, uniformization, and Lusin-Suslin

Formalization targets for
`polish-space/src/polish-space-book/separation-uniformization-lusin-souslin.md`.

Formalized here are the Baire-property definition, Lusin separation and its
Suslin-theorem consequence, the definition of uniformization, the corrected
open-refinement step in the Jankov--von Neumann construction, countable-union
closure of analytic sets, and both forms of the Lusin--Suslin statement.

The early separation API uses mathlib's theorem. Its rank proof is now
formalized separately in `LusinRankSeparation`: the metric neighborhood tree,
Borel indicator coding, convergence of branch witnesses, direct Borel recursion
on countable ordinal bounds, and the previously constructed joint-tree bound.
The direct rank-layer recursion avoids using Suslin's theorem in this implication.
The separated-prefix proof of Lusin--Suslin is supplied by
`LusinSuslinPrefixTests`, `LusinSuslinPrefixImage`, and `LusinSuslinRefinement`:
levelwise separation, finite disjointification, prefix compatibility, the metric
image formula, the cylinder-based inverse, and Borel-domain refinement.
`JankovVonNeumannSelection` and `JankovVonNeumannUniformization` complete
Jankov--von Neumann: least-index decisions, their measurable finite histories,
Cauchy limits in closed sections, and open-preimage measurability.
`UniformizationFromBorelGraphs` derives the partial Borel maps and their union
from the cited Lusin--Novikov decomposition. The decomposition itself remains
an external theorem, as declared in the book.
`KondoUniformization` and its construction modules prove the local scale-based
argument for Kondo uniformization. Scale existence and norm-comparison machinery
remain cited inputs, as do the projective hierarchy and regularity survey.
-/

namespace PolishSpaceBook

noncomputable section

universe u v

open Function MeasureTheory Set Topology
open scoped symmDiff

section BaireProperty

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Let $A$ be a subset of a topological space $X$. The set $A$ has the \termdefine{Baire property} if there is an open
    set
    $U\IncludedIn X$ such that
    $$
    (\SetDifference{A}{U})\cup(\SetDifference{U}{A})
    $$
    is \termuseas{meager set}{meager}. Equivalently, $A$ differs from an open set by a meager set.
-/
/-- The property of Baire, using mathlib's equivalent Borel-modulo-meagre
definition. -/
abbrev HasBaireProperty {X : Type u} [TopologicalSpace X] (A : Set X) : Prop :=
  BaireMeasurableSet A

/-- A set has the Baire property exactly when it differs from an open set by a
meagre set. -/
theorem hasBaireProperty_iff_exists_open_meagre
    {X : Type u} [TopologicalSpace X] {A : Set X} :
    HasBaireProperty A ↔ ∃ U : Set X, IsOpen U ∧ IsMeagre (A ∆ U) := by
  change BaireMeasurableSet A ↔ ∃ U : Set X, IsOpen U ∧ IsMeagre (A ∆ U)
  rw [BaireMeasurableSet.iff_residualEq_isOpen]
  apply exists_congr
  intro U
  refine and_congr_right fun _hU => ?_
  rw [IsMeagre, Filter.eventuallyEqSet_iff]
  change {x | x ∈ A ↔ x ∈ U} ∈ residual X ↔ (A ∆ U)ᶜ ∈ residual X
  have hsets : {x | x ∈ A ↔ x ∈ U} = (A ∆ U)ᶜ := by
    ext x
    simp only [mem_ofPred_eq, mem_compl_iff, mem_symmDiff]
    tauto
  rw [hsets]

end BaireProperty

section Separation

variable {X : Type u} [TopologicalSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: statement
  kind: theorem
  title: Lusin separation
-/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    two disjoint
    analytic sets can still be pulled apart by a Borel set.
-/
/-- Lusin separation for disjoint analytic subsets of a Polish space. -/
theorem lusinSeparation {A₀ A₁ : Set X}
    (hA₀ : AnalyticSet A₀) (hA₁ : AnalyticSet A₁) (hdisj : Disjoint A₀ A₁) :
    ∃ B : Set X, A₀ ⊆ B ∧ B ⊆ A₁ᶜ ∧ MeasurableSet B := by
  rcases hA₀.measurablySeparable hA₁ hdisj with ⟨B, hA₀B, hA₁B, hB⟩
  exact ⟨B, hA₀B, hA₁B.le_compl_left, hB⟩

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Equivalently, disjoint analytic sets are \termdefine{Borel separable}.
-/
/-- Measurable separation, called Borel separation when the measurable space
is the Borel sigma-algebra. -/
abbrev BorelSeparable (A₀ A₁ : Set X) : Prop :=
  MeasurablySeparable A₀ A₁

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    The theorem supplies the separation step in the proof of \termuse{Suslin's theorem} from §{sec:analytic-sets}. If
    $A$ is
    both analytic and coanalytic, then $A$ and $\SetDifference{X}{A}$ are disjoint analytic sets; separating $A$ from
    $\SetDifference{X}{A}$ gives a Borel set squeezed between them, hence exactly $A$.
-/
/-- Suslin's theorem follows immediately from Lusin separation. -/
theorem suslin_measurable_of_analytic_compl {A : Set X}
    (hA : AnalyticSet A) (hAc : AnalyticSet Aᶜ) : MeasurableSet A :=
  hA.measurableSet_of_compl hAc

end Separation

section Uniformization

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    For $A\IncludedIn X\times Y$, a map $u:\pi_X(A)\to Y$ uniformizes $A$ if
    $$
    (x,u(x))\in A \qquad (x\in\pi_X(A)).
    $$
-/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Projection loses witnesses: from $x\in\pi_X(A)$ one knows only that some $y$ satisfies $(x,y)\in A$. A
    \termdefine{uniformization} restores witnesses by choosing one such $y$ for each $x$ in the projection.
-/
/-- A function on the first projection uniformizes a relation when its graph
lies in that relation. -/
def Uniformizes {X : Type u} {Y : Type v} (A : Set (X × Y))
    (u : (Prod.fst '' A) → Y) : Prop :=
  ∀ x, (x.1, u x) ∈ A

variable {Z : Type u} [PseudoMetricSpace Z]

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    Such a $W_i$ exists: choose $z^*\in C_x\cap U_n(x)$ and then use the refinement property to find an eligible $W_i$
    containing $z^*$.
-/
/-- If an open refinement covers each point of `U`, a member meeting `C ∩ U`
also meets `C`; this is the corrected inductive existence step. -/
theorem exists_refinement_meeting
    {C U : Set Z} {ε : ℝ} {V : ℕ → Set Z}
    (hCU : (C ∩ U).Nonempty)
    (hrefine : ∀ z ∈ U, ∃ i, z ∈ V i ∧ closure (V i) ⊆ U ∧ Metric.diam (V i) < ε) :
    ∃ i, closure (V i) ⊆ U ∧ Metric.diam (V i) < ε ∧ (C ∩ V i).Nonempty := by
  rcases hCU with ⟨z, hzC, hzU⟩
  rcases hrefine z hzU with ⟨i, hzV, hiU, hiε⟩
  exact ⟨i, hiU, hiε, z, hzC, hzV⟩

end Uniformization

section AnalyticUnions

variable {X : Type u} [TopologicalSpace X]

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    is analytic: countable unions of analytic sets are analytic, as one sees by presenting each summand as a continuous
    image of a Polish space and taking their countable disjoint sum.
-/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Fix an injective numbering $\iota:\finseq{\omega}\to\omega$ of finite sequences. For each $s$, the union
    $$\bigcup_{\substack{|t|=|s|\\t\ne s}}A_t
-/
/-- Countable unions of analytic sets are analytic. -/
theorem analyticSet_iUnion {A : ℕ → Set X} (hA : ∀ n, AnalyticSet (A n)) :
    AnalyticSet (⋃ n, A n) := by
  choose Z tZ hZ f hf hr using fun n => (analyticSet_iff_continuous_image_polish (A n)).mp (hA n)
  let : ∀ n, TopologicalSpace (Z n) := tZ
  let : ∀ n, PolishSpace (Z n) := hZ
  let : PolishSpace (Sigma Z) := countable_disjoint_union_polish
  let g : Sigma Z → X := fun z => f z.1 z.2
  have hg : Continuous g := continuous_sigma hf
  have heq : range g = ⋃ n, A n := by
    ext x
    constructor
    · rintro ⟨⟨n, z⟩, rfl⟩
      exact mem_iUnion.mpr ⟨n, hr n ▸ mem_range_self z⟩
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      obtain ⟨z, rfl⟩ := (hr n).symm ▸ hn
      exact ⟨⟨n, z⟩, rfl⟩
  rw [← heq]
  exact analyticSet_range_via_baire_surjection hg

end AnalyticUnions

section LusinSuslin

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: statement
  kind: theorem
  title: Lusin–Suslin
-/
/-- The Borel-map form of Lusin--Suslin. A measurable embedding packages
measurability and injectivity together with Borelness of all Borel images, and
hence the measurable inverse on the range. -/
theorem lusinSuslin {f : X → Y} {B : Set X}
    (hB : MeasurableSet B) (hf : Measurable f) (hinj : InjOn f B) :
    MeasurableSet (f '' B) ∧ MeasurableEmbedding (B.domRestrict f) := by
  refine ⟨hB.image_of_measurable_injOn hf hinj, ?_⟩
  let : StandardBorelSpace B := hB.standardBorel
  have hfB : Measurable (B.domRestrict f) :=
    hf.comp (MeasurableEmbedding.subtype_coe hB).measurable
  exact hfB.measurableEmbedding (injOn_iff_injective.mp hinj)

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: statement
  kind: corollary
  title: Continuous form
-/
/-- The continuous-injection form of Lusin--Suslin. -/
theorem continuous_injective_measurableEmbedding {f : X → Y}
    (hf : Continuous f) (hinj : Injective f) :
    MeasurableSet (range f) ∧ MeasurableEmbedding f :=
  ⟨measurableSet_range_of_continuous_injective hf hinj, hf.measurableEmbedding hinj⟩

end LusinSuslin

end

end PolishSpaceBook
