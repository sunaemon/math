module

public import Mathlib.Data.Set.SymmDiff
public import PolishSpaceBook.ProkhorovHilbert
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import PolishSpaceBook.KolmogorovTail
public import PolishSpaceBook.BorelStructure
public import PolishSpaceBook.BorelMeasureRegularity

@[expose] public section

/-!
# Borel measures on Polish spaces

Formalization targets for
`polish-space/src/polish-space-book/borel-measures-polish-spaces.md`.

Formalized here are the statement of Ulam inner regularity, both directions of
Prokhorov compactness in mathlib's canonical tightness formulation, the
compact-space clause for probability measures, Kolmogorov's zero-one law for
an independent sequence of sub-sigma-algebras via the prefix-algebra proof,
and the elementary
symmetric-difference inclusion used in the Hewitt--Savage proof.
`HewittSavage.lean` completes generating-algebra approximation and the
finite-block proof of Hewitt--Savage; `E0Nonsmooth.lean` supplies the fair-coin
nonatomicity and continuous-distribution-function argument used in Chapter 16.

`BorelMeasureRegularity.lean` supplies the two-sided closed/open approximation
and Ulam's intersection of finite ball-closure covers used below.
`LusinContinuity.lean` supplies Lusin's refinement proof, the category analogue,
and the positive-measure nowhere-dense indicator obstruction.
`ClopenMeasureExtension.lean` supplies the compact-clopen premeasure argument,
Caratheodory extension, uniqueness, and measurability of the resulting
probability family for both Borel evaluations and the weak topology.
`ConditionalClopenKernel.lean` factors scalar conditional expectations through
the observation map, normalizes all clopen identities on a common conull set,
and constructs the ambient Borel probability family with its clopen integral
identity. `ConditionalBorelKernel.lean` identifies the two finite measures
for each observation set, extends the identity to all Borel sets, corrects
concentration on the original Borel space, and pulls the probability family
back along its Borel embedding. `DisintegrationFibers.lean` completes the
countable fiber tests, recovers the conditional identity from the theorem's
two conditions, and proves uniqueness on a countable generating pi-system;
it assembles existence and uniqueness for arbitrary standard Borel spaces.
`KolmogorovTail.lean` supplies the prefix pi-system, the complement and disjoint-union
steps extending independence to all generated events, and the infinite-product
coordinate specialization. `TopologicalTail.lean` proves the rectangle lemma
for arbitrary second factors, identifies measurable tail events with finite-prefix
invariance, and proves the topological zero-one law through a finite-prefix box
and its arbitrary tail section. `AtomicMeasureDecomposition.lean` identifies
Boolean atoms with positive-mass points using the countable separating family,
constructs the nonatomic subspace and the weighted powerset of atomic points,
and proves the explicit measure-preserving Boolean product decomposition.
`MaharamInterval.lean` constructs the continuous cdf and its generalized inverse,
proves both pushforward identities, removes the countable set of nontrivial fibers,
and constructs the measure-preserving Borel isomorphism of conull interval subspaces.
`MaharamStandardBorel.lean` transports this construction along the countable-basis
and ternary Cantor embedding and compares any two nonatomic standard probabilities.
`MeasureAlgebraIsomorphism.lean` discards explicit Borel exceptional sets, constructs
the exact conull isomorphism, and proves the induced measure-preserving Boolean
isomorphism with both inverse-image and forward-image formulas.
`MeasureAlgebraMetric.lean` constructs the symmetric-difference metric and proves
that the Maharam maps are isometries. `DyadicMeasureAlgebra.lean` constructs the finite
prefix Boolean algebras, counts their atoms, proves equal splitting and countable
density using finite-coordinate approximation, and transports the construction to
all nonatomic standard probability algebras. `CylinderDisintegration.lean` normalizes
the restriction to each prefix cylinder, proves the finite conditional integral
identity and pointwise uniqueness, and identifies the tail law by cylinder calculations
and the generating-pi-system argument.
`ProkhorovHilbert.lean` supplies the book's Hilbert-cube proof in both directions:
the pushforward embedding, concentration of ambient limit measures, uniform
compact approximation inside opens, and the G-delta intersection construction.
The full Prokhorov--Varadarajan theorem on the complete Levy--Prokhorov metric
is explicitly cited external infrastructure in the book; its compact-space
clause is also recorded below.
-/

namespace PolishSpaceBook

noncomputable section

open Filter MeasureTheory MeasurableSpace ProbabilityTheory Set Topology
open scoped symmDiff

universe u

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: statement
  kind: theorem
  title: Ulam
-/
/-- Every finite Borel measure on a Polish space is inner regular by compact
sets, proved by closed-set regularity and the explicit finite-ball-cover
construction in `BorelMeasureRegularity`. -/
theorem ulam_innerRegular_compact
    {X : Type u} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    μ.InnerRegularWRT (fun s ↦ IsCompact s ∧ IsClosed s) MeasurableSet :=
  BorelMeasureRegularity.innerRegular_compact μ

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    If $X$ is compact, then $\ProbMeasures{X}$ is compact
-/
/-- Probability measures on a compact Borel Hausdorff space form a compact
space in the weak topology. -/
theorem probabilityMeasure_compact_of_compact
    (X : Type u) [MeasurableSpace X] [TopologicalSpace X]
    [T2Space X] [BorelSpace X] [CompactSpace X] :
    CompactSpace (ProbabilityMeasure X) :=
  inferInstance

/-- In a complete second-countable metric Borel space, a family of
probability measures is tight exactly when its closure is compact. -/
theorem prokhorov_compactClosure_iff_tight
    {X : Type u} [MetricSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (Γ : Set (ProbabilityMeasure X)) :
    IsCompact (closure Γ) ↔
      IsTightMeasureSet
        {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ Γ} :=
  ProkhorovHilbert.compactClosure_iff_tight Γ

/-- Kolmogorov's zero-one law for the tail sigma-algebra of an independent
sequence of sub-sigma-algebras, using the book's prefix-algebra proof. -/
theorem kolmogorov_zeroOne
    {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : ℕ → MeasurableSpace Ω)
    (h_le : ∀ n, s n ≤ m) (h_indep : iIndep s μ)
    {A : Set Ω} (hA : MeasurableSet[limsup s atTop] A) :
    μ A = 0 ∨ μ A = 1 :=
  KolmogorovTail.zero_one μ s h_le h_indep
    (by rw [KolmogorovTail.tail_eq_limsup]; exact hA)

/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  target: prose
  excerpt: |
    (S\cap T)\mathbin{\triangle}(S'\cap T')
    \IncludedIn (S\mathbin{\triangle} S')\cup(T\mathbin{\triangle} T')
-/
/-- Symmetric difference of intersections is controlled coordinatewise, the
set-theoretic estimate used in the Hewitt--Savage argument. -/
theorem inter_symmDiff_subset_union_symmDiff
    {α : Type u} (S T S' T' : Set α) :
    (S ∩ T) ∆ (S' ∩ T') ⊆ (S ∆ S') ∪ (T ∆ T') := by
  intro x hx
  simp only [mem_symmDiff, mem_inter_iff, mem_union] at hx ⊢
  tauto

end

end PolishSpaceBook
