module

public import PolishSpaceBook.EffrosBorel
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Metrizable.Urysohn

@[expose] public section

/-!
# Compact hyperspaces and Effros–Borel standardness

Compact misses are countable unions of complements of open hits. Together with
the finite-hit Vietoris basis this identifies the two measurable structures.
-/

namespace PolishSpaceBook

open Set TopologicalSpace Topology MeasurableSpace

/-- Transport a Polish realization of a measurable space along a measurable
bijection. This supplies the topology, rather than assuming it on the source. -/
theorem standardBorel_of_measurableEquiv {A B : Type*} [mA : MeasurableSpace A]
    [mB : MeasurableSpace B] [StandardBorelSpace B] (e : A ≃ᵐ B) : StandardBorelSpace A := by
  let := upgradeStandardBorel B
  let : TopologicalSpace A := TopologicalSpace.induced e inferInstance
  let : PolishSpace A := e.toEquiv.polishSpace_induced
  have h : borel A = mA := by
    rw [borel_comap, ← eq_borel_upgradeStandardBorel]
    exact e.measurableEmbedding.comap_eq
  let : BorelSpace A := ⟨h.symm⟩
  infer_instance

namespace EffrosBorel

attribute [local instance] measurableSpace

variable {X Y : Type*}

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    Each compact miss is Effros–Borel. Indeed, for compact $K\IncludedIn\hat X$, the set
    $\{\tilde C:\tilde C\cap K=\emptyset\}$ is the union, over $m\ge1$, of the complements of the hit sets for the open
    $1/m$-neighborhoods of $K$. When both sets are nonempty, disjointness gives positive distance by compactness.
    If either set is empty, the same equivalence holds directly. Consequently all members of the countable Vietoris
    basis are Effros–Borel, and every Vietoris open set is Effros–Borel. Conversely, open hits are Vietoris open. Thus the
    two $\sigma$-algebras coincide, so $\ClosedSets{\hat X}$ is standard Borel and $\Phi(\ClosedSets{X})$ is a Borel
    subspace.
-/
/-- For a compact set, avoiding it is witnessed by avoiding one of its
positive-radius open neighborhoods. This includes the empty compact set. -/
theorem miss_eq_iUnion [MetricSpace X] (K : Set X) (hK : IsCompact K) :
    {F : Closeds X | Disjoint (F : Set X) K} =
      ⋃ n : ℕ, (hit (Metric.thickening (1 / ((n : ℝ) + 1)) K))ᶜ := by
  ext F
  simp only [mem_ofPred_eq, mem_iUnion, mem_compl_iff]
  constructor
  · intro h
    obtain ⟨ε, hε, hdisj⟩ := h.symm.exists_thickenings hK F.isClosed
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨n, ?_⟩
    rintro ⟨x, hxF, hxK⟩
    exact Set.disjoint_left.mp hdisj (Metric.thickening_mono hn.le K hxK)
      (Metric.self_subset_thickening hε (F : Set X) hxF)
  · rintro ⟨n, hn⟩
    apply Set.disjoint_left.mpr
    intro x hxF hxK
    exact hn ⟨x, hxF, Metric.self_subset_thickening (by positivity) K hxK⟩

theorem measurable_miss_compact [MetricSpace X] (K : Set X) (hK : IsCompact K) :
    MeasurableSet {F : Closeds X | Disjoint (F : Set X) K} := by
  rw [miss_eq_iUnion K hK]
  exact MeasurableSet.iUnion fun _ => (measurable_hit Metric.isOpen_thickening).compl

/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: prose
  excerpt: |
    The nonempty members of $\ClosedSets{\hat X}$ form a compact Polish \termuse{hyperspace} under the Hausdorff metric;
    adjoining
    $\emptyset$ as an isolated point preserves compactness and Polishness [@Kechris1995, §4.F]. Its topology is the Vietoris
    topology. Fix a countable open basis of $\hat X$. Finite families from this basis give a countable Vietoris basis:
    a closed set must be contained in the union of the chosen basic opens and meet each of them. The containment
    condition is a miss of the compact complement of that union; the other conditions are open hits.
-/
/-- Finite families drawn from a countable basis give a countable Vietoris basis. -/
theorem compacts_secondCountable [TopologicalSpace X] [SecondCountableTopology X] :
    SecondCountableTopology (Compacts X) := by
  obtain ⟨U, hU⟩ := exists_seq_basis X
  exact hU.compacts.secondCountableTopology
    ((countable_ofPred_finite_subset (countable_range U)).image _)

/-- In a compact Hausdorff space, the canonical closed-set and compact-set types
have the same carriers. -/
def compactEquiv [TopologicalSpace X] [CompactSpace X] [T2Space X] : Closeds X ≃ Compacts X where
  toFun F := ⟨F, F.isClosed.isCompact⟩
  invFun K := K.toCloseds
  left_inv _ := Closeds.ext rfl
  right_inv _ := Compacts.ext rfl

/-- The finite-hit Vietoris basis is Effros measurable; its upper condition is
a compact miss and its lower conditions are open hits. -/
theorem compactEquiv_measurable [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] :
    @Measurable (Closeds X) (Compacts X) (measurableSpace X) (borel (Compacts X)) compactEquiv := by
  let : SecondCountableTopology (Compacts X) := compacts_secondCountable
  rw [Compacts.isTopologicalBasis.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro _ ⟨u, ⟨hu, hopen⟩, rfl⟩
  have hupper : MeasurableSet {F : Closeds X | (F : Set X) ⊆ ⋃₀ u} := by
    have h := measurable_miss_compact ((⋃₀ u)ᶜ) (isOpen_sUnion hopen).isClosed_compl.isCompact
    simpa only [disjoint_compl_right_iff_subset] using h
  have hlower : MeasurableSet {F : Closeds X | ∀ U ∈ u, ((F : Set X) ∩ U).Nonempty} := by
    simpa only [ofPred_forall, hit] using MeasurableSet.biInter hu.countable (fun U hU => measurable_hit (hopen U hU))
  exact hupper.inter hlower

/-- Open hit sets are Vietoris open, proving measurability in the other direction. -/
theorem compactEquiv_symm_measurable [MetricSpace X] [CompactSpace X] :
    @Measurable (Compacts X) (Closeds X) (borel (Compacts X)) (measurableSpace X) compactEquiv.symm := by
  let : MeasurableSpace (Compacts X) := borel (Compacts X)
  let : BorelSpace (Compacts X) := ⟨rfl⟩
  apply measurable_iff_hit.mpr
  intro U hU
  exact (Compacts.isOpen_inter_nonempty_of_isOpen hU).measurableSet

/-- The book's comparison of the compact Vietoris hyperspace with the Effros
space, retaining both maps explicitly. -/
def compactMeasurableEquiv [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] :
    @MeasurableEquiv (Closeds X) (Compacts X) (measurableSpace X) (borel (Compacts X)) := by
  letI : MeasurableSpace (Compacts X) := borel (Compacts X)
  exact { toEquiv := compactEquiv
          measurable_toFun := compactEquiv_measurable
          measurable_invFun := compactEquiv_symm_measurable }

/-- The compact ambient hyperspace is standard Borel for its Effros structure. -/
theorem compact_standardBorel [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] :
    StandardBorelSpace (Closeds X) := by
  let : SecondCountableTopology (Compacts X) := compacts_secondCountable
  let : MeasurableSpace (Compacts X) := borel (Compacts X)
  let : BorelSpace (Compacts X) := ⟨rfl⟩
  let := metrizableSpaceMetric (Compacts X)
  let : PolishSpace (Compacts X) := inferInstance
  exact standardBorel_of_measurableEquiv compactMeasurableEquiv

/-- A G-delta embedding into an ambient Effros standard Borel space transfers
standardness through the actual closure map and its Borel range. -/
theorem standardBorel_of_embedding [TopologicalSpace X] [TopologicalSpace Y] [PolishSpace Y]
    [StandardBorelSpace (Closeds Y)] (f : X → Y) (hf : IsEmbedding f) (hG : IsGδ (range f)) :
    StandardBorelSpace (Closeds X) := by
  let : StandardBorelSpace (range (ambientClosure f)) := (measurable_range_ambientClosure f hf hG).standardBorel
  exact standardBorel_of_measurableEquiv (ambientClosureEquiv f hf)

/-- Embed a Polish space as a G-delta in the Hilbert cube, and apply the preceding
construction to its closed subsets. -/
/-@ booklink:
  source: polish-space-book/standard-borel-classification-closed-sets.md
  target: statement
  kind: theorem
  excerpt: |
    For every Polish space $X$, $(\ClosedSets{X}, \text{Effros–Borel})$ is a standard Borel space [@Kechris1995, Theorem 12.6]. \end{theorem*}
-/
theorem standardBorel [TopologicalSpace X] [PolishSpace X] : StandardBorelSpace (Closeds X) := by
  obtain ⟨f, hf, hG⟩ := exists_hilbert_cube_embedding X
  let := metrizableSpaceMetric hilbert_cube
  let : StandardBorelSpace (Closeds hilbert_cube) := compact_standardBorel
  exact standardBorel_of_embedding f hf hG

end EffrosBorel
end PolishSpaceBook
