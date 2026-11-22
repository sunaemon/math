module

public import PolishSpaceBook.CantorBaireSpace

@[expose] public section

/-!
# Locally compact decomposition

Auxiliary results about the locally compact locus of a topological space.
These are kept separate from the Cantor/Baire chapter because they are
background infrastructure for possible mixed-case classification statements,
not part of the book proof formalized there.
-/

namespace PolishSpaceBook

universe u

open Set TopologicalSpace Topology

/-- The locally compact part: points that have a compact ambient neighborhood. -/
def locallyCompactPart (X : Type*) [TopologicalSpace X] : Set X :=
  {x | ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x}

/-- The nowhere locally compact part, as an ambient complement. -/
def nowhereLocallyCompactPart (X : Type*) [TopologicalSpace X] : Set X :=
  (locallyCompactPart X)ᶜ

theorem mem_locallyCompactPart {X : Type u} [TopologicalSpace X] {x : X} :
    x ∈ locallyCompactPart X ↔ ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x :=
  Iff.rfl

theorem mem_nowhereLocallyCompactPart {X : Type u} [TopologicalSpace X] {x : X} :
    x ∈ nowhereLocallyCompactPart X ↔ ¬ ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x :=
  Iff.rfl

theorem isOpen_locallyCompactPart (X : Type u) [TopologicalSpace X] :
    IsOpen (locallyCompactPart X) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with ⟨K, hK_compact, hK_nhds⟩
  rcases mem_nhds_iff.mp hK_nhds with ⟨U, hUK, hU_open, hxU⟩
  refine mem_nhds_iff.mpr ⟨U, ?_, hU_open, hxU⟩
  intro y hyU
  exact ⟨K, hK_compact, Filter.mem_of_superset (hU_open.mem_nhds hyU) hUK⟩

theorem isClosed_nowhereLocallyCompactPart (X : Type u) [TopologicalSpace X] :
    IsClosed (nowhereLocallyCompactPart X) := by
  simpa [nowhereLocallyCompactPart] using (isOpen_locallyCompactPart X).isClosed_compl

theorem locallyCompactPart_disjoint_nowhereLocallyCompactPart
    (X : Type u) [TopologicalSpace X] :
    Disjoint (locallyCompactPart X) (nowhereLocallyCompactPart X) := by
  rw [nowhereLocallyCompactPart]
  exact disjoint_compl_right

theorem locallyCompactPart_union_nowhereLocallyCompactPart
    (X : Type u) [TopologicalSpace X] :
    locallyCompactPart X ∪ nowhereLocallyCompactPart X = (Set.univ : Set X) := by
  simp [nowhereLocallyCompactPart]

theorem noCompactNeighborhoods_open_subtype_of_subset_nowhereLocallyCompactPart
    {X : Type u} [TopologicalSpace X] {s : Set X}
    (hs : IsOpen s) (hsub : s ⊆ nowhereLocallyCompactPart X) :
    NoCompactNeighborhoods s := by
  intro x hcompact
  rcases hcompact with ⟨K, hK_compact, hK_nhds⟩
  have hK_image_compact : IsCompact (((↑) : s → X) '' K) :=
    hK_compact.image continuous_subtype_val
  have hK_image_nhdsWithin : (((↑) : s → X) '' K) ∈ 𝓝[s] (x : X) :=
    (mem_nhds_subtype_iff_nhdsWithin (s := s) (a := x) (t := K)).mp hK_nhds
  have hK_image_nhds : (((↑) : s → X) '' K) ∈ 𝓝 (x : X) := by
    simpa [hs.nhdsWithin_eq x.2] using hK_image_nhdsWithin
  exact (hsub x.2) ⟨_, hK_image_compact, hK_image_nhds⟩

theorem noCompactNeighborhoods_nowhereLocallyCompactPart_of_isOpen
    {X : Type u} [TopologicalSpace X] (hopen : IsOpen (nowhereLocallyCompactPart X)) :
    NoCompactNeighborhoods (nowhereLocallyCompactPart X) :=
  noCompactNeighborhoods_open_subtype_of_subset_nowhereLocallyCompactPart hopen Subset.rfl

theorem noCompactNeighborhoods_interior_nowhereLocallyCompactPart
    (X : Type u) [TopologicalSpace X] :
    NoCompactNeighborhoods (interior (nowhereLocallyCompactPart X)) :=
  noCompactNeighborhoods_open_subtype_of_subset_nowhereLocallyCompactPart
    isOpen_interior interior_subset

theorem locallyCompactPart_weaklyLocallyCompactSpace
    (X : Type u) [MetricSpace X] :
    WeaklyLocallyCompactSpace (locallyCompactPart X) where
  exists_compact_mem_nhds x := by
    rcases x.2 with ⟨K, hK_compact, hK_nhds⟩
    have hx_lc : (x : X) ∈ locallyCompactPart X := x.2
    have htarget_nhds : K ∩ locallyCompactPart X ∈ 𝓝 (x : X) :=
      Filter.inter_mem hK_nhds ((isOpen_locallyCompactPart X).mem_nhds hx_lc)
    rcases Metric.mem_nhds_iff.mp htarget_nhds with ⟨ε, hε_pos, hε_subset⟩
    let C : Set (locallyCompactPart X) :=
      {y | (y : X) ∈ Metric.closedBall (x : X) (ε / 2)}
    have hclosed_subset :
        Metric.closedBall (x : X) (ε / 2) ⊆ K ∩ locallyCompactPart X :=
      (Metric.closedBall_subset_ball (half_lt_self hε_pos)).trans hε_subset
    have hclosed_compact : IsCompact (Metric.closedBall (x : X) (ε / 2)) :=
      hK_compact.of_isClosed_subset Metric.isClosed_closedBall
        (fun y hy => (hclosed_subset hy).1)
    have hC_image :
        ((↑) : locallyCompactPart X → X) '' C =
          Metric.closedBall (x : X) (ε / 2) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, (hclosed_subset hy).2⟩, hy, rfl⟩
    have hC_compact : IsCompact C := by
      rw [Subtype.isCompact_iff, hC_image]
      exact hclosed_compact
    have hC_nhds : C ∈ 𝓝 x := by
      simpa [C, Metric.closedBall, Subtype.dist_eq] using
        (continuous_subtype_val.continuousAt
          (Metric.closedBall_mem_nhds (x : X) (half_pos hε_pos)))
    exact ⟨C, hC_compact, hC_nhds⟩

theorem locallyCompactPart_polish
    (X : Type u) [TopologicalSpace X] [PolishSpace X] :
    PolishSpace (locallyCompactPart X) :=
  open_subspace_polish (isOpen_locallyCompactPart X)

theorem nowhereLocallyCompactPart_polish
    (X : Type u) [TopologicalSpace X] [PolishSpace X] :
    PolishSpace (nowhereLocallyCompactPart X) :=
  (isClosed_nowhereLocallyCompactPart X).polishSpace

theorem locallyCompactPart_decomposition (X : Type u) [TopologicalSpace X] :
    IsOpen (locallyCompactPart X) ∧
      IsClosed (nowhereLocallyCompactPart X) ∧
        Disjoint (locallyCompactPart X) (nowhereLocallyCompactPart X) ∧
          locallyCompactPart X ∪ nowhereLocallyCompactPart X = (Set.univ : Set X) ∧
            ∀ {s : Set X}, IsOpen s → s ⊆ nowhereLocallyCompactPart X →
              NoCompactNeighborhoods s := by
  refine ⟨isOpen_locallyCompactPart X, isClosed_nowhereLocallyCompactPart X,
    locallyCompactPart_disjoint_nowhereLocallyCompactPart X,
    locallyCompactPart_union_nowhereLocallyCompactPart X, ?_⟩
  intro s hs hsub
  exact noCompactNeighborhoods_open_subtype_of_subset_nowhereLocallyCompactPart hs hsub

theorem open_subspace_alexandrov_urysohn_hypotheses_of_subset_nowhereLocallyCompactPart
    {X : Type u} [TopologicalSpace X] {s : Set X}
    (hs : IsOpen s) [PerfectSpace X] (hzero : IsZeroDimensional X)
    (hsub : s ⊆ nowhereLocallyCompactPart X) :
    PerfectSpace s ∧ IsZeroDimensional s ∧ NoCompactNeighborhoods s := by
  exact ⟨perfectSpace_open_subtype hs, zeroDimensional_subtype s hzero,
    noCompactNeighborhoods_open_subtype_of_subset_nowhereLocallyCompactPart hs hsub⟩

end PolishSpaceBook
