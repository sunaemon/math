module

public import PolishSpaceBook.StrongChoquetMetric
public import PolishSpaceBook.MetricPointFiniteRefinement

@[expose] public section

/-! # Ambient point-finite covers following a strong Choquet strategy

Each node remembers the finite history and the last available response. The
next cover refines ambient neighborhoods of all strategy responses. Its index
retains the parent and the point used for the next move.
-/
noncomputable section
namespace PolishSpaceBook.StrongChoquetGame
open Set Metric Topology
universe u
variable {Y : Type u} [MetricSpace Y] (X : Set Y)

/-- A cover by ambient open sets, tagged by finite histories of length n. -/
structure AmbientCover (n : ℕ) where
  Index : Type u
  history : Index → List (Move X)
  history_length : ∀ i, (history i).length = n
  available : Index → Set X
  region : Index → Set Y
  region_open : ∀ i, IsOpen (region i)
  region_available : ∀ i, Subtype.val ⁻¹' region i ⊆ available i
  covers : ∀ x : X, ∃ i, x.val ∈ region i
  point_finite : ∀ y ∈ ⋃ i, region i, {i | y ∈ region i}.Finite

namespace AmbientCover
variable {X}

def root : AmbientCover X 0 where
  Index := PUnit
  history := fun _ => []
  history_length := fun _ => rfl
  available := fun _ => univ
  region := fun _ => univ
  region_open := fun _ => isOpen_univ
  region_available := fun _ => subset_univ _
  covers := fun _ => ⟨PUnit.unit, mem_univ _⟩
  point_finite := fun _ _ => Set.toFinite _

variable {n : ℕ} (C : AmbientCover X n)

/-- The point in a parent region determines the next move. -/
abbrev Candidate := Σ i : C.Index, {x : X // x.val ∈ C.region i}

def ambientMove (c : C.Candidate) : Move Y :=
  ⟨c.2.val.val, C.region c.1, C.region_open c.1, c.2.property⟩

def radius (c : C.Candidate) : ℝ := smallBallRadius n (C.ambientMove c)

def move (c : C.Candidate) : Move X where
  point := c.2.val
  openSet := Subtype.val ⁻¹' ball c.2.val.val (C.radius c)
  isOpen := isOpen_ball.preimage continuous_subtype_val
  mem := mem_ball_self (smallBallRadius_spec n (C.ambientMove c)).1

theorem move_available (c : C.Candidate) : (C.move c).openSet ⊆ C.available c.1 := by
  intro z hz
  apply C.region_available c.1
  exact (smallBallRadius_spec n (C.ambientMove c)).2.1 (subset_closure hz)

variable (σ : Strategy X)

/-- Lift the open response from the subspace to an ambient open set. -/
def responseAmbient (c : C.Candidate) : Set Y :=
  (isOpen_induced_iff.mp (σ (C.history c.1) (C.move c)).isOpen).choose

theorem responseAmbient_spec (c : C.Candidate) :
    IsOpen (C.responseAmbient σ c) ∧
      Subtype.val ⁻¹' C.responseAmbient σ c = (σ (C.history c.1) (C.move c)).openSet :=
  (isOpen_induced_iff.mp (σ (C.history c.1) (C.move c)).isOpen).choose_spec

/-- Keep the ambient response inside the controlled ball for this move. -/
def responseRegion (c : C.Candidate) : Set Y :=
  C.responseAmbient σ c ∩ ball c.2.val.val (C.radius c)

theorem responseRegion_open (c : C.Candidate) : IsOpen (C.responseRegion σ c) :=
  (C.responseAmbient_spec σ c).1.inter isOpen_ball

theorem point_mem_responseRegion (c : C.Candidate) : c.2.val.val ∈ C.responseRegion σ c := by
  refine ⟨?_, (C.move c).mem⟩
  have h := (σ (C.history c.1) (C.move c)).mem
  rw [← (C.responseAmbient_spec σ c).2] at h
  exact h

/-- Choose one precise point-finite refinement, retaining the candidate indices. -/
def refinement : C.Candidate → Set Y :=
  (metric_pointFinite_refinement (C.responseRegion σ) (C.responseRegion_open σ)).choose

theorem refinement_spec :
    (∀ c, IsOpen (C.refinement σ c)) ∧
    (∀ c, C.refinement σ c ⊆ C.responseRegion σ c) ∧
    (⋃ c, C.refinement σ c) = ⋃ c, C.responseRegion σ c ∧
    ∀ y ∈ ⋃ c, C.refinement σ c, {c | y ∈ C.refinement σ c}.Finite :=
  (metric_pointFinite_refinement (C.responseRegion σ) (C.responseRegion_open σ)).choose_spec

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: proof
  excerpt: |
    At level zero there is one node with empty history and region $\widehat X$, whose available set is $X$.
    At later nodes the available set is the last strategy response. Suppose the regions at level $n$ cover $X$,
    and the trace on $X$ of each region lies in its available set. For every node $i$ and
    point $x$ in its trace, choose an ambient ball about $x$ contained in that region, with positive radius at most
    $2^{-n}/2$. Its trace is a legal next move by Player I. The strategy responds with an open neighborhood of $x$
    in $X$. Lift this response to an ambient open set and intersect it with the chosen ball, obtaining $W_{i,x}$.
    These sets cover $X$. In their open union, take a locally finite open refinement indexed by the same pairs
    $(i,x)$, each member contained in $W_{i,x}$. Apply §{sec:appendix-metric-paracompactness} in this open metric
    subspace. The refined members
    are the next-level regions, tagged by the extended histories and their parent $i$. Let $G_n$ be the union of
    the regions at level $n$. Each $G_n$ is open and contains $X$, each child region lies in its parent, and only
    finitely many regions at a fixed level contain a given point of $G_n$.
-/
def next : AmbientCover X (n+1) where
  Index := C.Candidate
  history := fun c => C.history c.1 ++ [C.move c]
  history_length := fun c => by simp only [List.length_append, C.history_length, List.length_singleton]
  available := fun c => (σ (C.history c.1) (C.move c)).openSet
  region := C.refinement σ
  region_open := (C.refinement_spec σ).1
  region_available := by
    intro c z hz
    have h := ((C.refinement_spec σ).2.1 c hz).1
    change z ∈ Subtype.val ⁻¹' C.responseAmbient σ c at h
    rwa [(C.responseAmbient_spec σ c).2] at h
  covers := by
    intro x
    obtain ⟨i, hi⟩ := C.covers x
    have h : x.val ∈ ⋃ c, C.responseRegion σ c :=
      mem_iUnion.mpr ⟨⟨i, ⟨x,hi⟩⟩, C.point_mem_responseRegion σ _⟩
    rw [← (C.refinement_spec σ).2.2.1] at h
    exact mem_iUnion.mp h
  point_finite := (C.refinement_spec σ).2.2.2

/-- The next ambient region remains in its tagged parent. -/
theorem next_region_parent (c : (C.next σ).Index) : (C.next σ).region c ⊆ C.region c.1 := by
  intro y hy
  have h := ((C.refinement_spec σ).2.1 c hy).2
  exact (smallBallRadius_spec n (C.ambientMove c)).2.1 (subset_closure h)

/-- A point in a child region and a point in its I-move are uniformly close. -/
theorem next_region_dist (c : (C.next σ).Index) {y : Y} (hy : y ∈ (C.next σ).region c)
    {z : X} (hz : z ∈ (C.move c).openSet) : dist y z.val ≤ (1/2 : ℝ)^n := by
  have hyb := ((C.refinement_spec σ).2.1 c hy).2
  have hz' : dist z.val c.2.val.val < C.radius c := hz
  have hy' : dist y c.2.val.val < C.radius c := hyb
  calc
    dist y z.val ≤ dist y c.2.val.val + dist c.2.val.val z.val := dist_triangle _ _ _
    _ ≤ 2 * C.radius c := by rw [dist_comm c.2.val.val]; linarith
    _ ≤ _ := (smallBallRadius_spec n (C.ambientMove c)).2.2

end AmbientCover
end PolishSpaceBook.StrongChoquetGame
