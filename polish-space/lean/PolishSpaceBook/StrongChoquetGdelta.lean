module

public import PolishSpaceBook.StrongChoquetCovers
public import PolishSpaceBook.FiniteInverseSystem
public import Mathlib.Topology.GDelta.Basic

@[expose] public section

/-! # A winning strong Choquet strategy yields an ambient G-delta

Point-finiteness gives finite levels over a fixed ambient point. A coherent
branch of those levels determines a legal play. The winning point and the
ambient point lie in the same shrinking balls, so they coincide.
-/
noncomputable section
namespace PolishSpaceBook.StrongChoquetGame
open Set Metric Filter Topology
universe u
variable {Y : Type u} [MetricSpace Y] {X : Set Y} (σ : Strategy X)

def strategyCover : (n : ℕ) → AmbientCover X n
  | 0 => AmbientCover.root
  | n+1 => (strategyCover n).next σ

def coverUnion (n : ℕ) : Set Y := ⋃ i, (strategyCover σ n).region i

theorem coverUnion_open (n : ℕ) : IsOpen (coverUnion σ n) :=
  isOpen_iUnion (strategyCover σ n).region_open

/-- Nodes above y, with the parent projection inherited from the construction. -/
def pointTower (y : Y) : NatInverseSystem.{u} where
  Obj n := {i : (strategyCover σ n).Index // y ∈ (strategyCover σ n).region i}
  step n c := ⟨c.val.1, (strategyCover σ n).next_region_parent σ c.val c.property⟩

variable {σ} {y : Y} (p : (pointTower σ y).Limit)

theorem pointTower_parent (n : ℕ) : (p.val (n+1)).val.1 = (p.val n).val :=
  congrArg Subtype.val (p.property n)

def pathMove (n : ℕ) : Move X := (strategyCover σ n).move (p.val (n+1)).val

/-- The stored finite history is exactly the prefix of the recovered play. -/
theorem path_history (n : ℕ) :
    (strategyCover σ n).history (p.val n).val = (List.range n).map (pathMove p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (strategyCover σ n).history (p.val (n+1)).val.1 ++ [pathMove p n] = _
    rw [pointTower_parent p n, ih, List.range_succ, List.map_append, List.map_singleton]

/-- Parent coherence supplies the legality constraints at every round. -/
theorem path_legal : Legal X σ (pathMove p) := by
  intro n z hz
  have h := (strategyCover σ (n+1)).move_available (p.val (n+2)).val hz
  rw [pointTower_parent p (n+1)] at h
  change z ∈ (σ ((strategyCover σ n).history (p.val (n+1)).val.1) (pathMove p n)).openSet at h
  rw [pointTower_parent p n, path_history p n] at h
  exact h

variable (σ)

/-- The intersection of the open cover unions cannot acquire an extra point. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: proof
  excerpt: |
    Fix $y\in\bigcap_nG_n$. At each level the nodes whose regions contain $y$ form a finite nonempty set, and the
    parent maps preserve these sets. \termuse{König's lemma} gives a coherent sequence of nodes through all levels.
    Their stored histories determine a legal play following $\sigma$. Since the strategy wins, some $z\in X$
    belongs to all of Player I's moves. At round $n$, both $y$ and $z$ lie in the ambient ball used for that move,
    so $d(y,z)\le 2^{-n}$. Hence $y=z\in X$.
-/
theorem cover_inter_subset (hwin : Winning X σ) : (⋂ n, coverUnion σ n) ⊆ X := by
  intro y hy
  let S := pointTower σ y
  let (n : ℕ) : Fintype (S.Obj n) :=
    ((strategyCover σ n).point_finite y (mem_iInter.mp hy n)).fintype
  let (n : ℕ) : Nonempty (S.Obj n) := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (mem_iInter.mp hy n)
    exact ⟨⟨i,hi⟩⟩
  obtain ⟨p⟩ := S.nonempty_limit_of_finite
  obtain ⟨z, hz⟩ := hwin (pathMove p) (path_legal p)
  have hdist (n : ℕ) : dist y z.val ≤ (1/2 : ℝ)^n :=
    (strategyCover σ n).next_region_dist σ (p.val (n+1)).val (p.val (n+1)).property (hz n)
  have hpow : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hzero : dist y z.val ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hpow (Eventually.of_forall hdist)
  have heq : y = z.val := dist_le_zero.mp hzero
  exact heq.symm ▸ z.property

/-- Every metric-space subspace with a winning strong Choquet strategy is G-delta. -/
theorem isGdelta_of_strongChoquet (hX : IsStrongChoquet X) : IsGδ X := by
  obtain ⟨σ,hwin⟩ := hX
  have he : X = ⋂ n, coverUnion σ n := by
    apply Subset.antisymm
    · intro y hy
      apply mem_iInter.mpr
      intro n
      obtain ⟨i,hi⟩ := (strategyCover σ n).covers ⟨y,hy⟩
      exact mem_iUnion.mpr ⟨i,hi⟩
    · exact cover_inter_subset σ hwin
  rw [he]
  exact IsGδ.iInter_of_isOpen (coverUnion_open σ)

end PolishSpaceBook.StrongChoquetGame
