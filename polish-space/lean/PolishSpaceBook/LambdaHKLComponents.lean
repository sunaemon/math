module

public import PolishSpaceBook.LambdaCatalogTreeRefinement
public import PolishSpaceBook.LambdaHKLRefinement
public import PolishSpaceBook.HKLCompatibleRefinements

@[expose] public section

/-!
# Relative HKL component gluing and the rectangular stage

Each component carries relative codes in the same fixed parameter. Exact
node refinements propagate separately in the two trees. Equal saturations
restore the full joining edge, whose code is obtained by intersections.
Rectangle density is used only in the actual parameter catalog, and the
actual kernel supplies disjointness without a distinct-pair assumption.
-/

namespace PolishSpaceBook
namespace LambdaTree
open Set SimpleGraph

/-- The full bridge is coded in the same parameter as its relation and endpoints. -/
theorem projected_fullERBetween {ε : ℕ → ℕ} (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r) {A B : Set FusionReal}
    (hA : Projected ε A) (hB : Projected ε B) :
    ProjectedPairs ε (fullERBetween E A B) :=
  hA.leftPreimage.inter (hB.rightPreimage.inter hE)

structure ParameterSplitTree (ε : ℕ → ℕ) {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (a : V) (b : W) (E : Setoid FusionReal) where
  left : ParameterTreeSystem ε G
  right : ParameterTreeSystem ε H
  leftIn : left.val.EdgesIn E
  rightIn : right.val.EdgesIn E
  compatible : erSaturation E (left.val.node a) = erSaturation E (right.val.node b)

namespace ParameterSplitTree
variable {ε : ℕ → ℕ} {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  {a : V} {b : W} {E : Setoid FusionReal}

def joined (S : ParameterSplitTree ε G H a b E)
    (hE : ProjectedRelation ε E.r) :
    ParameterTreeSystem ε (joinedTreeGraph G H a b) := by
  let hEa := ProjectedPairs.analyticSet
    (P := {p : FusionReal × FusionReal | E.r p.1 p.2}) hE
  refine ⟨joinedTreeSystem S.left.val S.right.val a b E hEa S.compatible, ?_, ?_⟩
  · intro v
    cases v with
    | inl v => exact S.left.property.1 v
    | inr v => exact S.right.property.1 v
  · intro u v huv
    cases u with
    | inl u =>
      cases v with
      | inl v => exact S.left.property.2 u v ((joinedTreeGraph_inl a b u v).mp huv)
      | inr v => exact projected_fullERBetween E hE (S.left.property.1 u) (S.right.property.1 v)
    | inr u =>
      cases v with
      | inl v => exact projected_fullERBetween E hE (S.right.property.1 u) (S.left.property.1 v)
      | inr v => exact S.right.property.2 u v ((joinedTreeGraph_inr a b u v).mp huv)

theorem joined_edgesIn (S : ParameterSplitTree ε G H a b E)
    (hE : ProjectedRelation ε E.r) :
    (S.joined hE).val.EdgesIn E :=
  joinedTreeSystem_edgesIn S.left.val S.right.val a b E
    (ProjectedPairs.analyticSet (P := {p : FusionReal × FusionReal | E.r p.1 p.2}) hE)
    S.compatible S.leftIn S.rightIn

def Refines (T S : ParameterSplitTree ε G H a b E) : Prop :=
  T.left.val.Refines S.left.val ∧ T.right.val.Refines S.right.val

theorem Refines.refl (S : ParameterSplitTree ε G H a b E) : S.Refines S :=
  ⟨.refl _, .refl _⟩

theorem Refines.trans {R T S : ParameterSplitTree ε G H a b E}
    (hRT : R.Refines T) (hTS : T.Refines S) : R.Refines S :=
  ⟨hRT.1.trans hTS.1, hRT.2.trans hTS.2⟩

theorem Refines.joined {T S : ParameterSplitTree ε G H a b E}
    (hTS : T.Refines S) (hE : ProjectedRelation ε E.r) :
    (T.joined hE).val.Refines (S.joined hE).val :=
  joinedTreeSystem_refines hTS.1 hTS.2 a b E
    (ProjectedPairs.analyticSet (P := {p : FusionReal × FusionReal | E.r p.1 p.2}) hE)
    S.compatible T.compatible

def rectangle (S : ParameterSplitTree ε G H a b E)
    (hG : G.Connected) (hH : H.Connected) (r : V) (s : W) : ParameterCompatibleRectangle ε E :=
  ⟨(S.left.nodeCondition r, S.right.nodeCondition s), by
    change erSaturation E (S.left.val.node r) = erSaturation E (S.right.val.node s)
    rw [S.left.val.saturation_eq hG E S.leftIn r a,
      S.right.val.saturation_eq hH E S.rightIn s b]
    exact S.compatible⟩

theorem Refines.rectangle_le {T S : ParameterSplitTree ε G H a b E}
    (hTS : T.Refines S) (hG : G.Connected) (hH : H.Connected) (r : V) (s : W) :
    T.rectangle hG hH r s ≤ S.rectangle hG hH r s :=
  ⟨hTS.1.1 r, hTS.2.1 s⟩

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Propagate these two changes separately through
    the two components. Within either component, every edge lies in $E$ and has full projections, so all the resulting
    node sets have the saturation of the chosen starting set. The two starting sets had equal saturations. Hence the
    new endpoint sets at the joining edge still have equal saturations, and the full $E$-relation between them has full
    projections. Restoring that full relation is a restriction of the old joining relation. This proves that the two
    propagations are compatible.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Next handle every ordered pair of nodes with different last bits. Removing the joining edge separates these two
    nodes. Their rectangle is a condition in $\RestrictedGHProduct{E}$, so choose a refinement into $J_{n+1}$; apply
    disjoint compatible refinements to its two coordinates as well.
-/
/-- Propagate the prescribed endpoints along their separate trees, then
use equality of saturations to restore the full bridge. -/
theorem refine_rectangle (S : ParameterSplitTree ε G H a b E)
    (hG : G.IsTree) (hH : H.IsTree) (r : V) (s : W)
    (Q : ParameterCompatibleRectangle ε E)
    (hQ : Q ≤ S.rectangle hG.connected hH.connected r s) :
    ∃ T : ParameterSplitTree ε G H a b E, T.Refines S ∧
      T.rectangle hG.connected hH.connected r s = Q := by
  obtain ⟨L, hLS, hLr, _⟩ := S.left.refine_node hG r Q.val.1 hQ.1
  obtain ⟨R, hRS, hRs, _⟩ := S.right.refine_node hH s Q.val.2 hQ.2
  have heL : L.val.node r = Q.val.1.val.val :=
    congrArg (fun C : (parameterAnalyticCatalog ε).Condition => C.val.val) hLr
  have heR : R.val.node s = Q.val.2.val.val :=
    congrArg (fun C : (parameterAnalyticCatalog ε).Condition => C.val.val) hRs
  have hc : erSaturation E (L.val.node a) = erSaturation E (R.val.node b) := by
    rw [L.val.saturation_eq hG.connected E (hLS.edgesIn S.leftIn) a r,
      R.val.saturation_eq hH.connected E (hRS.edgesIn S.rightIn) b s, heL, heR]
    exact Q.property
  let T : ParameterSplitTree ε G H a b E :=
    ⟨L, R, hLS.edgesIn S.leftIn, hRS.edgesIn S.rightIn, hc⟩
  refine ⟨T, ⟨hLS, hRS⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext hLr hRs

/-- Meet a relative dense rectangle family and split the node sets using the
proved kernel lemma. Shrinking preserves membership in the lower family. -/
theorem refine_dense_disjoint_rectangle (S : ParameterSplitTree ε G H a b E)
    (hG : G.IsTree) (hH : H.IsTree)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (r : V) (s : W) (J : Set (ParameterCompatibleRectangle ε E))
    (hJd : IsCoinitial J) (hJl : IsLowerSet J)
    (hkernel : S.left.val.node r ⊆ equivalenceGapKernel E (invariantSetoid ε E)) :
    ∃ T : ParameterSplitTree ε G H a b E, T.Refines S ∧
      T.rectangle hG.connected hH.connected r s ∈ J ∧
      Disjoint (T.left.val.node r) (T.right.val.node s) := by
  obtain ⟨Q, hQJ, hQS⟩ := hJd (S.rectangle hG.connected hH.connected r s)
  obtain ⟨P, hPQ, hdisj⟩ := Q.disjoint_refinement hE hneE (fun x hx => hkernel (hQS.1 hx))
  obtain ⟨T, hTS, hTP⟩ := S.refine_rectangle hG hH r s P (hPQ.trans hQS)
  refine ⟨T, hTS, hTP.symm ▸ hJl hPQ hQJ, ?_⟩
  have heL := congrArg (fun q : ParameterCompatibleRectangle ε E => q.val.1.val.val) hTP
  have heR := congrArg (fun q : ParameterCompatibleRectangle ε E => q.val.2.val.val) hTP
  change T.left.val.node r = P.val.1.val.val at heL
  change T.right.val.node s = P.val.2.val.val at heR
  rwa [heL, heR]

/-- Process finitely many pairs; lower dense requirements and disjointness
survive the subsequent component refinements. -/
theorem refine_finite_dense_disjoint_rectangles (S : ParameterSplitTree ε G H a b E)
    (hG : G.IsTree) (hH : H.IsTree)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (F : Finset (V × W)) (J : Set (ParameterCompatibleRectangle ε E))
    (hJd : IsCoinitial J) (hJl : IsLowerSet J)
    (hkernel : ∀ r, S.left.val.node r ⊆ equivalenceGapKernel E (invariantSetoid ε E)) :
    ∃ T : ParameterSplitTree ε G H a b E, T.Refines S ∧
      ∀ p ∈ F, T.rectangle hG.connected hH.connected p.1 p.2 ∈ J ∧
        Disjoint (T.left.val.node p.1) (T.right.val.node p.2) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨S, .refl S, by simp⟩
  | @insert p F hp ih =>
    obtain ⟨T, hTS, hTF⟩ := ih
    obtain ⟨U, hUT, hUp, hUd⟩ := T.refine_dense_disjoint_rectangle hG hH hE hneE
      p.1 p.2 J hJd hJl ((hTS.1.1 p.1).trans (hkernel p.1))
    refine ⟨U, hUT.trans hTS, ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ⟨hUp, hUd⟩
    · exact ⟨hJl (hUT.rectangle_le hG.connected hH.connected q.1 q.2) (hTF q hq).1,
        (hTF q hq).2.mono (hUT.1.1 q.1) (hUT.2.1 q.2)⟩

end ParameterSplitTree

namespace ParameterCompatibleRectangle
variable {ε : ℕ → ℕ} {E : Setoid FusionReal}

def swap (P : ParameterCompatibleRectangle ε E) : ParameterCompatibleRectangle ε E :=
  ⟨(P.val.2, P.val.1), P.property.symm⟩

@[simp] theorem swap_swap (P : ParameterCompatibleRectangle ε E) : P.swap.swap = P := rfl

def bothOrientations (J : Set (ParameterCompatibleRectangle ε E)) := J ∩ swap ⁻¹' J

theorem bothOrientations_lower {J : Set (ParameterCompatibleRectangle ε E)}
    (hJl : IsLowerSet J) : IsLowerSet (bothOrientations J) := by
  intro Q P hPQ hQ
  exact ⟨hJl hPQ hQ.1, hJl (show P.swap ≤ Q.swap from ⟨hPQ.2, hPQ.1⟩) hQ.2⟩

theorem bothOrientations_coinitial {J : Set (ParameterCompatibleRectangle ε E)}
    (hJd : IsCoinitial J) (hJl : IsLowerSet J) : IsCoinitial (bothOrientations J) := by
  intro P
  obtain ⟨Q, hQJ, hQP⟩ := hJd P
  obtain ⟨R, hRJ, hRQ⟩ := hJd Q.swap
  have hTQ : R.swap ≤ Q := ⟨hRQ.2, hRQ.1⟩
  exact ⟨R.swap, ⟨hJl hTQ hQJ, hRJ⟩, hTQ.trans hQP⟩

end ParameterCompatibleRectangle

namespace ParameterSplitTree
variable {ε : ℕ → ℕ} {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  {a : V} {b : W} {E : Setoid FusionReal}

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Repeat for the finitely many pairs. Downward closure preserves all earlier dense
    requirements and all earlier disjointness requirements.
-/
/-- The entire finite rectangular stage, in both orientations, uses only
relative catalog density and the actual kernel's proved splitting property. -/
theorem refine_all_dense_disjoint_rectangles [Fintype V] [Fintype W]
    (S : ParameterSplitTree ε G H a b E) (hG : G.IsTree) (hH : H.IsTree)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (J : Set (ParameterCompatibleRectangle ε E)) (hJd : IsCoinitial J) (hJl : IsLowerSet J)
    (hkernel : ∀ r, S.left.val.node r ⊆ equivalenceGapKernel E (invariantSetoid ε E)) :
    ∃ T : ParameterSplitTree ε G H a b E, T.Refines S ∧
      ∀ r s, T.rectangle hG.connected hH.connected r s ∈ J ∧
        (T.rectangle hG.connected hH.connected r s).swap ∈ J ∧
        Disjoint (T.left.val.node r) (T.right.val.node s) := by
  obtain ⟨T, hTS, hTF⟩ := S.refine_finite_dense_disjoint_rectangles hG hH hE hneE Finset.univ
    (ParameterCompatibleRectangle.bothOrientations J)
    (ParameterCompatibleRectangle.bothOrientations_coinitial hJd hJl)
    (ParameterCompatibleRectangle.bothOrientations_lower hJl) hkernel
  refine ⟨T, hTS, ?_⟩
  intro r s
  have hp := hTF (r, s) (Finset.mem_univ _)
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

end ParameterSplitTree
end LambdaTree
end PolishSpaceBook
