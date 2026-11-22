module

public import PolishSpaceBook.LambdaHKLComponents
public import PolishSpaceBook.HKLLevelConstruction

@[expose] public section

/-!
# The three HKL refinement stages in the relative catalog

First process nodes in the joined tree, then compatible rectangles in the
two components, and finally the encoded edge conditions. Each stage stays
in the original parameter. Later restrictions preserve the earlier lower
requirements and disjointness. No generic-pair truth claim is made here.
-/

namespace PolishSpaceBook
namespace LambdaTree
open Set SimpleGraph

namespace ParameterTreeSystem
variable {ε : ℕ → ℕ} {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  {a : V} {b : W}

def leftComponent (S : ParameterTreeSystem ε (joinedTreeGraph G H a b)) :
    ParameterTreeSystem ε G :=
  ⟨S.val.leftComponent, fun v => S.property.1 (.inl v),
    fun u v h => S.property.2 _ _ ((joinedTreeGraph_inl a b u v).mpr h)⟩

def rightComponent (S : ParameterTreeSystem ε (joinedTreeGraph G H a b)) :
    ParameterTreeSystem ε H :=
  ⟨S.val.rightComponent, fun v => S.property.1 (.inr v),
    fun u v h => S.property.2 _ _ ((joinedTreeGraph_inr a b u v).mpr h)⟩

def rectangleCondition (S : ParameterTreeSystem ε G) (hG : G.Connected)
    (E : Setoid FusionReal) (hSE : S.val.EdgesIn E) (u v : V) :
    ParameterCompatibleRectangle ε E :=
  ⟨(S.nodeCondition u, S.nodeCondition v), S.val.saturation_eq hG E hSE u v⟩

end ParameterTreeSystem

namespace ParameterSplitTree
variable {ε : ℕ → ℕ} {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  {a : V} {b : W} {E : Setoid FusionReal}

/-- The node phase, retaining the component presentation and original codes. -/
theorem refine_all_nodes [Fintype V] [Fintype W]
    (S : ParameterSplitTree ε G H a b E) (hG : G.IsTree) (hH : H.IsTree)
    (hE : ProjectedRelation ε E.r)
    (D : Set (parameterAnalyticCatalog ε).Condition) (hDd : IsCoinitial D) (hDl : IsLowerSet D) :
    ∃ T : ParameterSplitTree ε G H a b E, T.Refines S ∧
      ∀ v, (T.joined hE).nodeCondition v ∈ D := by
  have htree : (joinedTreeGraph G H a b).IsTree := isTree_sum_join hG hH a b
  obtain ⟨U, hUS, hUD, _⟩ := (S.joined hE).nodes_dense_full htree Finset.univ
    (fun _ => D) (fun _ => hDd) (fun _ => hDl) E
  have hUE := hUS.edgesIn (S.joined_edgesIn hE)
  let T : ParameterSplitTree ε G H a b E := {
    left := U.leftComponent
    right := U.rightComponent
    leftIn := fun u v h => hUE _ _ ((joinedTreeGraph_inl a b u v).mpr h)
    rightIn := fun u v h => hUE _ _ ((joinedTreeGraph_inr a b u v).mpr h)
    compatible := U.val.saturation_eq htree.connected E hUE (.inl a) (.inr b) }
  have hTS : T.Refines S :=
    ⟨⟨fun v => hUS.1 (.inl v), fun u v => hUS.2 (.inl u) (.inl v)⟩,
      ⟨fun v => hUS.1 (.inr v), fun u v => hUS.2 (.inr u) (.inr v)⟩⟩
  refine ⟨T, hTS, ?_⟩
  intro v
  cases v with
  | inl v => exact hUD (.inl v) (Finset.mem_univ _)
  | inr v => exact hUD (.inr v) (Finset.mem_univ _)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    All node and rectangle requirements already obtained persist under restriction.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    At this last step the joining edge need no longer remain a full $E$-relation.
-/
/-- Assemble the node, rectangular and edge stages in the book's order,
with density throughout restricted to the fixed-parameter conditions. -/
theorem refine_three_stages [Fintype V] [Fintype W]
    (S : ParameterSplitTree ε G H a b E) (hG : G.IsTree) (hH : H.IsTree)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (D : Set (parameterAnalyticCatalog ε).Condition) (hDd : IsCoinitial D) (hDl : IsLowerSet D)
    (J : Set (ParameterCompatibleRectangle ε E)) (hJd : IsCoinitial J) (hJl : IsLowerSet J)
    (K : Set (parameterAnalyticCatalog ε).Condition) (hKd : IsCoinitial K) (hKl : IsLowerSet K)
    (hkernel : ∀ r, S.left.val.node r ⊆ equivalenceGapKernel E (invariantSetoid ε E)) :
    ∃ U : ParameterTreeSystem ε (joinedTreeGraph G H a b),
      U.val.Refines (S.joined hE).val ∧ (∀ v, U.nodeCondition v ∈ D) ∧
      (∀ u v (h : (joinedTreeGraph G H a b).Adj u v), U.edgeCondition h ∈ K) ∧
      ∃ hUE : U.val.EdgesIn E, ∀ r s,
        U.rectangleCondition (isTree_sum_join hG hH a b).connected E hUE (.inl r) (.inr s) ∈ J ∧
        U.rectangleCondition (isTree_sum_join hG hH a b).connected E hUE (.inr s) (.inl r) ∈ J ∧
        Disjoint (U.val.node (.inl r)) (U.val.node (.inr s)) := by
  classical
  obtain ⟨T, hTS, hTD⟩ := S.refine_all_nodes hG hH hE D hDd hDl
  obtain ⟨R, hRT, hRJ⟩ := T.refine_all_dense_disjoint_rectangles hG hH hE hneE J hJd hJl
    (fun r => (hTS.1.1 r).trans (hkernel r))
  have htree : (joinedTreeGraph G H a b).IsTree := isTree_sum_join hG hH a b
  let F := Finset.univ.filter (fun p : (V ⊕ W) × (V ⊕ W) =>
    (joinedTreeGraph G H a b).Adj p.1 p.2)
  have hF : ∀ p ∈ F, (joinedTreeGraph G H a b).Adj p.1 p.2 :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  obtain ⟨U, hUR, hUK⟩ := (R.joined hE).edges_dense htree F hF
    (fun _ _ => K) (fun _ _ _ => hKd) (fun _ _ _ => hKl)
  have hUE := hUR.edgesIn (R.joined_edgesIn hE)
  refine ⟨U, hUR.trans ((hRT.trans hTS).joined hE), ?_, ?_, hUE, ?_⟩
  · intro v
    have hRD : (R.joined hE).nodeCondition v ∈ D :=
      hDl ((hRT.joined hE).1 v) (hTD v)
    exact hDl (hUR.1 v) hRD
  · intro u v h
    exact hUK (u, v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  · intro r s
    have hf : U.rectangleCondition htree.connected E hUE (.inl r) (.inr s) ≤
        R.rectangle hG.connected hH.connected r s := ⟨hUR.1 (.inl r), hUR.1 (.inr s)⟩
    have hb : U.rectangleCondition htree.connected E hUE (.inr s) (.inl r) ≤
        (R.rectangle hG.connected hH.connected r s).swap := ⟨hUR.1 (.inr s), hUR.1 (.inl r)⟩
    exact ⟨hJl hf (hRJ r s).1, hJl hb (hRJ r s).2.1,
      (hRJ r s).2.2.mono (hUR.1 (.inl r)) (hUR.1 (.inr s))⟩

end ParameterSplitTree
end LambdaTree
end PolishSpaceBook
