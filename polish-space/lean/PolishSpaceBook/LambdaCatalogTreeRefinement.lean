module

public import PolishSpaceBook.LambdaTreeRefinement

@[expose] public section

/-!
# Finite HKL node and edge stages in the parameter catalog

Density is assumed only inside the actual relative lambda catalog.
Every chosen condition is realized exactly at the selected node or edge,
and propagation keeps all nodes and edges in that same catalog.
-/

namespace PolishSpaceBook
namespace LambdaTree
open Set SimpleGraph

abbrev ParameterTreeSystem (ε : ℕ → ℕ) {V : Type*} (G : SimpleGraph V) :=
  {S : AnalyticTreeSystem G FusionReal // TreeCoded ε S}

namespace ParameterTreeSystem
variable {ε : ℕ → ℕ} {V : Type*} {G : SimpleGraph V}

def nodeCondition (S : ParameterTreeSystem ε G) (v : V) : (parameterAnalyticCatalog ε).Condition :=
  parameterCondition ε (S.val.node v) (S.property.1 v) (S.val.node_nonempty v)

def edgeCondition (S : ParameterTreeSystem ε G) {u v : V} (h : G.Adj u v) :
    (parameterAnalyticCatalog ε).Condition :=
  parameterCondition ε {p | (leftBaire p, rightBaire p) ∈ S.val.edge u v}
    (S.property.2 u v h) (by
      obtain ⟨⟨x, y⟩, hxy⟩ := S.val.edge_nonempty h
      exact ⟨pairBaire x y, by simpa using hxy⟩)

theorem refine_node (hG : G.IsTree) (S : ParameterTreeSystem ε G) (r : V)
    (C : (parameterAnalyticCatalog ε).Condition) (hC : C ≤ S.nodeCondition r) :
    ∃ T : ParameterTreeSystem ε G, T.val.Refines S.val ∧ T.nodeCondition r = C ∧
      (∀ u v, T.val.edge u v = restrictTreeEdge (S.val.edge u v) (T.val.node u) (T.val.node v)) := by
  obtain ⟨T, hTc, hr, hTS, he, _⟩ := tree_node_refinement hG S.val S.property r
    (parameterCondition_projected ε C) C.val.property.2 hC
  exact ⟨⟨T, hTc⟩, hTS, Subtype.ext (Subtype.ext hr), he⟩

/-- Realize an encoded pair condition as an actual edge relation. -/
theorem refine_edge (hG : G.IsTree) (S : ParameterTreeSystem ε G)
    {u v : V} (h : G.Adj u v) (Q : (parameterAnalyticCatalog ε).Condition)
    (hQ : Q ≤ S.edgeCondition h) :
    ∃ T : ParameterTreeSystem ε G, T.val.Refines S.val ∧ T.edgeCondition h = Q := by
  let P : Set (FusionReal × FusionReal) := {p | pairBaire p.1 p.2 ∈ Q.val.val}
  have hP : ProjectedPairs ε P := by
    change Projected ε {p | pairBaire (leftBaire p) (rightBaire p) ∈ Q.val.val}
    simpa only [pairBaire_left_right, ofPred_mem_eq] using parameterCondition_projected ε Q
  have hn : P.Nonempty := by
    obtain ⟨p, hp⟩ := Q.val.property.2
    exact ⟨(leftBaire p, rightBaire p), by simpa [P] using hp⟩
  have hs : P ⊆ S.val.edge u v := by
    intro p hp
    have hh := hQ hp
    simpa only [edgeCondition, parameterCondition, mem_ofPred_eq, leftBaire_pair,
      rightBaire_pair, Prod.mk.eta] using hh
  obtain ⟨T, hTc, he, _, _, hTS⟩ := tree_edge_refinement hG S.val S.property h hP hn hs
  refine ⟨⟨T, hTc⟩, hTS, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change {p | (leftBaire p, rightBaire p) ∈ T.edge u v} = Q.val.val
  rw [he]
  simp only [P, mem_ofPred_eq, pairBaire_left_right, ofPred_mem_eq]

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    First refine every node into $D_{n+1}$, one at a time, using finite-tree refinement.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    During this step keep the new
    joining edge equal to the full $E$-relation between its endpoint sets.
-/
/-- Process the finite node stage. Only relative catalog density is used;
the exact edge formula preserves fullness of every joining edge. -/
theorem nodes_dense (hG : G.IsTree) (S : ParameterTreeSystem ε G)
    (F : Finset V) (D : V → Set (parameterAnalyticCatalog ε).Condition)
    (hDd : ∀ v, IsCoinitial (D v)) (hDl : ∀ v, IsLowerSet (D v)) :
    ∃ T : ParameterTreeSystem ε G, T.val.Refines S.val ∧
      (∀ v ∈ F, T.nodeCondition v ∈ D v) ∧
      (∀ u v, G.Adj u v → T.val.edge u v =
        restrictTreeEdge (S.val.edge u v) (T.val.node u) (T.val.node v)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨S, .refl _, by simp, ?_⟩
    intro u v h
    apply Subset.antisymm
    · intro p hp
      refine ⟨⟨hp, ?_⟩, ?_⟩
      · rw [← S.val.fst_edge u v h]
        exact mem_image_of_mem Prod.fst hp
      · rw [← S.val.snd_edge u v h]
        exact mem_image_of_mem Prod.snd hp
    · exact fun _ hp => hp.1.1
  | @insert v F hv ih =>
    obtain ⟨T, hTS, hTF, hTe⟩ := ih
    obtain ⟨C, hCD, hCT⟩ := hDd v (T.nodeCondition v)
    obtain ⟨U, hUT, hUv, hUe⟩ := T.refine_node hG v C hCT
    refine ⟨U, hUT.trans hTS, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rwa [hUv]
      · exact hDl w (hUT.1 w) (hTF w hw)
    · intro a b hab
      rw [hUe, hTe a b hab]
      exact restrictTreeEdge_restrict (hUT.1 a) (hUT.1 b)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Finally refine each edge relation into $K_{n+1}$ and propagate its projections into the two components as in the
    finite-tree refinement lemma.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    At this last step the joining edge need no longer remain a full $E$-relation.
-/
/-- A finite family of oriented edge requirements survives subsequent
shrinking because the dense families are lower in the restricted order. -/
theorem edges_dense (hG : G.IsTree) (S : ParameterTreeSystem ε G)
    (F : Finset (V × V)) (hF : ∀ e ∈ F, G.Adj e.1 e.2)
    (K : V → V → Set (parameterAnalyticCatalog ε).Condition)
    (hKd : ∀ u v, G.Adj u v → IsCoinitial (K u v))
    (hKl : ∀ u v, G.Adj u v → IsLowerSet (K u v)) :
    ∃ T : ParameterTreeSystem ε G, T.val.Refines S.val ∧
      ∀ e (he : e ∈ F), T.edgeCondition (hF e he) ∈ K e.1 e.2 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨S, .refl _, by simp⟩
  | @insert e F he ih =>
    have hF' : ∀ e ∈ F, G.Adj e.1 e.2 := fun e he => hF e (Finset.mem_insert_of_mem he)
    obtain ⟨T, hTS, hTF⟩ := ih hF'
    have heG := hF e (Finset.mem_insert_self _ _)
    obtain ⟨P, hPK, hPT⟩ := hKd e.1 e.2 heG (T.edgeCondition heG)
    obtain ⟨U, hUT, hUe⟩ := T.refine_edge hG heG P hPT
    refine ⟨U, hUT.trans hTS, ?_⟩
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · rwa [hUe]
    · exact hKl f.1 f.2 (hF' f hf) (fun p hp => hUT.2 f.1 f.2 hp) (hTF f hf)

/-- The node phase preserves fullness of every joining edge. -/
theorem nodes_dense_full (hG : G.IsTree) (S : ParameterTreeSystem ε G)
    (F : Finset V) (D : V → Set (parameterAnalyticCatalog ε).Condition)
    (hDd : ∀ v, IsCoinitial (D v)) (hDl : ∀ v, IsLowerSet (D v))
    (E : Setoid FusionReal) :
    ∃ T : ParameterTreeSystem ε G, T.val.Refines S.val ∧
      (∀ v ∈ F, T.nodeCondition v ∈ D v) ∧
      (∀ u v, G.Adj u v →
        S.val.edge u v = fullERBetween E (S.val.node u) (S.val.node v) →
        T.val.edge u v = fullERBetween E (T.val.node u) (T.val.node v)) := by
  obtain ⟨T, hTS, hTF, hTe⟩ := S.nodes_dense hG F D hDd hDl
  refine ⟨T, hTS, hTF, ?_⟩
  intro u v h huv
  rw [hTe u v h, huv]
  exact restrictTreeEdge_fullERBetween E (hTS.1 u) (hTS.1 v)

/-- The edge phase retains the earlier node requirements. The rectangular
middle phase and the full three-stage construction are supplied by
`LambdaHKLComponents` and `LambdaHKLStages`. -/
theorem nodes_edges_dense (hG : G.IsTree) (S : ParameterTreeSystem ε G)
    (F : Finset V) (J : Finset (V × V)) (hJ : ∀ e ∈ J, G.Adj e.1 e.2)
    (D : V → Set (parameterAnalyticCatalog ε).Condition)
    (hDd : ∀ v, IsCoinitial (D v)) (hDl : ∀ v, IsLowerSet (D v))
    (K : V → V → Set (parameterAnalyticCatalog ε).Condition)
    (hKd : ∀ u v, G.Adj u v → IsCoinitial (K u v))
    (hKl : ∀ u v, G.Adj u v → IsLowerSet (K u v)) :
    ∃ T : ParameterTreeSystem ε G, T.val.Refines S.val ∧
      (∀ v ∈ F, T.nodeCondition v ∈ D v) ∧
      ∀ e (he : e ∈ J), T.edgeCondition (hJ e he) ∈ K e.1 e.2 := by
  obtain ⟨T, hTS, hTF, _⟩ := S.nodes_dense hG F D hDd hDl
  obtain ⟨U, hUT, hUJ⟩ := T.edges_dense hG J hJ K hKd hKl
  exact ⟨U, hUT.trans hTS, fun v hv => hDl v (hUT.1 v) (hTF v hv), hUJ⟩

end ParameterTreeSystem
end LambdaTree
end PolishSpaceBook
