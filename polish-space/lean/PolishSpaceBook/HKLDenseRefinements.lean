module

public import PolishSpaceBook.HKLTreeRefinement
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Bounds.Defs

@[expose] public section

/-!
# Finite dense requirements in HKL refinement

Conditions are nonempty analytic sets, ordered by inclusion. Forcing density
is mathlib's `IsCoinitial`, and downward closure is `IsLowerSet`. The finite
iterations below process one node or edge at a time using tree refinement.
The rectangular middle stage is supplied by `HKLCompatibleRefinements.lean`
under the distinct-pair kernel hypothesis. `HKLLevelConstruction.lean`
assembles the stages and constructs all binary levels under that hypothesis.
`AnalyticConditionFusion.lean` proves witnessed fusion for supplied closed
Baire presentations; effective coding and dense scheduling remain open.
-/

namespace PolishSpaceBook
open Set Function SimpleGraph MeasureTheory

/-- The analytic forcing conditions with the inherited inclusion order. -/
abbrev AnalyticCondition (X : Type*) [TopologicalSpace X] :=
  {A : Set X // AnalyticSet A ∧ A.Nonempty}

variable {V X : Type*} [TopologicalSpace X] [PolishSpace X] {G : SimpleGraph V}

/-- The node regarded as a condition, with its actual nonemptiness witness. -/
def AnalyticTreeSystem.nodeCondition (S : AnalyticTreeSystem G X) (v : V) : AnalyticCondition X :=
  ⟨S.node v, S.node_analytic v, S.node_nonempty v⟩

/-- Only actual graph edges give nonempty analytic pair conditions. -/
def AnalyticTreeSystem.edgeCondition (S : AnalyticTreeSystem G X) {u v : V}
    (h : G.Adj u v) : AnalyticCondition (X × X) :=
  ⟨S.edge u v, S.edge_analytic u v h, S.edge_nonempty h⟩

/-- Every coordinate set and every relation is restricted. -/
def AnalyticTreeSystem.Refines (T S : AnalyticTreeSystem G X) : Prop :=
  (∀ v, T.node v ⊆ S.node v) ∧ ∀ u v, T.edge u v ⊆ S.edge u v

omit [PolishSpace X] in
theorem AnalyticTreeSystem.Refines.refl (S : AnalyticTreeSystem G X) : S.Refines S :=
  ⟨fun _ => Subset.rfl, fun _ _ => Subset.rfl⟩

omit [PolishSpace X] in
theorem AnalyticTreeSystem.Refines.trans {S T U : AnalyticTreeSystem G X}
    (hUT : U.Refines T) (hTS : T.Refines S) : U.Refines S :=
  ⟨fun v => (hUT.1 v).trans (hTS.1 v), fun u v => (hUT.2 u v).trans (hTS.2 u v)⟩

omit [TopologicalSpace X] [PolishSpace X] in
/-- Successive endpoint restrictions combine without changing the old relation. -/
theorem restrictTreeEdge_restrict {R : Set (X × X)} {A B C D : Set X}
    (hCA : C ⊆ A) (hDB : D ⊆ B) :
    restrictTreeEdge (restrictTreeEdge R A B) C D = restrictTreeEdge R C D := by
  ext p
  constructor
  · rintro ⟨⟨⟨⟨hpR, _⟩, _⟩, hpC⟩, hpD⟩
    exact ⟨⟨hpR, hpC⟩, hpD⟩
  · rintro ⟨⟨hpR, hpC⟩, hpD⟩
    exact ⟨⟨⟨⟨hpR, hCA hpC⟩, hDB hpD⟩, hpC⟩, hpD⟩

/-- Process a finite collection of node requirements. Old requirements persist
by downward closure; the edge formula also retains every full joining edge. -/
theorem analytic_tree_nodes_dense (hG : G.IsTree) (S : AnalyticTreeSystem G X)
    (F : Finset V) (D : V → Set (AnalyticCondition X))
    (hDd : ∀ v, IsCoinitial (D v)) (hDl : ∀ v, IsLowerSet (D v)) :
    ∃ T : AnalyticTreeSystem G X, T.Refines S ∧
      (∀ v ∈ F, T.nodeCondition v ∈ D v) ∧
      (∀ u v, G.Adj u v → T.edge u v = restrictTreeEdge (S.edge u v) (T.node u) (T.node v)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨S, .refl S, by simp, ?_⟩
    intro u v h
    apply Subset.antisymm
    · intro p hp
      refine ⟨⟨hp, ?_⟩, ?_⟩
      · rw [← S.fst_edge u v h]
        exact mem_image_of_mem Prod.fst hp
      · rw [← S.snd_edge u v h]
        exact mem_image_of_mem Prod.snd hp
    · exact fun _ hp => hp.1.1
  | @insert v F hv ih =>
    obtain ⟨T, hTS, hTF, hTe⟩ := ih
    obtain ⟨C, hCD, hCT⟩ := hDd v (T.nodeCondition v)
    obtain ⟨U, hUv, hUTn, hUe, _⟩ := analytic_tree_node_refinement hG T v C.property.1
      C.property.2 hCT
    have hUT : U.Refines T := ⟨hUTn, fun a b p hp => by rw [hUe] at hp; exact hp.1.1⟩
    refine ⟨U, hUT.trans hTS, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · have heq : U.nodeCondition w = C := Subtype.ext hUv
        rwa [heq]
      · exact hDl w (hUTn w) (hTF w hw)
    · intro a b hab
      rw [hUe, hTe a b hab]
      exact restrictTreeEdge_restrict (hUTn a) (hUTn b)

/-- Process a finite collection of oriented edge requirements. Refining a later
edge only restricts previous edges, so their downward-closed requirements survive. -/
theorem analytic_tree_edges_dense (hG : G.IsTree) (S : AnalyticTreeSystem G X)
    (F : Finset (V × V)) (hF : ∀ e ∈ F, G.Adj e.1 e.2)
    (K : V → V → Set (AnalyticCondition (X × X)))
    (hKd : ∀ u v, G.Adj u v → IsCoinitial (K u v))
    (hKl : ∀ u v, G.Adj u v → IsLowerSet (K u v)) :
    ∃ T : AnalyticTreeSystem G X, T.Refines S ∧
      ∀ e (he : e ∈ F), T.edgeCondition (hF e he) ∈ K e.1 e.2 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨S, .refl S, by simp⟩
  | @insert e F he ih =>
    have hF' : ∀ e ∈ F, G.Adj e.1 e.2 := fun e he => hF e (Finset.mem_insert_of_mem he)
    obtain ⟨T, hTS, hTF⟩ := ih hF'
    have heG := hF e (Finset.mem_insert_self _ _)
    obtain ⟨P, hPK, hPT⟩ := hKd e.1 e.2 heG (T.edgeCondition heG)
    obtain ⟨U, hUe, _, _, hUn, hUsub⟩ := analytic_tree_edge_refinement hG T heG
      P.property.1 P.property.2 hPT
    have hUT : U.Refines T := ⟨hUn, hUsub⟩
    refine ⟨U, hUT.trans hTS, ?_⟩
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · have heq : U.edgeCondition heG = P := Subtype.ext hUe
      rwa [heq]
    · exact hKl f.1 f.2 (hF' f hf) (hUsub f.1 f.2) (hTF f hf)

omit [PolishSpace X] in
/-- Earlier node requirements persist during any later refinement phase. -/
theorem AnalyticTreeSystem.Refines.node_mem {T S : AnalyticTreeSystem G X}
    (hTS : T.Refines S) {v : V} {D : Set (AnalyticCondition X)}
    (hD : IsLowerSet D) (hS : S.nodeCondition v ∈ D) : T.nodeCondition v ∈ D :=
  hD (hTS.1 v) hS

/-- A full joining edge stays full through the entire finite node phase. -/
theorem analytic_tree_nodes_dense_full (hG : G.IsTree) (S : AnalyticTreeSystem G X)
    (F : Finset V) (D : V → Set (AnalyticCondition X))
    (hDd : ∀ v, IsCoinitial (D v)) (hDl : ∀ v, IsLowerSet (D v))
    (E : Setoid X) :
    ∃ T : AnalyticTreeSystem G X, T.Refines S ∧
      (∀ v ∈ F, T.nodeCondition v ∈ D v) ∧
      (∀ u v, G.Adj u v →
        S.edge u v = fullERBetween E (S.node u) (S.node v) →
        T.edge u v = fullERBetween E (T.node u) (T.node v)) := by
  obtain ⟨T, hTS, hTF, hTe⟩ := analytic_tree_nodes_dense hG S F D hDd hDl
  refine ⟨T, hTS, hTF, ?_⟩
  intro u v h huv
  rw [hTe u v h, huv]
  exact restrictTreeEdge_fullERBetween E (hTS.1 u) (hTS.1 v)

/-- The finite node phase followed by the finite edge phase, with all node
requirements still satisfied at the end. The rectangular middle phase in
HKL is a separate obligation, not an assumption hidden in this theorem. -/
theorem analytic_tree_nodes_edges_dense (hG : G.IsTree) (S : AnalyticTreeSystem G X)
    (F : Finset V) (J : Finset (V × V)) (hJ : ∀ e ∈ J, G.Adj e.1 e.2)
    (D : V → Set (AnalyticCondition X))
    (hDd : ∀ v, IsCoinitial (D v)) (hDl : ∀ v, IsLowerSet (D v))
    (K : V → V → Set (AnalyticCondition (X × X)))
    (hKd : ∀ u v, G.Adj u v → IsCoinitial (K u v))
    (hKl : ∀ u v, G.Adj u v → IsLowerSet (K u v)) :
    ∃ T : AnalyticTreeSystem G X, T.Refines S ∧
      (∀ v ∈ F, T.nodeCondition v ∈ D v) ∧
      ∀ e (he : e ∈ J), T.edgeCondition (hJ e he) ∈ K e.1 e.2 := by
  obtain ⟨T, hTS, hTF, _⟩ := analytic_tree_nodes_dense hG S F D hDd hDl
  obtain ⟨U, hUT, hUJ⟩ := analytic_tree_edges_dense hG T J hJ K hKd hKl
  exact ⟨U, hUT.trans hTS, fun v hv => hUT.node_mem (hDl v) (hTF v hv), hUJ⟩

/-- On a finite tree, all nodes and all oriented edges can meet their respective
lower dense families at once. -/
theorem analytic_tree_all_nodes_edges_dense [Fintype V] (hG : G.IsTree)
    (S : AnalyticTreeSystem G X) (D : Set (AnalyticCondition X))
    (hDd : IsCoinitial D) (hDl : IsLowerSet D)
    (K : Set (AnalyticCondition (X × X))) (hKd : IsCoinitial K) (hKl : IsLowerSet K) :
    ∃ T : AnalyticTreeSystem G X, T.Refines S ∧
      (∀ v, T.nodeCondition v ∈ D) ∧
      ∀ u v (h : G.Adj u v), T.edgeCondition h ∈ K := by
  classical
  let J := Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2)
  have hJ : ∀ e ∈ J, G.Adj e.1 e.2 := fun _ he => (Finset.mem_filter.mp he).2
  obtain ⟨T, hTS, hTD, hTK⟩ := analytic_tree_nodes_edges_dense hG S Finset.univ J hJ
    (fun _ => D) (fun _ => hDd) (fun _ => hDl)
    (fun _ _ => K) (fun _ _ _ => hKd) (fun _ _ _ => hKl)
  refine ⟨T, hTS, fun v => hTD v (Finset.mem_univ _), ?_⟩
  intro u v h
  exact hTK (u, v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

/-- The restricted product consists of pairs with the same saturation. -/
abbrev CompatibleAnalyticRectangle (E : Setoid X) :=
  {p : AnalyticCondition X × AnalyticCondition X //
    erSaturation E p.1.val = erSaturation E p.2.val}

/-- Edge containment is the only equivalence-relation invariant needed here. -/
def AnalyticTreeSystem.EdgesIn (S : AnalyticTreeSystem G X) (E : Setoid X) : Prop :=
  ∀ u v, G.Adj u v → ∀ p ∈ S.edge u v, E.r p.1 p.2

omit [PolishSpace X] in
theorem AnalyticTreeSystem.Refines.edgesIn {T S : AnalyticTreeSystem G X}
    (hTS : T.Refines S) {E : Setoid X} (hS : S.EdgesIn E) : T.EdgesIn E :=
  fun u v h p hp => hS u v h p (hTS.2 u v hp)

omit [PolishSpace X] in
theorem AnalyticTreeSystem.saturation_eq (S : AnalyticTreeSystem G X)
    (hG : G.Connected) (E : Setoid X) (hSE : S.EdgesIn E) (u v : V) :
    erSaturation E (S.node u) = erSaturation E (S.node v) := by
  apply erSaturation_eq_of_connected_coherent G hG E S.node _ u v
  intro a b hab
  exact ⟨S.edge a b, S.fst_edge a b hab, S.snd_edge a b hab, hSE a b hab⟩

/-- Every node rectangle remains a legitimate restricted-product condition. -/
def AnalyticTreeSystem.rectangleCondition (S : AnalyticTreeSystem G X)
    (hG : G.Connected) (E : Setoid X) (hSE : S.EdgesIn E) (u v : V) :
    CompatibleAnalyticRectangle E :=
  ⟨(S.nodeCondition u, S.nodeCondition v), S.saturation_eq hG E hSE u v⟩

omit [PolishSpace X] in
/-- In particular, the final edge phase preserves every earlier requirement
in a lower dense family of the restricted product. Density is only needed
when obtaining the requirement, not when preserving it. -/
theorem AnalyticTreeSystem.Refines.rectangle_mem {T S : AnalyticTreeSystem G X}
    (hTS : T.Refines S) (hG : G.Connected) (E : Setoid X) (hSE : S.EdgesIn E)
    {u v : V} {J : Set (CompatibleAnalyticRectangle E)} (hJl : IsLowerSet J)
    (hS : S.rectangleCondition hG E hSE u v ∈ J) :
    T.rectangleCondition hG E (hTS.edgesIn hSE) u v ∈ J := by
  have hle : T.rectangleCondition hG E (hTS.edgesIn hSE) u v ≤
      S.rectangleCondition hG E hSE u v := ⟨hTS.1 u, hTS.1 v⟩
  exact hJl hle hS

omit [PolishSpace X] in
/-- Disjointness acquired in the rectangular stage survives every later phase. -/
theorem AnalyticTreeSystem.Refines.disjoint {T S : AnalyticTreeSystem G X}
    (hTS : T.Refines S) {u v : V} (hS : Disjoint (S.node u) (S.node v)) :
    Disjoint (T.node u) (T.node v) := hS.mono (hTS.1 u) (hTS.1 v)

end PolishSpaceBook
