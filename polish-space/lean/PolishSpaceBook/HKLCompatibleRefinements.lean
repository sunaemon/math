module

public import PolishSpaceBook.HKLDenseRefinements
public import PolishSpaceBook.HKLCrucialPairs

@[expose] public section

/-!
# Compatible refinements on the two components of an HKL level

The new level consists of two old trees connected by one full equivalence
edge. Refinements in the components are propagated separately; equal
saturations allow the full joining edge to be restored with full projections.
Finite rectangular refinement is proved in both orientations, with disjoint
node sets under an explicit distinct-related-pair hypothesis. The actual
relative kernel now supplies this property in `LambdaHKLRefinement.lean`.
This module uses the full boldface order. `LambdaHKLComponents.lean`
now proves its gluing and rectangular stage in the relative catalog. `HKLLevelConstruction.lean` assembles the three stages
on binary levels and constructs all levels under the kernel hypotheses.
-/

namespace PolishSpaceBook
open Set Function SimpleGraph MeasureTheory

variable {V W X : Type*} [TopologicalSpace X] [PolishSpace X]

/-- Two component trees with the designated new joining edge. -/
def joinedTreeGraph (G : SimpleGraph V) (H : SimpleGraph W) (a : V) (b : W) :=
  G.sum H ⊔ SimpleGraph.edge (.inl a) (.inr b)

@[simp] theorem joinedTreeGraph_inl {G : SimpleGraph V} {H : SimpleGraph W} (a : V) (b : W)
    (u v : V) : (joinedTreeGraph G H a b).Adj (.inl u) (.inl v) ↔ G.Adj u v := by
  simp [joinedTreeGraph, SimpleGraph.sum_adj, SimpleGraph.edge]

@[simp] theorem joinedTreeGraph_inr {G : SimpleGraph V} {H : SimpleGraph W} (a : V) (b : W)
    (u v : W) : (joinedTreeGraph G H a b).Adj (.inr u) (.inr v) ↔ H.Adj u v := by
  simp [joinedTreeGraph, SimpleGraph.sum_adj, SimpleGraph.edge]

@[simp] theorem joinedTreeGraph_cross {G : SimpleGraph V} {H : SimpleGraph W} (a : V) (b : W)
    (u : V) (v : W) : (joinedTreeGraph G H a b).Adj (.inl u) (.inr v) ↔ u = a ∧ v = b := by
  simp [joinedTreeGraph, SimpleGraph.sum_adj, SimpleGraph.edge]

theorem analyticSet_fullERBetween (E : Setoid X)
    (hE : AnalyticSet {p : X × X | E.r p.1 p.2}) {A B : Set X}
    (hA : AnalyticSet A) (hB : AnalyticSet B) : AnalyticSet (fullERBetween E A B) := by
  exact analyticSet_inter (hA.preimage continuous_fst)
    (analyticSet_inter (hB.preimage continuous_snd) hE)

/-- Inside a component keep its old edges; across the components use the full
relation. Only the designated joining pair is an actual cross edge. -/
def joinedTreeRelation {G : SimpleGraph V} {H : SimpleGraph W}
    (S : AnalyticTreeSystem G X) (T : AnalyticTreeSystem H X) (E : Setoid X) :
    V ⊕ W → V ⊕ W → Set (X × X)
  | .inl u, .inl v => S.edge u v
  | .inr u, .inr v => T.edge u v
  | .inl u, .inr v => fullERBetween E (S.node u) (T.node v)
  | .inr u, .inl v => fullERBetween E (T.node u) (S.node v)

/-- Rejoin two coherent components with equal endpoint saturations. -/
def joinedTreeSystem {G : SimpleGraph V} {H : SimpleGraph W}
    (S : AnalyticTreeSystem G X) (T : AnalyticTreeSystem H X) (a : V) (b : W)
    (E : Setoid X) (hE : AnalyticSet {p : X × X | E.r p.1 p.2})
    (hcompat : erSaturation E (S.node a) = erSaturation E (T.node b)) :
    AnalyticTreeSystem (joinedTreeGraph G H a b) X where
  node := Sum.elim S.node T.node
  edge := joinedTreeRelation S T E
  node_analytic := by intro v; cases v with
    | inl v => exact S.node_analytic v
    | inr v => exact T.node_analytic v
  node_nonempty := by intro v; cases v with
    | inl v => exact S.node_nonempty v
    | inr v => exact T.node_nonempty v
  edge_analytic := by
    intro u v h
    cases u with
    | inl u =>
      cases v with
      | inl v => exact S.edge_analytic u v ((joinedTreeGraph_inl a b u v).mp h)
      | inr v => exact analyticSet_fullERBetween E hE (S.node_analytic u) (T.node_analytic v)
    | inr u =>
      cases v with
      | inl v => exact analyticSet_fullERBetween E hE (T.node_analytic u) (S.node_analytic v)
      | inr v => exact T.edge_analytic u v ((joinedTreeGraph_inr a b u v).mp h)
  fst_edge := by
    intro u v h
    cases u with
    | inl u =>
      cases v with
      | inl v => exact S.fst_edge u v ((joinedTreeGraph_inl a b u v).mp h)
      | inr v =>
        obtain ⟨rfl, rfl⟩ := (joinedTreeGraph_cross a b u v).mp h
        exact (fullERBetween_projections E hcompat).1
    | inr u =>
      cases v with
      | inl v =>
        obtain ⟨rfl, rfl⟩ := (joinedTreeGraph_cross a b v u).mp h.symm
        exact (fullERBetween_projections E hcompat.symm).1
      | inr v => exact T.fst_edge u v ((joinedTreeGraph_inr a b u v).mp h)
  snd_edge := by
    intro u v h
    cases u with
    | inl u =>
      cases v with
      | inl v => exact S.snd_edge u v ((joinedTreeGraph_inl a b u v).mp h)
      | inr v =>
        obtain ⟨rfl, rfl⟩ := (joinedTreeGraph_cross a b u v).mp h
        exact (fullERBetween_projections E hcompat).2
    | inr u =>
      cases v with
      | inl v =>
        obtain ⟨rfl, rfl⟩ := (joinedTreeGraph_cross a b v u).mp h.symm
        exact (fullERBetween_projections E hcompat.symm).2
      | inr v => exact T.snd_edge u v ((joinedTreeGraph_inr a b u v).mp h)
  edge_swap := by
    intro u v h x y
    cases u with
    | inl u =>
      cases v with
      | inl v => exact S.edge_swap u v ((joinedTreeGraph_inl a b u v).mp h) x y
      | inr v =>
        change (x ∈ S.node u ∧ y ∈ T.node v ∧ E.r x y) ↔
          (y ∈ T.node v ∧ x ∈ S.node u ∧ E.r y x)
        exact ⟨fun h => ⟨h.2.1, h.1, E.symm h.2.2⟩, fun h => ⟨h.2.1, h.1, E.symm h.2.2⟩⟩
    | inr u =>
      cases v with
      | inr v => exact T.edge_swap u v ((joinedTreeGraph_inr a b u v).mp h) x y
      | inl v =>
        change (x ∈ T.node u ∧ y ∈ S.node v ∧ E.r x y) ↔
          (y ∈ S.node v ∧ x ∈ T.node u ∧ E.r y x)
        exact ⟨fun h => ⟨h.2.1, h.1, E.symm h.2.2⟩, fun h => ⟨h.2.1, h.1, E.symm h.2.2⟩⟩

/-- Restoring the full bridge after shrinking both components only restricts it. -/
theorem joinedTreeSystem_refines {G : SimpleGraph V} {H : SimpleGraph W}
    {S S' : AnalyticTreeSystem G X} {T T' : AnalyticTreeSystem H X}
    (hS : S'.Refines S) (hT : T'.Refines T) (a : V) (b : W) (E : Setoid X)
    (hE : AnalyticSet {p : X × X | E.r p.1 p.2})
    (hc : erSaturation E (S.node a) = erSaturation E (T.node b))
    (hc' : erSaturation E (S'.node a) = erSaturation E (T'.node b)) :
    (joinedTreeSystem S' T' a b E hE hc').Refines (joinedTreeSystem S T a b E hE hc) := by
  constructor
  · intro v
    cases v with
    | inl v => exact hS.1 v
    | inr v => exact hT.1 v
  · intro u v
    cases u with
    | inl u =>
      cases v with
      | inl v => exact hS.2 u v
      | inr v => exact fun p hp => ⟨hS.1 u hp.1, hT.1 v hp.2.1, hp.2.2⟩
    | inr u =>
      cases v with
      | inl v => exact fun p hp => ⟨hT.1 u hp.1, hS.1 v hp.2.1, hp.2.2⟩
      | inr v => exact hT.2 u v

theorem joinedTreeSystem_edgesIn {G : SimpleGraph V} {H : SimpleGraph W}
    (S : AnalyticTreeSystem G X) (T : AnalyticTreeSystem H X) (a : V) (b : W) (E : Setoid X)
    (hE : AnalyticSet {p : X × X | E.r p.1 p.2})
    (hc : erSaturation E (S.node a) = erSaturation E (T.node b))
    (hS : S.EdgesIn E) (hT : T.EdgesIn E) : (joinedTreeSystem S T a b E hE hc).EdgesIn E := by
  intro u v h
  cases u with
  | inl u =>
    cases v with
    | inl v => exact hS u v ((joinedTreeGraph_inl a b u v).mp h)
    | inr v => exact fun _ hp => hp.2.2
  | inr u =>
    cases v with
    | inl v => exact fun _ hp => hp.2.2
    | inr v => exact hT u v ((joinedTreeGraph_inr a b u v).mp h)

/-- Propagate a compatible pair of shrinks in the two components separately.
Their new bridge endpoints have equal saturations, even when the changed
nodes are far from the bridge. Hence restoration gives a coherent refinement. -/
theorem compatible_component_refinement {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.IsTree) (hH : H.IsTree) (S : AnalyticTreeSystem G X) (T : AnalyticTreeSystem H X)
    (a r : V) (b s : W) (E : Setoid X) (hE : AnalyticSet {p : X × X | E.r p.1 p.2})
    (hS : S.EdgesIn E) (hT : T.EdgesIn E)
    (hc : erSaturation E (S.node a) = erSaturation E (T.node b))
    {C D : Set X} (hCa : AnalyticSet C) (hCn : C.Nonempty) (hCs : C ⊆ S.node r)
    (hDa : AnalyticSet D) (hDn : D.Nonempty) (hDs : D ⊆ T.node s)
    (hCD : erSaturation E C = erSaturation E D) :
    ∃ (S' : AnalyticTreeSystem G X) (T' : AnalyticTreeSystem H X),
      S'.node r = C ∧ T'.node s = D ∧ S'.Refines S ∧ T'.Refines T ∧
      ∃ hc' : erSaturation E (S'.node a) = erSaturation E (T'.node b),
        (joinedTreeSystem S' T' a b E hE hc').Refines (joinedTreeSystem S T a b E hE hc) := by
  obtain ⟨S', hSr, hSn, hSe, _⟩ := analytic_tree_node_refinement hG S r hCa hCn hCs
  obtain ⟨T', hTs, hTn, hTe, _⟩ := analytic_tree_node_refinement hH T s hDa hDn hDs
  have hSS : S'.Refines S := ⟨hSn, fun u v p hp => by rw [hSe] at hp; exact hp.1.1⟩
  have hTT : T'.Refines T := ⟨hTn, fun u v p hp => by rw [hTe] at hp; exact hp.1.1⟩
  have hc' : erSaturation E (S'.node a) = erSaturation E (T'.node b) := by
    rw [S'.saturation_eq hG.connected E (hSS.edgesIn hS) a r,
      T'.saturation_eq hH.connected E (hTT.edgesIn hT) b s, hSr, hTs]
    exact hCD
  exact ⟨S', T', hSr, hTs, hSS, hTT, hc', joinedTreeSystem_refines hSS hTT a b E hE hc hc'⟩

/-- A level in its two-component form, retaining the full joining edge. -/
structure SplitAnalyticTreeSystem (G : SimpleGraph V) (H : SimpleGraph W)
    (a : V) (b : W) (E : Setoid X) where
  left : AnalyticTreeSystem G X
  right : AnalyticTreeSystem H X
  leftIn : left.EdgesIn E
  rightIn : right.EdgesIn E
  compatible : erSaturation E (left.node a) = erSaturation E (right.node b)

namespace SplitAnalyticTreeSystem
variable {G : SimpleGraph V} {H : SimpleGraph W} {a : V} {b : W} {E : Setoid X}

def joined (S : SplitAnalyticTreeSystem G H a b E)
    (hE : AnalyticSet {p : X × X | E.r p.1 p.2}) :=
  joinedTreeSystem S.left S.right a b E hE S.compatible

def Refines (T S : SplitAnalyticTreeSystem G H a b E) : Prop :=
  T.left.Refines S.left ∧ T.right.Refines S.right

omit [PolishSpace X] in
theorem Refines.refl (S : SplitAnalyticTreeSystem G H a b E) : S.Refines S :=
  ⟨.refl _, .refl _⟩

omit [PolishSpace X] in
theorem Refines.trans {R T S : SplitAnalyticTreeSystem G H a b E}
    (hRT : R.Refines T) (hTS : T.Refines S) : R.Refines S :=
  ⟨hRT.1.trans hTS.1, hRT.2.trans hTS.2⟩

theorem Refines.joined {T S : SplitAnalyticTreeSystem G H a b E}
    (hTS : T.Refines S) (hE : AnalyticSet {p : X × X | E.r p.1 p.2}) :
    (T.joined hE).Refines (S.joined hE) :=
  joinedTreeSystem_refines hTS.1 hTS.2 a b E hE S.compatible T.compatible

omit [PolishSpace X] in
def rectangle (S : SplitAnalyticTreeSystem G H a b E)
    (hG : G.Connected) (hH : H.Connected) (r : V) (s : W) : CompatibleAnalyticRectangle E :=
  ⟨(S.left.nodeCondition r, S.right.nodeCondition s), by
    change erSaturation E (S.left.node r) = erSaturation E (S.right.node s)
    rw [S.left.saturation_eq hG E S.leftIn r a,
      S.right.saturation_eq hH E S.rightIn s b]
    exact S.compatible⟩

omit [PolishSpace X] in
theorem Refines.rectangle_le {T S : SplitAnalyticTreeSystem G H a b E}
    (hTS : T.Refines S) (hG : G.Connected) (hH : H.Connected) (r : V) (s : W) :
    T.rectangle hG hH r s ≤ S.rectangle hG hH r s :=
  ⟨hTS.1.1 r, hTS.2.1 s⟩

/-- Realize a prescribed compatible subrectangle exactly at its two nodes. -/
theorem refine_rectangle (S : SplitAnalyticTreeSystem G H a b E)
    (hG : G.IsTree) (hH : H.IsTree) (hE : AnalyticSet {p : X × X | E.r p.1 p.2})
    (r : V) (s : W) (Q : CompatibleAnalyticRectangle E)
    (hQ : Q ≤ S.rectangle hG.connected hH.connected r s) :
    ∃ T : SplitAnalyticTreeSystem G H a b E, T.Refines S ∧
      T.rectangle hG.connected hH.connected r s = Q := by
  obtain ⟨L, R, hLr, hRs, hLS, hRS, hc, _⟩ := compatible_component_refinement
    hG hH S.left S.right a r b s E hE S.leftIn S.rightIn S.compatible
    Q.val.1.property.1 Q.val.1.property.2 hQ.1
    Q.val.2.property.1 Q.val.2.property.2 hQ.2 Q.property
  let T : SplitAnalyticTreeSystem G H a b E :=
    ⟨L, R, hLS.edgesIn S.leftIn, hRS.edgesIn S.rightIn, hc⟩
  refine ⟨T, ⟨hLS, hRS⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext (Subtype.ext hLr) (Subtype.ext hRs)

/-- A lower dense family can be met by one compatible two-component refinement. -/
theorem refine_dense_rectangle (S : SplitAnalyticTreeSystem G H a b E)
    (hG : G.IsTree) (hH : H.IsTree) (hE : AnalyticSet {p : X × X | E.r p.1 p.2})
    (r : V) (s : W) (J : Set (CompatibleAnalyticRectangle E)) (hJ : IsCoinitial J) :
    ∃ T : SplitAnalyticTreeSystem G H a b E, T.Refines S ∧
      T.rectangle hG.connected hH.connected r s ∈ J := by
  obtain ⟨Q, hQJ, hQS⟩ := hJ (S.rectangle hG.connected hH.connected r s)
  obtain ⟨T, hTS, hTQ⟩ := S.refine_rectangle hG hH hE r s Q hQS
  exact ⟨T, hTS, hTQ.symm ▸ hQJ⟩

/-- Sequentially process all specified cross-component rectangles. -/
theorem refine_finite_dense_rectangles (S : SplitAnalyticTreeSystem G H a b E)
    (hG : G.IsTree) (hH : H.IsTree) (hE : AnalyticSet {p : X × X | E.r p.1 p.2})
    (F : Finset (V × W)) (J : Set (CompatibleAnalyticRectangle E))
    (hJd : IsCoinitial J) (hJl : IsLowerSet J) :
    ∃ T : SplitAnalyticTreeSystem G H a b E, T.Refines S ∧
      ∀ p ∈ F, T.rectangle hG.connected hH.connected p.1 p.2 ∈ J := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨S, .refl S, by simp⟩
  | @insert p F hp ih =>
    obtain ⟨T, hTS, hTF⟩ := ih
    obtain ⟨U, hUT, hUp⟩ := T.refine_dense_rectangle hG hH hE p.1 p.2 J hJd
    refine ⟨U, hUT.trans hTS, ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hUp
    · exact hJl (hUT.rectangle_le hG.connected hH.connected q.1 q.2) (hTF q hq)

/-- Reverse the orientation of a compatible rectangle. -/
def swapRectangle (Q : CompatibleAnalyticRectangle E) : CompatibleAnalyticRectangle E :=
  ⟨(Q.val.2, Q.val.1), Q.property.symm⟩

omit [PolishSpace X] in
@[simp] theorem swapRectangle_swap (Q : CompatibleAnalyticRectangle E) :
    swapRectangle (swapRectangle Q) = Q := rfl

/-- Requiring both orientations is a finite intersection of lower dense families. -/
def bothOrientations (J : Set (CompatibleAnalyticRectangle E)) :=
  J ∩ swapRectangle ⁻¹' J

omit [PolishSpace X] in
theorem bothOrientations_lower {J : Set (CompatibleAnalyticRectangle E)}
    (hJl : IsLowerSet J) : IsLowerSet (bothOrientations J) := by
  intro Q P hPQ hQ
  have hswap : swapRectangle P ≤ swapRectangle Q := ⟨hPQ.2, hPQ.1⟩
  exact ⟨hJl hPQ hQ.1, hJl hswap hQ.2⟩

omit [PolishSpace X] in
theorem bothOrientations_coinitial {J : Set (CompatibleAnalyticRectangle E)}
    (hJd : IsCoinitial J) (hJl : IsLowerSet J) : IsCoinitial (bothOrientations J) := by
  intro P
  obtain ⟨Q, hQJ, hQP⟩ := hJd P
  obtain ⟨R, hRJ, hRQ⟩ := hJd (swapRectangle Q)
  have hTQ : swapRectangle R ≤ Q := ⟨hRQ.2, hRQ.1⟩
  exact ⟨swapRectangle R, ⟨hJl hTQ hQJ, hRJ⟩, hTQ.trans hQP⟩

section Disjoint
variable [MeasurableSpace X] [BorelSpace X]

/-- Meet the rectangular dense requirement and separate the two node sets.
The distinct related pair is an explicit kernel hypothesis; this theorem
does not purport to prove its existence in the HKL nonsmooth kernel. -/
theorem refine_dense_disjoint_rectangle (S : SplitAnalyticTreeSystem G H a b E)
    (hG : G.IsTree) (hH : H.IsTree) (hE : AnalyticSet {p : X × X | E.r p.1 p.2})
    (r : V) (s : W) (J : Set (CompatibleAnalyticRectangle E))
    (hJd : IsCoinitial J) (hJl : IsLowerSet J)
    (hsplit : ∀ Q : CompatibleAnalyticRectangle E,
      Q ≤ S.rectangle hG.connected hH.connected r s →
      ∃ x ∈ Q.val.1.val, ∃ y ∈ Q.val.2.val, E.r x y ∧ x ≠ y) :
    ∃ T : SplitAnalyticTreeSystem G H a b E, T.Refines S ∧
      T.rectangle hG.connected hH.connected r s ∈ J ∧
      Disjoint (T.left.node r) (T.right.node s) := by
  obtain ⟨Q, hQJ, hQS⟩ := hJd (S.rectangle hG.connected hH.connected r s)
  obtain ⟨x, hx, y, hy, hxy, hne⟩ := hsplit Q hQS
  obtain ⟨C, D, hCQ, hDQ, hCa, hDa, hCn, hDn, hdisj, hCD⟩ :=
    disjoint_analytic_compatible_refinement_of_related_pair E hE
      Q.val.1.property.1 Q.val.2.property.1 hx hy hxy hne
  let P : CompatibleAnalyticRectangle E := ⟨(⟨C, hCa, hCn⟩, ⟨D, hDa, hDn⟩), hCD⟩
  have hPQ : P ≤ Q := ⟨hCQ, hDQ⟩
  obtain ⟨T, hTS, hTP⟩ := S.refine_rectangle hG hH hE r s P (hPQ.trans hQS)
  refine ⟨T, hTS, hTP.symm ▸ hJl hPQ hQJ, ?_⟩
  have hleft : T.left.node r = C := congrArg (fun q : CompatibleAnalyticRectangle E => q.val.1.val) hTP
  have hright : T.right.node s = D := congrArg (fun q : CompatibleAnalyticRectangle E => q.val.2.val) hTP
  rwa [hleft, hright]

/-- The finite rectangular phase, including disjointness. Every step keeps
the joining edge full and preserves all requirements from earlier steps. -/
theorem refine_finite_dense_disjoint_rectangles (S : SplitAnalyticTreeSystem G H a b E)
    (hG : G.IsTree) (hH : H.IsTree) (hE : AnalyticSet {p : X × X | E.r p.1 p.2})
    (F : Finset (V × W)) (J : Set (CompatibleAnalyticRectangle E))
    (hJd : IsCoinitial J) (hJl : IsLowerSet J)
    (hsplit : ∀ r s (Q : CompatibleAnalyticRectangle E),
      Q ≤ S.rectangle hG.connected hH.connected r s →
      ∃ x ∈ Q.val.1.val, ∃ y ∈ Q.val.2.val, E.r x y ∧ x ≠ y) :
    ∃ T : SplitAnalyticTreeSystem G H a b E, T.Refines S ∧
      ∀ p ∈ F, T.rectangle hG.connected hH.connected p.1 p.2 ∈ J ∧
        Disjoint (T.left.node p.1) (T.right.node p.2) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨S, .refl S, by simp⟩
  | @insert p F hp ih =>
    obtain ⟨T, hTS, hTF⟩ := ih
    obtain ⟨U, hUT, hUp, hUdisj⟩ := T.refine_dense_disjoint_rectangle hG hH hE p.1 p.2 J
      hJd hJl (fun Q hQT => hsplit p.1 p.2 Q
        (hQT.trans (hTS.rectangle_le hG.connected hH.connected p.1 p.2)))
    refine ⟨U, hUT.trans hTS, ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ⟨hUp, hUdisj⟩
    · exact ⟨hJl (hUT.rectangle_le hG.connected hH.connected q.1 q.2) (hTF q hq).1,
        (hTF q hq).2.mono (hUT.1.1 q.1) (hUT.2.1 q.2)⟩

/-- The complete finite rectangular phase in two-component form. Both
orientations meet the dense family and every cross-component pair is disjoint.
The distinct-pair kernel hypothesis remains explicit. -/
theorem refine_all_dense_disjoint_rectangles [Fintype V] [Fintype W]
    (S : SplitAnalyticTreeSystem G H a b E)
    (hG : G.IsTree) (hH : H.IsTree) (hE : AnalyticSet {p : X × X | E.r p.1 p.2})
    (J : Set (CompatibleAnalyticRectangle E)) (hJd : IsCoinitial J) (hJl : IsLowerSet J)
    (hsplit : ∀ r s (Q : CompatibleAnalyticRectangle E),
      Q ≤ S.rectangle hG.connected hH.connected r s →
      ∃ x ∈ Q.val.1.val, ∃ y ∈ Q.val.2.val, E.r x y ∧ x ≠ y) :
    ∃ T : SplitAnalyticTreeSystem G H a b E, T.Refines S ∧
      ∀ r s, T.rectangle hG.connected hH.connected r s ∈ J ∧
        swapRectangle (T.rectangle hG.connected hH.connected r s) ∈ J ∧
        Disjoint (T.left.node r) (T.right.node s) := by
  obtain ⟨T, hTS, hTF⟩ := S.refine_finite_dense_disjoint_rectangles hG hH hE Finset.univ
    (bothOrientations J) (bothOrientations_coinitial hJd hJl) (bothOrientations_lower hJl) hsplit
  refine ⟨T, hTS, ?_⟩
  intro r s
  have hp := hTF (r, s) (Finset.mem_univ _)
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

end Disjoint
end SplitAnalyticTreeSystem
end PolishSpaceBook
