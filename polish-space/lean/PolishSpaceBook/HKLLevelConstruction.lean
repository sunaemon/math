module

public import PolishSpaceBook.HKLCompatibleRefinements

@[expose] public section

/-!
# Assembling the three finite stages of an HKL level

Node refinement is performed first while the joining edge stays full.
Compatible, disjoint rectangular refinements follow in the two components.
Only then are the edge relations refined into their dense family. The
successor step is transferred to binary words and iterated over all levels.
The nonempty analytic kernel and its distinct-related-pair property remain
explicit hypotheses. The kernel theorem, generic-pair theorem, and actual
analytic-condition fusion points are not proved by this module.
`AnalyticConditionFusion.lean` supplies closed-witness fusion in Baire space;
its application to these coherent levels is still a separate obligation.
-/

namespace PolishSpaceBook
open Set Function SimpleGraph MeasureTheory

variable {V W X : Type*} [TopologicalSpace X] [PolishSpace X]
variable {G : SimpleGraph V} {H : SimpleGraph W} {a : V} {b : W}

/-- Restrict a joined level to its left component. -/
def AnalyticTreeSystem.leftComponent
    (S : AnalyticTreeSystem (joinedTreeGraph G H a b) X) : AnalyticTreeSystem G X where
  node := fun v => S.node (.inl v)
  edge := fun u v => S.edge (.inl u) (.inl v)
  node_analytic := fun _ => S.node_analytic _
  node_nonempty := fun _ => S.node_nonempty _
  edge_analytic := fun u v h => S.edge_analytic _ _ ((joinedTreeGraph_inl a b u v).mpr h)
  fst_edge := fun u v h => S.fst_edge _ _ ((joinedTreeGraph_inl a b u v).mpr h)
  snd_edge := fun u v h => S.snd_edge _ _ ((joinedTreeGraph_inl a b u v).mpr h)
  edge_swap := fun u v h => S.edge_swap _ _ ((joinedTreeGraph_inl a b u v).mpr h)

/-- Restrict a joined level to its right component. -/
def AnalyticTreeSystem.rightComponent
    (S : AnalyticTreeSystem (joinedTreeGraph G H a b) X) : AnalyticTreeSystem H X where
  node := fun v => S.node (.inr v)
  edge := fun u v => S.edge (.inr u) (.inr v)
  node_analytic := fun _ => S.node_analytic _
  node_nonempty := fun _ => S.node_nonempty _
  edge_analytic := fun u v h => S.edge_analytic _ _ ((joinedTreeGraph_inr a b u v).mpr h)
  fst_edge := fun u v h => S.fst_edge _ _ ((joinedTreeGraph_inr a b u v).mpr h)
  snd_edge := fun u v h => S.snd_edge _ _ ((joinedTreeGraph_inr a b u v).mpr h)
  edge_swap := fun u v h => S.edge_swap _ _ ((joinedTreeGraph_inr a b u v).mpr h)

namespace SplitAnalyticTreeSystem
variable {E : Setoid X}

/-- Finish all node requirements and retain the two-component presentation. -/
theorem refine_all_nodes [Fintype V] [Fintype W]
    (S : SplitAnalyticTreeSystem G H a b E) (hG : G.IsTree) (hH : H.IsTree)
    (hE : AnalyticSet {p : X × X | E.r p.1 p.2})
    (D : Set (AnalyticCondition X)) (hDd : IsCoinitial D) (hDl : IsLowerSet D) :
    ∃ T : SplitAnalyticTreeSystem G H a b E, T.Refines S ∧
      ∀ v, (T.joined hE).nodeCondition v ∈ D := by
  have htree : (joinedTreeGraph G H a b).IsTree := isTree_sum_join hG hH a b
  obtain ⟨U, hUS, hUD, _⟩ := analytic_tree_nodes_dense_full htree (S.joined hE) Finset.univ
    (fun _ => D) (fun _ => hDd) (fun _ => hDl) E
  have hUE : U.EdgesIn E := hUS.edgesIn
    (joinedTreeSystem_edgesIn S.left S.right a b E hE S.compatible S.leftIn S.rightIn)
  let T : SplitAnalyticTreeSystem G H a b E := {
    left := U.leftComponent
    right := U.rightComponent
    leftIn := fun u v h => hUE _ _ ((joinedTreeGraph_inl a b u v).mpr h)
    rightIn := fun u v h => hUE _ _ ((joinedTreeGraph_inr a b u v).mpr h)
    compatible := U.saturation_eq htree.connected E hUE (.inl a) (.inr b) }
  have hTS : T.Refines S :=
    ⟨⟨fun v => hUS.1 (.inl v), fun u v => hUS.2 (.inl u) (.inl v)⟩,
      ⟨fun v => hUS.1 (.inr v), fun u v => hUS.2 (.inr u) (.inr v)⟩⟩
  refine ⟨T, hTS, ?_⟩
  intro v
  cases v with
  | inl v => exact hUD (.inl v) (Finset.mem_univ _)
  | inr v => exact hUD (.inr v) (Finset.mem_univ _)

variable [MeasurableSpace X] [BorelSpace X]

/-- Assemble node, rectangular, and edge refinement in the book's order.
Every final edge is contained in its original edge, and all previously
obtained node and rectangle requirements survive the last edge stage. -/
theorem refine_three_stages [Fintype V] [Fintype W]
    (S : SplitAnalyticTreeSystem G H a b E) (hG : G.IsTree) (hH : H.IsTree)
    (hE : AnalyticSet {p : X × X | E.r p.1 p.2})
    (D : Set (AnalyticCondition X)) (hDd : IsCoinitial D) (hDl : IsLowerSet D)
    (J : Set (CompatibleAnalyticRectangle E)) (hJd : IsCoinitial J) (hJl : IsLowerSet J)
    (K : Set (AnalyticCondition (X × X))) (hKd : IsCoinitial K) (hKl : IsLowerSet K)
    (hsplit : ∀ r s (Q : CompatibleAnalyticRectangle E),
      Q ≤ S.rectangle hG.connected hH.connected r s →
      ∃ x ∈ Q.val.1.val, ∃ y ∈ Q.val.2.val, E.r x y ∧ x ≠ y) :
    ∃ U : AnalyticTreeSystem (joinedTreeGraph G H a b) X,
      U.Refines (S.joined hE) ∧ (∀ v, U.nodeCondition v ∈ D) ∧
      (∀ u v (h : (joinedTreeGraph G H a b).Adj u v), U.edgeCondition h ∈ K) ∧
      ∃ hUE : U.EdgesIn E, ∀ r s,
        U.rectangleCondition (isTree_sum_join hG hH a b).connected E hUE (.inl r) (.inr s) ∈ J ∧
        U.rectangleCondition (isTree_sum_join hG hH a b).connected E hUE (.inr s) (.inl r) ∈ J ∧
        Disjoint (U.node (.inl r)) (U.node (.inr s)) := by
  classical
  obtain ⟨T, hTS, hTD⟩ := S.refine_all_nodes hG hH hE D hDd hDl
  obtain ⟨R, hRT, hRJ⟩ := T.refine_all_dense_disjoint_rectangles hG hH hE J hJd hJl
    (fun r s Q hQT => hsplit r s Q (hQT.trans (hTS.rectangle_le hG.connected hH.connected r s)))
  have htree : (joinedTreeGraph G H a b).IsTree := isTree_sum_join hG hH a b
  let F := Finset.univ.filter (fun p : (V ⊕ W) × (V ⊕ W) =>
    (joinedTreeGraph G H a b).Adj p.1 p.2)
  have hF : ∀ p ∈ F, (joinedTreeGraph G H a b).Adj p.1 p.2 :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  obtain ⟨U, hUR, hUK⟩ := analytic_tree_edges_dense htree (R.joined hE) F hF
    (fun _ _ => K) (fun _ _ _ => hKd) (fun _ _ _ => hKl)
  have hRE : (R.joined hE).EdgesIn E :=
    joinedTreeSystem_edgesIn R.left R.right a b E hE R.compatible R.leftIn R.rightIn
  have hUE := hUR.edgesIn hRE
  refine ⟨U, hUR.trans ((hRT.trans hTS).joined hE), ?_, ?_, hUE, ?_⟩
  · intro v
    exact hUR.node_mem hDl ((hRT.joined hE).node_mem hDl (hTD v))
  · intro u v h
    exact hUK (u, v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  · intro r s
    have hJrs : (R.joined hE).rectangleCondition htree.connected E hRE (.inl r) (.inr s) ∈ J :=
      (hRJ r s).1
    have hJsr : (R.joined hE).rectangleCondition htree.connected E hRE (.inr s) (.inl r) ∈ J :=
      (hRJ r s).2.1
    exact ⟨hUR.rectangle_mem htree.connected E hRE hJl hJrs,
      hUR.rectangle_mem htree.connected E hRE hJl hJsr,
      hUR.disjoint (hRJ r s).2.2⟩

end SplitAnalyticTreeSystem

/-- Transport all node sets and edge relations along a graph's vertex map. -/
def AnalyticTreeSystem.comap {A B : Type*} {L : SimpleGraph B}
    (S : AnalyticTreeSystem L X) (f : A → B) : AnalyticTreeSystem (L.comap f) X where
  node := fun v => S.node (f v)
  edge := fun u v => S.edge (f u) (f v)
  node_analytic := fun v => S.node_analytic (f v)
  node_nonempty := fun v => S.node_nonempty (f v)
  edge_analytic := fun u v h => S.edge_analytic (f u) (f v) h
  fst_edge := fun u v h => S.fst_edge (f u) (f v) h
  snd_edge := fun u v h => S.snd_edge (f u) (f v) h
  edge_swap := fun u v h => S.edge_swap (f u) (f v) h

/-- Initially the two last-bit components have exactly the old node sets and
relations. The new full joining edge has equal endpoint sets. -/
def duplicateBinaryLevel {n : ℕ} (S : AnalyticTreeSystem (crucialPairGraph n) X)
    (E : Setoid X) (hSE : S.EdgesIn E) :
    SplitAnalyticTreeSystem (crucialPairGraph n) (crucialPairGraph n)
      (zeroBinaryWord n) (zeroBinaryWord n) E :=
  ⟨S, S, hSE, hSE, rfl⟩

/-- Return from the two last-bit components to the next binary level. -/
def binarySuccessorSystem {n : ℕ}
    (S : AnalyticTreeSystem (joinedTreeGraph (crucialPairGraph n) (crucialPairGraph n)
      (zeroBinaryWord n) (zeroBinaryWord n)) X) : AnalyticTreeSystem (crucialPairGraph (n + 1)) X :=
  S.comap (splitLastBit n)

omit [PolishSpace X] in
@[simp] theorem binarySuccessorSystem_node_false {n : ℕ}
    (S : AnalyticTreeSystem (joinedTreeGraph (crucialPairGraph n) (crucialPairGraph n)
      (zeroBinaryWord n) (zeroBinaryWord n)) X) (s : binaryWord n) :
    (binarySuccessorSystem S).node (Fin.snoc s false) = S.node (.inl s) := by
  simp [binarySuccessorSystem, AnalyticTreeSystem.comap, splitLastBit]

omit [PolishSpace X] in
@[simp] theorem binarySuccessorSystem_node_true {n : ℕ}
    (S : AnalyticTreeSystem (joinedTreeGraph (crucialPairGraph n) (crucialPairGraph n)
      (zeroBinaryWord n) (zeroBinaryWord n)) X) (s : binaryWord n) :
    (binarySuccessorSystem S).node (Fin.snoc s true) = S.node (.inr s) := by
  simp [binarySuccessorSystem, AnalyticTreeSystem.comap, splitLastBit]

variable [MeasurableSpace X] [BorelSpace X]

/-- The three next-level requirements, together with parent containment. -/
def HKLSuccessorRequirements {n : ℕ} (E : Setoid X)
    (D : Set (AnalyticCondition X)) (J : Set (CompatibleAnalyticRectangle E))
    (K : Set (AnalyticCondition (X × X)))
    (S : AnalyticTreeSystem (crucialPairGraph n) X)
    (T : AnalyticTreeSystem (crucialPairGraph (n + 1)) X) : Prop :=
      (∀ s b, T.node (Fin.snoc s b) ⊆ S.node s) ∧
      (∀ s t b, T.edge (Fin.snoc s b) (Fin.snoc t b) ⊆ S.edge s t) ∧
      (∀ s, T.nodeCondition s ∈ D) ∧
      (∀ s t (h : (crucialPairGraph (n + 1)).Adj s t), T.edgeCondition h ∈ K) ∧
      ∃ hTE : T.EdgesIn E, ∀ r s,
        T.rectangleCondition (crucialPairGraph_isTree (n + 1)).connected E hTE
          (Fin.snoc r false) (Fin.snoc s true) ∈ J ∧
        T.rectangleCondition (crucialPairGraph_isTree (n + 1)).connected E hTE
          (Fin.snoc s true) (Fin.snoc r false) ∈ J ∧
        Disjoint (T.node (Fin.snoc r false)) (T.node (Fin.snoc s true))

/-- One full successor step of HKL on the actual binary words. Copied edges
remain inside their parent relations. The nonsmooth-kernel hypothesis and
subsequent infinite fusion are not assumed as conclusions of this step. -/
theorem hkl_successor_level {n : ℕ} (S : AnalyticTreeSystem (crucialPairGraph n) X)
    (E : Setoid X) (hE : AnalyticSet {p : X × X | E.r p.1 p.2}) (hSE : S.EdgesIn E)
    (D : Set (AnalyticCondition X)) (hDd : IsCoinitial D) (hDl : IsLowerSet D)
    (J : Set (CompatibleAnalyticRectangle E)) (hJd : IsCoinitial J) (hJl : IsLowerSet J)
    (K : Set (AnalyticCondition (X × X))) (hKd : IsCoinitial K) (hKl : IsLowerSet K)
    (hsplit : ∀ r s (Q : CompatibleAnalyticRectangle E),
      Q.val.1.val ⊆ S.node r → Q.val.2.val ⊆ S.node s →
      ∃ x ∈ Q.val.1.val, ∃ y ∈ Q.val.2.val, E.r x y ∧ x ≠ y) :
    ∃ T : AnalyticTreeSystem (crucialPairGraph (n + 1)) X,
      HKLSuccessorRequirements E D J K S T := by
  let B := duplicateBinaryLevel S E hSE
  obtain ⟨U, hUB, hUD, hUK, hUE, hUJ⟩ := B.refine_three_stages
    (crucialPairGraph_isTree n) (crucialPairGraph_isTree n) hE
    D hDd hDl J hJd hJl K hKd hKl (fun r s Q hQ => hsplit r s Q hQ.1 hQ.2)
  let T := binarySuccessorSystem U
  have hTE : T.EdgesIn E := fun u v h => hUE _ _ h
  refine ⟨T, ?_, ?_, ?_, ?_, hTE, ?_⟩
  · intro s b
    cases b
    · have h : U.node (.inl s) ⊆ S.node s := hUB.1 (.inl s)
      simpa only [T, binarySuccessorSystem_node_false] using h
    · have h : U.node (.inr s) ⊆ S.node s := hUB.1 (.inr s)
      simpa only [T, binarySuccessorSystem_node_true] using h
  · intro s t b
    cases b
    · have h : U.edge (.inl s) (.inl t) ⊆ S.edge s t := hUB.2 (.inl s) (.inl t)
      simpa [T, binarySuccessorSystem, AnalyticTreeSystem.comap, splitLastBit] using h
    · have h : U.edge (.inr s) (.inr t) ⊆ S.edge s t := hUB.2 (.inr s) (.inr t)
      simpa [T, binarySuccessorSystem, AnalyticTreeSystem.comap, splitLastBit] using h
  · intro s
    exact hUD (splitLastBit n s)
  · intro s t h
    exact hUK (splitLastBit n s) (splitLastBit n t) h
  · intro r s
    have hf : T.rectangleCondition (crucialPairGraph_isTree (n + 1)).connected E hTE
        (Fin.snoc r false) (Fin.snoc s true) =
        U.rectangleCondition (isTree_sum_join (crucialPairGraph_isTree n)
          (crucialPairGraph_isTree n) (zeroBinaryWord n) (zeroBinaryWord n)).connected E hUE
          (.inl r) (.inr s) := by
      apply Subtype.ext
      apply Prod.ext <;> apply Subtype.ext <;>
        simp [AnalyticTreeSystem.rectangleCondition, AnalyticTreeSystem.nodeCondition, T]
    have hb : T.rectangleCondition (crucialPairGraph_isTree (n + 1)).connected E hTE
        (Fin.snoc s true) (Fin.snoc r false) =
        U.rectangleCondition (isTree_sum_join (crucialPairGraph_isTree n)
          (crucialPairGraph_isTree n) (zeroBinaryWord n) (zeroBinaryWord n)).connected E hUE
          (.inr s) (.inl r) := by
      apply Subtype.ext
      apply Prod.ext <;> apply Subtype.ext <;>
        simp [AnalyticTreeSystem.rectangleCondition, AnalyticTreeSystem.nodeCondition, T]
    refine ⟨hf.symm ▸ (hUJ r s).1, hb.symm ▸ (hUJ r s).2.1, ?_⟩
    simpa only [T, binarySuccessorSystem_node_false, binarySuccessorSystem_node_true] using
      (hUJ r s).2.2

/-- Repeat the verified successor construction at every level. The initial
level is given, and the distinct-pair property is assumed on a common kernel.
This constructs the coherent systems, not their fusion points. -/
theorem hkl_coherent_levels (E : Setoid X)
    (hE : AnalyticSet {p : X × X | E.r p.1 p.2}) (Ω : Set X)
    (S₀ : AnalyticTreeSystem (crucialPairGraph 0) X) (hS₀E : S₀.EdgesIn E)
    (hS₀Ω : ∀ s, S₀.node s ⊆ Ω)
    (D : ℕ → Set (AnalyticCondition X)) (hDd : ∀ n, IsCoinitial (D n))
    (hDl : ∀ n, IsLowerSet (D n))
    (J : ℕ → Set (CompatibleAnalyticRectangle E)) (hJd : ∀ n, IsCoinitial (J n))
    (hJl : ∀ n, IsLowerSet (J n))
    (K : ℕ → Set (AnalyticCondition (X × X))) (hKd : ∀ n, IsCoinitial (K n))
    (hKl : ∀ n, IsLowerSet (K n))
    (hsplit : ∀ Q : CompatibleAnalyticRectangle E, Q.val.1.val ⊆ Ω → Q.val.2.val ⊆ Ω →
      ∃ x ∈ Q.val.1.val, ∃ y ∈ Q.val.2.val, E.r x y ∧ x ≠ y) :
    ∃ S : ∀ n, AnalyticTreeSystem (crucialPairGraph n) X,
      S 0 = S₀ ∧ (∀ n, (S n).EdgesIn E) ∧ (∀ n s, (S n).node s ⊆ Ω) ∧
      ∀ n, HKLSuccessorRequirements E (D (n + 1)) (J (n + 1)) (K (n + 1)) (S n) (S (n + 1)) := by
  classical
  let State (n : ℕ) := {S : AnalyticTreeSystem (crucialPairGraph n) X //
    S.EdgesIn E ∧ ∀ s, S.node s ⊆ Ω}
  have hnext (n : ℕ) (S : State n) : ∃ T : State (n + 1),
      HKLSuccessorRequirements E (D (n + 1)) (J (n + 1)) (K (n + 1)) S.val T.val := by
    obtain ⟨T, hT⟩ := hkl_successor_level S.val E hE S.property.1
      (D (n + 1)) (hDd _) (hDl _) (J (n + 1)) (hJd _) (hJl _)
      (K (n + 1)) (hKd _) (hKl _)
      (fun r s Q hQr hQs => hsplit Q (hQr.trans (S.property.2 r)) (hQs.trans (S.property.2 s)))
    obtain ⟨hTE, _⟩ := hT.2.2.2.2
    have hTΩ (w : binaryWord (n + 1)) : T.node w ⊆ Ω := by
      have hsub := hT.1 (Fin.init w) (w (Fin.last n))
      rw [Fin.snoc_init_self] at hsub
      exact hsub.trans (S.property.2 _)
    exact ⟨⟨T, hTE, hTΩ⟩, hT⟩
  let states : (n : ℕ) → State n :=
    fun n => Nat.rec (motive := fun n => State n) ⟨S₀, hS₀E, hS₀Ω⟩
      (fun n S => (hnext n S).choose) n
  refine ⟨fun n => (states n).val, rfl, fun n => (states n).property.1,
    fun n => (states n).property.2, ?_⟩
  intro n
  exact (hnext n (states n)).choose_spec

/-- The root level has its one nonempty analytic node and no graph edges. -/
def rootBinarySystem (C : AnalyticCondition X) : AnalyticTreeSystem (crucialPairGraph 0) X where
  node := fun _ => C.val
  edge := fun _ _ => ∅
  node_analytic := fun _ => C.property.1
  node_nonempty := fun _ => C.property.2
  edge_analytic := fun _ _ h => False.elim h
  fst_edge := fun _ _ h => False.elim h
  snd_edge := fun _ _ h => False.elim h
  edge_swap := fun _ _ h => False.elim h

/-- Start inside the nonempty analytic kernel, meet the zeroth node requirement,
and build all levels with all three families of conditions. The kernel and
its distinct-pair property are hypotheses, rather than axioms or established
conclusions about every nonsmooth Borel equivalence relation. -/
theorem hkl_coherent_levels_from_kernel (E : Setoid X)
    (hE : AnalyticSet {p : X × X | E.r p.1 p.2}) (Ω : Set X)
    (hΩa : AnalyticSet Ω) (hΩn : Ω.Nonempty)
    (D : ℕ → Set (AnalyticCondition X)) (hDd : ∀ n, IsCoinitial (D n))
    (hDl : ∀ n, IsLowerSet (D n))
    (J : ℕ → Set (CompatibleAnalyticRectangle E)) (hJd : ∀ n, IsCoinitial (J n))
    (hJl : ∀ n, IsLowerSet (J n))
    (K : ℕ → Set (AnalyticCondition (X × X))) (hKd : ∀ n, IsCoinitial (K n))
    (hKl : ∀ n, IsLowerSet (K n))
    (hsplit : ∀ Q : CompatibleAnalyticRectangle E, Q.val.1.val ⊆ Ω → Q.val.2.val ⊆ Ω →
      ∃ x ∈ Q.val.1.val, ∃ y ∈ Q.val.2.val, E.r x y ∧ x ≠ y) :
    ∃ S : ∀ n, AnalyticTreeSystem (crucialPairGraph n) X,
      (∀ n, (S n).EdgesIn E) ∧ (∀ n s, (S n).node s ⊆ Ω) ∧
      (∀ n s, (S n).nodeCondition s ∈ D n) ∧
      (∀ n s t (h : (crucialPairGraph n).Adj s t), (S n).edgeCondition h ∈ K n) ∧
      ∀ n, HKLSuccessorRequirements E (D (n + 1)) (J (n + 1)) (K (n + 1)) (S n) (S (n + 1)) := by
  obtain ⟨C, hCD, hCΩ⟩ := hDd 0 ⟨Ω, hΩa, hΩn⟩
  have hrootE : (rootBinarySystem C).EdgesIn E := fun _ _ h => False.elim h
  obtain ⟨S, hS0, hSE, hSΩ, hstep⟩ := hkl_coherent_levels E hE Ω (rootBinarySystem C)
    hrootE (fun _ => hCΩ) D hDd hDl J hJd hJl K hKd hKl hsplit
  refine ⟨S, hSE, hSΩ, ?_, ?_, hstep⟩
  · intro n
    cases n with
    | zero => intro s; rw [hS0]; exact hCD
    | succ n => exact (hstep n).2.2.1
  · intro n
    cases n with
    | zero => exact fun _ _ h => False.elim h
    | succ n => exact (hstep n).2.2.2.1

end PolishSpaceBook
