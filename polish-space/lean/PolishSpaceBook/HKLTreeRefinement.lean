module

public import PolishSpaceBook.EquivalenceRelationSeparation
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Propagating analytic refinements along a tree

The construction follows the book's outward propagation from a chosen root.
At every step the edge is restricted at its processed coordinate and its
other projection becomes the next node. Unique root paths ensure that these
local steps agree on every edge. Only finite paths are used, so the node
refinement construction also works for infinite trees. Both node and edge
refinement are proved. `HKLDenseRefinements.lean` supplies the finite node
and edge stages, and `HKLCompatibleRefinements.lean` supplies the rectangular
stage under the distinct-pair kernel hypothesis. Effective coding, the
kernel arguments, and analytic-condition fusion remain separate obligations.
-/

namespace PolishSpaceBook
open Set Function SimpleGraph MeasureTheory

variable {V X : Type*} [TopologicalSpace X] [PolishSpace X]

/-- Both orientations of each edge are stored, with coordinate swap relating
those orientations. The equivalence relation containing the edges is not
needed for propagation; containment is preserved because every edge shrinks. -/
structure AnalyticTreeSystem (G : SimpleGraph V) (X : Type*) [TopologicalSpace X] where
  node : V → Set X
  edge : V → V → Set (X × X)
  node_analytic : ∀ v, AnalyticSet (node v)
  node_nonempty : ∀ v, (node v).Nonempty
  edge_analytic : ∀ u v, G.Adj u v → AnalyticSet (edge u v)
  fst_edge : ∀ u v, G.Adj u v → Prod.fst '' edge u v = node u
  snd_edge : ∀ u v, G.Adj u v → Prod.snd '' edge u v = node v
  edge_swap : ∀ u v, G.Adj u v → ∀ x y, (x, y) ∈ edge u v ↔ (y, x) ∈ edge v u

/-- Process the edges of a walk in order, starting with the changed root set. -/
def propagateTreeSet {G : SimpleGraph V} (S : AnalyticTreeSystem G X) :
    {u v : V} → G.Walk u v → Set X → Set X
  | _, _, .nil, C => C
  | u, _, .cons (v := v) _ p, C =>
      propagateTreeSet S p (Prod.snd '' restrictRelationLeft (S.edge u v) C)

omit [PolishSpace X] in
@[simp] theorem propagateTreeSet_nil {G : SimpleGraph V} (S : AnalyticTreeSystem G X)
    (u : V) (C : Set X) : propagateTreeSet S (.nil : G.Walk u u) C = C := rfl

omit [PolishSpace X] in
theorem propagateTreeSet_concat {G : SimpleGraph V} (S : AnalyticTreeSystem G X)
    {u v w : V} (p : G.Walk u v) (h : G.Adj v w) (C : Set X) :
    propagateTreeSet S (p.concat h) C =
      Prod.snd '' restrictRelationLeft (S.edge v w) (propagateTreeSet S p C) := by
  induction p generalizing C with
  | nil => rfl
  | cons h p ih => exact ih _ _

/-- Every step retains nonemptiness, analyticity, and containment in the old node. -/
theorem propagateTreeSet_properties {G : SimpleGraph V} (S : AnalyticTreeSystem G X)
    {u v : V} (p : G.Walk u v) {C : Set X}
    (hCa : AnalyticSet C) (hCn : C.Nonempty) (hCs : C ⊆ S.node u) :
    AnalyticSet (propagateTreeSet S p C) ∧
      (propagateTreeSet S p C).Nonempty ∧ propagateTreeSet S p C ⊆ S.node v := by
  induction p generalizing C with
  | nil => exact ⟨hCa, hCn, hCs⟩
  | @cons u v w h p ih =>
    have hsub : C ⊆ Prod.fst '' S.edge u v := by rwa [S.fst_edge u v h]
    have ha := (analyticSet_inter (S.edge_analytic u v h)
      (hCa.preimage continuous_fst)).image_of_continuous continuous_snd
    have hn := (restrictRelationLeft_nonempty hsub hCn).image Prod.snd
    have hs : Prod.snd '' restrictRelationLeft (S.edge u v) C ⊆ S.node v := by
      rw [← S.snd_edge u v h]
      exact image_mono inter_subset_left
    exact ih ha hn hs

/-- The unique simple path from the changed node to a given node. -/
noncomputable def treeRootPath {G : SimpleGraph V} (hG : G.IsTree) (r v : V) : G.Walk r v :=
  (hG.connected.exists_isPath r v).choose

theorem treeRootPath_isPath {G : SimpleGraph V} (hG : G.IsTree) (r v : V) :
    (treeRootPath hG r v).IsPath := (hG.connected.exists_isPath r v).choose_spec

theorem treeRootPath_self {G : SimpleGraph V} (hG : G.IsTree) (r : V) :
    treeRootPath hG r r = .nil := by
  exact Subtype.mk.inj ((hG.isAcyclic.subsingleton_path r r).elim
    ⟨_, treeRootPath_isPath hG r r⟩ ⟨.nil, Walk.IsPath.nil⟩)

/-- On each edge, one root path extends the other by exactly that edge. -/
theorem treeRootPath_adj {G : SimpleGraph V} (hG : G.IsTree) (r : V)
    {u v : V} (h : G.Adj u v) :
    treeRootPath hG r v = (treeRootPath hG r u).concat h ∨
      treeRootPath hG r u = (treeRootPath hG r v).concat h.symm := by
  classical
  by_cases hu : u ∈ (treeRootPath hG r v).support
  · exact Or.inl (hG.isAcyclic.path_concat (treeRootPath_isPath hG r u)
      (treeRootPath_isPath hG r v) h hu)
  · have hv := hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
      (treeRootPath_isPath hG r u) (treeRootPath_isPath hG r v) h hu
    exact Or.inr (hG.isAcyclic.path_concat (treeRootPath_isPath hG r v)
      (treeRootPath_isPath hG r u) h.symm hv)

/-- Shrink both endpoint coordinates; outward propagation will ensure the
processed coordinate has no additional loss. -/
def restrictTreeEdge (R : Set (X × X)) (A B : Set X) : Set (X × X) :=
  (R ∩ Prod.fst ⁻¹' A) ∩ Prod.snd ⁻¹' B

omit [TopologicalSpace X] [PolishSpace X] in
theorem restrictTreeEdge_of_propagated {R : Set (X × X)} {A B : Set X}
    (hB : B = Prod.snd '' restrictRelationLeft R A) :
    restrictTreeEdge R A B = restrictRelationLeft R A := by
  apply Subset.antisymm inter_subset_left
  intro p hp
  exact ⟨hp, hB ▸ mem_image_of_mem Prod.snd hp⟩

omit [TopologicalSpace X] [PolishSpace X] in
theorem restrictTreeEdge_projections {R : Set (X × X)} {A B : Set X}
    (hA : A ⊆ Prod.fst '' R) (hB : B = Prod.snd '' restrictRelationLeft R A) :
    Prod.fst '' restrictTreeEdge R A B = A ∧
      Prod.snd '' restrictTreeEdge R A B = B := by
  rw [restrictTreeEdge_of_propagated hB]
  exact ⟨restrictRelationLeft_fst hA, hB.symm⟩

omit [TopologicalSpace X] [PolishSpace X] in
theorem fst_image_eq_snd_image_of_swap {R T : Set (X × X)}
    (h : ∀ x y, (x, y) ∈ R ↔ (y, x) ∈ T) : Prod.fst '' R = Prod.snd '' T := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    exact ⟨(b, a), (h a b).mp hab, rfl⟩
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    exact ⟨(b, a), (h b a).mpr hab, rfl⟩

/-- Any nonempty analytic shrink of a node propagates throughout the tree,
retaining full projections on every edge. Each new edge is exactly the old
edge restricted to its new endpoints. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Root the tree at the changed node, and put the prescribed subset there. If $u$ has been processed and $v$
    is its next neighbor away from the root, define
    $$A'_v:=\pi_1(R_{u,v}\cap(A'_u\times X)).$$
    Every point of $A'_u$ has a partner in the old relation, so this set is nonempty. Restricting the edge to
    $A'_u\times A'_v$ preserves exactly these two projections. Continue along the unique paths from the root,
    and finally restrict every old edge to its new endpoints. The unique-path property ensures consistency.
    In particular the chosen root set remains unchanged.

    Now prescribe a nonempty subrelation $P\IncludedIn R_{u,v}$, and put
    $$C:=\pi_0(P),\qquad D:=\pi_1(P).$$
    First propagate $C$ from $u$ as above. Every pair of $P$ survives the restriction of the edge, since its first
    coordinate lies in $C$ and its second lies in the propagated set at $v$. Next propagate $D$ from $v$ in this
    refined system. The new set at $u$ is contained in $C$. Conversely, each point of $C$ has a partner in $D$
    through $P$; the reverse edge retains that pair, so the point survives propagation back to $u$.
    Thus the endpoint sets are exactly $C,D$, and the refined edge still contains $P$. Replace it by $P$ and
    its reverse by the swapped relation. Both projections remain full, and all other edges stay coherent.
    All changes are restrictions, so previously satisfied downward-closed requirements are preserved.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{finite-tree refinement lemma}{Finite-tree refinement}]
-/
theorem analytic_tree_node_refinement {G : SimpleGraph V} (hG : G.IsTree)
    (S : AnalyticTreeSystem G X) (r : V) {C : Set X}
    (hCa : AnalyticSet C) (hCn : C.Nonempty) (hCs : C ⊆ S.node r) :
    ∃ T : AnalyticTreeSystem G X, T.node r = C ∧
      (∀ v, T.node v ⊆ S.node v) ∧
      (∀ u v, T.edge u v = restrictTreeEdge (S.edge u v) (T.node u) (T.node v)) ∧
      (∀ v, T.node v = propagateTreeSet S (treeRootPath hG r v) C) := by
  classical
  let B : V → Set X := fun v => propagateTreeSet S (treeRootPath hG r v) C
  let Q : V → V → Set (X × X) := fun u v => restrictTreeEdge (S.edge u v) (B u) (B v)
  have hB v : AnalyticSet (B v) ∧ (B v).Nonempty ∧ B v ⊆ S.node v :=
    propagateTreeSet_properties S _ hCa hCn hCs
  have hswap u v (h : G.Adj u v) (x y : X) : (x, y) ∈ Q u v ↔ (y, x) ∈ Q v u := by
    change ((x, y) ∈ S.edge u v ∧ x ∈ B u) ∧ y ∈ B v ↔
      ((y, x) ∈ S.edge v u ∧ y ∈ B v) ∧ x ∈ B u
    rw [S.edge_swap u v h x y]
    tauto
  have hproj u v (h : G.Adj u v) : Prod.fst '' Q u v = B u ∧ Prod.snd '' Q u v = B v := by
    obtain hp | hp := treeRootPath_adj hG r h
    · have heq : B v = Prod.snd '' restrictRelationLeft (S.edge u v) (B u) := by
        dsimp only [B]
        rw [hp, propagateTreeSet_concat]
      apply restrictTreeEdge_projections _ heq
      rw [S.fst_edge u v h]
      exact (hB u).2.2
    · have heq : B u = Prod.snd '' restrictRelationLeft (S.edge v u) (B v) := by
        dsimp only [B]
        rw [hp, propagateTreeSet_concat]
      have hsub : B v ⊆ Prod.fst '' S.edge v u := by
        rw [S.fst_edge v u h.symm]
        exact (hB v).2.2
      have hrev := restrictTreeEdge_projections hsub heq
      have hf := fst_image_eq_snd_image_of_swap (hswap u v h)
      have hs := fst_image_eq_snd_image_of_swap (hswap v u h.symm)
      exact ⟨hf.trans hrev.2, hs.symm.trans hrev.1⟩
  let T : AnalyticTreeSystem G X := {
    node := B
    edge := Q
    node_analytic := fun v => (hB v).1
    node_nonempty := fun v => (hB v).2.1
    edge_analytic := fun u v h => analyticSet_inter
      (analyticSet_inter (S.edge_analytic u v h) ((hB u).1.preimage continuous_fst))
      ((hB v).1.preimage continuous_snd)
    fst_edge := fun u v h => (hproj u v h).1
    snd_edge := fun u v h => (hproj u v h).2
    edge_swap := hswap }
  refine ⟨T, ?_, fun v => (hB v).2.2, (fun _ _ => rfl), (fun _ => rfl)⟩
  change propagateTreeSet S (treeRootPath hG r r) C = C
  rw [treeRootPath_self, propagateTreeSet_nil]

omit [PolishSpace X] in
/-- Full projections and a nonempty endpoint imply a nonempty edge. -/
theorem AnalyticTreeSystem.edge_nonempty {G : SimpleGraph V}
    (S : AnalyticTreeSystem G X) {u v : V} (h : G.Adj u v) : (S.edge u v).Nonempty := by
  have hn := S.node_nonempty u
  rw [← S.fst_edge u v h] at hn
  exact hn.of_image

/-- An adjacent vertex is reached by its single edge. -/
theorem treeRootPath_of_adj {G : SimpleGraph V} (hG : G.IsTree)
    {u v : V} (h : G.Adj u v) : treeRootPath hG u v = .cons h .nil := by
  exact Subtype.mk.inj ((hG.isAcyclic.subsingleton_path u v).elim
    ⟨_, treeRootPath_isPath hG u v⟩ (SimpleGraph.Path.singleton h))

omit [PolishSpace X] in
theorem propagateTreeSet_adj {G : SimpleGraph V} (hG : G.IsTree)
    (S : AnalyticTreeSystem G X) {u v : V} (h : G.Adj u v) (C : Set X) :
    propagateTreeSet S (treeRootPath hG u v) C =
      Prod.snd '' restrictRelationLeft (S.edge u v) C := by
  rw [treeRootPath_of_adj hG h]
  rfl

/-- The two projection changes of an edge refinement can be propagated while
retaining that entire chosen relation. The second propagation crosses the
chosen edge without further shrinking the first endpoint: every point there
still has its witness in the chosen relation. This implements the book's
two-component procedure by two root passes using the same edge-restriction
and projection operations. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Root the tree at the changed node, and put the prescribed subset there. If $u$ has been processed and $v$
    is its next neighbor away from the root, define
    $$A'_v:=\pi_1(R_{u,v}\cap(A'_u\times X)).$$
    Every point of $A'_u$ has a partner in the old relation, so this set is nonempty. Restricting the edge to
    $A'_u\times A'_v$ preserves exactly these two projections. Continue along the unique paths from the root,
    and finally restrict every old edge to its new endpoints. The unique-path property ensures consistency.
    In particular the chosen root set remains unchanged.

    Now prescribe a nonempty subrelation $P\IncludedIn R_{u,v}$, and put
    $$C:=\pi_0(P),\qquad D:=\pi_1(P).$$
    First propagate $C$ from $u$ as above. Every pair of $P$ survives the restriction of the edge, since its first
    coordinate lies in $C$ and its second lies in the propagated set at $v$. Next propagate $D$ from $v$ in this
    refined system. The new set at $u$ is contained in $C$. Conversely, each point of $C$ has a partner in $D$
    through $P$; the reverse edge retains that pair, so the point survives propagation back to $u$.
    Thus the endpoint sets are exactly $C,D$, and the refined edge still contains $P$. Replace it by $P$ and
    its reverse by the swapped relation. Both projections remain full, and all other edges stay coherent.
    All changes are restrictions, so previously satisfied downward-closed requirements are preserved.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{finite-tree refinement lemma}{Finite-tree refinement}]
-/
theorem analytic_tree_edge_endpoints {G : SimpleGraph V} (hG : G.IsTree)
    (S : AnalyticTreeSystem G X) {u v : V} (h : G.Adj u v) {P : Set (X × X)}
    (hPa : AnalyticSet P) (hPn : P.Nonempty) (hPs : P ⊆ S.edge u v) :
    ∃ T : AnalyticTreeSystem G X,
      T.node u = Prod.fst '' P ∧ T.node v = Prod.snd '' P ∧
      (∀ w, T.node w ⊆ S.node w) ∧
      (∀ a b, T.edge a b ⊆ S.edge a b) ∧ P ⊆ T.edge u v := by
  let C := Prod.fst '' P
  let D := Prod.snd '' P
  have hCs : C ⊆ S.node u := by rw [← S.fst_edge u v h]; exact image_mono hPs
  obtain ⟨T, hTu, hTsub, hTedge, hTprop⟩ := analytic_tree_node_refinement hG S u
    (hPa.image_of_continuous continuous_fst) (hPn.image Prod.fst) hCs
  have hTv : T.node v = Prod.snd '' restrictRelationLeft (S.edge u v) C := by
    rw [hTprop, propagateTreeSet_adj hG S h]
  have hPT : P ⊆ T.edge u v := by
    intro p hp
    rw [hTedge, hTu, hTv]
    exact ⟨⟨hPs hp, mem_image_of_mem Prod.fst hp⟩,
      ⟨p, ⟨hPs hp, mem_image_of_mem Prod.fst hp⟩, rfl⟩⟩
  have hDs : D ⊆ T.node v := by rw [← T.snd_edge u v h]; exact image_mono hPT
  obtain ⟨U, hUv, hUsub, hUedge, hUprop⟩ := analytic_tree_node_refinement hG T v
    (hPa.image_of_continuous continuous_snd) (hPn.image Prod.snd) hDs
  have hUu : U.node u = C := by
    apply Subset.antisymm
    · exact (hUsub u).trans (by rw [hTu])
    · rintro x ⟨p, hp, rfl⟩
      rw [hUprop, propagateTreeSet_adj hG T h.symm]
      exact ⟨(p.2, p.1), ⟨(T.edge_swap u v h p.1 p.2).mp (hPT hp),
        mem_image_of_mem Prod.snd hp⟩, rfl⟩
  refine ⟨U, hUu, hUv, fun w => (hUsub w).trans (hTsub w), ?_, ?_⟩
  · intro a b p hp
    rw [hUedge] at hp
    have hpT := hp.1.1
    rw [hTedge] at hpT
    exact hpT.1.1
  · intro p hp
    rw [hUedge, hUu, hUv]
    exact ⟨⟨hPT hp, mem_image_of_mem Prod.fst hp⟩, mem_image_of_mem Prod.snd hp⟩

/-- Replace one undirected edge after its two projections have been fixed. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Root the tree at the changed node, and put the prescribed subset there. If $u$ has been processed and $v$
    is its next neighbor away from the root, define
    $$A'_v:=\pi_1(R_{u,v}\cap(A'_u\times X)).$$
    Every point of $A'_u$ has a partner in the old relation, so this set is nonempty. Restricting the edge to
    $A'_u\times A'_v$ preserves exactly these two projections. Continue along the unique paths from the root,
    and finally restrict every old edge to its new endpoints. The unique-path property ensures consistency.
    In particular the chosen root set remains unchanged.

    Now prescribe a nonempty subrelation $P\IncludedIn R_{u,v}$, and put
    $$C:=\pi_0(P),\qquad D:=\pi_1(P).$$
    First propagate $C$ from $u$ as above. Every pair of $P$ survives the restriction of the edge, since its first
    coordinate lies in $C$ and its second lies in the propagated set at $v$. Next propagate $D$ from $v$ in this
    refined system. The new set at $u$ is contained in $C$. Conversely, each point of $C$ has a partner in $D$
    through $P$; the reverse edge retains that pair, so the point survives propagation back to $u$.
    Thus the endpoint sets are exactly $C,D$, and the refined edge still contains $P$. Replace it by $P$ and
    its reverse by the swapped relation. Both projections remain full, and all other edges stay coherent.
    All changes are restrictions, so previously satisfied downward-closed requirements are preserved.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{finite-tree refinement lemma}{Finite-tree refinement}]
-/
theorem analytic_tree_replace_edge [DecidableEq V] {G : SimpleGraph V}
    (S : AnalyticTreeSystem G X) {u v : V} (h : G.Adj u v) {P : Set (X × X)}
    (hPa : AnalyticSet P) (hPs : P ⊆ S.edge u v)
    (hPf : Prod.fst '' P = S.node u) (hPt : Prod.snd '' P = S.node v) :
    ∃ T : AnalyticTreeSystem G X, (∀ w, T.node w = S.node w) ∧
      T.edge u v = P ∧ (∀ a b, T.edge a b ⊆ S.edge a b) ∧
      (∀ a b, T.edge a b = if a = u ∧ b = v then P else
        if a = v ∧ b = u then Prod.swap ⁻¹' P else S.edge a b) := by
  classical
  let Q : V → V → Set (X × X) := fun a b =>
    if a = u ∧ b = v then P else if a = v ∧ b = u then Prod.swap ⁻¹' P else S.edge a b
  have hswap a b (hab : G.Adj a b) (x y : X) :
      (x, y) ∈ Q a b ↔ (y, x) ∈ Q b a := by
    by_cases ha : a = u ∧ b = v
    · rcases ha with ⟨rfl, rfl⟩
      simp [Q, h.ne, h.ne.symm]
    · by_cases hb : a = v ∧ b = u
      · rcases hb with ⟨rfl, rfl⟩
        simp [Q, h.ne, h.ne.symm]
      · have ha' : ¬ (b = v ∧ a = u) := by tauto
        have hb' : ¬ (b = u ∧ a = v) := by tauto
        simpa only [Q, ite_eq_right ha, ite_eq_right hb, ite_eq_right ha', ite_eq_right hb'] using
          S.edge_swap a b hab x y
  have hsub a b : Q a b ⊆ S.edge a b := by
    by_cases ha : a = u ∧ b = v
    · rcases ha with ⟨rfl, rfl⟩
      simpa [Q] using hPs
    · by_cases hb : a = v ∧ b = u
      · rcases hb with ⟨rfl, rfl⟩
        simp only [Q, ite_eq_right ha, and_self]
        intro p hp
        exact (S.edge_swap _ _ h p.2 p.1).mp (hPs hp)
      · simp only [Q, ite_eq_right ha, ite_eq_right hb]
        exact Subset.rfl
  have hproj a b (hab : G.Adj a b) :
      Prod.fst '' Q a b = S.node a ∧ Prod.snd '' Q a b = S.node b := by
    by_cases ha : a = u ∧ b = v
    · rcases ha with ⟨rfl, rfl⟩
      simpa [Q] using And.intro hPf hPt
    · by_cases hb : a = v ∧ b = u
      · rcases hb with ⟨rfl, rfl⟩
        simp only [Q, ite_eq_right ha, and_self]
        have hf : Prod.fst '' (Prod.swap ⁻¹' P) = Prod.snd '' P :=
          fst_image_eq_snd_image_of_swap (fun _ _ => Iff.rfl)
        have ht : Prod.fst '' P = Prod.snd '' (Prod.swap ⁻¹' P) :=
          fst_image_eq_snd_image_of_swap (fun _ _ => Iff.rfl)
        exact ⟨hf.trans hPt, ht.symm.trans hPf⟩
      · simp only [Q, ite_eq_right ha, ite_eq_right hb]
        exact ⟨S.fst_edge a b hab, S.snd_edge a b hab⟩
  have han a b (hab : G.Adj a b) : AnalyticSet (Q a b) := by
    dsimp only [Q]
    split_ifs
    · exact hPa
    · exact hPa.preimage continuous_swap
    · exact S.edge_analytic a b hab
  let T : AnalyticTreeSystem G X := {
    node := S.node
    edge := Q
    node_analytic := S.node_analytic
    node_nonempty := S.node_nonempty
    edge_analytic := han
    fst_edge := fun a b h => (hproj a b h).1
    snd_edge := fun a b h => (hproj a b h).2
    edge_swap := hswap }
  refine ⟨T, fun _ => rfl, ?_, hsub, fun _ _ => rfl⟩
  change Q u v = P
  simp [Q]

/-- Shrinking one edge to a nonempty analytic subset propagates its two
projections, and then retains precisely the requested subset on that edge. -/
theorem analytic_tree_edge_refinement {G : SimpleGraph V} (hG : G.IsTree)
    (S : AnalyticTreeSystem G X) {u v : V} (h : G.Adj u v) {P : Set (X × X)}
    (hPa : AnalyticSet P) (hPn : P.Nonempty) (hPs : P ⊆ S.edge u v) :
    ∃ T : AnalyticTreeSystem G X, T.edge u v = P ∧
      T.node u = Prod.fst '' P ∧ T.node v = Prod.snd '' P ∧
      (∀ w, T.node w ⊆ S.node w) ∧ (∀ a b, T.edge a b ⊆ S.edge a b) := by
  classical
  obtain ⟨T, hTu, hTv, hTn, hTe, hPT⟩ := analytic_tree_edge_endpoints hG S h hPa hPn hPs
  obtain ⟨U, hUn, hUe, hUsub, _⟩ := analytic_tree_replace_edge T h hPa hPT hTu.symm hTv.symm
  exact ⟨U, hUe, (hUn u).trans hTu, (hUn v).trans hTv,
    fun w => (hUn w).symm ▸ hTn w, fun a b => (hUsub a b).trans (hTe a b)⟩

omit [TopologicalSpace X] [PolishSpace X] in
/-- Restricting both endpoints of a full equivalence edge preserves fullness.
This is the invariant used for the joining edge before the final edge stage. -/
theorem restrictTreeEdge_fullERBetween (E : Setoid X) {A B C D : Set X}
    (hCA : C ⊆ A) (hDB : D ⊆ B) :
    restrictTreeEdge (fullERBetween E A B) C D = fullERBetween E C D := by
  ext p
  constructor
  · rintro ⟨⟨⟨_, _, hpE⟩, hpC⟩, hpD⟩
    exact ⟨hpC, hpD, hpE⟩
  · rintro ⟨hpC, hpD, hpE⟩
    exact ⟨⟨⟨hCA hpC, hDB hpD, hpE⟩, hpC⟩, hpD⟩

end PolishSpaceBook
