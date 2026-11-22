module

public import PolishSpaceBook.PermutationTopology
public import PolishSpaceBook.AnalyticBorelMaps
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Card
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Relabeling countable graphs

Edges are two-element finite subsets of the natural numbers, as in the book.
The Boolean product is identified with mathlib's simple graphs; relabeling is
continuous and its closed witness relation projects to graph isomorphism.
-/

namespace PolishSpaceBook.CountableGraphActions

open Set Topology MeasureTheory
open scoped PointwisePerm

/-- The unordered pairs of distinct vertices. -/
abbrev Edge := {s : Finset ℕ // s.card = 2}

instance : TopologicalSpace Edge := ⊥
instance : DiscreteTopology Edge := ⟨rfl⟩

/-- The book's product of independent edge coordinates. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    Let $[\NN]^2$ be the set of two-element subsets of $\NN$. A simple undirected graph on vertex set $\NN$ is a function
    $$
    G:[\NN]^2\to 2,
    $$
    where $G(\{i,j\})=1$ means that $i$ and $j$ are adjacent. The graph space is therefore
    $$
    \mathrm{Graphs}_\NN:=2^{[\NN]^2}.
    $$
-/
abbrev GraphCode := Edge → Bool

instance : PolishSpace GraphCode where
  toSecondCountableTopology := inferInstance
  toIsCompletelyMetrizableSpace := inferInstance

/-- An edge with its distinct endpoints displayed. -/
def edge (a b : ℕ) (h : a ≠ b) : Edge := ⟨{a, b}, Finset.card_pair h⟩

lemma edge_swap (a b : ℕ) (h : a ≠ b) : edge a b h = edge b a h.symm := by
  apply Subtype.ext
  exact Finset.pair_comm a b

lemma exists_endpoints (e : Edge) : ∃ a b, ∃ h : a ≠ b, e = edge a b h := by
  obtain ⟨a, b, h, he⟩ := Finset.card_eq_two.mp e.property
  exact ⟨a, b, h, Subtype.ext he⟩

instance : Infinite Edge := Infinite.of_injective
  (fun n : ℕ => edge 0 (n + 1) (by omega)) (by
    intro a b h
    change edge 0 (a + 1) _ = edge 0 (b + 1) _ at h
    have hm : a + 1 ∈ (edge 0 (b + 1) (by omega)).val := by
      rw [← h]
      simp [edge]
    simpa [edge] using hm)

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    The set $[\NN]^2$ is countable and is infinite because $n\mapsto\{0,n+1\}$ is injective.
    Choose an enumeration without repetitions $e:\NN\to[\NN]^2$. Then
    $$G\longmapsto(n\longmapsto G(e(n)))$$
    is a homeomorphism from $\mathrm{Graphs}_\NN$ to $\CantorSpace$: both it and its inverse just reindex the discrete
    coordinates. A basic clopen neighborhood specifies finitely many edges and non-edges.
-/
/-- Enumerating unordered pairs identifies the graph space with Cantor space. -/
noncomputable def cantorHomeomorph : GraphCode ≃ₜ (ℕ → Bool) :=
  Homeomorph.piCongrLeft (Y := fun _ : ℕ => Bool)
    (Classical.choice (inferInstance : Nonempty (Edge ≃ ℕ)))

/-- Relabel an unordered edge. -/
def mapEdge (p : Equiv.Perm ℕ) (e : Edge) : Edge :=
  ⟨e.val.map p.toEmbedding, by simp [e.property]⟩

@[simp] lemma mapEdge_edge (p : Equiv.Perm ℕ) (a b : ℕ) (h : a ≠ b) :
    mapEdge p (edge a b h) = edge (p a) (p b) (p.injective.ne h) := by
  apply Subtype.ext
  simp [mapEdge, edge]

@[simp] lemma mapEdge_one (e : Edge) : mapEdge 1 e = e := by
  apply Subtype.ext
  change Finset.map (Function.Embedding.refl ℕ) e.val = e.val
  exact Finset.map_refl

lemma mapEdge_mul (p q : Equiv.Perm ℕ) (e : Edge) :
    mapEdge (p * q) e = mapEdge p (mapEdge q e) := by
  obtain ⟨a, b, h, rfl⟩ := exists_endpoints e
  simp

/-- The action relabels the inputs by the inverse permutation. -/
instance : MulAction (Equiv.Perm ℕ) GraphCode where
  smul p G e := G (mapEdge p⁻¹ e)
  one_smul G := by
    ext e
    change G (mapEdge (1 : Equiv.Perm ℕ)⁻¹ e) = G e
    simp
  mul_smul p q G := by
    ext e
    change G (mapEdge (p * q)⁻¹ e) = G (mapEdge q⁻¹ (mapEdge p⁻¹ e))
    rw [mul_inv_rev, mapEdge_mul]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    The infinite symmetric group acts by relabeling:
    $$
    (\sigma\cdot G)(\{i,j\})
    :=
    G(\{\sigma^{-1}(i),\sigma^{-1}(j)\}).
    $$
-/
@[simp] lemma smul_apply (p : Equiv.Perm ℕ) (G : GraphCode) (e : Edge) :
    (p • G) e = G (mapEdge p⁻¹ e) := rfl

/-- A total pair constructor, used only to expose finite-coordinate continuity. -/
def pairOrDefault (ab : ℕ × ℕ) : Edge :=
  if h : ab.1 ≠ ab.2 then edge ab.1 ab.2 h else edge 0 1 (by omega)

lemma continuous_mapEdge (e : Edge) : Continuous (fun p : Equiv.Perm ℕ => mapEdge p e) := by
  obtain ⟨a, b, h, rfl⟩ := exists_endpoints e
  have hp : Continuous pairOrDefault := continuous_of_discreteTopology
  have hc := hp.comp ((PointwisePerm.continuous_apply a).prodMk
    (PointwisePerm.continuous_apply b))
  convert hc using 1
  funext p
  simp [pairOrDefault, p.injective.ne h]

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Continuity is a finite-coordinate check. To decide whether $(\sigma\cdot G)(\{i,j\})=1$, one only
    needs the two values $\sigma^{-1}(i)$ and $\sigma^{-1}(j)$ and the single edge coordinate
    $G(\{\sigma^{-1}(i),\sigma^{-1}(j)\})$. In the topology of pointwise convergence on $\InfiniteSymmetricGroup$, the
    conditions $\sigma^{-1}(i)=a$ and $\sigma^{-1}(j)=b$ define a clopen neighborhood of $\sigma$, and the condition
    $G(\{a,b\})=\epsilon$ defines a clopen neighborhood of $G$. Hence every edge coordinate of the output is locally
    constant, so the action is continuous.
-/
/-- Every edge coordinate uses just two inverse-permutation values and one graph bit. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{proposition*} The relabeling action
-/
instance : ContinuousSMul (Equiv.Perm ℕ) GraphCode where
  continuous_smul := by
    apply continuous_pi
    intro e
    have he : Continuous (fun z : Equiv.Perm ℕ × GraphCode => mapEdge z.1⁻¹ e) :=
      (continuous_mapEdge e).comp (continuous_inv.comp continuous_fst)
    have hv : Continuous (fun z : GraphCode × Edge => z.1 z.2) :=
      continuous_prod_of_discrete_right.mpr (fun e => continuous_apply e)
    exact hv.comp (continuous_snd.prodMk he)

/-- Interpret the edge bits as a canonical simple graph. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    This example is the concrete model for the phrase "classification by countable structures." A graph is already a
    countable structure in the one-relation language $\{E\}$, with $E$ binary, symmetric, and irreflexive.
-/
def toGraph (G : GraphCode) : SimpleGraph ℕ where
  Adj a b := ∃ h : a ≠ b, G (edge a b h) = true
  symm := ⟨by
    rintro a b ⟨h, he⟩
    exact ⟨h.symm, by simpa only [← edge_swap a b h] using he⟩⟩
  loopless := ⟨fun a ⟨h, _⟩ => h rfl⟩

@[simp] lemma toGraph_adj (G : GraphCode) (a b : ℕ) (h : a ≠ b) :
    (toGraph G).Adj a b ↔ G (edge a b h) = true := by
  exact ⟨fun ⟨_, he⟩ => he, fun he => ⟨h, he⟩⟩

/-- Relabeling is exactly transport of graph adjacency. -/
lemma toGraph_smul_adj (p : Equiv.Perm ℕ) (G : GraphCode) (a b : ℕ) :
    (toGraph (p • G)).Adj a b ↔ (toGraph G).Adj (p⁻¹ a) (p⁻¹ b) := by
  by_cases h : a = b
  · subst b
    simp
  · simp [toGraph_adj, h, p.symm.injective.ne h, smul_apply]

lemma toGraph_injective : Function.Injective toGraph := by
  intro G H h
  funext e
  obtain ⟨a, b, hab, rfl⟩ := exists_endpoints e
  have he : (G (edge a b hab) = true) ↔ H (edge a b hab) = true := by
    rw [← toGraph_adj, ← toGraph_adj, h]
  exact Bool.eq_iff_iff.mpr he

/-- Record the adjacency of the two vertices of each edge. -/
noncomputable def fromGraph (H : SimpleGraph ℕ) : GraphCode := fun e =>
  @decide (∃ a ∈ e.val, ∃ b ∈ e.val, H.Adj a b) (Classical.propDecidable _)

@[simp] lemma fromGraph_edge (H : SimpleGraph ℕ) (a b : ℕ) (h : a ≠ b) :
    fromGraph H (edge a b h) = true ↔ H.Adj a b := by
  simp [fromGraph, edge, H.adj_comm]

@[simp] lemma toGraph_fromGraph (H : SimpleGraph ℕ) : toGraph (fromGraph H) = H := by
  ext a b
  by_cases h : a = b
  · subst b
    simp
  · rw [toGraph_adj _ _ _ h, fromGraph_edge]

/-- Every simple graph has exactly one edge-bit presentation. -/
noncomputable def graphEquiv : GraphCode ≃ SimpleGraph ℕ where
  toFun := toGraph
  invFun := fromGraph
  left_inv G := toGraph_injective (toGraph_fromGraph (toGraph G))
  right_inv := toGraph_fromGraph

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: proof
  excerpt: |
    Two graphs $G,H\in\mathrm{Graphs}_\NN$ lie in the same orbit exactly when there is a permutation
    $\sigma\in\InfiniteSymmetricGroup$ such that $H=\sigma\cdot G$. This says
    $$
    H(\{i,j\})=G(\{\sigma^{-1}(i),\sigma^{-1}(j)\})
    \qquad(i\ne j),
    $$
    which is precisely that $\sigma^{-1}$ is an isomorphism from $H$ to $G$, equivalently that $\sigma$ is an isomorphism
    from $G$ to $H$. Thus the orbit relation is graph isomorphism.
-/
/-- A canonical graph isomorphism supplies precisely the required permutation. -/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: statement
  excerpt: |
    \begin{proposition*} The relabeling action
-/
/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    The graph-isomorphism relation is therefore
    $$
    G\cong_{\mathrm{Graph}}H
    \quad\Longleftrightarrow\quad
    \exists\sigma\in\InfiniteSymmetricGroup\; H=\sigma\cdot G.
    $$
-/
theorem orbit_iff_graph_iso (G H : GraphCode) :
    (∃ p : Equiv.Perm ℕ, H = p • G) ↔ Nonempty (toGraph G ≃g toGraph H) := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨{ toEquiv := p, map_rel_iff' := ?_ }⟩
    intro a b
    simp [toGraph_smul_adj]
  · rintro ⟨e⟩
    refine ⟨e.toEquiv, toGraph_injective ?_⟩
    ext a b
    rw [toGraph_smul_adj]
    exact (e.symm.map_adj_iff).symm

/-- The witness relation is closed before projecting away the permutation. -/
def witnessSet : Set ((GraphCode × GraphCode) × Equiv.Perm ℕ) :=
  {z | z.1.2 = z.2 • z.1.1}

theorem isClosed_witnessSet : IsClosed witnessSet :=
  isClosed_eq (continuous_snd.comp continuous_fst)
    (continuous_snd.smul (continuous_fst.comp continuous_fst))

/-@ booklink:
  source: polish-space-book/polish-groups.md
  target: prose
  excerpt: |
    To verify analyticity, in $(\mathrm{Graphs}_\NN\times\mathrm{Graphs}_\NN)\times\InfiniteSymmetricGroup$ put
    $$C:=\{((G,H),\sigma):H=\sigma\cdot G\}.$$
    Each edge coordinate imposes equality of two continuous Boolean-valued functions, so $C$ is an intersection of
    closed sets. Hence $C$ is a closed subspace of a Polish space and is itself Polish. The continuous projection
    $$\pi:C\to\mathrm{Graphs}_\NN\times\mathrm{Graphs}_\NN,\qquad\pi((G,H),\sigma):=(G,H)$$
    has image exactly $\{(G,H):G\cong_{\mathrm{Graph}}H\}$. This continuous image of a Polish space is analytic by
    §{sec:analytic-sets}.
-/
/-- Closedness of the witness space and projection give analyticity. -/
theorem analyticSet_graph_iso :
    AnalyticSet {z : GraphCode × GraphCode | Nonempty (toGraph z.1 ≃g toGraph z.2)} := by
  have : PolishSpace witnessSet := isClosed_witnessSet.polishSpace
  have ha := analyticSet_range_via_baire_surjection (Z := witnessSet)
    (continuous_fst.comp continuous_subtype_val)
  convert ha using 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_range, Subtype.exists, Prod.exists, witnessSet]
  constructor
  · intro h
    obtain ⟨p, hp⟩ := (orbit_iff_graph_iso z.1 z.2).mpr h
    exact ⟨z.1, z.2, p, hp, rfl⟩
  · rintro ⟨G, H, p, hp, he⟩
    cases he
    exact (orbit_iff_graph_iso G H).mp ⟨p, hp⟩

end PolishSpaceBook.CountableGraphActions
