module

public import PolishSpaceBook.HKLDenseRefinements
public import PolishSpaceBook.LambdaIndexedOperations
public import PolishSpaceBook.LambdaCatalogProjections

@[expose] public section

/-!
# Tree refinement in the original parameter

The node sets and actual edge relations have relative lambda tree codes.
Outward propagation follows the same root paths as `HKLTreeRefinement`.
Every restriction and projection keeps the parameter fixed; arbitrary analytic
subsets are not admitted as stronger conditions.
-/

namespace PolishSpaceBook
namespace LambdaTree
open Set SimpleGraph MeasureTheory NamedLambda NamedLambda.AlphaTerm

def swapPairTerm : AlphaTerm :=
  pairNumerical (numericalProjectionTerm false) (numericalProjectionTerm true)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    To reverse a coded pair, use the closed numerical term
    $$\lambdaab{z}{\LambdaNumericPair\,(\LambdaNumericProjection{2}z)\,(\LambdaNumericProjection{1}z)}.$$
    On the numeral for a numerical pair it returns the numeral for the reversed pair, by the two projection
    equations and the pairing equation. Mapping this operation over the first finite word of a pair-tree
    node, while leaving its witness word unchanged, gives the inverse-image tree for the swapped relation.
    Thus replacing a directed edge also supplies the presentation for its reverse.
-/
theorem swapPair_computes : NumericalComputes swapPairTerm (fun z => Nat.pair z.unpair.2 z.unpair.1) :=
  (projection_computes false).pair (projection_computes true)

/-- A set of actual pairs, coded coordinatewise as a set of Baire reals. -/
def ProjectedPairs (ε : ℕ → ℕ) (P : Set (FusionReal × FusionReal)) : Prop :=
  ProjectedRelation ε (fun x y => (x, y) ∈ P)

namespace ProjectedPairs
variable {ε : ℕ → ℕ} {P : Set (FusionReal × FusionReal)}

theorem analyticSet (hP : ProjectedPairs ε P) : AnalyticSet P := by
  have hc : Continuous (fun p : FusionReal × FusionReal => pairBaire p.1 p.2) := by
    unfold pairBaire
    fun_prop
  convert (Projected.analyticSet hP).preimage hc using 1
  ext p
  change p ∈ P ↔ (leftBaire (pairBaire p.1 p.2), rightBaire (pairBaire p.1 p.2)) ∈ P
  simp

theorem swap (hP : ProjectedPairs ε P) : ProjectedPairs ε (Prod.swap ⁻¹' P) := by
  have h := hP.coordinatePreimage swapPair_computes
  change Projected ε {p | (rightBaire p, leftBaire p) ∈ P}
  convert h using 1
  ext p
  change (rightBaire p, leftBaire p) ∈ P ↔
    (leftBaire (pairBaire (rightBaire p) (leftBaire p)),
      rightBaire (pairBaire (rightBaire p) (leftBaire p))) ∈ P
  simp

theorem snd (hP : ProjectedPairs ε P) : Projected ε (Prod.snd '' P) := by
  have h := hP.projectRight
  have he : rightBaire '' {p | (leftBaire p, rightBaire p) ∈ P} = Prod.snd '' P := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(leftBaire p, rightBaire p), hp, rfl⟩
    · rintro ⟨⟨x, y⟩, hp, rfl⟩
      exact ⟨pairBaire x y, by simpa using hp, rightBaire_pair x y⟩
  exact he ▸ h

theorem fst (hP : ProjectedPairs ε P) : Projected ε (Prod.fst '' P) := by
  have h := hP.projectLeft
  have he : leftBaire '' {p | (leftBaire p, rightBaire p) ∈ P} = Prod.fst '' P := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(leftBaire p, rightBaire p), hp, rfl⟩
    · rintro ⟨⟨x, y⟩, hp, rfl⟩
      exact ⟨pairBaire x y, by simpa using hp, leftBaire_pair x y⟩
  exact he ▸ h

theorem restrictLeft (hP : ProjectedPairs ε P) {A : Set FusionReal}
    (hA : Projected ε A) : ProjectedPairs ε (restrictRelationLeft P A) :=
  hP.inter hA.leftPreimage

theorem restrict (hP : ProjectedPairs ε P) {A B : Set FusionReal}
    (hA : Projected ε A) (hB : Projected ε B) :
    ProjectedPairs ε (restrictTreeEdge P A B) :=
  (hP.inter hA.leftPreimage).inter hB.rightPreimage

end ProjectedPairs

variable {V : Type*} {G : SimpleGraph V} {ε : ℕ → ℕ}

/-- Only edges of the graph are required to be coded. -/
def TreeCoded (ε : ℕ → ℕ) (S : AnalyticTreeSystem G FusionReal) : Prop :=
  (∀ v, Projected ε (S.node v)) ∧
  ∀ u v, G.Adj u v → ProjectedPairs ε (S.edge u v)

theorem projected_propagateTreeSet (S : AnalyticTreeSystem G FusionReal)
    (hS : TreeCoded ε S) {u v : V} (p : G.Walk u v) {C : Set FusionReal}
    (hC : Projected ε C) : Projected ε (propagateTreeSet S p C) := by
  induction p generalizing C with
  | nil => exact hC
  | cons h p ih => exact ih (((hS.2 _ _ h).restrictLeft hC).snd)

/-- For a fixed finite path, propagation is a total lambda transformation of
analytic indices, even when the input index is a partial program. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For one step, restrict an edge by taking the inverse image of the new node set under the first point
    projection and intersecting with the edge relation. Project to the second coordinate. These are the
    lambda tree operations of §{sec:edst-coordinate-projections}. Iterating them along a finite path gives
    its propagated set; equivalently, compose the relational-image index transformations from
    §{sec:edst-hkl-kernel}. The empty path uses the identity transformation. Every input index is allowed
    because the delayed tree presentation is defined on all indices.

    To restrict both endpoints, take both coordinate inverse images and intersect them with the edge.
    To reverse an edge, apply numerical coordinate swap to every entry of its coded point. List mapping
    and numerical pairing compute this inverse image. Thus the two propagation passes and the final edge
    replacement preserve the original parameter. The explicit swap and path-composition terms are given
    in §{sec:lambda-lusin-image-programs}. Nonemptiness and containment are hypotheses on the chosen
    shrinking sets; the finite programs do not test these properties.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For a fixed finite path with $k$ edges, let the closed numerical terms $\LambdaTermName{edgeMap}_0, \ldots,
    \LambdaTermName{edgeMap}_{k-1}$ compute
    the relational-image index transformations of its successive directed edges. Put
    $$\LambdaTermName{pathStage}_0:=\lambdaab{e}{e},\qquad
    \LambdaTermName{pathStage}_{j+1}:= \lambdaab{e}{ \LambdaTermName{edgeMap}_j( \LambdaTermName{pathStage}_j e)}
    \quad(0 \le j<k).$$
    Expand the supplied closed terms and choose fresh binders. Induction on the path length proves that
    $\LambdaTermName{pathStage}_j$ computes the index of the set obtained after the first $j$ propagation steps.
    Each step terminates
    on every numerical input, so the composite is total, including the identity program for a path of length
    zero. The path and edge presentations are fixed finite data in this assertion. Choosing dense refinements
    through infinitely many levels remains the existence construction described in the main text.
-/
theorem exists_propagateTreeIndices (S : AnalyticTreeSystem G FusionReal)
    (hS : TreeCoded ε S) {u v : V} (p : G.Walk u v) :
    ∃ f : ℕ → ℕ, (∃ F, NumericalComputes F f) ∧ ∀ e,
      indexedProjection ε (f e) = propagateTreeSet S p (indexedProjection ε e) := by
  induction p with
  | nil => exact ⟨id,⟨numericalIdentity,numericalIdentity_computes⟩,fun _ => rfl⟩
  | @cons u v w h p ih =>
    obtain ⟨g,⟨G,hG⟩,hg⟩ := ih
    obtain ⟨f,⟨F,hF⟩,hf⟩ := exists_relationalImageIndices ε
      (fun x y => (x,y) ∈ S.edge u v) (hS.2 u v h)
    refine ⟨fun e => g (f e),⟨numericalCompose G F,hG.comp hF⟩,fun e => ?_⟩
    rw [hg,hf]
    change propagateTreeSet S p {y | ∃ x ∈ indexedProjection ε e, (x,y) ∈ S.edge u v} = _
    congr 1
    ext y
    constructor
    · rintro ⟨x,hx,hxy⟩
      exact ⟨(x,y),⟨hxy,hx⟩,rfl⟩
    · rintro ⟨⟨x,y'⟩,⟨hxy,hx⟩,rfl⟩
      exact ⟨x,hx,hxy⟩

/-- The geometric proof supplies exact root-path and edge formulas;
those formulas certify that its refinement stays in the same parameter. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For one step, restrict an edge by taking the inverse image of the new node set under the first point
    projection and intersecting with the edge relation. Project to the second coordinate. These are the
    lambda tree operations of §{sec:edst-coordinate-projections}. Iterating them along a finite path gives
    its propagated set; equivalently, compose the relational-image index transformations from
    §{sec:edst-hkl-kernel}. The empty path uses the identity transformation. Every input index is allowed
    because the delayed tree presentation is defined on all indices.

    To restrict both endpoints, take both coordinate inverse images and intersect them with the edge.
    To reverse an edge, apply numerical coordinate swap to every entry of its coded point. List mapping
    and numerical pairing compute this inverse image. Thus the two propagation passes and the final edge
    replacement preserve the original parameter. The explicit swap and path-composition terms are given
    in §{sec:lambda-lusin-image-programs}. Nonemptiness and containment are hypotheses on the chosen
    shrinking sets; the finite programs do not test these properties.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: corollary
  title: Fixed-parameter tree refinement
-/
theorem tree_node_refinement (hG : G.IsTree) (S : AnalyticTreeSystem G FusionReal)
    (hS : TreeCoded ε S) (r : V) {C : Set FusionReal}
    (hC : Projected ε C) (hCn : C.Nonempty) (hCs : C ⊆ S.node r) :
    ∃ T : AnalyticTreeSystem G FusionReal, TreeCoded ε T ∧ T.node r = C ∧
      T.Refines S ∧
      (∀ u v, T.edge u v = restrictTreeEdge (S.edge u v) (T.node u) (T.node v)) ∧
      (∀ v, T.node v = propagateTreeSet S (treeRootPath hG r v) C) := by
  obtain ⟨T, hr, hn, he, hp⟩ := analytic_tree_node_refinement hG S r hC.analyticSet hCn hCs
  have hc v : Projected ε (T.node v) := by
    rw [hp]
    exact projected_propagateTreeSet S hS _ hC
  refine ⟨T, ⟨hc, ?_⟩, hr, ⟨hn, ?_⟩, he, hp⟩
  · intro u v huv
    rw [he]
    exact (hS.2 u v huv).restrict (hc u) (hc v)
  · intro u v p hp
    rw [he] at hp
    exact hp.1.1

/-- The two passes used for an edge shrink preserve relative codes at every
node. Every point of the chosen edge retains its witness in both passes. -/
theorem tree_edge_endpoints (hG : G.IsTree) (S : AnalyticTreeSystem G FusionReal)
    (hS : TreeCoded ε S) {u v : V} (h : G.Adj u v) {P : Set (FusionReal × FusionReal)}
    (hP : ProjectedPairs ε P) (hPn : P.Nonempty) (hPs : P ⊆ S.edge u v) :
    ∃ T : AnalyticTreeSystem G FusionReal, TreeCoded ε T ∧
      T.node u = Prod.fst '' P ∧ T.node v = Prod.snd '' P ∧ T.Refines S ∧ P ⊆ T.edge u v := by
  let C := Prod.fst '' P
  let D := Prod.snd '' P
  have hCs : C ⊆ S.node u := by rw [← S.fst_edge u v h]; exact image_mono hPs
  obtain ⟨T, hTc, hTu, hTS, hTe, hTprop⟩ := tree_node_refinement hG S hS u hP.fst (hPn.image Prod.fst) hCs
  have hTv : T.node v = Prod.snd '' restrictRelationLeft (S.edge u v) C := by
    rw [hTprop, propagateTreeSet_adj hG S h]
  have hPT : P ⊆ T.edge u v := by
    intro p hp
    rw [hTe, hTu, hTv]
    exact ⟨⟨hPs hp, mem_image_of_mem Prod.fst hp⟩,
      ⟨p, ⟨hPs hp, mem_image_of_mem Prod.fst hp⟩, rfl⟩⟩
  have hDs : D ⊆ T.node v := by rw [← T.snd_edge u v h]; exact image_mono hPT
  obtain ⟨U, hUc, hUv, hUT, hUe, hUprop⟩ := tree_node_refinement hG T hTc v hP.snd (hPn.image Prod.snd) hDs
  have hUu : U.node u = C := by
    apply Subset.antisymm
    · exact (hUT.1 u).trans (by rw [hTu])
    · rintro x ⟨p, hp, rfl⟩
      rw [hUprop, propagateTreeSet_adj hG T h.symm]
      exact ⟨(p.2, p.1), ⟨(T.edge_swap u v h p.1 p.2).mp (hPT hp),
        mem_image_of_mem Prod.snd hp⟩, rfl⟩
  refine ⟨U, hUc, hUu, hUv, hUT.trans hTS, ?_⟩
  intro p hp
  rw [hUe, hUu, hUv]
  exact ⟨⟨hPT hp, mem_image_of_mem Prod.fst hp⟩, mem_image_of_mem Prod.snd hp⟩

/-- Replacing the selected edge also replaces its reverse by coordinate swap.
All other edge codes are retained. -/
theorem tree_replace_edge (S : AnalyticTreeSystem G FusionReal)
    (hS : TreeCoded ε S) {u v : V} (h : G.Adj u v) {P : Set (FusionReal × FusionReal)}
    (hP : ProjectedPairs ε P) (hPs : P ⊆ S.edge u v)
    (hPf : Prod.fst '' P = S.node u) (hPt : Prod.snd '' P = S.node v) :
    ∃ T : AnalyticTreeSystem G FusionReal, TreeCoded ε T ∧
      (∀ w, T.node w = S.node w) ∧ T.edge u v = P ∧ T.Refines S := by
  classical
  obtain ⟨T, hn, he, hs, hf⟩ := analytic_tree_replace_edge S h hP.analyticSet hPs hPf hPt
  refine ⟨T, ⟨?_, ?_⟩, hn, he, ⟨?_, hs⟩⟩
  · intro w
    rw [hn]
    exact hS.1 w
  · intro a b hab
    rw [hf]
    split_ifs
    · exact hP
    · exact hP.swap
    · exact hS.2 a b hab
  · intro w
    rw [hn]

/-- A relative analytic edge shrink propagates throughout the tree and
remains exactly the chosen relation, with both coordinate projections. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For one step, restrict an edge by taking the inverse image of the new node set under the first point
    projection and intersecting with the edge relation. Project to the second coordinate. These are the
    lambda tree operations of §{sec:edst-coordinate-projections}. Iterating them along a finite path gives
    its propagated set; equivalently, compose the relational-image index transformations from
    §{sec:edst-hkl-kernel}. The empty path uses the identity transformation. Every input index is allowed
    because the delayed tree presentation is defined on all indices.

    To restrict both endpoints, take both coordinate inverse images and intersect them with the edge.
    To reverse an edge, apply numerical coordinate swap to every entry of its coded point. List mapping
    and numerical pairing compute this inverse image. Thus the two propagation passes and the final edge
    replacement preserve the original parameter. The explicit swap and path-composition terms are given
    in §{sec:lambda-lusin-image-programs}. Nonemptiness and containment are hypotheses on the chosen
    shrinking sets; the finite programs do not test these properties.
    \end{proof}
-/
theorem tree_edge_refinement (hG : G.IsTree) (S : AnalyticTreeSystem G FusionReal)
    (hS : TreeCoded ε S) {u v : V} (h : G.Adj u v) {P : Set (FusionReal × FusionReal)}
    (hP : ProjectedPairs ε P) (hPn : P.Nonempty) (hPs : P ⊆ S.edge u v) :
    ∃ T : AnalyticTreeSystem G FusionReal, TreeCoded ε T ∧ T.edge u v = P ∧
      T.node u = Prod.fst '' P ∧ T.node v = Prod.snd '' P ∧ T.Refines S := by
  obtain ⟨T, hTc, hTu, hTv, hTS, hPT⟩ := tree_edge_endpoints hG S hS h hP hPn hPs
  obtain ⟨U, hUc, hUn, hUe, hUT⟩ := tree_replace_edge T hTc h hP hPT hTu.symm hTv.symm
  exact ⟨U, hUc, hUe, (hUn u).trans hTu, (hUn v).trans hTv, hUT.trans hTS⟩

end LambdaTree
end PolishSpaceBook
