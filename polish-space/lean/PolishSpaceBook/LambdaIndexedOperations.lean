module

public import PolishSpaceBook.LambdaEffectiveSeparation

@[expose] public section

/-! # Joint lambda tree operations and relational-image indices

The family index stays ordinary input data through every word operation.
Specialization constructs actual lambda-computed numerical indices.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance indexedOpListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance indexedOpPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

theorem coordinatePreimage_family_decidable {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree))
    {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) =>
      z.2 ∈ ((T z.1).coordinatePreimage hF).tree) := by
  have hw := projection_computes false
  have hs := computes_codeFirst hw
  have ht := computes_codeSecond hw
  exact hT.precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) => (z.1,(z.2.1.map f,z.2.2)))
    ((projection_computes true).pair (((mapWord_computes hF).comp hs).pair ht))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])

theorem intersection_family_decidable {ε : ℕ → ℕ} (T S : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree))
    (hS : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (S z.1).tree)) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) =>
      z.2 ∈ ((T z.1).intersection (S z.1)).tree) := by
  have ht := hT.precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) => (z.1,(z.2.1,leftWitness z.2.2)))
    ((projection_computes true).pair ((witnessReindex_computes true).comp (projection_computes false)))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma,leftWitness])
  have hs := hS.precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) => (z.1,(z.2.1,rightWitness z.2.2)))
    ((projection_computes true).pair ((witnessReindex_computes false).comp (projection_computes false)))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma,rightWitness])
  exact ht.and hs

theorem pairTreeBody_intersection {ε : ℕ → ℕ} (T S : PairTree ε) (x q : ℕ → ℕ) :
    (x,q) ∈ pairTreeBody (T.intersection S).tree ↔
      (x,leftBaire q) ∈ pairTreeBody T.tree ∧ (x,rightBaire q) ∈ pairTreeBody S.tree := by
  simp only [pairTreeBody,PairTree.intersection,Set.mem_ofPred_eq,
    leftWitness_prefix,rightWitness_prefix,forall_and]

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Let the closed term $\LambdaTermName{wordMap}$ compute the numerical word transformation $\varphi$. To retain a
    family index, use the closed wrapper
    $$\LambdaTermName{keepIndex}:= \lambdaab{ \LambdaTermName{mapArg}}{ \lambdaab{z}{ \LambdaNumericPair\,(
    \LambdaNumericProjection{1}z)\,
     (\LambdaTermName{mapArg}(\LambdaNumericProjection{2}z))}}.$$
    If $z= \NatPair{i}{w}$, then $\LambdaTermName{keepIndex} \LambdaTermName{wordMap}$ sends its numeral to the
    numeral for $\NatPair{i}{ \varphi(w)}$.
    Thus a joint tree decider $\LambdaTermName{familyPredicate}$ is reindexed by $\lambdaab{o}{ \lambdaab{z}{
    \LambdaTermName{familyPredicate}o( \LambdaTermName{keepIndex} \LambdaTermName{wordMap}z)}}$ without changing its
    parameter.
    Apply this wrapper to the word operations for coordinatewise inverse images, witness intersections,
    and coordinate projections. For projection, apply the finite-test construction after reindexing.
    This supplies the joint family deciders used for relational-image and invalid-code indices.
-/
theorem projectRight_family_decidable {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree)) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) =>
      z.2 ∈ (T z.1).projectRight.tree) := by
  apply finiteCheck_family_decidable (test := fun i => rightProjectionTest (T i).tree)
  exact hT.precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) =>
      (z.1,(pairWords (leftWitness z.2.2) z.2.1,rightWitness z.2.2)))
    ((projection_computes true).pair (rightProjectionInput_computes.comp (projection_computes false)))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])

/-- Relational image is a total lambda operation on indices at a fixed parameter. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: statement
  kind: proposition
  title: Relational images on indices
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the uniform indexed tree for $A_e$. Pull back its first word by the first numerical projection,
    intersect with the fixed tree presenting $R$, and project to the second point coordinate, as in
    §{sec:edst-coordinate-projections}. In every finite computation retain $e$ alongside the node code.
    List mapping, witness pairing, finite tabulation, and the bounded prefix tests therefore give a joint
    decider for the resulting family. Its projection is exactly the displayed relational image by the three
    body identities. Specializing this decider by $e$ supplies $h$ through the lambda syntax transformation
    of §{sec:edst-pair-tree-indices}. Thus the uniformity follows from a concrete program, not from separate
    choices of presentations for the images.
    \end{proof}
-/
theorem exists_relationalImageIndices (ε : ℕ → ℕ)
    (R : (ℕ → ℕ) → (ℕ → ℕ) → Prop) (hR : ProjectedRelation ε R) :
    ∃ image : ℕ → ℕ, (∃ F, NumericalComputes F image) ∧ ∀ e,
      indexedProjection ε (image e) = {y | ∃ x ∈ indexedProjection ε e, R x y} := by
  obtain ⟨TR,hTR⟩ := hR
  let T := indexedTree ε
  let L := fun i => (T i).coordinatePreimage (projection_computes true)
  let P := fun i => (TR.intersection (L i)).projectRight
  have hL := coordinatePreimage_family_decidable T (indexedTree_family_decidable ε)
    (projection_computes true)
  have hP := projectRight_family_decidable (fun i => TR.intersection (L i))
    (intersection_family_decidable (fun _ => TR) L (constantTree_family_decidable TR) hL)
  obtain ⟨image,hi,hc⟩ := treeFamily_indices ε P hP
  refine ⟨image,hi,fun e => ?_⟩
  change pairTreeProjection (indexedTree ε (image e)).tree = _
  rw [pairTreeProjection_indexedTree ε (image e) _ (hc e)]
  change pairTreeProjection (TR.intersection (L e)).projectRight.tree = _
  rw [pairTreeProjection_projectRight,pairTreeProjection_intersection]
  have hLe := pairTreeProjection_coordinatePreimage (T e) (projection_computes true)
  rw [hLe,← hTR]
  ext y
  constructor
  · rintro ⟨p,⟨hrel,hx⟩,rfl⟩
    exact ⟨leftBaire p,hx,hrel⟩
  · rintro ⟨x,hx,hrel⟩
    refine ⟨pairBaire x y,?_,rightBaire_pair x y⟩
    simpa only [mem_inter_iff,mem_ofPred_eq,mem_preimage,leftBaire_pair,rightBaire_pair,
      pairBaire,Nat.unpair_pair,indexedProjection,T,Function.comp_def,ite_true]
      using And.intro hrel hx

end LambdaTree
end PolishSpaceBook
