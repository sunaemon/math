module

public import PolishSpaceBook.LambdaTreeMapPrograms

@[expose] public section

/-! # Effective separation by closed lambda comparison programs

Both output trees use the original parameter. Disjointness is required for
the separation theorem, not for the total decision programs or index maps.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance separatorListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance separatorPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

def treeMapCode {ε : ℕ → ℕ} (T S : PairTree ε)
    (rootTest : List ℕ → Prop) (hr : LambdaRelative.DecidablePredicate ε rootTest) : PairTree ε :=
  finiteCheckTree (treeMapFiniteTest T.tree S.tree rootTest)
    (treeMapFiniteTest_decidable T S rootTest hr)

theorem pairTreeProjection_treeMapCode {ε : ℕ → ℕ} (T S : PairTree ε)
    (rootTest : List ℕ → Prop) (hr : LambdaRelative.DecidablePredicate ε rootTest) :
    pairTreeProjection (treeMapCode T S rootTest hr).tree =
      {x | ∃ q, rootTest (codedWordMap q []) ∧
        IsTreeMapWitness (rootedSection T x) (rootedSection S x) (codedWordMap q)} := by
  ext x
  apply exists_congr
  intro q
  change (x,q) ∈ pairTreeBody (finiteCheckNodes _) ↔ _
  rw [pairTreeBody_finiteCheckNodes]
  exact all_treeMapFiniteTest_iff T S rootTest x q

theorem treeMapCode_family_decidable {ε : ℕ → ℕ} (T S : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree))
    (hS : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (S z.1).tree))
    (rootTest : List ℕ → Prop) (hr : LambdaRelative.DecidablePredicate ε rootTest) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) =>
      z.2 ∈ (treeMapCode (T z.1) (S z.1) rootTest hr).tree) :=
  finiteCheck_family_decidable
    (test := fun i => treeMapFiniteTest (T i).tree (S i).tree rootTest)
    (treeMapFiniteTest_family_decidable T S hT hS rootTest hr)

theorem nil_decidable (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε (fun t : List ℕ => t = []) := by
  have h := (numerical_zero_decidable numericalIdentity_computes ε).precompNumerical
    (g := fun t : List ℕ => NatListCode.encode t) numericalIdentity_computes (fun _ => rfl)
  simpa only [id_eq,← decode_eq_nil_iff,NatListCode.decode_encode] using h

def comparisonLeTree {ε : ℕ → ℕ} (T S : PairTree ε) : PairTree ε :=
  treeMapCode T S (fun t => t = []) (nil_decidable ε)

def comparisonLtTree {ε : ℕ → ℕ} (T S : PairTree ε) : PairTree ε :=
  treeMapCode T S (fun t => t ≠ []) (nil_decidable ε).not

theorem pairTreeProjection_comparisonLeTree {ε : ℕ → ℕ} (T S : PairTree ε) :
    pairTreeProjection (comparisonLeTree T S).tree =
      {x | TreeComparisonLe (rootedSection T x) (rootedSection S x)} := by
  rw [comparisonLeTree,pairTreeProjection_treeMapCode]
  ext x
  exact (treeComparisonLe_iff_code _ _).symm

theorem pairTreeProjection_comparisonLtTree {ε : ℕ → ℕ} (T S : PairTree ε) :
    pairTreeProjection (comparisonLtTree T S).tree =
      {x | TreeComparisonLt (rootedSection T x) (rootedSection S x)} := by
  rw [comparisonLtTree,pairTreeProjection_treeMapCode]
  ext x
  exact (treeComparisonLt_iff_code _ _).symm

theorem comparisonLeTree_family_decidable {ε : ℕ → ℕ} (T S : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree))
    (hS : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (S z.1).tree)) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) =>
      z.2 ∈ (comparisonLeTree (T z.1) (S z.1)).tree) :=
  treeMapCode_family_decidable T S hT hS _ (nil_decidable ε)

theorem comparisonLtTree_family_decidable {ε : ℕ → ℕ} (T S : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree))
    (hS : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (S z.1).tree)) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) =>
      z.2 ∈ (comparisonLtTree (T z.1) (S z.1)).tree) :=
  treeMapCode_family_decidable T S hT hS _ (nil_decidable ε).not

/-- Reverse non-strict comparison and forward strict comparison are complementary. -/
theorem comparison_separation {ε : ℕ → ℕ} (T S : PairTree ε)
    (hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree)) :
    pairTreeProjection T.tree ⊆ pairTreeProjection (comparisonLeTree S T).tree ∧
    pairTreeProjection (comparisonLeTree S T).tree ⊆ (pairTreeProjection S.tree)ᶜ ∧
    pairTreeProjection (comparisonLeTree S T).tree =
      (pairTreeProjection (comparisonLtTree T S).tree)ᶜ := by
  have hT : {x | ∃ p, p ∈ treeBody (rootedSection T x).tree} = pairTreeProjection T.tree := by
    ext x
    exact branch_rootedSection_iff T x
  have hS : {x | ∃ p, p ∈ treeBody (rootedSection S x).tree} = pairTreeProjection S.tree := by
    ext x
    exact branch_rootedSection_iff S x
  have hdis : Disjoint {x | ∃ p, p ∈ treeBody (rootedSection T x).tree}
      {x | ∃ p, p ∈ treeBody (rootedSection S x).tree} := by rwa [hT,hS]
  simpa only [hT,hS,pairTreeProjection_comparisonLeTree,pairTreeProjection_comparisonLtTree]
    using tree_comparison_separates (rootedSection T) (rootedSection S) hdis

theorem effective_separation {ε : ℕ → ℕ} {A B : Set (ℕ → ℕ)}
    (hA : Projected ε A) (hB : Projected ε B) (hd : Disjoint A B) :
    ∃ D, Complemented ε D ∧ A ⊆ D ∧ D ⊆ Bᶜ := by
  obtain ⟨T,rfl⟩ := hA
  obtain ⟨S,rfl⟩ := hB
  obtain ⟨hleft,hright,hcompl⟩ := comparison_separation T S hd
  refine ⟨pairTreeProjection (comparisonLeTree S T).tree,
    ⟨⟨comparisonLeTree S T,rfl⟩,?_⟩,hleft,hright⟩
  exact ⟨comparisonLtTree T S,by rw [hcompl,compl_compl]⟩

/-- Reindex a jointly decidable family using a closed numerical program. -/
theorem indexedTree_reindex_decidable (ε : ℕ → ℕ) {F : AlphaTerm} {f : ℕ → ℕ}
    (hF : NumericalComputes F f) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) =>
      z.2 ∈ (indexedTree ε (f z.1)).tree) :=
  (indexedTree_family_decidable ε).precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) => (f z.1,z.2))
    ((hF.comp (projection_computes true)).pair (projection_computes false))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])

/-- The transformations are total on all input indices; only their separation
properties require disjointness. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: proposition
  title: Uniform separation at a fixed parameter
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Take $D=\pi_0([C_{=}(S,T)])$ and $D'=\pi_0([C_{\ne}(T,S)])$, where the subscripts specify the two
    root tests. At least one of $T_x,S_x$ is well founded. If both are well founded, the tree-rank comparison
    lemma identifies the two conditions with $\rho(S_x)\le\rho(T_x)$ and $\rho(T_x)<\rho(S_x)$.
    If just one is ill founded, a branch supplies the map into that tree, and a map in the other direction
    would produce a branch in a well-founded tree. Thus the two conditions are complementary and give the
    required inclusions. For indices, first use the delayed tree presentations, which form a jointly decidable
    family on all indices. Apply the two comparison constructions to this family, then specialize each joint
    decision program by inserting the paired input index into its fixed syntax. The specialization construction
    of §{sec:edst-pair-tree-indices} is itself lambda-computable and preserves the projections.
    No decision of disjointness and no enlargement of $\varepsilon$ occurs.
    \end{proof}
-/
theorem exists_separationIndices (ε : ℕ → ℕ) :
    ∃ sep co : ℕ → ℕ, (∃ F, NumericalComputes F sep) ∧
      (∃ G, NumericalComputes G co) ∧ ∀ e f,
      Disjoint (indexedProjection ε e) (indexedProjection ε f) →
      indexedProjection ε e ⊆ indexedProjection ε (sep (Nat.pair e f)) ∧
      indexedProjection ε (sep (Nat.pair e f)) ⊆ (indexedProjection ε f)ᶜ ∧
      indexedProjection ε (sep (Nat.pair e f)) =
        (indexedProjection ε (co (Nat.pair e f)))ᶜ := by
  let T := fun (i : ℕ) => indexedTree ε i.unpair.1
  let S := fun (i : ℕ) => indexedTree ε i.unpair.2
  have hT := indexedTree_reindex_decidable ε (computes_codeFirst numericalIdentity_computes)
  have hS := indexedTree_reindex_decidable ε (computes_codeSecond numericalIdentity_computes)
  obtain ⟨sep,hsep,hs⟩ := treeFamily_indices ε (fun i => comparisonLeTree (S i) (T i))
    (comparisonLeTree_family_decidable S T hS hT)
  obtain ⟨co,hco,hc⟩ := treeFamily_indices ε (fun i => comparisonLtTree (T i) (S i))
    (comparisonLtTree_family_decidable T S hT hS)
  refine ⟨sep,co,hsep,hco,fun e f hd => ?_⟩
  have hsEq := pairTreeProjection_indexedTree ε (sep (Nat.pair e f)) _ (hs (Nat.pair e f))
  have hcEq := pairTreeProjection_indexedTree ε (co (Nat.pair e f)) _ (hc (Nat.pair e f))
  change indexedProjection ε e ⊆ pairTreeProjection (indexedTree ε (sep (Nat.pair e f))).tree ∧
    pairTreeProjection (indexedTree ε (sep (Nat.pair e f))).tree ⊆ (indexedProjection ε f)ᶜ ∧
    pairTreeProjection (indexedTree ε (sep (Nat.pair e f))).tree =
      (pairTreeProjection (indexedTree ε (co (Nat.pair e f))).tree)ᶜ
  rw [hsEq,hcEq]
  simpa only [T,S,Nat.unpair_pair,indexedProjection] using
    comparison_separation (indexedTree ε e) (indexedTree ε f) hd

end LambdaTree
end PolishSpaceBook
