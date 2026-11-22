module

public import PolishSpaceBook.LambdaFinitePointclasses
public import PolishSpaceBook.LambdaProjectionOperations

@[expose] public section

/-! # The closed-product and recursive-pair-tree analytic bases agree

Both conversions keep the original parameter. Finite word pairing and the
inverse projections are computed by the existing numerical lambda terms.
The finite-check construction includes the empty prefix test.
-/
noncomputable section
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm LambdaTree
namespace LambdaFinite
local instance projectiveBaseWords : Encodable (List ℕ) := NatListCode.encodable
local instance projectiveBasePairs : Encodable (List ℕ × List ℕ) := wordPairEncodable

/-- Decode both coordinate prefixes before applying the pair-tree decider. -/
def encodedPairPrefixTree {ε : ℕ → ℕ} (T : LambdaTree.PairTree ε) : PrefixTree ε where
  tree := {u | (leftWitness u, rightWitness u) ∈ T.tree}
  downward := by
    intro s t ht hst
    obtain ⟨v, rfl⟩ := hst
    simpa only [leftWitness, rightWitness, ← List.map_take,
      List.take_left, Set.mem_ofPred_eq] using T.downward _ ht s.length
  decidable := T.decidable.precompNumerical
    (g := fun u : List ℕ => (leftWitness u, rightWitness u))
    ((witnessProjection_computes true).pair (witnessProjection_computes false))
    (fun u => by simp [Encodable.encode, leftWitness, rightWitness])

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    And $A\IncludedIn\BaireSpace$ lies in $\lSigma^1_1(a)$ iff there is an $a$-recursive tree
    $T\IncludedIn\finseq{\omega}\times\finseq{\omega}$ such that
    $$
    p\in A
    \quad\Longleftrightarrow\quad
    \exists q\in\BaireSpace\ \forall n\; (\restrict{p}{n},\ \restrict{q}{n})\in T.
    $$
-/
theorem projectiveSigma_zero_iff_projected (ε : ℕ → ℕ) (A : Set (ℕ → ℕ)) :
    ProjectiveSigma ε 0 A ↔ LambdaTree.Projected ε A := by
  constructor
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨T, rfl⟩ := (relativelyEffectivelyClosed_iff_recursive_tree ε C).mp hC
    have hd : LambdaRelative.DecidablePredicate ε
        (fun z : List ℕ × List ℕ => pairWords z.1 z.2 ∈ T.tree) :=
      T.decidable.precompNumerical (g := fun z : List ℕ × List ℕ => pairWords z.1 z.2)
        pairWords_computes (fun z => by simp [Encodable.encode])
    have hp := projected_finiteChecks hd
    convert hp using 1
    ext p
    simp only [Set.mem_ofPred_eq, treeBody, pairWords_prefix]
  · rintro ⟨T, rfl⟩
    refine ⟨treeBody (encodedPairPrefixTree T).tree,
      recursive_tree_body_relativelyEffectivelyClosed ε (encodedPairPrefixTree T), ?_⟩
    ext p
    simp only [pairTreeProjection, pairTreeBody, treeBody, encodedPairPrefixTree,
      Set.mem_ofPred_eq, leftWitness_prefix, rightWitness_prefix, leftBaire_pair, rightBaire_pair]

end LambdaFinite
end PolishSpaceBook
