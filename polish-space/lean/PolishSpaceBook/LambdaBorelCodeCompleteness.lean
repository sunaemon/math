module

public import PolishSpaceBook.BorelExpressionCompleteness
public import PolishSpaceBook.LambdaSectionEdgeCodes
public import PolishSpaceBook.LambdaBorelEvaluation
public import PolishSpaceBook.LambdaArithmeticNormalForm

@[expose] public section

/-! # Recursive Borel codes from complementary lambda-decided trees

The separating code uses the joint search tree itself as the rank bound.
Its validity follows from disjointness, while its labels use only the two
original decision programs. No ordinal-notation selector is assumed.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm BorelExpression
namespace LambdaTree
local instance recursiveCodeListEncoding : Encodable (List ℕ) := NatListCode.encodable

/-- A valid external expression with labels computed at the given parameter. -/
def HasRecursiveBorelCode (ε : ℕ → ℕ) (A : Set (ℕ → ℕ)) : Prop :=
  ∃ c : Code, (∃ P, LambdaRelative.Computes ε P c.val) ∧ A = c.value cylinderBasis

noncomputable def recursiveSeparatorCode {ε : ℕ → ℕ} (T S : PairTree ε)
    (hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree)) : Code :=
  RankBound.code (sectionEdgeCode S) (jointTree T S).codedExtension
    ((jointTree T S).codedExtension_wellFounded (jointTree_wellFounded T S hd)) 0 0

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Programs for the recursive Borel separator
  excerpt: |
    The closed terms $\LambdaTermName{jointRelation}$ and $\LambdaTermName{edgeLabel}_Q$ decide the joint-tree
    relation and compute the
    section-edge
    labels, respectively, at the original parameter. Therefore
    $$\lambdaab{o}{\lambdaab{w}{\LambdaRankLabelProgram{\LambdaTermName{edgeLabel}_Q}{\LambdaTermName{jointRelation}}\,o\,
     \LambdaNumericPairValue{\ChurchNumeral{0}}{\LambdaNumericPairValue{\ChurchNumeral{0}}{w}}}}$$
    computes every label of the separating expression whenever the two projections are disjoint.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    List mapping computes each coordinate of the joint word, and the supplied deciders compute the two
    membership bits. Their product and the root test give $\LambdaTermName{jointNode}$. The further products, prefix
    test, and
    strict length comparison give $\LambdaTermName{jointRelation}$. The same numerical rules give the four factors
    of $\LambdaTermName{edgeGuard}$.
    At address code zero, $\LambdaTermName{edgeLabel}_Q$ returns the union label one. At a nonempty address, predecessor and
    projection recover $k,r$. A true guard selects the leaf label $k+3$ at its root and zero elsewhere;
    a false guard selects the empty-expression labels two at the root, three at its child zero, and zero
    elsewhere. These are precisely the labels of the edge expression. Every step has a finite beta/query
    derivation by the numerical reduction lemmas and totality of the supplied deciders. The rank-label
    iteration theorem then applies with both root indices fixed at zero. Disjointness is used to prove
    validity of the final expression; none of these programs tests disjointness or selects a branch.
-/
theorem recursiveSeparatorCode_computable {ε : ℕ → ℕ} (T S : PairTree ε)
    (hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree)) :
    ∃ P, LambdaRelative.Computes ε P (recursiveSeparatorCode T S hd).val := by
  classical
  obtain ⟨P,hP⟩ := sectionEdgeLabels_computable S
  obtain ⟨Q,hQ⟩ := jointTree_relation_decidable T S
  exact ⟨_,RankBound.rankCodeLabelProgram_computes (sectionEdgeCode S)
    (jointTree T S).codedExtension
    ((jointTree T S).codedExtension_wellFounded (jointTree_wellFounded T S hd)) hP hQ 0 0⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Use word codes as the nodes of a relation on $\NN$. Put $u_b:=\LambdaListDecode{b}$ and define
    $$R(b,a)\quad\Longleftrightarrow\quad
    u_b,u_a\in J,\quad u_a\prefixOf u_b,\quad \Length{u_a}<\Length{u_b}.$$
    Codes of words outside $J$ are isolated. Thus $R$ is well founded, its root is zero, and its decision
    program uses only word projections, prefix tests, lengths, and the two original membership programs.
    For the section $S_x$, let $E_x(b,a)$ be the same strict-extension relation on its word codes.
    The rank bound just proved shows that the layer $\RankLayer{0}{0}$ for these relations contains $A$.
    It is disjoint from $B$, since a branch of $S_x$ gives an infinite descending chain from its root.
-/
theorem recursiveSeparatorCode_value {ε : ℕ → ℕ} (T S : PairTree ε)
    (hd : Disjoint (pairTreeProjection T.tree) (pairTreeProjection S.tree)) :
    pairTreeProjection T.tree ⊆ (recursiveSeparatorCode T S hd).value cylinderBasis ∧
    (recursiveSeparatorCode T S hd).value cylinderBasis ⊆ (pairTreeProjection S.tree)ᶜ := by
  have he : (recursiveSeparatorCode T S hd).value cylinderBasis =
      {x | RankBound.Holds (jointTree T S).codedExtension
        ((jointTree T S).codedExtension_wellFounded (jointTree_wellFounded T S hd))
        (rootedSection S x).codedExtension 0 0} := by
    ext x
    rw [recursiveSeparatorCode,RankBound.mem_value_code_iff cylinderBasis
      (by simp [cylinderBasis,NatListCode.decode])]
    have hr : (fun b a => x ∈ (sectionEdgeCode S b a).value cylinderBasis) =
        (rootedSection S x).codedExtension := by
      funext b a
      exact propext (mem_sectionEdgeCode S b a x)
    rw [hr]
    rfl
  rw [he]
  exact jointRank_separates T S hd

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: theorem
  title: Recursive Borel separation
  excerpt: |
    If $A,B$ have pair-tree presentations decidable relative to $\varepsilon$ and $A\cap B=\emptyset$,
    there is a valid Borel expression $c$ whose labels are computable relative to $\varepsilon$ and
    $$A\IncludedIn\BorelValue{c}\IncludedIn B^{\complement}.$$
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    Take the relation $R$ of the joint tree and the edge expressions $e_{b,a}$ above. Apply the rank-layer
    construction with both root indices zero and set $c=\RankLayerCode{0}{0}$. The relation is well founded
    and the edge expressions are valid, so $c$ is valid. Its value is $\RankLayer{0}{0}$, which separates
    the two projections by the joint-tree rank bound. The decision program for $R$ and the joint edge-label
    program are total at $\varepsilon$. The rank-label program therefore computes every label of $c$ at
    that same parameter. This constructs the bound and the label program directly from the pair trees;
    no choice of an ordinal notation or of a branch is part of the computation.
-/
theorem recursiveBorel_separation {ε : ℕ → ℕ} {A B : Set (ℕ → ℕ)}
    (hA : Projected ε A) (hB : Projected ε B) (hd : Disjoint A B) :
    ∃ C, HasRecursiveBorelCode ε C ∧ A ⊆ C ∧ C ⊆ Bᶜ := by
  obtain ⟨T,rfl⟩ := hA
  obtain ⟨S,rfl⟩ := hB
  exact ⟨_,⟨recursiveSeparatorCode T S hd,recursiveSeparatorCode_computable T S hd,rfl⟩,
    recursiveSeparatorCode_value T S hd⟩

theorem complemented_iff_recursiveBorelCode {ε : ℕ → ℕ} (A : Set (ℕ → ℕ)) :
    Complemented ε A ↔ HasRecursiveBorelCode ε A := by
  constructor
  · rintro ⟨hA,hAc⟩
    obtain ⟨C,hC,hleft,hright⟩ := recursiveBorel_separation hA hAc disjoint_compl_right
    have he : A = C := Set.Subset.antisymm hleft (by simpa only [compl_compl] using hright)
    exact he ▸ hC
  · rintro ⟨c,⟨P,hP⟩,rfl⟩
    exact complemented_evaluate c.val hP c.property

/-- The formula-based lightface statement follows through the proved
arithmetic pair-tree normal form in both directions. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: corollary
  title: Recursive Borel-code completeness
  excerpt: |
    A set of Baire reals is $\lDelta^1_1(\varepsilon)$ if and only if it is the value of a valid Borel
    expression whose labels are computable relative to $\varepsilon$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    By the pair-tree normal form, the set and its complement have decidable pair-tree presentations at
    $\varepsilon$. Apply recursive Borel separation to those two presentations. The separating value
    contains the set and is contained in the complement of its complement, so it equals the set.
    Conversely, Borel evaluation at a fixed parameter supplies decidable pair-tree presentations of the
    value and its complement from any valid expression with a label program. Thus both are
    $\lSigma^1_1(\varepsilon)$, as required.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    For sets of Baire reals, §{sec:edst-recursive-borel-completeness} gives both directions: the joint tree
    supplies a well-founded bound, the section-edge programs and rank-label iteration compute a valid
    Borel expression, and evaluation certificates give the converse. This constructs the labels of an
    expression for a set of reals; it does not compute its membership from one fixed jump.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    There is also a lightface theorem for subsets of Baire space:
    the sets that are both effectively analytic and effectively coanalytic are exactly those with recursive Borel codes.
-/
theorem formulaDelta_iff_recursiveBorelCode (ε : ℕ → ℕ) (A : Set (ℕ → ℕ)) :
    (FormulaAnalytic ε A ∧ FormulaAnalytic ε Aᶜ) ↔ HasRecursiveBorelCode ε A := by
  rw [formulaAnalytic_iff_projected,formulaAnalytic_iff_projected]
  exact complemented_iff_recursiveBorelCode A

/-- Forgetting relative effectivity leaves an ordinary countable Borel expression. -/
theorem HasRecursiveBorelCode.measurable {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)}
    (hA : HasRecursiveBorelCode ε A) : MeasurableSet A := by
  obtain ⟨c, _, hA⟩ := hA
  apply (BorelExpression.measurableSet_iff_hasCode A).mpr
  exact ⟨c.val, c.property, hA.symm⟩

/-- The parameter records the actual Borel-expression labels; no uniform
selection of a code from unspecified Borel-set data is asserted. -/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The assertion for sets of reals relativizes to give the boldface Suslin theorem
    $\bDelta^1_1=\text{Borel}$. A $\bDelta^1_1$ set belongs to $\lDelta^1_1(a)$ for some real parameter $a$.
    Its relative recursive Borel code is in particular an ordinary countable Borel code, so the set is Borel.
-/
theorem measurableSet_iff_exists_complemented (A : Set (ℕ → ℕ)) :
    MeasurableSet A ↔ ∃ ε : ℕ → ℕ, Complemented ε A := by
  constructor
  · intro hA
    obtain ⟨c, hc, hca⟩ := (BorelExpression.measurableSet_iff_hasCode A).mp hA
    let ε : ℕ → ℕ := fun n => c (NatListCode.decode n)
    have hp : LambdaRelative.Computes ε identityProgram c := by
      refine ⟨identityProgram_closed, ?_⟩
      intro s
      simpa [ε, Encodable.encode] using identityProgram_runs ε (NatListCode.encode s)
    exact ⟨ε, (complemented_iff_recursiveBorelCode A).mpr
      ⟨⟨c, hc⟩, ⟨identityProgram, hp⟩, hca.symm⟩⟩
  · rintro ⟨ε, hA⟩
    exact ((complemented_iff_recursiveBorelCode A).mp hA).measurable

end LambdaTree
end PolishSpaceBook
