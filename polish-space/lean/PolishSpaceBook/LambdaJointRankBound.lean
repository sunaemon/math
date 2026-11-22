module

public import PolishSpaceBook.JointTreeRankBound
public import PolishSpaceBook.LambdaTreeMapPrograms

@[expose] public section

/-! # Lambda decisions for the concrete joint rank bound

All tests use the original parameter. Well-foundedness is supplied by
disjointness only after constructing the numerical decision program.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance jointPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a word code $w$, the joint-tree membership body is
    $$\begin{aligned}
    \LambdaTermName{jointNode}(o,w):= \LambdaTermName{chooseLe} \bigl(w, \ChurchNumeral{0}; \ChurchNumeral{1},
    \qquad \qquad \qquad \quad&\\
     \LambdaMul\,(Po \LambdaNumericPairValue{ \LambdaTermName{wordProjection}_1w}{
    \LambdaTermName{wordProjection}_1( \LambdaTermName{wordProjection}_2w)})
     (Qo \LambdaNumericPairValue{ \LambdaTermName{wordProjection}_1w}{ \LambdaTermName{wordProjection}_2(
    \LambdaTermName{wordProjection}_2w)}) \bigr).&
    \end{aligned}$$
    On input $z= \NatPair{b}{a}$, write $b:= \LambdaNumericProjection{1}z$ and $a:= \LambdaNumericProjection{2}z$
    within the following body. The relation
    program is
    $$\begin{aligned}
    \LambdaTermName{strictExtension}(a,b)&:= \LambdaMul\,( \LambdaListPrefix \LambdaNumericPairValue{a}{b})\,(
    \LambdaTermName{less}( \LambdaTermName{length}(a), \LambdaTermName{length}(b))),\\
    \LambdaTermName{jointRelation}&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,(\LambdaTermName{jointNode}(o,b))\,
     (\LambdaMul\,(\LambdaTermName{jointNode}(o,a))\,(\LambdaTermName{strictExtension}(a,b)))}}.
    \end{aligned}$$
    The root test in $\LambdaTermName{jointNode}$ accepts the empty word. Both node tests in
    $\LambdaTermName{jointRelation}$ ensure that codes outside
    the tree are isolated. Prefix and length tests give exactly strict extension.
-/
theorem flattenedTree_decidable {ε : ℕ → ℕ} (D : PairTree ε) :
    LambdaRelative.DecidablePredicate ε (fun n : ℕ => NatListCode.decode n ∈ (flattenedTree D).tree) := by
  have h := D.decidable.precompNumerical
    (g := fun n : ℕ => (leftWitness (NatListCode.decode n),rightWitness (NatListCode.decode n)))
    ((witnessProjection_computes true).pair (witnessProjection_computes false))
    (fun n => by simp [Encodable.encode,leftWitness,rightWitness])
  simpa only [flattenedTree,mem_ofPred_eq,decode_eq_nil_iff,id_eq] using
    (numerical_zero_decidable numericalIdentity_computes ε).or h

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a word code $w$, the joint-tree membership body is
    $$\begin{aligned}
    \LambdaTermName{jointNode}(o,w):= \LambdaTermName{chooseLe} \bigl(w, \ChurchNumeral{0}; \ChurchNumeral{1},
    \qquad \qquad \qquad \quad&\\
     \LambdaMul\,(Po \LambdaNumericPairValue{ \LambdaTermName{wordProjection}_1w}{
    \LambdaTermName{wordProjection}_1( \LambdaTermName{wordProjection}_2w)})
     (Qo \LambdaNumericPairValue{ \LambdaTermName{wordProjection}_1w}{ \LambdaTermName{wordProjection}_2(
    \LambdaTermName{wordProjection}_2w)}) \bigr).&
    \end{aligned}$$
    On input $z= \NatPair{b}{a}$, write $b:= \LambdaNumericProjection{1}z$ and $a:= \LambdaNumericProjection{2}z$
    within the following body. The relation
    program is
    $$\begin{aligned}
    \LambdaTermName{strictExtension}(a,b)&:= \LambdaMul\,( \LambdaListPrefix \LambdaNumericPairValue{a}{b})\,(
    \LambdaTermName{less}( \LambdaTermName{length}(a), \LambdaTermName{length}(b))),\\
    \LambdaTermName{jointRelation}&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,(\LambdaTermName{jointNode}(o,b))\,
     (\LambdaMul\,(\LambdaTermName{jointNode}(o,a))\,(\LambdaTermName{strictExtension}(a,b)))}}.
    \end{aligned}$$
    The root test in $\LambdaTermName{jointNode}$ accepts the empty word. Both node tests in
    $\LambdaTermName{jointRelation}$ ensure that codes outside
    the tree are isolated. Prefix and length tests give exactly strict extension.
-/
theorem codedExtension_decidable {ε : ℕ → ℕ} (T : RootedPrefixTree)
    (hT : LambdaRelative.DecidablePredicate ε (fun n : ℕ => NatListCode.decode n ∈ T.tree)) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ => T.codedExtension z.unpair.1 z.unpair.2) := by
  have hb := hT.precompNumerical (g := fun z : ℕ => z.unpair.1)
    (projection_computes true) (fun _ => rfl)
  have ha := hT.precompNumerical (g := fun z : ℕ => z.unpair.2)
    (projection_computes false) (fun _ => rfl)
  have hp := word_prefix_decidable (projection_computes false) (projection_computes true) ε
  have hl := numerical_lt_decidable
    (listLength_computes.comp (projection_computes false))
    (listLength_computes.comp (projection_computes true)) ε
  exact hb.and (ha.and (hp.and hl))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a word code $w$, the joint-tree membership body is
    $$\begin{aligned}
    \LambdaTermName{jointNode}(o,w):= \LambdaTermName{chooseLe} \bigl(w, \ChurchNumeral{0}; \ChurchNumeral{1},
    \qquad \qquad \qquad \quad&\\
     \LambdaMul\,(Po \LambdaNumericPairValue{ \LambdaTermName{wordProjection}_1w}{
    \LambdaTermName{wordProjection}_1( \LambdaTermName{wordProjection}_2w)})
     (Qo \LambdaNumericPairValue{ \LambdaTermName{wordProjection}_1w}{ \LambdaTermName{wordProjection}_2(
    \LambdaTermName{wordProjection}_2w)}) \bigr).&
    \end{aligned}$$
    On input $z= \NatPair{b}{a}$, write $b:= \LambdaNumericProjection{1}z$ and $a:= \LambdaNumericProjection{2}z$
    within the following body. The relation
    program is
    $$\begin{aligned}
    \LambdaTermName{strictExtension}(a,b)&:= \LambdaMul\,( \LambdaListPrefix \LambdaNumericPairValue{a}{b})\,(
    \LambdaTermName{less}( \LambdaTermName{length}(a), \LambdaTermName{length}(b))),\\
    \LambdaTermName{jointRelation}&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,(\LambdaTermName{jointNode}(o,b))\,
     (\LambdaMul\,(\LambdaTermName{jointNode}(o,a))\,(\LambdaTermName{strictExtension}(a,b)))}}.
    \end{aligned}$$
    The root test in $\LambdaTermName{jointNode}$ accepts the empty word. Both node tests in
    $\LambdaTermName{jointRelation}$ ensure that codes outside
    the tree are isolated. Prefix and length tests give exactly strict extension.
-/
theorem jointTree_relation_decidable {ε : ℕ → ℕ} (T S : PairTree ε) :
    LambdaRelative.DecidablePredicate ε
      (fun z : ℕ => (jointTree T S).codedExtension z.unpair.1 z.unpair.2) :=
  codedExtension_decidable _ (flattenedTree_decidable (T.intersection S))

end LambdaTree
end PolishSpaceBook
