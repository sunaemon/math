module

public import PolishSpaceBook.LambdaBoundedPrefixTests
public import PolishSpaceBook.LambdaCountableOperations

@[expose] public section

/-! # Number quantifiers as relative pair-tree projections

Witness digits select the existential numerical witnesses; no computable
selection of these digits is asserted.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance arithmeticListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance arithmeticPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

private theorem prefix_getD (p : ℕ → ℕ) {n i : ℕ} (h : i < n) :
    (seqPrefix p n).getD i 0 = p i := by
  simp [seqPrefix,h,List.getD_eq_getElem?_getD]

/-- Row input (n,(s,t)) becomes (s(0),(n,t(n))). -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let a closed program $\LambdaTermName{numberPredicate}$ decide $\mathcal R(e,n,k)$ at parameter $\varepsilon$,
    with numerical input
    $\NatPair{e}{\NatPair{n}{k}}$. On a row input $z=\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$,
    use the following term abbreviations:
    $$\begin{aligned}
    \LambdaTermName{rowIndex}(z)&:=\LambdaNumericProjection{1}z,\\
    \LambdaTermName{pointWord}(z)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
    \LambdaTermName{witnessWord}(z)&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z),\\
    \LambdaTermName{entry}(a,j)&:=\LambdaListGet(\LambdaNumericPair\,a\,j),\\
    \LambdaTermName{firstEntry}(z)&:=\LambdaTermName{entry}(\LambdaTermName{pointWord}(z),\ChurchNumeral{0}).
    \end{aligned}$$
    Then the two row testers are the closed terms obtained by expanding
    $$\begin{aligned}
    \LambdaTermName{numberRow}_{ \forall \exists}&:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{numberPredicate}o
    \bigl( \LambdaNumericPair\, \LambdaTermName{firstEntry}(z)\,
     ( \LambdaNumericPair\, \LambdaTermName{rowIndex}(z)\, \LambdaTermName{entry}( \LambdaTermName{witnessWord}(z),
    \LambdaTermName{rowIndex}(z))) \bigr)}},\\
    \LambdaTermName{numberRow}_{ \exists \forall}&:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{numberPredicate}o
    \bigl( \LambdaNumericPair\, \LambdaTermName{firstEntry}(z)\,
     ( \LambdaNumericPair\, \LambdaTermName{entry}( \LambdaTermName{witnessWord}(z), \ChurchNumeral{0})\,
    \LambdaTermName{rowIndex}(z)) \bigr)}}.
    \end{aligned}$$
-/
def forallExistsInputTerm : AlphaTerm := pairNumerical
  (numericalCompose listGetTerm (pairNumerical
    (codeFirst (numericalProjectionTerm false)) (numericalConstant 0)))
  (pairNumerical (numericalProjectionTerm true)
    (numericalCompose listGetTerm (pairNumerical
      (codeSecond (numericalProjectionTerm false)) (numericalProjectionTerm true))))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Numerical projections recover the row number and both word codes. List access reads the indicated
    entries, returning zero when an entry is missing. Pairing therefore feeds $\LambdaTermName{numberPredicate}$ the code of
    $\Tuple{s(0),i,t(i)}$ in the first case and $\Tuple{s(0),t(0),i}$ in the second. Two outer beta contractions expose
    these computations at the original parameter. Every component terminates. For prefixes of length
    $i+1$, every indicated entry is present, so these tests have exactly the meanings asserted in the
    numerical-quantifier lemma. Use the successor program for the prefix bound. To obtain the complement
    of the first projection, apply the second construction to the decision program for $\neg \mathcal R$.
    \end{proof}
-/
theorem forallExistsInput_computes : NumericalComputes forallExistsInputTerm
    (fun z => Nat.pair ((NatListCode.decode z.unpair.2.unpair.1).getD 0 0)
      (Nat.pair z.unpair.1 ((NatListCode.decode z.unpair.2.unpair.2).getD z.unpair.1 0))) := by
  simpa only [forallExistsInputTerm,codeFirst,codeSecond,Nat.unpair_pair,ite_true,
    Bool.false_eq_true,ite_false] using
    (listGet_computes.comp ((computes_codeFirst (projection_computes false)).pair
      (numericalConstant_computes 0))).pair
    ((projection_computes true).pair (listGet_computes.comp
      ((computes_codeSecond (projection_computes false)).pair (projection_computes true))))

/-- Row input (m,(s,t)) becomes (s(0),(t(0),m)). -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let a closed program $\LambdaTermName{numberPredicate}$ decide $\mathcal R(e,n,k)$ at parameter $\varepsilon$,
    with numerical input
    $\NatPair{e}{\NatPair{n}{k}}$. On a row input $z=\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$,
    use the following term abbreviations:
    $$\begin{aligned}
    \LambdaTermName{rowIndex}(z)&:=\LambdaNumericProjection{1}z,\\
    \LambdaTermName{pointWord}(z)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
    \LambdaTermName{witnessWord}(z)&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z),\\
    \LambdaTermName{entry}(a,j)&:=\LambdaListGet(\LambdaNumericPair\,a\,j),\\
    \LambdaTermName{firstEntry}(z)&:=\LambdaTermName{entry}(\LambdaTermName{pointWord}(z),\ChurchNumeral{0}).
    \end{aligned}$$
    Then the two row testers are the closed terms obtained by expanding
    $$\begin{aligned}
    \LambdaTermName{numberRow}_{ \forall \exists}&:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{numberPredicate}o
    \bigl( \LambdaNumericPair\, \LambdaTermName{firstEntry}(z)\,
     ( \LambdaNumericPair\, \LambdaTermName{rowIndex}(z)\, \LambdaTermName{entry}( \LambdaTermName{witnessWord}(z),
    \LambdaTermName{rowIndex}(z))) \bigr)}},\\
    \LambdaTermName{numberRow}_{ \exists \forall}&:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{numberPredicate}o
    \bigl( \LambdaNumericPair\, \LambdaTermName{firstEntry}(z)\,
     ( \LambdaNumericPair\, \LambdaTermName{entry}( \LambdaTermName{witnessWord}(z), \ChurchNumeral{0})\,
    \LambdaTermName{rowIndex}(z)) \bigr)}}.
    \end{aligned}$$
-/
def existsForallInputTerm : AlphaTerm := pairNumerical
  (numericalCompose listGetTerm (pairNumerical
    (codeFirst (numericalProjectionTerm false)) (numericalConstant 0)))
  (pairNumerical
    (numericalCompose listGetTerm (pairNumerical
      (codeSecond (numericalProjectionTerm false)) (numericalConstant 0)))
    (numericalProjectionTerm true))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Numerical projections recover the row number and both word codes. List access reads the indicated
    entries, returning zero when an entry is missing. Pairing therefore feeds $\LambdaTermName{numberPredicate}$ the code of
    $\Tuple{s(0),i,t(i)}$ in the first case and $\Tuple{s(0),t(0),i}$ in the second. Two outer beta contractions expose
    these computations at the original parameter. Every component terminates. For prefixes of length
    $i+1$, every indicated entry is present, so these tests have exactly the meanings asserted in the
    numerical-quantifier lemma. Use the successor program for the prefix bound. To obtain the complement
    of the first projection, apply the second construction to the decision program for $\neg \mathcal R$.
    \end{proof}
-/
theorem existsForallInput_computes : NumericalComputes existsForallInputTerm
    (fun z => Nat.pair ((NatListCode.decode z.unpair.2.unpair.1).getD 0 0)
      (Nat.pair ((NatListCode.decode z.unpair.2.unpair.2).getD 0 0) z.unpair.1)) := by
  simpa only [existsForallInputTerm,codeFirst,codeSecond,Nat.unpair_pair,ite_true,
    Bool.false_eq_true,ite_false] using
    (listGet_computes.comp ((computes_codeFirst (projection_computes false)).pair
      (numericalConstant_computes 0))).pair
    ((listGet_computes.comp ((computes_codeSecond (projection_computes false)).pair
      (numericalConstant_computes 0))).pair (projection_computes true))

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For $A$, let the witness $q$ store a suitable number $q(n)$ for every $n$ and impose
    $$R(x(0),n,q(n))\qquad(n\in\NN).$$
    For the complement, let $q(0)$ name an input for which every trial fails and impose
    $$\neg R(x(0),q(0),k)\qquad(k\in\NN).$$
    In either case row $i$ reads only the first $i+1$ entries of the point and witness. On arbitrary finite
    words, read missing entries as zero; this makes each row a total decidable predicate on word codes.
    The bounded-prefix construction of §{sec:lambda-recursive-borel-separation} turns these rows, with bound
    $i+1$, into a decidable pair tree. A branch satisfies every row, and every pair satisfying the rows is
    a branch. Projecting the first tree yields $A$: existence of all the numerical witnesses permits choosing
    the sequence $q$. Projecting the second yields its complement: a single failed input can be stored in
    a constant sequence. This is an existence argument for witnesses, not a procedure selecting them.
    The lambda terms implementing the two row tests are given in §{sec:lambda-graph-tests}.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let a closed program $\LambdaTermName{numberPredicate}$ decide $\mathcal R(e,n,k)$ at parameter $\varepsilon$,
    with numerical input
    $\NatPair{e}{\NatPair{n}{k}}$. On a row input $z=\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$,
    use the following term abbreviations:
    $$\begin{aligned}
    \LambdaTermName{rowIndex}(z)&:=\LambdaNumericProjection{1}z,\\
    \LambdaTermName{pointWord}(z)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
    \LambdaTermName{witnessWord}(z)&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z),\\
    \LambdaTermName{entry}(a,j)&:=\LambdaListGet(\LambdaNumericPair\,a\,j),\\
    \LambdaTermName{firstEntry}(z)&:=\LambdaTermName{entry}(\LambdaTermName{pointWord}(z),\ChurchNumeral{0}).
    \end{aligned}$$
    Then the two row testers are the closed terms obtained by expanding
    $$\begin{aligned}
    \LambdaTermName{numberRow}_{ \forall \exists}&:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{numberPredicate}o
    \bigl( \LambdaNumericPair\, \LambdaTermName{firstEntry}(z)\,
     ( \LambdaNumericPair\, \LambdaTermName{rowIndex}(z)\, \LambdaTermName{entry}( \LambdaTermName{witnessWord}(z),
    \LambdaTermName{rowIndex}(z))) \bigr)}},\\
    \LambdaTermName{numberRow}_{ \exists \forall}&:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{numberPredicate}o
    \bigl( \LambdaNumericPair\, \LambdaTermName{firstEntry}(z)\,
     ( \LambdaNumericPair\, \LambdaTermName{entry}( \LambdaTermName{witnessWord}(z), \ChurchNumeral{0})\,
    \LambdaTermName{rowIndex}(z)) \bigr)}}.
    \end{aligned}$$
-/
theorem projected_forall_exists {ε : ℕ → ℕ} {R : ℕ → ℕ → ℕ → Prop}
    (hR : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (ℕ × ℕ) => R z.1 z.2.1 z.2.2)) :
    Projected ε {x | ∀ n, ∃ m, R (x 0) n m} := by
  have hp : LambdaRelative.DecidablePredicate ε (fun z : ℕ × PrefixPair =>
      R (z.2.1.getD 0 0) z.1 (z.2.2.getD z.1 0)) :=
    hR.precompNumerical (g := fun z : ℕ × PrefixPair => (z.2.1.getD 0 0,(z.1,z.2.2.getD z.1 0)))
      forallExistsInput_computes (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have h := projected_forall_finitePrefixTests
    (p := fun i z => R (z.1.getD 0 0) i (z.2.getD i 0)) hp successor_computes
  have he : {x | ∃ y, ∀ i, R ((seqPrefix x (i+1)).getD 0 0) i
      ((seqPrefix y (i+1)).getD i 0)} = {x | ∀ n, ∃ m, R (x 0) n m} := by
    ext x
    simp only [mem_ofPred_eq,prefix_getD _ (Nat.zero_lt_succ _),prefix_getD _ (Nat.lt_succ_self _)]
    exact Classical.skolem.symm
  exact he ▸ h

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For $A$, let the witness $q$ store a suitable number $q(n)$ for every $n$ and impose
    $$R(x(0),n,q(n))\qquad(n\in\NN).$$
    For the complement, let $q(0)$ name an input for which every trial fails and impose
    $$\neg R(x(0),q(0),k)\qquad(k\in\NN).$$
    In either case row $i$ reads only the first $i+1$ entries of the point and witness. On arbitrary finite
    words, read missing entries as zero; this makes each row a total decidable predicate on word codes.
    The bounded-prefix construction of §{sec:lambda-recursive-borel-separation} turns these rows, with bound
    $i+1$, into a decidable pair tree. A branch satisfies every row, and every pair satisfying the rows is
    a branch. Projecting the first tree yields $A$: existence of all the numerical witnesses permits choosing
    the sequence $q$. Projecting the second yields its complement: a single failed input can be stored in
    a constant sequence. This is an existence argument for witnesses, not a procedure selecting them.
    The lambda terms implementing the two row tests are given in §{sec:lambda-graph-tests}.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let a closed program $\LambdaTermName{numberPredicate}$ decide $\mathcal R(e,n,k)$ at parameter $\varepsilon$,
    with numerical input
    $\NatPair{e}{\NatPair{n}{k}}$. On a row input $z=\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$,
    use the following term abbreviations:
    $$\begin{aligned}
    \LambdaTermName{rowIndex}(z)&:=\LambdaNumericProjection{1}z,\\
    \LambdaTermName{pointWord}(z)&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
    \LambdaTermName{witnessWord}(z)&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z),\\
    \LambdaTermName{entry}(a,j)&:=\LambdaListGet(\LambdaNumericPair\,a\,j),\\
    \LambdaTermName{firstEntry}(z)&:=\LambdaTermName{entry}(\LambdaTermName{pointWord}(z),\ChurchNumeral{0}).
    \end{aligned}$$
    Then the two row testers are the closed terms obtained by expanding
    $$\begin{aligned}
    \LambdaTermName{numberRow}_{ \forall \exists}&:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{numberPredicate}o
    \bigl( \LambdaNumericPair\, \LambdaTermName{firstEntry}(z)\,
     ( \LambdaNumericPair\, \LambdaTermName{rowIndex}(z)\, \LambdaTermName{entry}( \LambdaTermName{witnessWord}(z),
    \LambdaTermName{rowIndex}(z))) \bigr)}},\\
    \LambdaTermName{numberRow}_{ \exists \forall}&:= \lambdaab{o}{ \lambdaab{z}{ \LambdaTermName{numberPredicate}o
    \bigl( \LambdaNumericPair\, \LambdaTermName{firstEntry}(z)\,
     ( \LambdaNumericPair\, \LambdaTermName{entry}( \LambdaTermName{witnessWord}(z), \ChurchNumeral{0})\,
    \LambdaTermName{rowIndex}(z)) \bigr)}}.
    \end{aligned}$$
-/
theorem projected_exists_forall {ε : ℕ → ℕ} {R : ℕ → ℕ → ℕ → Prop}
    (hR : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (ℕ × ℕ) => R z.1 z.2.1 z.2.2)) :
    Projected ε {x | ∃ n, ∀ m, R (x 0) n m} := by
  have hp : LambdaRelative.DecidablePredicate ε (fun z : ℕ × PrefixPair =>
      R (z.2.1.getD 0 0) (z.2.2.getD 0 0) z.1) :=
    hR.precompNumerical (g := fun z : ℕ × PrefixPair => (z.2.1.getD 0 0,(z.2.2.getD 0 0,z.1)))
      existsForallInput_computes (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have h := projected_forall_finitePrefixTests
    (p := fun i z => R (z.1.getD 0 0) (z.2.getD 0 0) i) hp successor_computes
  have he : {x | ∃ y, ∀ i, R ((seqPrefix x (i+1)).getD 0 0)
      ((seqPrefix y (i+1)).getD 0 0) i} = {x | ∃ n, ∀ m, R (x 0) n m} := by
    ext x
    simp only [mem_ofPred_eq,prefix_getD _ (Nat.zero_lt_succ _)]
    constructor
    · rintro ⟨y,hy⟩; exact ⟨y 0,hy⟩
    · rintro ⟨n,hn⟩; exact ⟨fun _ => n,hn⟩
  exact he ▸ h

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: statement
  kind: lemma
  title: Numerical quantifiers as tree projections
-/
theorem complemented_forall_exists {ε : ℕ → ℕ} {R : ℕ → ℕ → ℕ → Prop}
    (hR : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (ℕ × ℕ) => R z.1 z.2.1 z.2.2)) :
    Complemented ε {x | ∀ n, ∃ m, R (x 0) n m} := by
  refine ⟨projected_forall_exists hR,?_⟩
  convert projected_exists_forall (R := fun e n m => ¬ R e n m) hR.not using 1
  ext x
  simp

end LambdaTree
end PolishSpaceBook
