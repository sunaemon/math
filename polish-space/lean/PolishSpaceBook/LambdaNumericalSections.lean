module

public import PolishSpaceBook.LambdaUniformFamilies

@[expose] public section

/-! # Numerical sections of a relative pair-tree projection

A bound number is paired with each input digit. One numerical program transforms
all finite nodes jointly in that number, so countable operations preserve the
original parameter without choosing a separate decider for each section.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance sectionListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance sectionPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

def bindNumber (n : ℕ) (x : ℕ → ℕ) : ℕ → ℕ := fun k => Nat.pair n (x k)

@[simp] theorem leftBaire_bindNumber (n : ℕ) (x : ℕ → ℕ) :
    leftBaire (bindNumber n x) = fun _ => n := by
  funext k
  simp [leftBaire,bindNumber]

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    Fix the parameter $\varepsilon$. We encode a numerical variable together with an input sequence by
    \begin{mathmeta}
      \define{NumberBinding}
    \end{mathmeta}
    $$\NumberBinding{n}{x}(k):=\NatPair{n}{x(k)}.$$
    The first projection at coordinate zero recovers $n$, and the second projection at every coordinate
    recovers $x$.
-/
@[simp] theorem rightBaire_bindNumber (n : ℕ) (x : ℕ → ℕ) :
    rightBaire (bindNumber n x) = x := by
  funext k
  simp [rightBaire,bindNumber]

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    Repeating this operation encodes finitely many numerical variables.
-/
/-- A finite stack of numerical bindings retains the input sequence. -/
theorem rightBaire_iterate_bindNumbers (ns : List ℕ) (x : ℕ → ℕ) :
    (rightBaire^[ns.length]) (ns.foldr bindNumber x) = x := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simpa only [List.length_cons, List.foldr_cons, Function.iterate_succ_apply,
      rightBaire_bindNumber] using ih

/-- Input ((number,word-code),position) pairs the number with that entry. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To compute the finite word whose entries are $\NatPair{n}{s(k)}$, take
    $z=\NatPair{n}{\LambdaListCode{s}}$ and use the following closed numerical terms:
    $$\begin{aligned}
    F&:=\lambdaab{v}{\LambdaNumericPair\,
     (\LambdaNumericProjection{1}(\LambdaNumericProjection{1}v))\,
     (\LambdaListGet(\LambdaNumericPair\,
       (\LambdaNumericProjection{2}(\LambdaNumericProjection{1}v))\,
       (\LambdaNumericProjection{2}v)))},\\
    W&:=\lambdaab{z}{\LambdaListTabulate{F}\,
     (\LambdaNumericPair\,z\,(\LambdaListLength(\LambdaNumericProjection{2}z)))}.
    \end{aligned}$$
    For the joint tree input $u=\NatPair{n}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$,
    abbreviate $n=\LambdaNumericProjection{1}u$, $a=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}u)$,
    and $b=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}u)$. If $P$ decides the original tree,
    expand these abbreviations in
    $$J:=\lambdaab{o}{\lambdaab{u}{Po(\LambdaNumericPair\,(W(\LambdaNumericPair\,n\,a))\,b)}}.$$
-/
def numberWordEntryTerm : AlphaTerm := pairNumerical
  (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true))
  (numericalCompose listGetTerm
    (pairNumerical
      (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm true))
      (numericalProjectionTerm false)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    On input $\NatPair{z}{k}$, the term $F$ returns $\NatPair{n}{s(k)}$ for every position in range.
    Finite tabulation runs it at exactly the positions below the length of $s$, so $W$ returns the
    code of the word obtained by pairing $n$ with each entry. The term $J$ retains the second word and
    passes the transformed node to $P$. Every component terminates and the input parameter is unchanged.
    Thus one program decides the whole family of numerical sections, including the empty word case.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    Each binding and
    projection uses the numerical pairing programs already constructed.
-/
theorem numberWordEntry_computes : NumericalComputes numberWordEntryTerm
    (fun z => Nat.pair z.unpair.1.unpair.1
      ((NatListCode.decode z.unpair.1.unpair.2).getD z.unpair.2 0)) := by
  simpa [numberWordEntryTerm] using ((projection_computes true).comp (projection_computes true)).pair
    (listGet_computes.comp
      (((projection_computes false).comp (projection_computes true)).pair
        (projection_computes false)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To compute the finite word whose entries are $\NatPair{n}{s(k)}$, take
    $z=\NatPair{n}{\LambdaListCode{s}}$ and use the following closed numerical terms:
    $$\begin{aligned}
    F&:=\lambdaab{v}{\LambdaNumericPair\,
     (\LambdaNumericProjection{1}(\LambdaNumericProjection{1}v))\,
     (\LambdaListGet(\LambdaNumericPair\,
       (\LambdaNumericProjection{2}(\LambdaNumericProjection{1}v))\,
       (\LambdaNumericProjection{2}v)))},\\
    W&:=\lambdaab{z}{\LambdaListTabulate{F}\,
     (\LambdaNumericPair\,z\,(\LambdaListLength(\LambdaNumericProjection{2}z)))}.
    \end{aligned}$$
    For the joint tree input $u=\NatPair{n}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$,
    abbreviate $n=\LambdaNumericProjection{1}u$, $a=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}u)$,
    and $b=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}u)$. If $P$ decides the original tree,
    expand these abbreviations in
    $$J:=\lambdaab{o}{\lambdaab{u}{Po(\LambdaNumericPair\,(W(\LambdaNumericPair\,n\,a))\,b)}}.$$
-/
def numberWordTerm : AlphaTerm := numericalCompose (listTabulateTerm numberWordEntryTerm)
  (pairNumerical numericalIdentity
    (numericalCompose listLengthTerm (numericalProjectionTerm false)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    On input $\NatPair{z}{k}$, the term $F$ returns $\NatPair{n}{s(k)}$ for every position in range.
    Finite tabulation runs it at exactly the positions below the length of $s$, so $W$ returns the
    code of the word obtained by pairing $n$ with each entry. The term $J$ retains the second word and
    passes the transformed node to $P$. Every component terminates and the input parameter is unchanged.
    Thus one program decides the whole family of numerical sections, including the empty word case.
-/
theorem numberWord_computes : NumericalComputes numberWordTerm
    (fun z => NatListCode.encode ((NatListCode.decode z.unpair.2).map (Nat.pair z.unpair.1))) := by
  have h := (listTabulate_computes numberWordEntry_computes).comp
    (numericalIdentity_computes.pair (listLength_computes.comp (projection_computes false)))
  have h' : NumericalComputes numberWordTerm (fun z => NatListCode.encode
      ((List.range (NatListCode.decode z.unpair.2).length).map
        (fun k => Nat.pair z.unpair.1 ((NatListCode.decode z.unpair.2).getD k 0)))) := by
    simpa [numberWordTerm] using h
  convert h' using 1
  funext z
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    simp [List.getD_eq_getElem?_getD,show i < (NatListCode.decode z.unpair.2).length from by simpa using hi]

/-- The family index and both node words are ordinary numerical data. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To compute the finite word whose entries are $\NatPair{n}{s(k)}$, take
    $z=\NatPair{n}{\LambdaListCode{s}}$ and use the following closed numerical terms:
    $$\begin{aligned}
    F&:=\lambdaab{v}{\LambdaNumericPair\,
     (\LambdaNumericProjection{1}(\LambdaNumericProjection{1}v))\,
     (\LambdaListGet(\LambdaNumericPair\,
       (\LambdaNumericProjection{2}(\LambdaNumericProjection{1}v))\,
       (\LambdaNumericProjection{2}v)))},\\
    W&:=\lambdaab{z}{\LambdaListTabulate{F}\,
     (\LambdaNumericPair\,z\,(\LambdaListLength(\LambdaNumericProjection{2}z)))}.
    \end{aligned}$$
    For the joint tree input $u=\NatPair{n}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$,
    abbreviate $n=\LambdaNumericProjection{1}u$, $a=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}u)$,
    and $b=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}u)$. If $P$ decides the original tree,
    expand these abbreviations in
    $$J:=\lambdaab{o}{\lambdaab{u}{Po(\LambdaNumericPair\,(W(\LambdaNumericPair\,n\,a))\,b)}}.$$
-/
def numericalSectionInputTerm : AlphaTerm := pairNumerical
  (numericalCompose numberWordTerm
    (pairNumerical (numericalProjectionTerm true)
      (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))))
  (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    On input $\NatPair{z}{k}$, the term $F$ returns $\NatPair{n}{s(k)}$ for every position in range.
    Finite tabulation runs it at exactly the positions below the length of $s$, so $W$ returns the
    code of the word obtained by pairing $n$ with each entry. The term $J$ retains the second word and
    passes the transformed node to $P$. Every component terminates and the input parameter is unchanged.
    Thus one program decides the whole family of numerical sections, including the empty word case.
-/
theorem numericalSectionInput_computes : NumericalComputes numericalSectionInputTerm
    (fun z => Nat.pair
      (NatListCode.encode ((NatListCode.decode z.unpair.2.unpair.1).map (Nat.pair z.unpair.1)))
      z.unpair.2.unpair.2) := by
  simpa [numericalSectionInputTerm] using
    (numberWord_computes.comp ((projection_computes true).pair
      ((projection_computes true).comp (projection_computes false)))).pair
      ((projection_computes false).comp (projection_computes false))

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Choose a tree $T$ presenting $A$. For a finite word $s$, let $s_n$ have entries
    $s_n(k)=\NatPair{n}{s(k)}$. Put
    $$T_n:=\{(s,t):(s_n,t)\in T\}.$$
    Mapping entries preserves length and commutes with truncation, so these are synchronized trees.
    The numerical program in §{sec:lambda-arithmetic-normal-form-programs} computes the code of $s_n$
    jointly from $n$ and the code of $s$. Pairing it with the code of $t$ and running the fixed decider
    for $T$ gives one joint decider for the family. On infinite branches the same identity gives
    $\pi_0([T_n])=A_n$. Apply the uniform countable-union and countable-intersection constructions.
    The joint decider, rather than a separate choice of a decider for each $n$, justifies these applications.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{numerical sections of relative tree projections}{Numerical sections of tree projections}]
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To compute the finite word whose entries are $\NatPair{n}{s(k)}$, take
    $z=\NatPair{n}{\LambdaListCode{s}}$ and use the following closed numerical terms:
    $$\begin{aligned}
    F&:=\lambdaab{v}{\LambdaNumericPair\,
     (\LambdaNumericProjection{1}(\LambdaNumericProjection{1}v))\,
     (\LambdaListGet(\LambdaNumericPair\,
       (\LambdaNumericProjection{2}(\LambdaNumericProjection{1}v))\,
       (\LambdaNumericProjection{2}v)))},\\
    W&:=\lambdaab{z}{\LambdaListTabulate{F}\,
     (\LambdaNumericPair\,z\,(\LambdaListLength(\LambdaNumericProjection{2}z)))}.
    \end{aligned}$$
    For the joint tree input $u=\NatPair{n}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$,
    abbreviate $n=\LambdaNumericProjection{1}u$, $a=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}u)$,
    and $b=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}u)$. If $P$ decides the original tree,
    expand these abbreviations in
    $$J:=\lambdaab{o}{\lambdaab{u}{Po(\LambdaNumericPair\,(W(\LambdaNumericPair\,n\,a))\,b)}}.$$
-/
theorem Projected.numericalSections {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)} (hA : Projected ε A) :
    UniformProjected ε (fun n => {x | bindNumber n x ∈ A}) := by
  obtain ⟨T,rfl⟩ := hA
  let hf := fun n => (numericalConstant_computes n).pair numericalIdentity_computes
  refine ⟨fun n => T.coordinatePreimage (hf n),?_,?_⟩
  · exact T.decidable.precompNumerical
      (g := fun z : ℕ × (List ℕ × List ℕ) => (z.2.1.map (Nat.pair z.1),z.2.2))
      numericalSectionInput_computes (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  · intro n
    change {x : ℕ → ℕ | (fun k => Nat.pair n (x k)) ∈ pairTreeProjection T.tree} = _
    simpa [Function.comp_def,Set.preimage] using
      (pairTreeProjection_coordinatePreimage T (hf n)).symm

theorem UniformProjected.iUnion {ε : ℕ → ℕ} {A : ℕ → Set (ℕ → ℕ)}
    (hA : UniformProjected ε A) : Projected ε (⋃ n, A n) := by
  obtain ⟨T,hT,eT⟩ := hA
  simpa only [eT] using projected_uniform_iUnion T hT

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Choose a tree $T$ presenting $A$. For a finite word $s$, let $s_n$ have entries
    $s_n(k)=\NatPair{n}{s(k)}$. Put
    $$T_n:=\{(s,t):(s_n,t)\in T\}.$$
    Mapping entries preserves length and commutes with truncation, so these are synchronized trees.
    The numerical program in §{sec:lambda-arithmetic-normal-form-programs} computes the code of $s_n$
    jointly from $n$ and the code of $s$. Pairing it with the code of $t$ and running the fixed decider
    for $T$ gives one joint decider for the family. On infinite branches the same identity gives
    $\pi_0([T_n])=A_n$. Apply the uniform countable-union and countable-intersection constructions.
    The joint decider, rather than a separate choice of a decider for each $n$, justifies these applications.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{numerical sections of relative tree projections}{Numerical sections of tree projections}]
-/
theorem Projected.existsNumber {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)} (hA : Projected ε A) :
    Projected ε {x | ∃ n, bindNumber n x ∈ A} := by
  simpa only [Set.iUnion_ofPred] using hA.numericalSections.iUnion

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Choose a tree $T$ presenting $A$. For a finite word $s$, let $s_n$ have entries
    $s_n(k)=\NatPair{n}{s(k)}$. Put
    $$T_n:=\{(s,t):(s_n,t)\in T\}.$$
    Mapping entries preserves length and commutes with truncation, so these are synchronized trees.
    The numerical program in §{sec:lambda-arithmetic-normal-form-programs} computes the code of $s_n$
    jointly from $n$ and the code of $s$. Pairing it with the code of $t$ and running the fixed decider
    for $T$ gives one joint decider for the family. On infinite branches the same identity gives
    $\pi_0([T_n])=A_n$. Apply the uniform countable-union and countable-intersection constructions.
    The joint decider, rather than a separate choice of a decider for each $n$, justifies these applications.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{numerical sections of relative tree projections}{Numerical sections of tree projections}]
-/
theorem Projected.forallNumber {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)} (hA : Projected ε A) :
    Projected ε {x | ∀ n, bindNumber n x ∈ A} := by
  simpa only [Set.iInter_ofPred] using hA.numericalSections.iInter

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Induct on the finite formation of the predicate. For an atomic predicate, repeat its decision bit
    in every output coordinate and use the constant-one inverse-image construction of
    §{sec:edst-baire-quantifiers}. Reversing the decision bit handles its negation.
    Negation exchanges the two presentations. Conjunction uses intersection for the positive side and
    union for the negative side; disjunction follows by De Morgan's identity. For a numerical quantifier,
    apply the preceding lemma to both presentations: existential quantification uses union on the positive
    side and intersection on the negative side, and universal quantification reverses those roles.
    This proves every finite step without changing the parameter or requiring a computable choice of witnesses.
-/
theorem Complemented.existsNumber {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)} (hA : Complemented ε A) :
    Complemented ε {x | ∃ n, bindNumber n x ∈ A} := by
  refine ⟨hA.1.existsNumber,?_⟩
  simpa only [Set.compl_ofPred,not_exists,Set.mem_compl_iff] using hA.2.forallNumber

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    Induct on the finite formation of the predicate. For an atomic predicate, repeat its decision bit
    in every output coordinate and use the constant-one inverse-image construction of
    §{sec:edst-baire-quantifiers}. Reversing the decision bit handles its negation.
    Negation exchanges the two presentations. Conjunction uses intersection for the positive side and
    union for the negative side; disjunction follows by De Morgan's identity. For a numerical quantifier,
    apply the preceding lemma to both presentations: existential quantification uses union on the positive
    side and intersection on the negative side, and universal quantification reverses those roles.
    This proves every finite step without changing the parameter or requiring a computable choice of witnesses.
-/
theorem Complemented.forallNumber {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)} (hA : Complemented ε A) :
    Complemented ε {x | ∀ n, bindNumber n x ∈ A} := by
  classical
  refine ⟨hA.1.forallNumber,?_⟩
  simpa only [Set.compl_ofPred,not_forall,Set.mem_compl_iff] using hA.2.existsNumber

end LambdaTree
end PolishSpaceBook
