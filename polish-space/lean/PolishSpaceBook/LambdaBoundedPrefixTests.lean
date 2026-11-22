module

public import PolishSpaceBook.LambdaTreeMapPrograms

@[expose] public section

/-! # Lambda programs for clauses with finite prefix bounds

At length n, test every row i < n whose prescribed prefix fits. Truncate to
that row's bound before testing; this makes eventual testing exact without
assuming that the original predicate is stable under extension.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance boundedListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance boundedPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

abbrev PrefixPair := List ℕ × List ℕ

def boundedPrefixTest (p : ℕ → PrefixPair → Prop) (b : ℕ → ℕ) (z : PrefixPair) : Prop :=
  ∀ i < z.1.length, b i ≤ z.1.length → p i (z.1.take (b i), z.2.take (b i))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    More generally, let $\LambdaTermName{clausePredicate}$ decide numbered clauses on pairs of words, and let a
    closed numerical term $\LambdaTermName{prefixBound}$
    compute their numerical prefix-bound function $\chi$. For finite words $s,t$, let $w= \NatPair{
    \LambdaListCode{s}}{ \LambdaListCode{t}}$.
    For a trial $i$, put
    $$\begin{aligned}
    \LambdaTermName{trialPair}(v)&:= \LambdaNumericProjection{1}v, \qquad \LambdaTermName{trialIndex}(v):=
    \LambdaNumericProjection{2}v,\\
    \LambdaTermName{pairLength}(w)&:=\LambdaListLength(\LambdaNumericProjection{1}w),\\
    \LambdaTermName{boundedPrefixes}(w,i)&:=\LambdaNumericPair\,
     (\LambdaListTake(\LambdaNumericPair\,(\LambdaNumericProjection{1}w)\,(\LambdaTermName{prefixBound}i)))\\
     &\qquad\qquad (\LambdaListTake(\LambdaNumericPair\,(\LambdaNumericProjection{2}w)\,(\LambdaTermName{prefixBound}i))),\\
    \LambdaTermName{clauseAt}(o,w,i)&:= \LambdaTermName{clausePredicate}o( \LambdaNumericPair\,i\,
    \LambdaTermName{boundedPrefixes}(w,i)),\\
    \LambdaTermName{guardedClause}&:= \lambdaab{o}{ \lambdaab{v}{ \LambdaLeCase{ \LambdaTermName{prefixBound}
    \LambdaTermName{trialIndex}(v)}{ \LambdaTermName{pairLength}( \LambdaTermName{trialPair}(v))}
     {\LambdaTermName{clauseAt}(o,\LambdaTermName{trialPair}(v),\LambdaTermName{trialIndex}(v))}{\ChurchNumeral{1}}}},\\
    \LambdaTermName{boundedClauses}&:=\lambdaab{o}{\lambdaab{w}{\LambdaRelativeProduct{\LambdaTermName{guardedClause}}\,o\,
     (\LambdaNumericPair\,w\,\LambdaTermName{pairLength}(w))}}.
    \end{aligned}$$
    The bounded product checks exactly $i<\Length{s}$, skipping a row when its bound exceeds $\Length{s}$,
    and otherwise
    passing the prefixes of length $\chi(i)$ to $\LambdaTermName{clausePredicate}$. Apply
    §{sec:lambda-kleene-brouwer} to $\LambdaTermName{boundedClauses}$ to obtain
    a downward-closed tree. On an infinite pair, every row is encountered by length
    $\max\{i+1,\chi(i)\}$; truncation at that length supplies precisely the prescribed prefixes. Thus its
    projection is exactly the set of points admitting a witness satisfying all numbered clauses.
    Taking $\LambdaTermName{clausePredicate}= \LambdaTermName{evalRow}_ \zeta$ and $\LambdaTermName{prefixBound}=
    \LambdaTermName{evalBound}$ gives the two
    Borel evaluation trees.
-/
theorem boundedPrefixTest_decidable {ε : ℕ → ℕ} {p : ℕ → PrefixPair → Prop}
    {B : AlphaTerm} {b : ℕ → ℕ}
    (hp : LambdaRelative.DecidablePredicate ε (fun z : ℕ × PrefixPair => p z.1 z.2))
    (hb : NumericalComputes B b) : LambdaRelative.DecidablePredicate ε (boundedPrefixTest p b) := by
  have hi := projection_computes false
  have hword := projection_computes true
  have hbound := hb.comp hi
  have hlen := listLength_computes.comp ((projection_computes true).comp hword)
  have harg := hi.pair (takePair_computes.comp (hword.pair hbound))
  have ht := hp.precompNumerical (g := fun z : ℕ =>
    (z.unpair.2, ((NatListCode.decode z.unpair.1.unpair.1).take (b z.unpair.2),
      (NatListCode.decode z.unpair.1.unpair.2).take (b z.unpair.2)))) harg
    (fun z => by simp [takePairCode,Encodable.encode,Encodable.encodeSigma])
  have htest := (numerical_le_decidable hbound hlen ε).imp ht
  have hall := htest.boundedAll (listLength_computes.comp (projection_computes true))
  have h := hall.precompNumerical (g := fun z : PrefixPair =>
    Nat.pair (NatListCode.encode z.1) (NatListCode.encode z.2)) numericalIdentity_computes
    (fun z => rfl)
  change LambdaRelative.DecidablePredicate ε (fun z : PrefixPair =>
    ∀ i < z.1.length, b i ≤ z.1.length → p i (z.1.take (b i),z.2.take (b i)))
  simpa using h

/-- Keep the family index in every bounded row query. -/
theorem boundedPrefixTest_family_decidable {ε : ℕ → ℕ} {p : ℕ → ℕ → PrefixPair → Prop}
    {B : AlphaTerm} {b : ℕ → ℕ}
    (hp : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (ℕ × PrefixPair) => p z.1 z.2.1 z.2.2))
    (hb : NumericalComputes B b) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × PrefixPair => boundedPrefixTest (p z.1) b z.2) := by
  have hi := projection_computes false
  have hfam := (projection_computes true).comp (projection_computes true)
  have hword := (projection_computes false).comp (projection_computes true)
  have hbound := hb.comp hi
  have hlen := listLength_computes.comp ((projection_computes true).comp hword)
  have harg := hfam.pair (hi.pair (takePair_computes.comp (hword.pair hbound)))
  have ht := hp.precompNumerical (g := fun z : ℕ =>
    (z.unpair.1.unpair.1,(z.unpair.2,
      ((NatListCode.decode z.unpair.1.unpair.2.unpair.1).take (b z.unpair.2),
       (NatListCode.decode z.unpair.1.unpair.2.unpair.2).take (b z.unpair.2))))) harg
    (fun z => by simp [takePairCode,Encodable.encode,Encodable.encodeSigma])
  have htest := (numerical_le_decidable hbound hlen ε).imp ht
  have hall := htest.boundedAll (listLength_computes.comp
    ((projection_computes true).comp (projection_computes false)))
  have h := hall.precompNumerical (g := fun z : ℕ × PrefixPair => Encodable.encode z)
    numericalIdentity_computes (fun _ => rfl)
  simpa [boundedPrefixTest,Encodable.encode,Encodable.encodeSigma] using h

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    More generally, let $\LambdaTermName{clausePredicate}$ decide numbered clauses on pairs of words, and let a
    closed numerical term $\LambdaTermName{prefixBound}$
    compute their numerical prefix-bound function $\chi$. For finite words $s,t$, let $w= \NatPair{
    \LambdaListCode{s}}{ \LambdaListCode{t}}$.
    For a trial $i$, put
    $$\begin{aligned}
    \LambdaTermName{trialPair}(v)&:= \LambdaNumericProjection{1}v, \qquad \LambdaTermName{trialIndex}(v):=
    \LambdaNumericProjection{2}v,\\
    \LambdaTermName{pairLength}(w)&:=\LambdaListLength(\LambdaNumericProjection{1}w),\\
    \LambdaTermName{boundedPrefixes}(w,i)&:=\LambdaNumericPair\,
     (\LambdaListTake(\LambdaNumericPair\,(\LambdaNumericProjection{1}w)\,(\LambdaTermName{prefixBound}i)))\\
     &\qquad\qquad (\LambdaListTake(\LambdaNumericPair\,(\LambdaNumericProjection{2}w)\,(\LambdaTermName{prefixBound}i))),\\
    \LambdaTermName{clauseAt}(o,w,i)&:= \LambdaTermName{clausePredicate}o( \LambdaNumericPair\,i\,
    \LambdaTermName{boundedPrefixes}(w,i)),\\
    \LambdaTermName{guardedClause}&:= \lambdaab{o}{ \lambdaab{v}{ \LambdaLeCase{ \LambdaTermName{prefixBound}
    \LambdaTermName{trialIndex}(v)}{ \LambdaTermName{pairLength}( \LambdaTermName{trialPair}(v))}
     {\LambdaTermName{clauseAt}(o,\LambdaTermName{trialPair}(v),\LambdaTermName{trialIndex}(v))}{\ChurchNumeral{1}}}},\\
    \LambdaTermName{boundedClauses}&:=\lambdaab{o}{\lambdaab{w}{\LambdaRelativeProduct{\LambdaTermName{guardedClause}}\,o\,
     (\LambdaNumericPair\,w\,\LambdaTermName{pairLength}(w))}}.
    \end{aligned}$$
    The bounded product checks exactly $i<\Length{s}$, skipping a row when its bound exceeds $\Length{s}$,
    and otherwise
    passing the prefixes of length $\chi(i)$ to $\LambdaTermName{clausePredicate}$. Apply
    §{sec:lambda-kleene-brouwer} to $\LambdaTermName{boundedClauses}$ to obtain
    a downward-closed tree. On an infinite pair, every row is encountered by length
    $\max\{i+1,\chi(i)\}$; truncation at that length supplies precisely the prescribed prefixes. Thus its
    projection is exactly the set of points admitting a witness satisfying all numbered clauses.
    Taking $\LambdaTermName{clausePredicate}= \LambdaTermName{evalRow}_ \zeta$ and $\LambdaTermName{prefixBound}=
    \LambdaTermName{evalBound}$ gives the two
    Borel evaluation trees.
-/
theorem boundedPrefixTest_iff (p : ℕ → PrefixPair → Prop) (b : ℕ → ℕ) (x y : ℕ → ℕ) :
    (∀ n, boundedPrefixTest p b (seqPrefix x n, seqPrefix y n)) ↔
      ∀ i, p i (seqPrefix x (b i), seqPrefix y (b i)) := by
  constructor
  · intro h i
    let n := max (i+1) (b i)
    have hi : i < n := lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left _ _)
    have hb : b i ≤ n := le_max_right _ _
    have ht := h n i (by simpa [seqPrefix_length] using hi) (by simpa [seqPrefix_length] using hb)
    simpa only [seqPrefix_take_of_le _ hb] using ht
  · intro h n i _ hb
    have hb' : b i ≤ n := by simpa [seqPrefix_length] using hb
    simpa only [seqPrefix_take_of_le _ hb'] using h i

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    More generally, let $\LambdaTermName{clausePredicate}$ decide numbered clauses on pairs of words, and let a
    closed numerical term $\LambdaTermName{prefixBound}$
    compute their numerical prefix-bound function $\chi$. For finite words $s,t$, let $w= \NatPair{
    \LambdaListCode{s}}{ \LambdaListCode{t}}$.
    For a trial $i$, put
    $$\begin{aligned}
    \LambdaTermName{trialPair}(v)&:= \LambdaNumericProjection{1}v, \qquad \LambdaTermName{trialIndex}(v):=
    \LambdaNumericProjection{2}v,\\
    \LambdaTermName{pairLength}(w)&:=\LambdaListLength(\LambdaNumericProjection{1}w),\\
    \LambdaTermName{boundedPrefixes}(w,i)&:=\LambdaNumericPair\,
     (\LambdaListTake(\LambdaNumericPair\,(\LambdaNumericProjection{1}w)\,(\LambdaTermName{prefixBound}i)))\\
     &\qquad\qquad (\LambdaListTake(\LambdaNumericPair\,(\LambdaNumericProjection{2}w)\,(\LambdaTermName{prefixBound}i))),\\
    \LambdaTermName{clauseAt}(o,w,i)&:= \LambdaTermName{clausePredicate}o( \LambdaNumericPair\,i\,
    \LambdaTermName{boundedPrefixes}(w,i)),\\
    \LambdaTermName{guardedClause}&:= \lambdaab{o}{ \lambdaab{v}{ \LambdaLeCase{ \LambdaTermName{prefixBound}
    \LambdaTermName{trialIndex}(v)}{ \LambdaTermName{pairLength}( \LambdaTermName{trialPair}(v))}
     {\LambdaTermName{clauseAt}(o,\LambdaTermName{trialPair}(v),\LambdaTermName{trialIndex}(v))}{\ChurchNumeral{1}}}},\\
    \LambdaTermName{boundedClauses}&:=\lambdaab{o}{\lambdaab{w}{\LambdaRelativeProduct{\LambdaTermName{guardedClause}}\,o\,
     (\LambdaNumericPair\,w\,\LambdaTermName{pairLength}(w))}}.
    \end{aligned}$$
    The bounded product checks exactly $i<\Length{s}$, skipping a row when its bound exceeds $\Length{s}$,
    and otherwise
    passing the prefixes of length $\chi(i)$ to $\LambdaTermName{clausePredicate}$. Apply
    §{sec:lambda-kleene-brouwer} to $\LambdaTermName{boundedClauses}$ to obtain
    a downward-closed tree. On an infinite pair, every row is encountered by length
    $\max\{i+1,\chi(i)\}$; truncation at that length supplies precisely the prescribed prefixes. Thus its
    projection is exactly the set of points admitting a witness satisfying all numbered clauses.
    Taking $\LambdaTermName{clausePredicate}= \LambdaTermName{evalRow}_ \zeta$ and $\LambdaTermName{prefixBound}=
    \LambdaTermName{evalBound}$ gives the two
    Borel evaluation trees.
-/
theorem projected_forall_finitePrefixTests {ε : ℕ → ℕ} {p : ℕ → PrefixPair → Prop}
    {B : AlphaTerm} {b : ℕ → ℕ}
    (hp : LambdaRelative.DecidablePredicate ε (fun z : ℕ × PrefixPair => p z.1 z.2))
    (hb : NumericalComputes B b) :
    Projected ε {x | ∃ y, ∀ i, p i (seqPrefix x (b i),seqPrefix y (b i))} := by
  simpa only [boundedPrefixTest_iff] using projected_finiteChecks (boundedPrefixTest_decidable hp hb)
end LambdaTree
end PolishSpaceBook
