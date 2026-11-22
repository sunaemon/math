module

public import PolishSpaceBook.LambdaIndexedTrees

@[expose] public section

/-! # Finite tests and coordinatewise inverse images with lambda programs

Every trial uses the same fixed parameter. Prefix tests include length zero.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaRelative
/-- Bounded universal quantification by a relative product of decision bits. -/
theorem DecidablePredicate.boundedAll {ε : ℕ → ℕ} {R : ℕ → Prop}
    (hR : DecidablePredicate ε R) {N : AlphaTerm} {n : ℕ → ℕ}
    (hN : NumericalComputes N n) :
    DecidablePredicate ε (fun z : ℕ => ∀ i < n z, R (Nat.pair z i)) := by
  classical
  obtain ⟨P,hP⟩ := hR
  let t : ℕ → ℕ := fun z => if R z then 1 else 0
  have ht : Computes ε P t := ⟨hP.1,fun z => hP.runs z⟩
  have hc := ht.boundedProduct.reindex (numericalIdentity_computes.pair hN)
  refine ⟨_,hc.1,fun z => ?_⟩
  have hr := hc.2 z
  simp only [Nat.unpair_pair,id_eq] at hr
  change OracleRuns ε _ z (boundedProduct t z (n z)) at hr
  have hb := boundedProduct_zero_or_one t z (n z) (fun i => by dsimp [t]; split_ifs <;> simp)
  have he : boundedProduct t z (n z) ≠ 0 ↔ ∀ i < n z, R (Nat.pair z i) := by
    rw [boundedProduct_ne_zero]
    simp [t]
  constructor
  · intro h
    simpa only [Encodable.encode_nat,hb.resolve_left (he.mpr h)] using hr
  · intro h
    have hz : boundedProduct t z (n z) = 0 := not_not.mp (fun hn => h (he.mp hn))
    simpa only [Encodable.encode_nat,hz] using hr
end LambdaRelative
namespace LambdaTree
local instance finiteCheckListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance finiteCheckPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

/-- Require all prefix tests, including the empty prefix. -/
def finiteCheckNodes (test : List ℕ × List ℕ → Prop) : Set (List ℕ × List ℕ) :=
  {z | z.1.length = z.2.length ∧ ∀ n ≤ z.1.length, test (z.1.take n,z.2.take n)}

theorem finiteCheckNodes_downward (test : List ℕ × List ℕ → Prop)
    {z : List ℕ × List ℕ} (hz : z ∈ finiteCheckNodes test) (n : ℕ) :
    (z.1.take n,z.2.take n) ∈ finiteCheckNodes test := by
  refine ⟨by simp [hz.1],fun i hi => ?_⟩
  simp only [List.length_take] at hi
  simpa only [List.take_take] using hz.2 (min i n) (by omega)

/-- Input ((index,node),stage) retains the index and truncates both words. -/
def finiteCheckInputTerm : AlphaTerm :=
  pairNumerical (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true))
    (numericalCompose takePairTerm
      (pairNumerical (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm true))
        (numericalProjectionTerm false)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Fix a parameter $\varepsilon$. Suppose $P$ decides $\mathcal R_i(s,t)$ on the numerical input
    $\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$.
    Define $S_i$ to consist of the equal-length pairs $\Pair{s}{t}$ for which
    $\mathcal R_i(\restrict{s}{j},\restrict{t}{j})$ holds for every $j\le\Length{s}$.
    Use the truncation body $\LambdaTermName{truncatePair}$, length terms $\LambdaTermName{firstLength},
    \LambdaTermName{secondLength}$, and equality bit $\LambdaTermName{sameLength}$ of
    §{sec:lambda-pair-tree-programs}, now with $z=\NatPair{i}{w}$ as the family input. For a trial input $v$,
    expand the abbreviations
    $$\begin{aligned}
    \LambdaTermName{trialData}(v)&:= \LambdaNumericProjection{1}v, \qquad \LambdaTermName{trialLength}(v):=
    \LambdaNumericProjection{2}v,\\
    \LambdaTermName{familyIndex}(v)&:= \LambdaNumericProjection{1} \LambdaTermName{trialData}(v), \qquad
    \LambdaTermName{nodeCode}(v):= \LambdaNumericProjection{2} \LambdaTermName{trialData}(v),\\
    \LambdaTermName{prefixTest}_P&:= \lambdaab{o}{ \lambdaab{v}{Po( \LambdaNumericPair\,
    \LambdaTermName{familyIndex}(v)\, \LambdaTermName{truncatePair}( \LambdaTermName{nodeCode}(v),
    \LambdaTermName{trialLength}(v)))}},\\
    \LambdaTermName{finiteTree}_P&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,\LambdaTermName{sameLength}(z)\,
     \bigl( \LambdaRelativeProduct{ \LambdaTermName{prefixTest}_P}\,o\,( \LambdaNumericPair\,z\,( \LambdaSucc\,
    \LambdaTermName{firstLength}(z))) \bigr)}}.
    \end{aligned}$$
    Choose distinct fresh binders and expand all abbreviations before abstraction.
-/
theorem finiteCheckInput_computes : NumericalComputes finiteCheckInputTerm
    (fun z => Nat.pair z.unpair.1.unpair.1
      (takePairCode z.unpair.1.unpair.2 z.unpair.2)) := by
  simpa only [finiteCheckInputTerm,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using
    ((projection_computes true).comp (projection_computes true)).pair
      (takePair_computes.comp
        (((projection_computes false).comp (projection_computes true)).pair (projection_computes false)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Decision programs for finite-test trees
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Numerical projections and $\LambdaTermName{truncatePair}$ turn the trial input into exactly the code expected by
    $P$ for the two
    length-$j$ prefixes. Every call terminates and returns a decision bit. The bounded-product theorem multiplies
    these bits for $j<\Length{s}+1$, retaining the same parameter at every stage. Its result is one exactly when all
    prefix tests pass. Multiplication by $\LambdaTermName{sameLength}(z)$ also requires equal lengths. On empty
    words there is one trial,
    so its failure rejects the empty node. Treating the index as ordinary input data proves uniformity; fixing
    that input gives the single-predicate construction.
    \end{proof}
-/
theorem finiteCheck_family_decidable {ε : ℕ → ℕ} {test : ℕ → List ℕ × List ℕ → Prop}
    (ht : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => test z.1 z.2)) :
    LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ finiteCheckNodes (test z.1)) := by
  have htrial := ht.precompNumerical (g := fun z : ℕ =>
    (z.unpair.1.unpair.1,((NatListCode.decode z.unpair.1.unpair.2.unpair.1).take z.unpair.2,
      (NatListCode.decode z.unpair.1.unpair.2.unpair.2).take z.unpair.2)))
    finiteCheckInput_computes (fun z => by simp [takePairCode,Encodable.encode,Encodable.encodeSigma])
  have hall := htrial.boundedAll (successor_computes.comp familyLength_computes)
  have hall' := hall.precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) =>
      Nat.pair z.1 (Nat.pair (NatListCode.encode z.2.1) (NatListCode.encode z.2.2)))
    numericalIdentity_computes (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have hlen : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2.1.length = z.2.2.length) := by
    apply numericalDecision familyLengthEquality_computes ε
    · intro z hz; simp [Encodable.encode,Encodable.encodeSigma,hz]
    · intro z hz; simp [Encodable.encode,Encodable.encodeSigma,hz]
  simpa only [Nat.unpair_pair,NatListCode.decode_encode,Nat.succ_eq_add_one,Nat.lt_add_one_iff,
    finiteCheckNodes,Set.mem_ofPred_eq] using hlen.and hall'

theorem finiteCheck_decidable {ε : ℕ → ℕ} {test : List ℕ × List ℕ → Prop}
    (ht : LambdaRelative.DecidablePredicate ε test) :
    LambdaRelative.DecidablePredicate ε (· ∈ finiteCheckNodes test) := by
  have hf := finiteCheck_family_decidable (test := fun _ => test)
    (ht.precompNumerical (g := fun z : ℕ × (List ℕ × List ℕ) => z.2)
      (projection_computes false) (fun z => by simp [Encodable.encode,Encodable.encodeSigma]))
  exact hf.precompNumerical (g := fun z => (0,z))
    ((numericalConstant_computes 0).pair numericalIdentity_computes)
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Trees defined by finite tests
-/
def finiteCheckTree {ε : ℕ → ℕ} (test : List ℕ × List ℕ → Prop)
    (ht : LambdaRelative.DecidablePredicate ε test) : PairTree ε where
  tree := finiteCheckNodes test
  synchronized := fun _ h => h.1
  downward := fun _ h n => finiteCheckNodes_downward test h n
  decidable := finiteCheck_decidable ht

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Compute the two lengths and, for each $j\le|s|$, extract the two prefixes and apply the supplied decider
    with the same index and parameter. Multiply these decision bits and the length-equality bit. List truncation
    and the relative bounded-product term make this one terminating program, as detailed in
    §{sec:lambda-kleene-brouwer}. If a node is truncated to length $m$, each subsequent prefix test is a
    test at length $\min(j,m)$ already required at the original node. Thus the accepted nodes form a tree.
    A branch satisfies the test at length $j$ by applying the node condition to its length-$j$ prefix.
    Conversely, if all branch tests hold, every test on every prefix holds. This proves the body identity;
    existentially quantifying the second coordinate gives the projection identity.
    \end{proof}
-/
theorem pairTreeBody_finiteCheckNodes (test : List ℕ × List ℕ → Prop) :
    pairTreeBody (finiteCheckNodes test) =
      {p | ∀ n, test (seqPrefix p.1 n,seqPrefix p.2 n)} := by
  ext p
  constructor
  · intro hp n
    have h := (hp n).2 n (by simp [seqPrefix_length])
    simpa only [seqPrefix_take_of_le _ (le_refl n)] using h
  · intro hp n
    refine ⟨by simp [seqPrefix_length],fun i hi => ?_⟩
    simp only [seqPrefix_length] at hi
    simpa only [seqPrefix_take_of_le _ hi] using hp i

theorem projected_finiteChecks {ε : ℕ → ℕ} {test : List ℕ × List ℕ → Prop}
    (ht : LambdaRelative.DecidablePredicate ε test) :
    Projected ε {p | ∃ q, ∀ n, test (seqPrefix p n,seqPrefix q n)} := by
  refine ⟨finiteCheckTree test ht,?_⟩
  ext p
  change (∃ q, ∀ n, test (seqPrefix p n,seqPrefix q n)) ↔
    ∃ q, (p,q) ∈ pairTreeBody (finiteCheckNodes test)
  rw [pairTreeBody_finiteCheckNodes]
  rfl

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    The test at length zero is included: if $R_i(\varnothing,\varnothing)$ fails, $S_i$ is empty.
    If $R_i$ is already membership in a synchronized downward-closed tree, the construction preserves every node.
    These facts distinguish this construction from the delayed-rejection trees of §{sec:edst-pair-tree-indices},
    which always contain the empty node and need preserve only bodies and projections.
-/
theorem finiteCheckNodes_empty {test : List ℕ × List ℕ → Prop} (h : ¬ test ([],[])) :
    finiteCheckNodes test = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact h (by simpa using hz.2 0 (Nat.zero_le _))

theorem finiteCheckNodes_of_tree {ε : ℕ → ℕ} (T : PairTree ε) :
    finiteCheckNodes (· ∈ T.tree) = T.tree := by
  ext z
  constructor
  · intro h
    have hs := h.2 z.1.length (le_refl _)
    rw [List.take_length, h.1, List.take_length] at hs
    exact hs
  · intro h
    exact ⟨T.synchronized z h,fun n _ => T.downward z h n⟩

/-- Apply an actual numerical program to every entry of a word. -/
theorem mapWord_computes {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) :
    NumericalComputes (app listMapTerm F)
      (fun e => NatListCode.encode ((NatListCode.decode e).map f)) :=
  ⟨closed_app listMapTerm_closed hF.1,listMapTerm_apply hF.1 f hF.2⟩

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For the coordinatewise inverse image, let $F$ compute the total numerical function $f$ and let $Q$ decide
    membership in $V$. Define
    $$\begin{aligned}
    \LambdaTermName{mapWord}_F&:=\LambdaListMap\,F,\\
    \LambdaTermName{mapNode}_F&:=\lambdaab{w}{\LambdaNumericPair\,
     \bigl(\LambdaTermName{mapWord}_F(\LambdaNumericProjection{1}w)\bigr)\,(\LambdaNumericProjection{2}w)},\\
    \LambdaTermName{preimage}_{Q,F}&:=\lambdaab{o}{\lambdaab{w}{Qo(\LambdaTermName{mapNode}_Fw)}}.
    \end{aligned}$$
    The list-map theorem gives exactly the code of the entrywise image of the first word. Pairing leaves the
    second word unchanged, and two beta contractions feed this code to $Q$ at the original parameter. Thus
    $\LambdaTermName{preimage}_{Q,F}$ decides the tree used in §{sec:edst-finite-check-trees}.
-/
def PairTree.coordinatePreimage {ε : ℕ → ℕ} (T : PairTree ε)
    {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) : PairTree ε where
  tree := {z | (z.1.map f,z.2) ∈ T.tree}
  synchronized := by
    intro z hz
    simpa using T.synchronized _ hz
  downward := by
    intro z hz n
    change ((z.1.take n).map f,z.2.take n) ∈ T.tree
    simpa only [List.map_take] using T.downward _ hz n
  decidable := T.decidable.precompNumerical (g := fun z : List ℕ × List ℕ => (z.1.map f,z.2))
    (((mapWord_computes hF).comp (projection_computes true)).pair (projection_computes false))
    (fun z => by simp [Encodable.encode])

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Coordinatewise inverse images of tree projections
-/
theorem pairTreeBody_coordinatePreimage {ε : ℕ → ℕ} (T : PairTree ε)
    {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) :
    pairTreeBody (T.coordinatePreimage hF).tree =
      (fun p : (ℕ → ℕ) × (ℕ → ℕ) => (f ∘ p.1,p.2)) ⁻¹' pairTreeBody T.tree := by
  ext p
  simp only [pairTreeBody,PairTree.coordinatePreimage,Set.mem_ofPred_eq,Set.mem_preimage,
    seqPrefix,List.map_ofFn,Function.comp_def]

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Apply the list-map term to the code of $s$, retain the code of $t$, pair the results, and run the decider for
    $T$. Totality of $f$ gives termination on every finite word. Mapping preserves length and commutes with
    truncation, so synchronization and downward closure follow from those of $T$. For every infinite sequence,
    mapping its length-$n$ prefix gives the length-$n$ prefix of its image. Applying this identity at every
    length proves the body equality. The witness $q$ is unchanged in both directions, giving the projection
    equality. This proves closure for coordinatewise maps. The construction in §{sec:edst-computable-preimages}
    extends it to arbitrary total computable maps between Baire spaces.
    \end{proof}
-/
theorem pairTreeProjection_coordinatePreimage {ε : ℕ → ℕ} (T : PairTree ε)
    {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) :
    pairTreeProjection (T.coordinatePreimage hF).tree =
      (fun p : ℕ → ℕ => f ∘ p) ⁻¹' pairTreeProjection T.tree := by
  ext p
  change (∃ q, (p,q) ∈ pairTreeBody (T.coordinatePreimage hF).tree) ↔ _
  rw [pairTreeBody_coordinatePreimage]
  rfl

theorem Projected.coordinatePreimage {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)}
    (hA : Projected ε A) {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) :
    Projected ε ((fun p : ℕ → ℕ => f ∘ p) ⁻¹' A) := by
  obtain ⟨T,rfl⟩ := hA
  exact ⟨T.coordinatePreimage hF,(pairTreeProjection_coordinatePreimage T hF).symm⟩
end LambdaTree
end PolishSpaceBook
