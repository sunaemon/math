module

public import PolishSpaceBook.LambdaRecursiveTrees
public import PolishSpaceBook.PairTreeGeometry
public import PolishSpaceBook.LambdaRelativeComposition
public import PolishSpaceBook.LambdaInputPrefixes

@[expose] public section

/-! # Pair trees with lambda decision programs

Finite word pairs use the book's list code and numerical pairing. Each
operation retains one fixed parameter; the topological proofs are shared
with the geometric tree constructions.
-/
namespace PolishSpaceBook
open Set MeasureTheory NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance pairTreeListEncoding : Encodable (List ℕ) := NatListCode.encodable

/-- Explicit pair coding, with no ambient list-encoding convention. -/
@[reducible] def wordPairEncodable : Encodable (List ℕ × List ℕ) where
  encode z := Nat.pair (NatListCode.encode z.1) (NatListCode.encode z.2)
  decode e := some (NatListCode.decode e.unpair.1, NatListCode.decode e.unpair.2)
  encodek z := by simp
local instance pairTreeWordPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    For analytic sets one uses trees on pairs of finite sequences. A tree on pairs is a set
    $T\IncludedIn\finseq{\omega}\times\finseq{\omega}$ such that $(s,t)\in T$ implies $|s|=|t|$ and
    $(\restrict{s}{n},\restrict{t}{n})\in T$ for every $n$. It is recursive relative to a fixed parameter
    $\varepsilon$ if a closed lambda program decides membership on the code
    $\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}$. Its body and projection are
    $$\begin{aligned}
    [T]&=\{(p,q):(\restrict{p}{n},\restrict{q}{n})\in T\text{ for all }n\},\\
    \pi_0([T])&=\{p:\exists q\ (p,q)\in[T]\}.
    \end{aligned}$$
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Here we give the programs used for effective separation. A pair tree is a downward-closed set of equal-length
    pairs of finite words. Its section at $x$ consists of the words $u$ with $(\restrict{x}{|u|},u)$ in the tree,
    with the empty word added. Suppose closed programs $P_T,P_S$ decide two families of pair trees at the same
    parameter, on input $\NatPair{i}{\NatPair{a}{b}}$, where $a,b$ are word codes. In this subsection,
    expand all abbreviations before abstraction and choose fresh binders. The symbol $Z$ denotes the numerical
    zero test returning one on zero and zero otherwise.
-/
structure PairTree (ε : ℕ → ℕ) where
  tree : Set (List ℕ × List ℕ)
  synchronized : ∀ z ∈ tree, z.1.length = z.2.length
  downward : ∀ z ∈ tree, ∀ n, (z.1.take n,z.2.take n) ∈ tree
  decidable : LambdaRelative.DecidablePredicate ε (· ∈ tree)

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Operations on relative pair trees
-/
instance countablePairTree (ε : ℕ → ℕ) : Countable (PairTree ε) := by
  let := LambdaRelative.countable_decidablePredicates (List ℕ × List ℕ) ε
  apply Function.Injective.countable
    (f := fun T : PairTree ε =>
      (⟨(· ∈ T.tree),T.decidable⟩ :
        {R : List ℕ × List ℕ → Prop // LambdaRelative.DecidablePredicate ε R}))
  intro ⟨T,hs,hd,hc⟩ ⟨S,hs',hd',hc'⟩ h
  have heq : T = S := congrArg Subtype.val h
  cases heq
  rfl

/-- Project every entry of the combined witness. -/
def witnessProjectionTerm (first : Bool) : AlphaTerm :=
  app listMapTerm (numericalProjectionTerm first)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Use $i=1,2$ for the two numerical projections. On a list code, the closed term
    $\LambdaTermName{wordProjection}_i:= \LambdaListMap\, \LambdaNumericProjection{i}$ computes the code of the list
    obtained by projecting each
    entry. To keep the first word and project the witness word, use
    $$\LambdaTermName{nodeProjection}_i:=\lambdaab{z}{\LambdaNumericPair\,(\LambdaNumericProjection{1}z)
    \bigl(\LambdaTermName{wordProjection}_i(\LambdaNumericProjection{2}z)\bigr)}.$$
    For relative membership deciders $P,Q$, the intersection decider is
    $$\lambdaab{o}{ \lambdaab{z}{ \LambdaMul\, \bigl(Po( \LambdaTermName{nodeProjection}_1z) \bigr)\, \bigl(Qo(
    \LambdaTermName{nodeProjection}_2z) \bigr)}}.$$
    All abbreviations are expanded before abstraction. The bound variables are distinct and fresh for the component
    terms, which are closed.
-/
theorem witnessProjection_computes (first : Bool) :
    NumericalComputes (witnessProjectionTerm first)
      (fun e => NatListCode.encode ((NatListCode.decode e).map
        (fun k => if first then k.unpair.1 else k.unpair.2))) :=
  ⟨closed_app listMapTerm_closed (projection_computes first).1,
    listMapTerm_apply (projection_computes first).1 _ (projection_computes first).2⟩

def witnessReindexTerm (first : Bool) : AlphaTerm :=
  pairNumerical (numericalProjectionTerm true)
    (numericalCompose (witnessProjectionTerm first) (numericalProjectionTerm false))

theorem witnessReindex_computes (first : Bool) :
    NumericalComputes (witnessReindexTerm first)
      (fun e => Nat.pair e.unpair.1 (NatListCode.encode
        ((NatListCode.decode e.unpair.2).map
          (fun k => if first then k.unpair.1 else k.unpair.2)))) := by
  exact (projection_computes true).pair
    ((witnessProjection_computes first).comp (projection_computes false))

/-- Intersection uses independent witnesses, coded together entry by entry. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Pair-tree decision programs
-/
def PairTree.intersection {ε : ℕ → ℕ} (T S : PairTree ε) : PairTree ε where
  tree := {z | (z.1,leftWitness z.2) ∈ T.tree ∧ (z.1,rightWitness z.2) ∈ S.tree}
  synchronized := by
    intro z hz
    simpa [leftWitness] using T.synchronized _ hz.1
  downward := by
    intro z hz n
    constructor
    · simpa [leftWitness,List.map_take] using T.downward _ hz.1 n
    · simpa [rightWitness,List.map_take] using S.downward _ hz.2 n
  decidable :=
    (T.decidable.precompNumerical (g := fun z : List ℕ × List ℕ => (z.1,leftWitness z.2))
      (witnessReindex_computes true) (fun z => by
        simp [Encodable.encode,leftWitness])).and
    (S.decidable.precompNumerical (g := fun z : List ℕ × List ℕ => (z.1,rightWitness z.2))
      (witnessReindex_computes false) (fun z => by
        simp [Encodable.encode,rightWitness]))

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    A membership decider determines its tree uniquely, so countability follows from the countability of relative
    predicates. For each length, the allowed prefix pairs give a clopen condition on the two infinite sequences.
    Intersecting these conditions gives the closed body; its continuous projection is analytic. For two trees $T,S$,
    write $u_1,u_2$ for the words obtained by applying the two numerical projections to every entry of $u$, and put
    $$R=\{(s,u):(s,u_1)\in T\text{ and }(s,u_2)\in S\}.$$
    The list-map and numerical-pairing terms compute the two membership inputs, and multiplication combines the two
    zero/one answers. Word projection commutes with truncation, so this is a synchronized downward-closed tree.
    A branch through $R$ gives two witnesses. Conversely, witnesses $q,r$ for the same point are combined into the
    sequence $\Sequence{\NatPair{q(n)}{r(n)}}{n\in\omega}$. Hence $\pi_0([R])=\pi_0([T])\cap\pi_0([S])$.
    The full tree consists of all pairs of equal length; equality of the computed lengths decides membership.
    Its projection is the whole space, which also handles the empty intersection.
-/
theorem pairTreeProjection_intersection {ε : ℕ → ℕ} (T S : PairTree ε) :
    pairTreeProjection (T.intersection S).tree =
      pairTreeProjection T.tree ∩ pairTreeProjection S.tree := by
  ext p
  constructor
  · rintro ⟨q,hq⟩
    constructor
    · refine ⟨fun n => (q n).unpair.1,fun n => ?_⟩
      simpa [leftWitness,seqPrefix,List.map_ofFn,Function.comp_def] using (hq n).1
    · refine ⟨fun n => (q n).unpair.2,fun n => ?_⟩
      simpa [rightWitness,seqPrefix,List.map_ofFn,Function.comp_def] using (hq n).2
  · rintro ⟨⟨q,hq⟩,⟨r,hr⟩⟩
    refine ⟨fun n => Nat.pair (q n) (r n),fun n => ?_⟩
    constructor
    · simpa [leftWitness,seqPrefix,List.map_ofFn,Function.comp_def] using hq n
    · simpa [rightWitness,seqPrefix,List.map_ofFn,Function.comp_def] using hr n

/-- Relative tree projections, without a formula normal-form claim. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The first lightface classes can be described in terms of effective tests on names. For an effectively open set,
    membership is witnessed by a cylinder already seen in an enumeration. For an effectively closed set, nonmembership is
    witnessed by a forbidden finite prefix. For an effectively analytic set, membership is witnessed by an infinite sequence
    whose finite approximations pass all recursive tests. In this last case, the witness need not be finite or computable.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Effective analytic sets are projections of recursive trees. More explicitly, $A \IncludedIn \BaireSpace$ is
    $\lSigma^1_1$
    iff there is a recursive tree $T \IncludedIn \finseq{\omega} \times \finseq{\omega}$ such that
    $$p \in A \quad\Longleftrightarrow\quad \exists q \in \BaireSpace\; \forall n\; (\restrict{p}{n},\;\restrict{q}{n}) \in
    T.$$
    The real $q$ is the witness. This is the effective analogue of the classical fact that analytic sets are projections of
    closed subsets of a product Polish space.
-/
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
def Projected (ε : ℕ → ℕ) (A : Set (ℕ → ℕ)) : Prop :=
  ∃ T : PairTree ε, A = pairTreeProjection T.tree

theorem Projected.analyticSet {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)}
    (hA : Projected ε A) : AnalyticSet A := by
  obtain ⟨T,rfl⟩ := hA
  exact analyticSet_pairTreeProjection T.tree

theorem Projected.inter {ε : ℕ → ℕ} {A B : Set (ℕ → ℕ)}
    (hA : Projected ε A) (hB : Projected ε B) : Projected ε (A ∩ B) := by
  obtain ⟨T,rfl⟩ := hA
  obtain ⟨S,rfl⟩ := hB
  exact ⟨T.intersection S,(pairTreeProjection_intersection T S).symm⟩

theorem countable_projected (ε : ℕ → ℕ) : {A | Projected ε A}.Countable := by
  have heq : {A | Projected ε A} =
      Set.range (fun T : PairTree ε => pairTreeProjection T.tree) := by
    ext A
    simp [Projected,eq_comm]
  rw [heq]
  exact Set.countable_range _

/-- An ordinary numerical test is also a test relative to any fixed parameter. -/
theorem numericalDecision {α : Type*} [Encodable α] {F : AlphaTerm} {f : ℕ → ℕ}
    (hF : NumericalComputes F f) (ε : ℕ → ℕ) (R : α → Prop)
    (hpos : ∀ a, R a → f (Encodable.encode a) = 1)
    (hneg : ∀ a, ¬ R a → f (Encodable.encode a) = 0) :
    LambdaRelative.DecidablePredicate ε R := by
  refine ⟨liftNumericalProgram F,hF.uniform.1,fun a => ⟨?_,?_⟩⟩
  · intro h; simpa only [hpos a h] using hF.uniform.2 ε (Encodable.encode a)
  · intro h; simpa only [hneg a h] using hF.uniform.2 ε (Encodable.encode a)

/-- Prefix comparison with a fixed word, in either orientation. -/
theorem prefix_decidable (ε : ℕ → ℕ) (s : List ℕ) :
    LambdaRelative.DecidablePredicate ε (fun t : List ℕ => prefixOf s t) ∧
    LambdaRelative.DecidablePredicate ε (fun t : List ℕ => prefixOf t s) := by
  have h₁ := listPrefix_computes.comp
    ((numericalConstant_computes (NatListCode.encode s)).pair numericalIdentity_computes)
  have h₂ := listPrefix_computes.comp
    (numericalIdentity_computes.pair (numericalConstant_computes (NatListCode.encode s)))
  constructor
  · apply numericalDecision h₁ ε (fun t : List ℕ => prefixOf s t)
    · intro t h; simpa [Encodable.encode,prefixOf] using h
    · intro t h; simpa [Encodable.encode,prefixOf] using h
  · apply numericalDecision h₂ ε (fun t : List ℕ => prefixOf t s)
    · intro t h; simpa [Encodable.encode,prefixOf] using h
    · intro t h; simpa [Encodable.encode,prefixOf] using h

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    The list-map reduction theorem applies to each numerical projection, so it computes every projected entry and
    preserves the list's length and order. Numerical pairing then constructs exactly the two input codes required
    by $P,Q$. Both decisions terminate at the fixed parameter; their zero-or-one outputs multiply to one exactly when
    both hold. For a fixed word $\sigma$, test whether $\sigma$ is a prefix of the variable word or conversely,
    using the two
    orientations of the list-prefix test. Boolean disjunction combines them. Do this in both coordinates and conjoin
    the results with the original membership test. This retains short nodes compatible with the cylinder. Finally,
    apply the list-length term to each coordinate and use numerical equality to decide equal lengths.
-/
theorem prefixCompatible_decidable (ε : ℕ → ℕ) (s : List ℕ) :
    LambdaRelative.DecidablePredicate ε (prefixCompatible s) := by
  change LambdaRelative.DecidablePredicate ε (fun t => prefixOf s t ∨ prefixOf t s)
  have h := prefix_decidable ε s
  simpa only [not_and_or,not_not] using (h.1.not.and h.2.not).not

/-- Restriction checks compatibility, since a node may be shorter than the cylinder word. -/
def PairTree.restrictPrefixes {ε : ℕ → ℕ} (T : PairTree ε) (s t : List ℕ) : PairTree ε where
  tree := {z | z ∈ T.tree ∧ prefixCompatible s z.1 ∧ prefixCompatible t z.2}
  synchronized := fun z hz => T.synchronized z hz.1
  downward := fun z hz n =>
    ⟨T.downward z hz.1 n,prefixCompatible_take hz.2.1 n,prefixCompatible_take hz.2.2 n⟩
  decidable := T.decidable.and
    (((prefixCompatible_decidable ε s).precompNumerical (g := Prod.fst)
      (projection_computes true) (fun z => by
        simp [Encodable.encode])).and
    ((prefixCompatible_decidable ε t).precompNumerical (g := Prod.snd)
      (projection_computes false) (fun z => by
        simp [Encodable.encode])))

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    For the cylinder restriction, retain those $(s,t)\in T$ for which $s,a$ are comparable by the prefix relation,
    and likewise $t,b$. Both comparisons are decidable by finite-list prefix tests. Comparability is preserved by
    truncating the variable word. An infinite sequence has every prefix comparable with $a$ exactly when it extends
    $a$: test the prefix of length $|a|$ for the nontrivial implication. Thus the restricted body is exactly
    $[T]\cap(\cyl{a}\times\cyl{b})$. Apply this to the full tree with $b$ empty to obtain the cylinder $\cyl{a}$ as a
    projection. The explicit programs are given in §{sec:lambda-pair-tree-programs}.
-/
theorem pairTreeBody_restrictPrefixes {ε : ℕ → ℕ} (T : PairTree ε) (s t : List ℕ) :
    pairTreeBody (T.restrictPrefixes s t).tree = pairTreeBody T.tree ∩ (cyl s ×ˢ cyl t) := by
  ext p
  change (∀ n, (seqPrefix p.1 n,seqPrefix p.2 n) ∈ T.tree ∧
      prefixCompatible s (seqPrefix p.1 n) ∧ prefixCompatible t (seqPrefix p.2 n)) ↔ _
  simp only [forall_and,all_prefixCompatible_iff,Set.mem_inter_iff,Set.mem_prod,
    pairTreeBody,Set.mem_ofPred_eq]

def fullPairTree (ε : ℕ → ℕ) : PairTree ε where
  tree := {z | z.1.length = z.2.length}
  synchronized := fun _ h => h
  downward := by
    intro z hz n
    change z.1.length = z.2.length at hz
    simp only [Set.mem_ofPred_eq,List.length_take,hz]
  decidable := by
    have h := (listLength_computes.comp (projection_computes true)).combine
      (listLength_computes.comp (projection_computes false)) equalityTerm_closed
      (fun a b => if a = b then 1 else 0) equalityTerm_apply
    apply numericalDecision h ε (fun z : List ℕ × List ℕ => z.1.length = z.2.length)
    · intro z hz
      simp [Encodable.encode,hz]
    · intro z hz
      simp [Encodable.encode,hz]

theorem pairTreeBody_full (ε : ℕ → ℕ) : pairTreeBody (fullPairTree ε).tree = Set.univ := by
  ext p
  simp [pairTreeBody,fullPairTree,seqPrefix_length]

instance nonemptyPairTree (ε : ℕ → ℕ) : Nonempty (PairTree ε) := ⟨fullPairTree ε⟩

theorem projected_cyl (ε : ℕ → ℕ) (s : List ℕ) : Projected ε (cyl s) := by
  refine ⟨(fullPairTree ε).restrictPrefixes s [],?_⟩
  rw [pairTreeProjection_eq_image,pairTreeBody_restrictPrefixes,pairTreeBody_full]
  ext p
  simp only [Set.mem_image,Set.mem_inter_iff,Set.mem_univ,true_and,Set.mem_prod]
  constructor
  · intro hp
    exact ⟨(p,fun _ => 0),⟨hp,by simp [cyl,prefixOfSeq]⟩,rfl⟩
  · rintro ⟨⟨p,q⟩,hp,rfl⟩
    exact hp.1

/-- The two inputs share one parameter, with entrywise numerical pairing. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For sections, combine the two parameters as $\delta(n)=\NatPair{\varepsilon(n)}{p(n)}$. Define accessors
    $$\LambdaTermName{inputProjection}_i:=\lambdaab{o}{\lambdaab{k}{\LambdaNumericProjection{i}(ok)}}.$$
    Using the finite-prefix reader, define
    $$\begin{aligned}
    \LambdaTermName{sectionInput}&:=\lambdaab{o}{\lambdaab{z}{\LambdaNumericPair\,
     \bigl(\LambdaInputPrefix\,(\LambdaTermName{inputProjection}_2o)\,(\LambdaListLength z)\bigr)\,z}},\\
    \LambdaTermName{section}_P&:= \lambdaab{o}{ \lambdaab{z}{P( \LambdaTermName{inputProjection}_1o)(
    \LambdaTermName{sectionInput}oz)}}.
    \end{aligned}$$
    The accessors recover the original parameter and the base point from the same supplied input. In particular,
    $\LambdaTermName{sectionInput}$ computes the code of $\Pair{\restrict{p}{\Length{t}}}{t}$ on the list code of $t$.
-/
def sectionParameter (ε p : ℕ → ℕ) (k : ℕ) : ℕ := Nat.pair (ε k) (p k)

def parameterProjectionProgram (first : Bool) : AlphaTerm :=
  mapOutputProgram (numericalProjectionTerm first) identityProgram

theorem parameterProjection_computes (first : Bool) (ε p : ℕ → ℕ) :
    LambdaRelative.Computes (sectionParameter ε p) (parameterProjectionProgram first)
      (fun k => if first then ε k else p k) := by
  refine ⟨mapOutputProgram_closed (projection_computes first).1 identityProgram_closed,fun k => ?_⟩
  exact mapOutputProgram_runs (projection_computes first).1 identityProgram_closed
    (identityProgram_runs (sectionParameter ε p) k)
    (by simpa [sectionParameter] using (projection_computes first).2 (Nat.pair (ε k) (p k)))

/-- Compute the synchronized pair consisting of the parameter prefix and the input word. -/
def sectionInputProgram : AlphaTerm :=
  pairOutputProgram
    (reindexProgram (compositionProgram prefixProgram (parameterProjectionProgram false)) listLengthTerm)
    (liftNumericalProgram numericalIdentity)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Section decision program
-/
theorem sectionInput_computes (ε p : ℕ → ℕ) :
    LambdaRelative.Computes (sectionParameter ε p) sectionInputProgram
      (fun t : List ℕ => (seqPrefix p t.length,t)) := by
  have hright : LambdaRelative.Computes (sectionParameter ε p)
      (parameterProjectionProgram false) p := parameterProjection_computes false ε p
  have hprefix : LambdaRelative.Computes (sectionParameter ε p)
      (compositionProgram prefixProgram (parameterProjectionProgram false))
      (fun n : ℕ => NatListCode.encode (seqPrefix p n)) :=
    ⟨compositionProgram_closed prefixProgram_closed hright.1,
      fun n => compositionProgram_runs prefixProgram_closed hright.1 (prefixProgram_runs p n) hright.2⟩
  have h := (hprefix.reindex listLength_computes).pair
    (LambdaRelative.ofNumerical numericalIdentity_computes (sectionParameter ε p))
  refine ⟨h.1,fun t => ?_⟩
  simpa [Encodable.encode,sectionInputProgram] using h.2 (NatListCode.encode t)

/-- A section is recursive relative to the original parameter together with its base point. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Relative computation of a section tree
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    From a finite word $t$, compute its length, read the first $|t|$ values of $p$, and form the pair of list codes
    for $(\restrict{p}{|t|},t)$. Feed this pair into the decider for $T$. Each query to $\varepsilon$ and each query to
    $p$ is answered by the corresponding numerical projection of a query to $\delta$. Only finitely many values of
    $p$ are needed for each input, and the decider terminates relative to the fixed $\varepsilon$.
    Truncating the pair shows that $T_p$ is downward closed. This construction uses both inputs; it does not assert
    that an arbitrary section is recursive relative to $\varepsilon$ alone.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    Each accessor query reduces to the corresponding projection of the numerical pair returned by the input.
    The prefix-reader theorem therefore gives the first $\Length{t}$ entries of $p$, and numerical pairing gives the
    required membership input. Substitution of the first accessor in the finite beta/query derivation for $P$
    replaces each query by a computation of the same answer. Finally, two outer beta steps feed the output of
    $\LambdaTermName{sectionInput}$
    into this substituted program. All these steps retain the same supplied parameter, and both component
    computations terminate. The result is exactly the zero-or-one answer for membership in $T_p$.
-/
def PairTree.section {ε : ℕ → ℕ} (T : PairTree ε) (p : ℕ → ℕ) :
    PrefixTree (sectionParameter ε p) where
  tree := pairSectionTree T.tree p
  downward := by
    intro s t ht hst
    have h := T.downward (seqPrefix p t.length,t) ht s.length
    have hs : s = t.take s.length := List.prefix_iff_eq_take.mp hst
    simpa only [Prod.fst,Prod.snd,seqPrefix_take_of_le p hst.length_le,← hs,
      pairSectionTree,Set.mem_ofPred_eq] using h
  decidable := by
    obtain ⟨P,hP⟩ := T.decidable
    have hleft : LambdaRelative.Computes (sectionParameter ε p)
        (parameterProjectionProgram true) ε := parameterProjection_computes true ε p
    exact ⟨_,(hP.changeParameter hleft).precomp (sectionInput_computes ε p)⟩

end LambdaTree
end PolishSpaceBook
