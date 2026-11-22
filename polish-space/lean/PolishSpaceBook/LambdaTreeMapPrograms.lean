module

public import PolishSpaceBook.LambdaTreeMapFiniteTests

@[expose] public section

/-! # Lambda decision programs for comparison-map finite tests

All selectors are closed numerical lambda programs. Tree queries use the
original parameter; the two word loops use relative bounded products.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaRelative

theorem DecidablePredicate.or {α : Type*} [Encodable α] {ε : ℕ → ℕ}
    {R S : α → Prop} (hR : DecidablePredicate ε R) (hS : DecidablePredicate ε S) :
    DecidablePredicate ε (fun z => R z ∨ S z) := by
  simpa only [not_and_or,not_not] using (hR.not.and hS.not).not

theorem DecidablePredicate.imp {α : Type*} [Encodable α] {ε : ℕ → ℕ}
    {R S : α → Prop} (hR : DecidablePredicate ε R) (hS : DecidablePredicate ε S) :
    DecidablePredicate ε (fun z => R z → S z) := by
  simpa only [imp_iff_not_or] using (hR.not.or hS)

end LambdaRelative
namespace LambdaTree
local instance mapProgramListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance mapProgramPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

theorem numerical_le_decidable {A B : AlphaTerm} {a b : ℕ → ℕ}
    (hA : NumericalComputes A a) (hB : NumericalComputes B b) (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ => a z ≤ b z) := by
  apply numericalDecision
    (hA.ifLe hB (numericalConstant_computes 1) (numericalConstant_computes 0)) ε
  · intro z h; simp [h]
  · intro z h; simp [h]

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P,Q$ decide membership in the pair trees $T,S$, taking a numerical pair of word codes and
    returning zero or one. We give the numerical tests and the joint edge-label program needed by
    §{sec:edst-recursive-borel-completeness}. All computations use the original oracle argument $o$.
    In this subsection abbreviate
    $$\begin{aligned}
    p_i&:=\LambdaNumericProjection{i},&A_i&:=\LambdaListMap\,p_i,\\
    \langle X,Y\rangle_\lambda&:=\LambdaNumericPair\,X\,Y,&
    \ell(X)&:=\LambdaListLength\,X,\\
    C(X,Y;U,V)&:=\LambdaLeCase{X}{Y}{U}{V},&
    L(X,Y)&:=C(\LambdaSucc\,X,Y;\ChurchNumeral{1},\ChurchNumeral{0}).
    \end{aligned}$$
    Thus $A_i$ projects every entry of a word, and $L$ tests strict numerical inequality.
    Expand each abbreviation before abstraction, with fresh bound variables.
-/
theorem numerical_lt_decidable {A B : AlphaTerm} {a b : ℕ → ℕ}
    (hA : NumericalComputes A a) (hB : NumericalComputes B b) (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ => a z < b z) :=
  numerical_le_decidable (successor_computes.comp hA) hB ε

theorem numerical_zero_decidable {A : AlphaTerm} {a : ℕ → ℕ}
    (hA : NumericalComputes A a) (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ => a z = 0) := by
  apply numericalDecision (reverseZero_computes.comp hA) ε
  · intro z h; simp [h]
  · intro z h; simp [h]

@[simp] theorem decode_eq_nil_iff (e : ℕ) : NatListCode.decode e = [] ↔ e = 0 := by
  constructor
  · intro h
    have := congrArg NatListCode.encode h
    simpa [NatListCode.encode_decode,NatListCode.encode] using this
  · rintro rfl; simp [NatListCode.decode]

theorem word_prefix_decidable {A B : AlphaTerm} {a b : ℕ → ℕ}
    (hA : NumericalComputes A a) (hB : NumericalComputes B b) (ε : ℕ → ℕ) :
    LambdaRelative.DecidablePredicate ε
      (fun z : ℕ => prefixOf (NatListCode.decode (a z)) (NatListCode.decode (b z))) := by
  apply numericalDecision (listPrefix_computes.comp (hA.pair hB)) ε
  · intro z h; simpa [prefixOf] using h
  · intro z h; simpa [prefixOf] using h

/-- The output is itself a word code, including the default zero entry. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Use the following numerical bodies and Boolean operations on bits:
    $$\begin{aligned}
    \ell(a)&:=\LambdaListLength\,a,\\
    m(b,u)&:=\LambdaListGet(\LambdaNumericPair\,b\,u),\\
    p(u,v)&:=\LambdaListPrefix(\LambdaNumericPair\,u\,v),\\
    L(u,v)&:=\LambdaLeCase{u}{v}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
    K(u,v)&:=L(\LambdaSucc\,u,v),\\
    B(d,e)&:=Z(\LambdaMul\,d\,(Ze)),\\
    O(d,e)&:=Z(\LambdaMul\,(Zd)\,(Ze)).
    \end{aligned}$$
    When $b$ codes a list of image-word codes, the body $m(b,u)$ computes the Church numeral for the selected
    image-word code; no word decoder is needed inside the program.
    The bodies $B$ and $O$ compute implication and disjunction. Juxtaposed multiplication of bits below
    means repeated application of $\LambdaMul$.
-/
theorem finiteWordMap_computes {Q U : AlphaTerm} {q u : ℕ → ℕ}
    (hQ : NumericalComputes Q q) (hU : NumericalComputes U u) :
    NumericalComputes (numericalCompose listGetTerm (pairNumerical Q U))
      (fun z => NatListCode.encode (finiteWordMap (NatListCode.decode (q z))
        (NatListCode.decode (u z)))) := by
  simpa only [finiteWordMap,wordOfCode,NatListCode.encode_decode,Nat.unpair_pair,
    List.getD_eq_getElem?_getD] using listGet_computes.comp (hQ.pair hU)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For a family decider $P$, the finite section decision is the body
    $$\begin{aligned}
    A_P(o,i,a,u)&:=O\bigl(Zu,Po\,k(i,a,u)\bigr),\\
    k(i,a,u)&:=\LambdaNumericPair\,i\,
     \bigl(\LambdaNumericPair\,(\LambdaListTake(\LambdaNumericPair\,a\,\ell(u)))\,u\bigr).
    \end{aligned}$$
    It accepts the empty word and otherwise queries the tree on the point prefix of the word's length.
    All calls terminate even if the two supplied words have different lengths. Fix a root-test term
    $r=Z$ or $r=\lambdaab{u}{Z(Zu)}$, for an empty or nonempty image root respectively.
-/
theorem finiteSectionNode_family_decidable {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree))
    {I S U : AlphaTerm} {i s u : ℕ → ℕ}
    (hI : NumericalComputes I i) (hS : NumericalComputes S s) (hU : NumericalComputes U u) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ =>
      finiteSectionNode (T (i z)).tree (NatListCode.decode (s z)) (NatListCode.decode (u z))) := by
  have htake := listTake_computes.comp (hS.pair (listLength_computes.comp hU))
  have ht := hT.precompNumerical
    (g := fun z : ℕ => (i z,((NatListCode.decode (s z)).take (NatListCode.decode (u z)).length,
      NatListCode.decode (u z))))
    (hI.pair (htake.pair hU))
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  simpa only [finiteSectionNode,decode_eq_nil_iff] using (numerical_zero_decidable hU ε).or ht

/-- One guarded strict-edge obligation. -/
def mapEdgeTest (s q : List ℕ) (u v : ℕ) : Prop :=
  v < s.length → prefixOf (wordOfCode v) (wordOfCode u) →
  (wordOfCode v).length < (wordOfCode u).length →
  prefixOf (finiteWordMap q (wordOfCode v)) (finiteWordMap q (wordOfCode u)) ∧
    (finiteWordMap q (wordOfCode v)).length < (finiteWordMap q (wordOfCode u)).length

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For the following bodies extract $z=\NatPair{i}{\NatPair{a}{b}}$ by numerical projections and put
    $n=\ell(a)$. In the edge body the input is $v=\NatPair{w}{j}$ with $w=\NatPair{z}{u}$:
    $$\begin{aligned}
    E(o,z,u,j)&:=B\bigl(K(j,n)\,p(j,u)\,K(\ell(j),\ell(u)),\\
     &\quad p(m(b,j),m(b,u))\,K(\ell(m(b,j)),\ell(m(b,u)))\bigr),\\
    V&:=\lambdaab{o}{\lambdaab{v}{E(o,z,u,j)}}.
    \end{aligned}$$
    The products here are products of bits, not applications of one bit to another. The body checks precisely
    the guarded strict-edge obligation for the words coded by $u,j$.
-/
theorem treeMapEdge_decidable {ε : ℕ → ℕ}
    {S Q U V : AlphaTerm} {s q u v : ℕ → ℕ}
    (hS : NumericalComputes S s) (hQ : NumericalComputes Q q)
    (hU : NumericalComputes U u) (hV : NumericalComputes V v) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ =>
      mapEdgeTest (NatListCode.decode (s z)) (NatListCode.decode (q z)) (u z) (v z)) := by
  have hmu := finiteWordMap_computes hQ hU
  have hmv := finiteWordMap_computes hQ hV
  have ha := numerical_lt_decidable hV (listLength_computes.comp hS) ε
  have hb := word_prefix_decidable hV hU ε
  have hc := numerical_lt_decidable (listLength_computes.comp hV) (listLength_computes.comp hU) ε
  have hd := word_prefix_decidable hmv hmu ε
  have he := numerical_lt_decidable (listLength_computes.comp hmv) (listLength_computes.comp hmu) ε
  simpa only [mapEdgeTest,wordOfCode,NatListCode.decode_encode] using ha.imp (hb.imp (hc.imp (hd.and he)))

/-- A source-word obligation and all of its bounded edge obligations. -/
def mapNodeTest (T S : Set (List ℕ × List ℕ)) (s q : List ℕ) (u : ℕ) : Prop :=
  u < s.length → (wordOfCode u).length ≤ s.length →
  finiteSectionNode T s (wordOfCode u) →
  ((finiteWordMap q (wordOfCode u)).length ≤ s.length →
    finiteSectionNode S s (finiteWordMap q (wordOfCode u))) ∧
  ∀ j < s.length, mapEdgeTest s q u j

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For the node body, with input $w=\NatPair{z}{u}$, define
    $$\begin{aligned}
    G(o,z,u)&:=K(u,n)\,L(\ell(u),n)\,A_{P_T}(o,i,a,u),\\
    H(o,z,u)&:=B\bigl(L(\ell(m(b,u)),n),A_{P_S}(o,i,a,m(b,u))\bigr),\\
    J(o,w)&:=\LambdaRelativeProduct{V}\,o\,(\LambdaNumericPair\,w\,n),\\
    U&:=\lambdaab{o}{\lambdaab{w}{B\bigl(G(o,z,u),H(o,z,u)\,J(o,w)\bigr)}},\\
    Q_r&:=\lambdaab{o}{\lambdaab{z}{\LambdaMul\,
     B(K(\ChurchNumeral{0},n),r(m(b,\ChurchNumeral{0})))\\
     &\hspace{27mm}(\LambdaRelativeProduct{U}\,o\,(\LambdaNumericPair\,z\,n))}}.
    \end{aligned}$$
    The symbols $i,a,b,n,z,u,j$ in these expressions always abbreviate projections or numerical computations
    from the current input. After expansion the displayed programs are closed.
-/
theorem treeMapNode_decidable {ε : ℕ → ℕ} (T S : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree))
    (hS : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (S z.1).tree))
    {I A Q U : AlphaTerm} {i a q u : ℕ → ℕ}
    (hI : NumericalComputes I i) (hA : NumericalComputes A a)
    (hQ : NumericalComputes Q q) (hU : NumericalComputes U u) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ =>
      mapNodeTest (T (i z)).tree (S (i z)).tree
        (NatListCode.decode (a z)) (NatListCode.decode (q z)) (u z)) := by
  have hm := finiteWordMap_computes hQ hU
  have hn := listLength_computes.comp hA
  have ha := numerical_lt_decidable hU hn ε
  have hb := numerical_le_decidable (listLength_computes.comp hU) hn ε
  have hc := finiteSectionNode_family_decidable T hT hI hA hU
  have hd := numerical_le_decidable (listLength_computes.comp hm) hn ε
  have he := finiteSectionNode_family_decidable S hS hI hA hm
  have hj := treeMapEdge_decidable (ε := ε)
    (hA.comp (projection_computes true)) (hQ.comp (projection_computes true))
    (hU.comp (projection_computes true)) (projection_computes false)
  have hall := hj.boundedAll hn
  simpa only [mapNodeTest,wordOfCode,Nat.unpair_pair,NatListCode.decode_encode,
    ite_true,Bool.false_eq_true,ite_false]
    using ha.imp (hb.imp (hc.imp ((hd.imp he).and hall)))

/-- The finite test expressed by its two bounded numerical loops. -/
theorem treeMapFiniteTest_iff (T S : Set (List ℕ × List ℕ))
    (rootTest : List ℕ → Prop) (s q : List ℕ) :
    treeMapFiniteTest T S rootTest (s,q) ↔
      (0 < s.length → rootTest (finiteWordMap q [])) ∧
      ∀ u < s.length, mapNodeTest T S s q u := by
  simp only [treeMapFiniteTest,mapNodeTest,mapEdgeTest,wordOfCode,
    NatListCode.encode,NatListCode.encode_decode,forall_eq]

/-- The family index and both words remain numerical input data. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Decision programs for comparison trees
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    List access gives the correct image code, and the finite section body agrees with $R_T$.
    The comparisons and Boolean operations therefore give exactly the root, image-membership, and edge
    conditions. The inner bounded product ranges over $j<n$, and the outer one over $u<n$; the word code
    bijection turns these into precisely the two loops of the comparison test. Every component is total, so
    both products terminate, including at length zero when they return one. The outer root guard also returns
    one at length zero. Prefix closure is imposed afterwards by the finite-test tree construction, which
    checks all shorter prefixes as well. The family index remains input data throughout, so specialization
    provides total lambda-computed indices without deciding whether the input projections are disjoint.
    \end{proof}
-/
theorem treeMapFiniteTest_family_decidable {ε : ℕ → ℕ} (T S : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree))
    (hS : LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (S z.1).tree))
    (rootTest : List ℕ → Prop) (hr : LambdaRelative.DecidablePredicate ε rootTest) :
    LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) =>
      treeMapFiniteTest (T z.1).tree (S z.1).tree rootTest z.2) := by
  have hi := computes_codeFirst numericalIdentity_computes
  have hw := computes_codeSecond numericalIdentity_computes
  have hs := computes_codeFirst hw
  have hq := computes_codeSecond hw
  have hn := listLength_computes.comp hs
  have hu := treeMapNode_decidable T S hT hS
    (hi.comp (projection_computes true)) (hs.comp (projection_computes true))
    (hq.comp (projection_computes true)) (projection_computes false)
  have hall := hu.boundedAll hn
  have hm := finiteWordMap_computes hq (numericalConstant_computes 0)
  have hroot := hr.precompNumerical
    (g := fun z : ℕ => finiteWordMap (NatListCode.decode z.unpair.2.unpair.2) []) hm
    (fun z => by simp [Encodable.encode,NatListCode.decode,id_eq])
  have hguard := numerical_lt_decidable (numericalConstant_computes 0) hn ε
  have hboth := (hguard.imp hroot).and hall
  have htyped := hboth.precompNumerical
    (g := fun z : ℕ × (List ℕ × List ℕ) =>
      Nat.pair z.1 (Nat.pair (NatListCode.encode z.2.1) (NatListCode.encode z.2.2)))
    numericalIdentity_computes (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  change LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) =>
    treeMapFiniteTest (T z.1).tree (S z.1).tree rootTest (z.2.1,z.2.2))
  simpa only [treeMapFiniteTest_iff,Encodable.encode,Encodable.encodeSigma,
    Nat.unpair_pair,NatListCode.decode_encode,id_eq,ite_true,Bool.false_eq_true,ite_false] using htyped

/-- A constant family retains its original decision program. -/
theorem constantTree_family_decidable {ε : ℕ → ℕ} (T : PairTree ε) :
    LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ T.tree) :=
  T.decidable.precompNumerical (g := fun z : ℕ × (List ℕ × List ℕ) => z.2)
    (projection_computes false) (fun z => by simp [Encodable.encode,Encodable.encodeSigma])

theorem treeMapFiniteTest_decidable {ε : ℕ → ℕ} (T S : PairTree ε)
    (rootTest : List ℕ → Prop) (hr : LambdaRelative.DecidablePredicate ε rootTest) :
    LambdaRelative.DecidablePredicate ε (treeMapFiniteTest T.tree S.tree rootTest) := by
  have hf := treeMapFiniteTest_family_decidable (fun _ => T) (fun _ => S)
    (constantTree_family_decidable T) (constantTree_family_decidable S) rootTest hr
  exact hf.precompNumerical (g := fun z => (0,z))
    ((numericalConstant_computes 0).pair numericalIdentity_computes)
    (fun z => by simp [Encodable.encode,Encodable.encodeSigma])

end LambdaTree
end PolishSpaceBook
