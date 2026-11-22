module

public import PolishSpaceBook.LambdaProjectionOperations

@[expose] public section

/-! # Uniform countable operations with one fixed lambda parameter

The family index and node have one joint decider. The union witness reserves
its first digit for the index; the intersection witness stores all rows.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance countableListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance countablePairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

def codeFirst (F : AlphaTerm) := numericalCompose (numericalProjectionTerm true) F
def codeSecond (F : AlphaTerm) := numericalCompose (numericalProjectionTerm false) F

theorem computes_codeFirst {F : AlphaTerm} {f : ℕ → ℕ} (h : NumericalComputes F f) :
    NumericalComputes (codeFirst F) (fun z => (f z).unpair.1) := (projection_computes true).comp h

theorem computes_codeSecond {F : AlphaTerm} {f : ℕ → ℕ} (h : NumericalComputes F f) :
    NumericalComputes (codeSecond F) (fun z => (f z).unpair.2) := (projection_computes false).comp h

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P$ be a closed program deciding $(s,t)\in T_i$ at parameter $\varepsilon$ on input
    $\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$.
    Throughout this subsection, expand all abbreviations before abstraction and choose distinct fresh binders.
    For a node code $z$, put
    $$\begin{aligned}
    d(z)&:=\LambdaListField{2}(\LambdaNumericProjection{2}z),\qquad
    h(z):=\LambdaListGet(\LambdaNumericPair\,(\LambdaNumericProjection{2}z)\,\ChurchNumeral{0}),\\
    Z&:=\lambdaab{r}{\LambdaZeroTest\,r\,\ChurchNumeral{1}\,\ChurchNumeral{0}}.
    \end{aligned}$$
    The field program also returns zero at the empty-list code, so it computes the tail code for every list.
    The term $Z$ reverses a decision bit.
-/
theorem tailCode_computes : NumericalComputes (listFieldTerm false)
    (fun e => NatListCode.encode (NatListCode.decode e).tail) :=
  ⟨listFieldTerm_closed false,fun e => by simpa only [NatListCode.encode_decode] using listTail_code (NatListCode.decode e)⟩

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P$ be a closed program deciding $(s,t)\in T_i$ at parameter $\varepsilon$ on input
    $\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$.
    Throughout this subsection, expand all abbreviations before abstraction and choose distinct fresh binders.
    For a node code $z$, put
    $$\begin{aligned}
    d(z)&:=\LambdaListField{2}(\LambdaNumericProjection{2}z),\qquad
    h(z):=\LambdaListGet(\LambdaNumericPair\,(\LambdaNumericProjection{2}z)\,\ChurchNumeral{0}),\\
    Z&:=\lambdaab{r}{\LambdaZeroTest\,r\,\ChurchNumeral{1}\,\ChurchNumeral{0}}.
    \end{aligned}$$
    The field program also returns zero at the empty-list code, so it computes the tail code for every list.
    The term $Z$ reverses a decision bit.
-/
def unionInputTerm : AlphaTerm :=
  let s := numericalProjectionTerm true
  let v := numericalProjectionTerm false
  let t := numericalCompose (listFieldTerm false) v
  pairNumerical (numericalCompose listGetTerm (pairNumerical v (numericalConstant 0)))
    (pairNumerical (numericalCompose listTakeTerm
      (pairNumerical s (numericalCompose listLengthTerm t))) t)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $P$ be a closed program deciding $(s,t)\in T_i$ at parameter $\varepsilon$ on input
    $\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$.
    Throughout this subsection, expand all abbreviations before abstraction and choose distinct fresh binders.
    For a node code $z$, put
    $$\begin{aligned}
    d(z)&:=\LambdaListField{2}(\LambdaNumericProjection{2}z),\qquad
    h(z):=\LambdaListGet(\LambdaNumericPair\,(\LambdaNumericProjection{2}z)\,\ChurchNumeral{0}),\\
    Z&:=\lambdaab{r}{\LambdaZeroTest\,r\,\ChurchNumeral{1}\,\ChurchNumeral{0}}.
    \end{aligned}$$
    The field program also returns zero at the empty-list code, so it computes the tail code for every list.
    The term $Z$ reverses a decision bit.
-/
theorem unionInput_computes : NumericalComputes unionInputTerm (fun z =>
    Nat.pair ((NatListCode.decode z.unpair.2).getD 0 0)
      (Nat.pair (NatListCode.encode ((NatListCode.decode z.unpair.1).take
        (NatListCode.decode z.unpair.2).tail.length))
        (NatListCode.encode (NatListCode.decode z.unpair.2).tail))) := by
  have ht := tailCode_computes.comp (projection_computes false)
  have hi := listGet_computes.comp ((projection_computes false).pair (numericalConstant_computes 0))
  have hs := listTake_computes.comp ((projection_computes true).pair (listLength_computes.comp ht))
  simpa only [unionInputTerm,Nat.unpair_pair,NatListCode.decode_encode,ite_true,Bool.false_eq_true,ite_false] using hi.pair (hs.pair ht)

def unionTest (T : ℕ → Set (List ℕ × List ℕ)) (z : List ℕ × List ℕ) : Prop :=
  z.2 = [] ∨ (z.1.take z.2.tail.length,z.2.tail) ∈ T (z.2.getD 0 0)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For the union, define
    $$\begin{aligned}
    K_U&:=\lambdaab{z}{\LambdaNumericPair\,h(z)\,
     (\LambdaNumericPair\,
      (\LambdaListTake(\LambdaNumericPair\,(\LambdaNumericProjection{1}z)\,(\LambdaListLength\,d(z))))\,d(z))},\\
    E(z)&:=Z(\LambdaNumericProjection{2}z),\qquad D(o,z):=Po(K_Uz),\\
    Q_U&:=\lambdaab{o}{\lambdaab{z}{Z(\LambdaMul\,(Z(E(z)))\,(Z(D(o,z))))}}.
    \end{aligned}$$
    On a nonempty witness word, $K_U$ returns the selected index together with the shortened first word and
    the witness tail. The bit $E(z)$ tests whether the witness word is empty; the outer expression is the
    Boolean disjunction of this bit and $D(o,z)$. Thus $Q_U$ decides the union test of
    §{sec:edst-uniform-countable-operations}. Every component terminates, even on unequal input lengths.
    Applying the finite-test construction gives the required tree decider.
-/
theorem unionTest_decidable {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree)) :
    LambdaRelative.DecidablePredicate ε (unionTest (fun i => (T i).tree)) := by
  have ht := hT.precompNumerical
    (g := fun z : List ℕ × List ℕ => (z.2.getD 0 0,(z.1.take z.2.tail.length,z.2.tail)))
    unionInput_computes (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have hn : LambdaRelative.DecidablePredicate ε (fun z : List ℕ × List ℕ => z.2 = []) := by
    apply numericalDecision (reverseZero_computes.comp (projection_computes false)) ε
    · intro z h; simp [Encodable.encode,h,NatListCode.encode]
    · intro z h
      have he : NatListCode.encode z.2 ≠ 0 := by
        intro he
        apply h
        have := congrArg NatListCode.decode he
        simpa [NatListCode.decode] using this
      simp [Encodable.encode,he]
  unfold unionTest
  simpa only [not_and_or,not_not] using (hn.not.and ht.not).not

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Uniform countable unions
-/
def unionTree {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree)) : PairTree ε :=
  finiteCheckTree (unionTest (fun i => (T i).tree)) (unionTest_decidable T hT)

theorem prefix_succ_head (q : ℕ → ℕ) (n : ℕ) :
    seqPrefix q (n+1) = q 0 :: seqPrefix (fun i => q (i+1)) n := by
  simp [seqPrefix,List.ofFn_succ]

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the finite-test construction of §{sec:edst-finite-check-trees} with
    $$\begin{aligned}
    R(s,[])&\quad\Longleftrightarrow\quad\text{true},\\
    R(s,i::t)&\quad\Longleftrightarrow\quad(\restrict{s}{|t|},t)\in T_i.
    \end{aligned}$$
    The head and tail of a list, its length, and prefix extraction are computed by total numerical lambda
    terms, so the joint decider decides this test at the original parameter. A branch passes the test at
    length $n+1$ exactly when the length-$n$ prefixes of its first coordinate and shifted witness lie in the
    tree selected by its first witness entry. This proves the body identity. Taking that entry as the chosen
    index gives one projection inclusion. For the other, prepend the chosen index to a witness in its tree.
    The empty-prefix test always passes, but the test at length one checks the empty node of the selected
    tree. Thus an empty selected tree produces no spurious branch.
    \end{proof}
-/
theorem pairTreeBody_unionTree {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree))
    (x q : ℕ → ℕ) :
    (x,q) ∈ pairTreeBody (unionTree T hT).tree ↔
      (x,fun i => q (i+1)) ∈ pairTreeBody (T (q 0)).tree := by
  change (x,q) ∈ pairTreeBody (finiteCheckNodes _) ↔ _
  rw [pairTreeBody_finiteCheckNodes]
  constructor
  · intro h n
    have hn := h (n+1)
    simpa [unionTest,prefix_succ_head q,seqPrefix_length,
      seqPrefix_take_of_le _ (Nat.le_succ n)] using hn
  · intro h n
    cases n with
    | zero => simp [unionTest,seqPrefix]
    | succ n =>
      simpa [unionTest,prefix_succ_head q,seqPrefix_length,
        seqPrefix_take_of_le _ (Nat.le_succ n)] using h n

theorem pairTreeProjection_unionTree {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree)) :
    pairTreeProjection (unionTree T hT).tree = ⋃ i, pairTreeProjection (T i).tree := by
  ext x
  constructor
  · rintro ⟨q,hq⟩
    exact mem_iUnion.mpr ⟨q 0,fun i => q (i+1),(pairTreeBody_unionTree T hT x q).mp hq⟩
  · intro hx
    obtain ⟨i,q,hq⟩ := mem_iUnion.mp hx
    let r : ℕ → ℕ := fun n => Nat.casesOn n i q
    exact ⟨r,(pairTreeBody_unionTree T hT x r).mpr hq⟩

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    The constructions below
    use the joint decider and do not add a parameter encoding a choice of separate programs.
-/
theorem projected_uniform_iUnion {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree)) :
    Projected ε (⋃ i, pairTreeProjection (T i).tree) :=
  ⟨unionTree T hT,(pairTreeProjection_unionTree T hT).symm⟩

def witnessRow (v : List ℕ) (i k : ℕ) : List ℕ :=
  (List.range k).map (fun j => v.getD (Nat.pair i j) 0)

/-- Input is ((word-code,row),column). -/
def rowEntryTerm : AlphaTerm := numericalCompose listGetTerm
  (pairNumerical (codeFirst (numericalProjectionTerm true))
    (pairNumerical (codeSecond (numericalProjectionTerm true)) (numericalProjectionTerm false)))

theorem rowEntry_computes : NumericalComputes rowEntryTerm (fun z =>
    (NatListCode.decode z.unpair.1.unpair.1).getD (Nat.pair z.unpair.1.unpair.2 z.unpair.2) 0) := by
  simpa only [rowEntryTerm,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using listGet_computes.comp
    ((computes_codeFirst (projection_computes true)).pair
      ((computes_codeSecond (projection_computes true)).pair (projection_computes false)))

/-- Input is (word-code,(row,length)). -/
def witnessRowTerm : AlphaTerm := numericalCompose (listTabulateTerm rowEntryTerm)
  (pairNumerical (pairNumerical (numericalProjectionTerm true) (codeFirst (numericalProjectionTerm false)))
    (codeSecond (numericalProjectionTerm false)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{LambdaWitnessRow}
    \end{mathmeta}
    To extract a finite witness row, decode $u=\NatPair{\NatPair{e}{i}}{j}$ inside the first term below.
    In the second, abbreviate $c(z)=\LambdaNumericProjection{2}z$:
    $$\begin{aligned}
    F_{\mathrm{row}}&:=\lambdaab{u}{\LambdaListGet(\LambdaNumericPair\,e\,(\LambdaNumericPair\,i\,j))},\\
    \LambdaWitnessRow&:=\lambdaab{z}{\LambdaListTabulate{F_{\mathrm{row}}}\,
     (\LambdaNumericPair\,
      (\LambdaNumericPair\,(\LambdaNumericProjection{1}z)\,(\LambdaNumericProjection{1}c(z)))\,
      (\LambdaNumericProjection{2}c(z)))}.
    \end{aligned}$$
    Here $e,i,j$ mean the corresponding numerical projections of $u$ only within $F_{\mathrm{row}}$.
    The list-access theorem and finite tabulation show that on input
    $\NatPair{\LambdaListCode{t}}{\NatPair{i}{k}}$ the second term returns
    $\LambdaListCode{\WitnessRow{t}{i}{k}}$. This works for every input, including an empty row and missing
    entries, which are replaced by zero.
-/
theorem witnessRow_computes : NumericalComputes witnessRowTerm (fun z =>
    NatListCode.encode (witnessRow (NatListCode.decode z.unpair.1) z.unpair.2.unpair.1 z.unpair.2.unpair.2)) := by
  simpa only [witnessRowTerm,witnessRow,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using
    (listTabulate_computes rowEntry_computes).comp
      (((projection_computes true).pair (computes_codeFirst (projection_computes false))).pair
        (computes_codeSecond (projection_computes false)))

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{WitnessRow}
    \end{mathmeta}
    For intersections, store all witnesses in one sequence, with row $i$ occupying positions $\NatPair{i}{j}$.
    For finite words define
    $$\WitnessRow{v}{i}{k}:=[v^*_{\NatPair{i}{j}}]_{j<k},\qquad
    v^*_r:=\begin{cases}v_r,&r<|v|,\\0,&r\ge|v|.\end{cases}$$
    Entries are listed in increasing order of $j$. If $\NatPair{i}{k}<|v|$, every entry used in this row exists:
    numerical pairing is strictly increasing in its second argument. Consequently,
    $$\WitnessRow{\restrict{q}{n}}{i}{k}
     =\restrict{\Sequence{q(\NatPair{i}{j})}{j\in\omega}}{k}
     \quad\text{when }\NatPair{i}{k}<n.$$
    The guard is sufficient, though it need not be the earliest stage at which the row can be read.
-/
theorem witnessRow_prefix (q : ℕ → ℕ) (i k n : ℕ) (h : Nat.pair i k < n) :
    witnessRow (seqPrefix q n) i k = seqPrefix (fun j => q (Nat.pair i j)) k := by
  apply List.ext_getElem
  · simp [witnessRow,seqPrefix_length]
  · intro j hj hj'
    have hjk : j < k := by simpa [seqPrefix_length] using hj'
    have hjn : Nat.pair i j < n := (Nat.pair_lt_pair_right i hjk).trans h
    simp [witnessRow,seqPrefix,hjn,List.getD_eq_getElem?_getD]

/-- Input is ((node-code,row),depth). -/
def interInputTerm : AlphaTerm :=
  let w := codeFirst (numericalProjectionTerm true)
  let i := codeSecond (numericalProjectionTerm true)
  let k := numericalProjectionTerm false
  pairNumerical i (pairNumerical
    (numericalCompose listTakeTerm (pairNumerical (codeFirst w) k))
    (numericalCompose witnessRowTerm (pairNumerical (codeSecond w) (pairNumerical i k))))

theorem interInput_computes : NumericalComputes interInputTerm (fun z =>
    Nat.pair z.unpair.1.unpair.2 (Nat.pair
      (NatListCode.encode ((NatListCode.decode z.unpair.1.unpair.1.unpair.1).take z.unpair.2))
      (NatListCode.encode (witnessRow (NatListCode.decode z.unpair.1.unpair.1.unpair.2)
        z.unpair.1.unpair.2 z.unpair.2)))) := by
  have hw := computes_codeFirst (projection_computes true)
  have hi := computes_codeSecond (projection_computes true)
  have hk := projection_computes false
  have hs := listTake_computes.comp ((computes_codeFirst hw).pair hk)
  have hr := witnessRow_computes.comp ((computes_codeSecond hw).pair (hi.pair hk))
  simpa only [interInputTerm,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using hi.pair (hs.pair hr)

def interBoundTerm : AlphaTerm :=
  let w := codeFirst (numericalProjectionTerm true)
  let i := codeSecond (numericalProjectionTerm true)
  let k := numericalProjectionTerm false
  numericalIfLe (numericalCompose successorTerm (pairNumerical i k))
    (numericalCompose listLengthTerm (codeSecond w)) (numericalConstant 1) (numericalConstant 0)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For an intersection trial input, decode $u=\NatPair{\NatPair{z}{i}}{k}$ and expand
    $$\begin{aligned}
    L(u)&:=\LambdaListTake(\LambdaNumericPair\,(\LambdaNumericProjection{1}z)\,k),\\
    W(u)&:=\LambdaWitnessRow(\LambdaNumericPair\,(\LambdaNumericProjection{2}z)\,(\LambdaNumericPair\,i\,k)),\\
    K_V&:=\lambdaab{u}{\LambdaNumericPair\,i\,(\LambdaNumericPair\,L(u)\,W(u))},\\
    B(u)&:=\LambdaLeCase{\LambdaSucc(\LambdaNumericPair\,i\,k)}
     {\LambdaListLength\,(\LambdaNumericProjection{2}z)}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
    Q_V&:=\lambdaab{o}{\lambdaab{u}{Z(\LambdaMul\,B(u)\,(Z(Po(K_Vu))))}}.
    \end{aligned}$$
    Within these bodies, $z,i,k$ are numerical projections of $u$. The guard $B(u)$ is one exactly when
    $\NatPair{i}{k}<|v|$, and $K_V$ constructs the input for the tree test on the first $k$ entries and the
    extracted row. The last term computes implication: a failed guard returns one, and a true guard returns
    the supplied tree decision. All numerical components and the joint decider terminate.
-/
theorem interBound_computes : NumericalComputes interBoundTerm (fun z =>
    if Nat.pair z.unpair.1.unpair.2 z.unpair.2 < (NatListCode.decode z.unpair.1.unpair.1.unpair.2).length
    then 1 else 0) := by
  have hw := computes_codeFirst (projection_computes true)
  have hi := computes_codeSecond (projection_computes true)
  have hk := projection_computes false
  simpa only [interBoundTerm,Nat.succ_le_iff,ite_true,Bool.false_eq_true,ite_false] using
    (successor_computes.comp (hi.pair hk)).ifLe (listLength_computes.comp (computes_codeSecond hw))
      (numericalConstant_computes 1) (numericalConstant_computes 0)

def interTest (T : ℕ → Set (List ℕ × List ℕ)) (z : List ℕ × List ℕ) : Prop :=
  ∀ i < z.1.length, ∀ k < z.1.length,
    Nat.pair i k < z.2.length → (z.1.take k,witnessRow z.2 i k) ∈ T i

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Finally put $n(z)=\LambdaListLength\,(\LambdaNumericProjection{1}z)$. With $v=\NatPair{z}{i}$ in the first body, define
    $$\begin{aligned}
    I&:=\lambdaab{o}{\lambdaab{v}{\LambdaRelativeProduct{Q_V}\,o\,
     (\LambdaNumericPair\,v\,n(\LambdaNumericProjection{1}v))}},\\
    J&:=\lambdaab{o}{\lambdaab{z}{\LambdaRelativeProduct{I}\,o\,
     (\LambdaNumericPair\,z\,n(z))}}.
    \end{aligned}$$
    The inner product ranges over $k<|s|$, retaining the node code and row index. The outer product ranges
    over $i<|s|$, retaining the node code. Both use the same parameter $o$. The bounded-product theorem
    therefore proves that $J$ decides exactly the intersection test of §{sec:edst-uniform-countable-operations}.
    Applying the finite-test construction once more gives its downward-closed tree. At length zero both
    products are empty and return one; the later prefix tests still inspect the empty node of each component
    tree. No test of an infinite witness and no program selecting such witnesses is used.
-/
theorem interTest_decidable {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree)) :
    LambdaRelative.DecidablePredicate ε (interTest (fun i => (T i).tree)) := by
  have hc := hT.precompNumerical (g := fun z : ℕ => (z.unpair.1.unpair.2,
    ((NatListCode.decode z.unpair.1.unpair.1.unpair.1).take z.unpair.2,
      witnessRow (NatListCode.decode z.unpair.1.unpair.1.unpair.2) z.unpair.1.unpair.2 z.unpair.2)))
    interInput_computes (fun z => by simp [Encodable.encode,Encodable.encodeSigma])
  have hb : LambdaRelative.DecidablePredicate ε (fun z : ℕ =>
      Nat.pair z.unpair.1.unpair.2 z.unpair.2 < (NatListCode.decode z.unpair.1.unpair.1.unpair.2).length) := by
    apply numericalDecision interBound_computes ε
    · intro z h; simp [h]
    · intro z h; simp [h]
  have hp : LambdaRelative.DecidablePredicate ε (fun z : ℕ =>
      Nat.pair z.unpair.1.unpair.2 z.unpair.2 < (NatListCode.decode z.unpair.1.unpair.1.unpair.2).length →
      ((NatListCode.decode z.unpair.1.unpair.1.unpair.1).take z.unpair.2,
        witnessRow (NatListCode.decode z.unpair.1.unpair.1.unpair.2) z.unpair.1.unpair.2 z.unpair.2)
          ∈ (T z.unpair.1.unpair.2).tree) := by
    convert (hb.and hc.not).not using 1
    funext z
    exact propext (by tauto)
  have hinner := hp.boundedAll (listLength_computes.comp (computes_codeFirst (projection_computes true)))
  have houter := hinner.boundedAll (listLength_computes.comp (projection_computes true))
  have h := houter.precompNumerical (g := fun z : List ℕ × List ℕ => Encodable.encode z)
    numericalIdentity_computes (fun z => rfl)
  unfold interTest
  simpa only [Nat.unpair_pair,Encodable.encode,NatListCode.decode_encode,ite_true,Bool.false_eq_true,ite_false] using h

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Uniform countable intersections
-/
def interTree {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree)) : PairTree ε :=
  finiteCheckTree (interTest (fun i => (T i).tree)) (interTest_decidable T hT)

theorem pairTreeBody_interTree {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree))
    (x q : ℕ → ℕ) :
    (x,q) ∈ pairTreeBody (interTree T hT).tree ↔
      ∀ i, (x,fun j => q (Nat.pair i j)) ∈ pairTreeBody (T i).tree := by
  change (x,q) ∈ pairTreeBody (finiteCheckNodes _) ↔ _
  rw [pairTreeBody_finiteCheckNodes]
  constructor
  · intro h i k
    let n := Nat.pair i k + i + k + 1
    have hi : i < n := by omega
    have hk : k < n := by omega
    have hp : Nat.pair i k < n := by omega
    have hn := h n i (by simpa [seqPrefix_length] using hi) k
      (by simpa [seqPrefix_length] using hk) (by simpa [seqPrefix_length] using hp)
    simpa only [seqPrefix_take_of_le x hk.le,witnessRow_prefix q i k n hp] using hn
  · intro h n i hi k hk hp
    simp only [seqPrefix_length] at hi hk hp
    simpa only [seqPrefix_take_of_le x hk.le,witnessRow_prefix q i k n hp] using h i k

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Apply the finite-test construction to
    $$\begin{aligned}
    R(s,v)\quad\Longleftrightarrow\quad
     &\forall i<|s|\ \forall k<|s|,\\
     &\NatPair{i}{k}<|v|\ \Longrightarrow
     (\restrict{s}{k},\WitnessRow{v}{i}{k})\in T_i.
    \end{aligned}$$
    Finite tabulation computes the row, and two bounded products decide the two finite universal quantifiers.
    The concrete terms are given in §{sec:lambda-projection-programs}. Every call uses the original
    parameter. Suppose all prefix tests pass. For any $i,k$, choose
    $n=\NatPair{i}{k}+i+k+1$. The length-$n$ test includes this pair of indices and its guard holds.
    The row identity then gives the required length-$k$ node in $T_i$. Conversely, if every row is a witness,
    that identity verifies each guarded finite test. This proves the body identity.

    For the projection identity, each row of a new witness gives a witness in its corresponding tree.
    Conversely, choose witnesses $q_i$ for a point in every projection and define
    $q(\NatPair{i}{j})=q_i(j)$. Pairing is a bijection, so this defines a single sequence with exactly those
    rows. This use of countable choice proves existence; it does not assert a computable selection of witnesses.
    The case $k=0$ is tested at a sufficiently long prefix for every $i$, so an empty component tree also
    makes the new body empty.
    \end{proof}
-/
theorem pairTreeProjection_interTree {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree)) :
    pairTreeProjection (interTree T hT).tree = ⋂ i, pairTreeProjection (T i).tree := by
  ext x
  constructor
  · rintro ⟨q,hq⟩
    exact mem_iInter.mpr fun i => ⟨_,(pairTreeBody_interTree T hT x q).mp hq i⟩
  · intro hx
    have hh : ∀ i, ∃ q, (x,q) ∈ pairTreeBody (T i).tree := fun i => mem_iInter.mp hx i
    choose q hq using hh
    let r : ℕ → ℕ := fun n => q n.unpair.1 n.unpair.2
    refine ⟨r,(pairTreeBody_interTree T hT x r).mpr ?_⟩
    intro i
    simpa only [r,Nat.unpair_pair] using hq i

theorem projected_uniform_iInter {ε : ℕ → ℕ} (T : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree)) :
    Projected ε (⋂ i, pairTreeProjection (T i).tree) :=
  ⟨interTree T hT,(pairTreeProjection_interTree T hT).symm⟩

/-- Both a set and its complement have relative pair-tree presentations. -/
def Complemented (ε : ℕ → ℕ) (A : Set (ℕ → ℕ)) : Prop := Projected ε A ∧ Projected ε Aᶜ

theorem Complemented.measurableSet {ε : ℕ → ℕ} {A : Set (ℕ → ℕ)} (h : Complemented ε A) :
    MeasurableSet A := h.1.analyticSet.measurableSet_of_compl h.2.analyticSet

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: corollary
  title: Uniform presentations of sets and complements
-/
theorem complemented_uniform_iUnion {ε : ℕ → ℕ} (T S : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree))
    (hS : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (S z.1).tree))
    (hc : ∀ i, pairTreeProjection (S i).tree = (pairTreeProjection (T i).tree)ᶜ) :
    Complemented ε (⋃ i, pairTreeProjection (T i).tree) := by
  refine ⟨projected_uniform_iUnion T hT,?_⟩
  simpa only [hc,Set.compl_iUnion] using projected_uniform_iInter S hS

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Apply the two constructions to the two families and use De Morgan's identities. A relative pair-tree
    projection is analytic, so each resulting set and its complement are analytic. The Suslin theorem gives
    Borelness. This argument gives relative tree presentations; it does not yet construct effective Borel
    codes or a uniform effective separator.
    \end{proof}
-/
theorem complemented_uniform_iInter {ε : ℕ → ℕ} (T S : ℕ → PairTree ε)
    (hT : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (T z.1).tree))
    (hS : LambdaRelative.DecidablePredicate ε (fun z : ℕ × (List ℕ × List ℕ) => z.2 ∈ (S z.1).tree))
    (hc : ∀ i, pairTreeProjection (S i).tree = (pairTreeProjection (T i).tree)ᶜ) :
    Complemented ε (⋂ i, pairTreeProjection (T i).tree) := by
  refine ⟨projected_uniform_iInter T hT,?_⟩
  simpa only [hc,Set.compl_iInter] using projected_uniform_iUnion S hS
end LambdaTree
end PolishSpaceBook
