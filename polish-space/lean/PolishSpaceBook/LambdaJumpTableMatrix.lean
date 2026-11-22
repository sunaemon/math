module

public import PolishSpaceBook.LambdaJumpTables
public import PolishSpaceBook.LambdaArithmeticNormalForm

@[expose] public section

/-! # A finite-quantifier matrix for jump-table witnesses -/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace KleeneNotation
open LambdaRelative LambdaTree
set_option maxHeartbeats 1000000

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Decode $\nu=\NatPair{b}{\NatPair{n}{\NatPair{p}{c}}}$ and
    $c=\NatPair{i}{s}$. Define $M(q,\nu,j)$ as the conjunction of the following six tests:
    $$\begin{aligned}
    &G_b(n)\in\{0,1\};\\
    &p\in D,\ \mathcal C(p,\NatPair{b}{c})\ \Longrightarrow\ b\in D;\\
    &1\in D\ \Longrightarrow\ G_1(n)=0;\\
    &b>0,\ 2^b\in D,\ G_{2^b}(n)=1\ \Longrightarrow\ \mathcal B(G_b,n,n,j)=1;\\
    &b>0,\ 2^b\in D,\ \mathcal B(G_b,n,n,c)=1\ \Longrightarrow\ G_{2^b}(n)=1;\\
    &3\cdot5^p\in D,\ \mathcal E(p,i,b,s)=1\ \Longrightarrow\ G_{3\cdot5^p}(\NatPair{i}{n})=G_b(n).
    \end{aligned}$$
    The same field $c$ can serve different roles in different tests: universal quantification over $\nu$
    ranges over every quadruple $b,n,p,c$.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We give the arithmetic predicate needed in §{sec:edst-hyperarithmetic-inclusion} explicitly.
    Decode a sequence $q$ into
    $$D:=\{b:\NatProjection{1}{q(b)}=1\},\qquad G_b(n):=\NatProjection{2}{q(\NatPair{b}{n})}.$$
    The predicate $J_\emptyset(q)$ requires all row entries to be bits, downward closure of $D$ under
    certified candidate steps, a zero row at notation $1$, jump rows at successors, and joined rows at
    certified limit outputs. Use the certificate predicate $\mathcal C$ of §{sec:lambda-certified-descent}.
    Write $\mathcal B(g,e,n,k)$ for the zero-or-one output of $\LambdaQueryOutputCandidate$ with input function $g$
    and numerical arguments $e,n,k$, and write $\mathcal E(e,i,b,s)$ for the output of $\LambdaOutputTest$.
    Both tests terminate for every input; no indexed computation is run to completion.
-/
def jumpTableMatrix (q : ℕ → ℕ) (t j : ℕ) : Prop :=
  let b := t.unpair.1
  let n := t.unpair.2.unpair.1
  let p := t.unpair.2.unpair.2.unpair.1
  let c := t.unpair.2.unpair.2.unpair.2
  (tableRow q b n = 0 ∨ tableRow q b n = 1) ∧
  (tableDomain q p → edgeCertificate (Nat.pair p (Nat.pair b c)) → tableDomain q b) ∧
  (tableDomain q 1 → tableRow q 1 n = 0) ∧
  (0 < b → tableDomain q (successorCode b) → tableRow q (successorCode b) n = 1 →
    Term.oracleOutputCandidate (tableRow q b) n n j = true) ∧
  (0 < b → tableDomain q (successorCode b) → Term.oracleOutputCandidate (tableRow q b) n n c = true →
    tableRow q (successorCode b) n = 1) ∧
  (tableDomain q (limitCode p) → Term.outputTest p c.unpair.1 b c.unpair.2 = true →
    tableRow q (limitCode p) (Nat.pair c.unpair.1 n) = tableRow q b n)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    If $J_\emptyset(q)$ holds, choose $j$ as a halting certificate when the fourth antecedent holds;
    otherwise choose zero. All other clauses follow directly from the table conditions. Conversely, every
    quadruple occurs as a decoded $\nu$. The fourth and fifth clauses together say exactly that a successor
    bit is one if and only if some finite halting certificate exists. The other clauses recover the remaining
    table conditions. This proves the equivalence, so two number quantifiers applied to the total matrix
    make $J_\emptyset$ arithmetical.
    \end{proof}
-/
theorem jumpTable_iff_matrix (q : ℕ → ℕ) : JumpTable ∅ q ↔ ∀ t, ∃ j, jumpTableMatrix q t j := by
  classical
  constructor
  · intro h t
    let b := t.unpair.1
    let n := t.unpair.2.unpair.1
    let p := t.unpair.2.unpair.2.unpair.1
    let c := t.unpair.2.unpair.2.unpair.2
    have hx : ∃ j, (0 < b → tableDomain q (successorCode b) → tableRow q (successorCode b) n = 1 →
        Term.oracleOutputCandidate (tableRow q b) n n j = true) := by
      by_cases hg : 0 < b ∧ tableDomain q (successorCode b) ∧ tableRow q (successorCode b) n = 1
      · obtain ⟨j,hj⟩ := (mem_jump_iff_candidates _ _).mp ((h.succ b hg.1 hg.2.1 n).mp hg.2.2)
        exact ⟨j,fun _ _ _ => hj⟩
      · exact ⟨0,fun hb hd hv => (hg ⟨hb,hd,hv⟩).elim⟩
    obtain ⟨j,hj⟩ := hx
    refine ⟨j,h.bits b n,h.down p b c,?_,hj,?_,fun hd ht => h.limit p c.unpair.1 b c.unpair.2 hd ht n⟩
    · intro hd
      simpa [characteristic] using h.zero hd n
    · intro hb hd hc
      exact (h.succ b hb hd n).mpr ((mem_jump_iff_candidates _ _).mpr ⟨c,hc⟩)
  · intro h
    have hex (b n p c : ℕ) := h (Nat.pair b (Nat.pair n (Nat.pair p c)))
    simp only [jumpTableMatrix,Nat.unpair_pair] at hex
    constructor
    · intro b n
      obtain ⟨_,hc⟩ := hex b n 0 0
      exact hc.1
    · intro p b c hd he
      obtain ⟨_,hc⟩ := hex b 0 p c
      exact hc.2.1 hd he
    · intro hd n
      obtain ⟨_,hc⟩ := hex 0 n 0 0
      simpa [characteristic] using hc.2.2.1 hd
    · intro b hb hd n
      constructor
      · intro hv
        obtain ⟨j,hc⟩ := hex b n 0 0
        exact (mem_jump_iff_candidates _ _).mpr ⟨j,hc.2.2.2.1 hb hd hv⟩
      · intro hn
        obtain ⟨c,hc⟩ := (mem_jump_iff_candidates _ _).mp hn
        obtain ⟨_,ht⟩ := hex b n 0 c
        exact ht.2.2.2.2.1 hb hd hc
    · intro e i b s hd ht m
      obtain ⟨_,hc⟩ := hex b m e (Nat.pair i s)
      simpa only [Nat.unpair_pair] using hc.2.2.2.2.2 hd (by simpa using ht)

/-- Read the original table after the two numerical quantifiers have been bound. -/
def matrixTable (p : ℕ → ℕ) := rightBaire (rightBaire (rightBaire p))
def matrixTrial (p : ℕ → ℕ) := leftBaire (rightBaire (rightBaire p)) 0
def matrixWitness (p : ℕ → ℕ) := leftBaire (rightBaire p) 0

theorem uniform_decidable_precomp {R : (ℕ → ℕ) → ℕ → Prop}
    (hR : UniformDecidablePredicate R) {F : AlphaTerm} {f : (ℕ → ℕ) → ℕ → ℕ}
    (hF : UniformNumericalComputes F f) : UniformDecidablePredicate (fun p n => R p (f p n)) := by
  obtain ⟨P,hP⟩ := hR
  exact ⟨relativeComposeProgram P F,fun p => (hP p).precomp ⟨hF.1,hF.2 p⟩⟩

theorem fixed_decider_uniform {R : ℕ → Prop} (hR : DecidablePredicate (fun _ => 0) R) :
    UniformDecidablePredicate (fun _ n => R n) := by
  obtain ⟨P,hP⟩ := hR
  exact ⟨compositionProgram P (constantProgram 0),fun p => hP.changeParameter
    ⟨(uniform_constant 0).1,(uniform_constant 0).2 p⟩⟩

/-- All numerical fields are read from the bound trial number, never from a validity test. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    \begin{mathmeta}
      \define{JumpTupleBody}
    \end{mathmeta}
    On input $o=\NamePair{\varepsilon}{\NumberBinding{j}{\NumberBinding{\nu}{q}}}$, use the finite term bodies
    $$\begin{aligned}
    \LambdaTermName{table}(o,k)&:= \LambdaNumericProjection{2}( \LambdaNumericProjection{2}(
    \LambdaNumericProjection{2}(ok))),\\
    \JumpTupleBody{o}&:= \LambdaNumericProjection{1}( \LambdaNumericProjection{2}( \LambdaNumericProjection{2}(o
    \ChurchNumeral{0}))), \qquad
     \LambdaTermName{bound}(o):=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}(o\ChurchNumeral{0})),\\
    \LambdaTermName{domainBit}(o,b)&:=\LambdaNumericProjection{1}(\LambdaTermName{table}(o,b)),\\
    \LambdaTermName{row}(o,b)&:= \lambdaab{m}{ \LambdaNumericProjection{2}( \LambdaTermName{table}(o,
    \LambdaNumericPair\,b\,m))}.
    \end{aligned}$$
    Expand these abbreviations and abstract all free variables using fresh binders. They read $q(k)$, the
    bound numbers, the domain entry, and the row input function. Further numerical projections of $\JumpTupleBody{o}$
    supply the fields $b,n,p,c$. Powers, equality, ordering, and the finite checkers already have total
    closed programs. Substituting $\LambdaTermName{row}(o,b)$ into the input position of $\LambdaQueryOutputCandidate$
    therefore computes both successor tests, even though the row number depends on the input.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For terms $\LambdaTermName{left}, \LambdaTermName{right}$ representing decision bits, use multiplication for
    conjunction and the term bodies
    $$\begin{aligned}
    \LambdaTermName{not}( \LambdaTermName{left})&:= \LambdaZeroTest\, \LambdaTermName{left}\, \ChurchNumeral{1}\,
    \ChurchNumeral{0},\\
    \LambdaTermName{orBits}( \LambdaTermName{left}, \LambdaTermName{right})&:= \LambdaTermName{not}( \LambdaMul\,(
    \LambdaTermName{not}(
    \LambdaTermName{left}))\,( \LambdaTermName{not}( \LambdaTermName{right}))), \qquad  \LambdaTermName{implies}(
    \LambdaTermName{left}, \LambdaTermName{right}):=
    \LambdaTermName{orBits}( \LambdaTermName{not}( \LambdaTermName{left}), \LambdaTermName{right})
    \end{aligned}$$
    for negation, disjunction, and implication. Combining the six tests gives one closed decision program.
    Every component has a finite beta/query derivation on every input, and composition preserves those
    outputs. The program ignores $\varepsilon$; no validity test is hidden in it.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We give the arithmetic predicate needed in §{sec:edst-hyperarithmetic-inclusion} explicitly.
    Decode a sequence $q$ into
    $$D:=\{b:\NatProjection{1}{q(b)}=1\},\qquad G_b(n):=\NatProjection{2}{q(\NatPair{b}{n})}.$$
    The predicate $J_\emptyset(q)$ requires all row entries to be bits, downward closure of $D$ under
    certified candidate steps, a zero row at notation $1$, jump rows at successors, and joined rows at
    certified limit outputs. Use the certificate predicate $\mathcal C$ of §{sec:lambda-certified-descent}.
    Write $\mathcal B(g,e,n,k)$ for the zero-or-one output of $\LambdaQueryOutputCandidate$ with input function $g$
    and numerical arguments $e,n,k$, and write $\mathcal E(e,i,b,s)$ for the output of $\LambdaOutputTest$.
    Both tests terminate for every input; no indexed computation is run to completion.
-/
theorem matrix_uniform : UniformDecidablePredicate
    (fun p (_ : ℕ) => jumpTableMatrix (matrixTable p) (matrixTrial p) (matrixWitness p)) := by
  have right := projection_computes false
  have left := projection_computes true
  have query := numericalIdentity_computes.uniform.query
  have query0 := (uniform_constant 0).query
  have q := query.map (right.comp (right.comp right))
  have t := query0.map (left.comp (right.comp right))
  have j := query0.map (left.comp right)
  have b := t.map left
  have n := t.map (left.comp right)
  have p := t.map (left.comp (right.comp right))
  have c := t.map (right.comp (right.comp right))
  have ci := c.map left
  have cs := c.map right
  have one := uniform_constant 1
  have zero := uniform_constant 0
  have row := (q.comp (b.pair n)).map right
  have domainB := (q.comp b).map left
  have domainP := (q.comp p).map left
  have domainOne := (q.comp one).map left
  have rowOne := (q.comp (one.pair n)).map right
  have succB := b.map powerTwo_computes
  have domainSucc := (q.comp succB).map left
  have rowSucc := (q.comp (succB.pair n)).map right
  have limP := p.map limitCodeProgram_computes
  have domainLim := (q.comp limP).map left
  have rowLim := (q.comp (limP.pair (ci.pair n))).map right
  have rowAccessor := (q.comp (b.pair numericalIdentity_computes.uniform)).map right
  have posTest := (jointCandidateProgram_computes.changeInput rowAccessor).comp (n.pair (n.pair j))
  have negTest := (jointCandidateProgram_computes.changeInput rowAccessor).comp (n.pair (n.pair c))
  have limitTest := candidateTupleProgram_computes.uniform.comp (p.pair (ci.pair (b.pair cs)))
  have edgeTest := uniform_decidable_precomp (fixed_decider_uniform (edgeCertificate_decidable (fun _ => 0)))
    (p.pair (b.pair c))
  have bits := (UniformDecidablePredicate.eq row zero).or (UniformDecidablePredicate.eq row one)
  have down := (UniformDecidablePredicate.eq domainP one).imp
    (edgeTest.imp (UniformDecidablePredicate.eq domainB one))
  have base := (UniformDecidablePredicate.eq domainOne one).imp (UniformDecidablePredicate.eq rowOne zero)
  have positive := (UniformDecidablePredicate.le one b).imp
    ((UniformDecidablePredicate.eq domainSucc one).imp
      ((UniformDecidablePredicate.eq rowSucc one).imp (UniformDecidablePredicate.eq posTest one)))
  have negative := (UniformDecidablePredicate.le one b).imp
    ((UniformDecidablePredicate.eq domainSucc one).imp
      ((UniformDecidablePredicate.eq negTest one).imp (UniformDecidablePredicate.eq rowSucc one)))
  have limit := (UniformDecidablePredicate.eq domainLim one).imp
    ((UniformDecidablePredicate.eq limitTest one).imp (UniformDecidablePredicate.eq rowLim row))
  have result := bits.and (down.and (base.and (positive.and (negative.and limit))))
  unfold jumpTableMatrix matrixTable matrixTrial matrixWitness tableRow tableDomain leftBaire rightBaire
  simpa [jumpTableMatrix,matrixTable,matrixTrial,matrixWitness,tableRow,tableDomain,
    leftBaire,rightBaire,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false,successorCode,
    Term.outputCandidate,ite_eq_left_iff,zero_ne_one,imp_false,not_not,Nat.succ_le_iff] using result

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: A total matrix for jump tables
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    Write $J_A(q)$ for these conditions. They do not require $D$ to consist of valid notations.
    When $A=\emptyset$, the predicate $J_\emptyset(q)$ is arithmetical: every computation in the conditions
    has a finite certificate, and only natural-number quantifiers remain.
    §{sec:lambda-certified-descent} supplies a total lambda matrix for this assertion.
-/
theorem jumpTables_arithmetical (ε : ℕ → ℕ) : ArithmeticalSet ε {q | JumpTable ∅ q} := by
  obtain ⟨P,hP⟩ := matrix_uniform
  let B : Set (ℕ → ℕ) := {y | jumpTableMatrix (rightBaire (rightBaire y))
    (leftBaire (rightBaire y) 0) (leftBaire y 0)}
  have hB : ArithmeticalSet ε B := .atom B P (fun y => by
    simpa only [matrixTable,matrixTrial,matrixWitness,rightBaire_pair,B,Set.mem_ofPred_eq]
      using hP (pairBaire ε y))
  have h := hB.existsNumber.forallNumber
  have he : {q | ∀ t, ∃ j, bindNumber j (bindNumber t q) ∈ B} = {q | JumpTable ∅ q} := by
    ext q
    simp only [Set.mem_ofPred_eq,B,rightBaire_bindNumber,leftBaire_bindNumber]
    exact (jumpTable_iff_matrix q).symm
  exact he ▸ h

end KleeneNotation
end PolishSpaceBook
