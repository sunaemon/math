module

public import PolishSpaceBook.LambdaJumpTableMatrix

@[expose] public section

/-! # Sets computed from iterated jumps are effectively ambiguous

A positive or negative answer is witnessed by one jump table and one finite
beta/query certificate. The construction never decides membership in Kleene O.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace KleeneNotation
open LambdaRelative LambdaTree
set_option maxHeartbeats 1000000

/-- One finite output test on a designated table row. -/
def tableOutput (a e v : ℕ) (z : ℕ → ℕ) (s : ℕ) : Prop :=
  tableDomain (rightBaire z) a ∧
    Term.oracleOutputCandidate (tableRow (rightBaire z) a) e (leftBaire z 0) (Nat.pair v s) = true

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For the last output certificate in §{sec:edst-hyperarithmetic-inclusion}, fix $a,e,v$ and use
    $o=\NamePair{\varepsilon}{\NamePair{x}{q}}$. Put
    $$\begin{aligned}
    \LambdaTermName{outTable}(o,k)&:= \LambdaNumericProjection{2}( \LambdaNumericProjection{2}(ok)), \qquad
    \LambdaTermName{outInput}(o):= \LambdaNumericProjection{1}( \LambdaNumericProjection{2}(o \ChurchNumeral{0})),\\
    \LambdaTermName{outRow}(o)&:= \lambdaab{m}{ \LambdaNumericProjection{2}( \LambdaTermName{outTable}(o,
    \LambdaNumericPair\, \ChurchNumeral{a}\,m))},\\
    \LambdaTermName{outputCert}&:=\lambdaab{o}{\lambdaab{s}{\LambdaQueryOutputCandidate\,(\LambdaTermName{outRow}(o))\,
     \ChurchNumeral{e}\,(\LambdaTermName{outInput}(o))\,(\LambdaNumericPair\,\ChurchNumeral{v}\,s)}}.
    \end{aligned}$$
    Conjoin its output bit with the test $\LambdaNumericProjection{1}( \LambdaTermName{outTable}(o,
    \ChurchNumeral{a}))=1$ for domain membership.
    The same substitution and query equations show that this is a total checker for a finite computation
    of $P_e$ on $x(0)$ with input function $G_a$ and output $v$. Existentially quantify its numerical
    certificate, intersect with the table predicate, and project out $q$. This supplies the recursive pair
    trees for both answers in the theorem.
-/
theorem tableOutput_uniform (a e v : ℕ) : UniformDecidablePredicate
    (fun p s => tableOutput a e v (rightBaire p) s) := by
  have right := projection_computes false
  have left := projection_computes true
  have query := numericalIdentity_computes.uniform.query
  have q := query.map (right.comp right)
  have n := (uniform_constant 0).query.map (left.comp right)
  have aa := uniform_constant a
  have domain := (q.comp aa).map left
  have row := (q.comp (aa.pair numericalIdentity_computes.uniform)).map right
  have test := (jointCandidateProgram_computes.changeInput row).comp
    ((uniform_constant e).pair (n.pair ((uniform_constant v).pair numericalIdentity_computes.uniform)))
  have h := (UniformDecidablePredicate.eq domain (uniform_constant 1)).and
    (UniformDecidablePredicate.eq test (uniform_constant 1))
  unfold tableOutput tableDomain tableRow leftBaire rightBaire
  simpa using h

theorem tableOutput_projected (ε : ℕ → ℕ) (a e v : ℕ) :
    Projected ε {x | ∃ q, JumpTable ∅ q ∧ ∃ s, tableOutput a e v (pairBaire x q) s} := by
  have hu := (tableOutput_uniform a e v).precompNumerical
    (projection_computes true) (g := fun z : ℕ => z.unpair.1) (by simp)
  obtain ⟨P,hP⟩ := hu
  have hS : Projected ε {z | ∃ s, tableOutput a e v z s} := by
    have hh := projected_exists_forall_baire (R := fun z s (_ : ℕ) => tableOutput a e v z s)
      (P := P) (ε := ε) (fun z => by simpa only [rightBaire_pair] using hP (pairBaire ε z))
    simpa only [forall_const] using hh
  have hh := ((jumpTables_arithmetical ε).complemented.1.rightPreimage.inter hS).projectLeft
  convert hh using 1
  ext x
  constructor
  · rintro ⟨q,hq,s,hs⟩
    exact ⟨pairBaire x q,⟨by simpa using hq,⟨s,hs⟩⟩,by simp⟩
  · rintro ⟨z,⟨hq,hs⟩,rfl⟩
    exact ⟨rightBaire z,hq,by simpa using hs⟩

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $a\in\KleeneO$ and let $P_e$ compute $\chi_B$ from $\chi_{\IteratedJump{\emptyset}{a}}$.
    For $v\in\{0,1\}$, the equation $\chi_B(n)=v$ is equivalent to the existence of a table $q$ with
    $J_\emptyset(q)$ and $a\in D$, together with a finite beta/query certificate that $P_e$, using row $G_a$,
    returns $\ChurchNumeral{v}$ on input $n$. In one direction use the table constructed in the lemma and
    termination of $P_e$. In the other, row uniqueness supplies the intended input function, and uniqueness
    of numerical output gives the required bit.
-/
theorem tableOutput_iff (a : ℕ) (ha : Valid a) (e n v : ℕ) :
    (∃ q, JumpTable ∅ q ∧ ∃ s, tableDomain q a ∧
      Term.oracleOutputCandidate (tableRow q a) e n (Nat.pair v s) = true) ↔
    OracleRuns (characteristic (iteratedJump ∅ a ha)) (Term.closedProgram e) n v := by
  constructor
  · rintro ⟨q,hq,s,hd,hs⟩
    rw [hq.row_unique a ha hd] at hs
    apply (oracle_outputTest_exists_iff _ e n v).mp
    exact ⟨s,by simpa only [Term.oracleOutputCandidate,Nat.unpair_pair] using hs⟩
  · intro hr
    obtain ⟨s,hs⟩ := (oracle_outputTest_exists_iff _ e n v).mpr hr
    refine ⟨canonicalJumpTable ∅,canonicalJumpTable_spec ∅,s,
      (canonicalJumpTable_domain ∅ a).mpr ha,?_⟩
    have hrow := funext (canonicalJumpTable_row ∅ a ha)
    rw [hrow]
    simpa only [Term.oracleOutputCandidate,Nat.unpair_pair] using hs

/-- A numerical predicate is represented on Baire space by its zeroth coordinate. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    The predicate after $\exists q$ is arithmetical. §{sec:lambda-certified-descent} gives a
    uniform finite checker for the last certificate as well. The arithmetic pair-tree normal form therefore
    gives a recursive tree presentation for each bit. Taking $v=1$ presents $B$ and taking $v=0$ presents
    $\SetDifference{\NN}{B}$. For the Baire-space definition of the pointclasses, apply the same construction to
    $\{x\in\BaireSpace:x(0)\in B\}$. Hence $B\in\lSigma^1_1\cap\lPi^1_1=\lDelta^1_1$.
    \end{proof}
-/
theorem iteratedJump_output_projected (ε : ℕ → ℕ) (a : ℕ) (ha : Valid a) (e v : ℕ) :
    Projected ε {x | OracleRuns (characteristic (iteratedJump ∅ a ha)) (Term.closedProgram e) (x 0) v} := by
  have hh := tableOutput_projected ε a e v
  have he : {x | ∃ q, JumpTable ∅ q ∧ ∃ s, tableOutput a e v (pairBaire x q) s} =
      {x | OracleRuns (characteristic (iteratedJump ∅ a ha)) (Term.closedProgram e) (x 0) v} := by
    ext x
    simp only [Set.mem_ofPred_eq,tableOutput,rightBaire_pair,leftBaire_pair]
    exact tableOutput_iff a ha e (x 0) v
  exact he ▸ hh

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    The \termdefineas{hyperarithmetic set}{hyperarithmetic} sets $\HyperarithmeticalSets$ are the subsets of the
    natural numbers computable from $\IteratedJump{\emptyset}{a}$ for some $a\in\KleeneO$.
-/
def Hyperarithmetic (B : Set ℕ) : Prop :=
  ∃ a, ∃ ha : Valid a, Computable (characteristic (iteratedJump ∅ a ha)) (characteristic B)

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: theorem
  title: Hyperarithmetic inclusion
-/
theorem hyperarithmetic_complemented {B : Set ℕ} (hB : Hyperarithmetic B) :
    Complemented (fun _ => 0) {x | x 0 ∈ B} := by
  classical
  obtain ⟨a,ha,P,hP⟩ := hB
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP.1
  have equiv (v : ℕ) (n : ℕ) :
      OracleRuns (characteristic (iteratedJump ∅ a ha)) (Term.closedProgram e) n v ↔
      characteristic B n = v := by
    rw [he]
    constructor
    · intro hr
      exact (hP.2 n).output_unique hr
    · intro hv
      simpa only [Encodable.encode_nat,hv] using hP.2 n
  constructor
  · convert iteratedJump_output_projected (fun _ => 0) a ha e 1 using 1
    ext x
    simp only [Set.mem_ofPred_eq,equiv]
    simp [characteristic]
  · convert iteratedJump_output_projected (fun _ => 0) a ha e 0 using 1
    ext x
    simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,equiv]
    simp [characteristic]

end KleeneNotation
end PolishSpaceBook
