module

public import PolishSpaceBook.LambdaProgramTotality
public import PolishSpaceBook.LambdaRelativeIndices

@[expose] public section

/-! # The jump of a parameter, using lambda program indices

A finite-certificate search semidecides diagonal numerical halting. Its
complement cannot be a numerical halting domain. A fixed program template
also reduces every parameter bit to its jump; its index map is computed by
a closed numerical lambda term.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
set_option maxHeartbeats 800000
namespace LambdaRelative

/-- Diagonal numerical halting in the book's enumeration of closed terms. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    **The jump.** For $A\IncludedIn\omega$, write $\chi_A(n)=1$ if $n\in A$ and $\chi_A(n)=0$ otherwise.
    The \termdefine{Turing jump} is
    $$A':=\{e\in\omega:\varphi_e^A(e)\downarrow\},$$
    where $\varphi_e^A$ is the partial numerical function of the closed lambda program $P_e$, with access to
    $\chi_A$. Here halting means returning a Church numeral by finitely many beta/query steps; reaching an
    arbitrary normal form is not enough.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: prose
  excerpt: |
    For an arbitrary numerical parameter $\varepsilon$, let $K^\varepsilon$ be the set of indices whose
    programs return a numeral on their own index with input function $\varepsilon$, and put
    $\varepsilon':=\chi_{K^\varepsilon}$. Thus $(\chi_A)'=\chi_{A'}$.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix an arbitrary parameter $\varepsilon:\NN\to\NN$ and put
    $$K^\varepsilon:=\{e:\exists m\;\LambdaInputSteps{\varepsilon}{P_eo\ChurchNumeral{e}}{\ChurchNumeral{m}}\}.$$
    For $A\IncludedIn\NN$, let $\chi_A$ be one on $A$ and zero outside $A$.
    Thus $K^\varepsilon$ records numerical halting on the program's own index. When $\varepsilon=\chi_A$, it is
    $A'$ from §{sec:hyperarithmetic-hierarchy}. Write $p_i:=\LambdaNumericProjection{i}$. With fresh binders, set
    $$\begin{aligned}
    T&:=\lambdaab{o}{\lambdaab{z}{\LambdaQueryOutputCandidate\,o\,(p_1z)\,(p_1z)\,(p_2z)}},\\
    J&:=\LambdaRelativeSearch{T}.
    \end{aligned}$$
    The paired input of $T$ is $\NatPair{e}{k}$, where $k$ codes an output candidate and a finite certificate bound.
    Each trial terminates for every parameter and every input.
-/
def Jump (ε : ℕ → ℕ) : Set ℕ :=
  {e | ∃ m, OracleRuns ε (Term.closedProgram e) e m}

theorem mem_jump_iff_candidates (ε : ℕ → ℕ) (e : ℕ) :
    e ∈ Jump ε ↔ ∃ k, Term.oracleOutputCandidate ε e e k = true := by
  simpa only [Jump,Set.mem_ofPred_eq,candidateTest,Nat.unpair_pair] using (candidateTest_exists_iff ε e e).symm

end LambdaRelative
namespace NamedLambda.AlphaTerm

/-- From (e,k), form the triple (e,(e,k)) for the joint finite checker. -/
def jumpTrialReindex : AlphaTerm := pairNumerical (numericalProjectionTerm true)
  (pairNumerical (numericalProjectionTerm true) (numericalProjectionTerm false))

theorem jumpTrialReindex_computes : NumericalComputes jumpTrialReindex
    (fun z => Nat.pair z.unpair.1 (Nat.pair z.unpair.1 z.unpair.2)) :=
  (projection_computes true).pair ((projection_computes true).pair (projection_computes false))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix an arbitrary parameter $\varepsilon:\NN\to\NN$ and put
    $$K^\varepsilon:=\{e:\exists m\;\LambdaInputSteps{\varepsilon}{P_eo\ChurchNumeral{e}}{\ChurchNumeral{m}}\}.$$
    For $A\IncludedIn\NN$, let $\chi_A$ be one on $A$ and zero outside $A$.
    Thus $K^\varepsilon$ records numerical halting on the program's own index. When $\varepsilon=\chi_A$, it is
    $A'$ from §{sec:hyperarithmetic-hierarchy}. Write $p_i:=\LambdaNumericProjection{i}$. With fresh binders, set
    $$\begin{aligned}
    T&:=\lambdaab{o}{\lambdaab{z}{\LambdaQueryOutputCandidate\,o\,(p_1z)\,(p_1z)\,(p_2z)}},\\
    J&:=\LambdaRelativeSearch{T}.
    \end{aligned}$$
    The paired input of $T$ is $\NatPair{e}{k}$, where $k$ codes an output candidate and a finite certificate bound.
    Each trial terminates for every parameter and every input.
-/
def jumpTrialProgram : AlphaTerm := reindexProgram jointCandidateProgram jumpTrialReindex

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix an arbitrary parameter $\varepsilon:\NN\to\NN$ and put
    $$K^\varepsilon:=\{e:\exists m\;\LambdaInputSteps{\varepsilon}{P_eo\ChurchNumeral{e}}{\ChurchNumeral{m}}\}.$$
    For $A\IncludedIn\NN$, let $\chi_A$ be one on $A$ and zero outside $A$.
    Thus $K^\varepsilon$ records numerical halting on the program's own index. When $\varepsilon=\chi_A$, it is
    $A'$ from §{sec:hyperarithmetic-hierarchy}. Write $p_i:=\LambdaNumericProjection{i}$. With fresh binders, set
    $$\begin{aligned}
    T&:=\lambdaab{o}{\lambdaab{z}{\LambdaQueryOutputCandidate\,o\,(p_1z)\,(p_1z)\,(p_2z)}},\\
    J&:=\LambdaRelativeSearch{T}.
    \end{aligned}$$
    The paired input of $T$ is $\NatPair{e}{k}$, where $k$ codes an output candidate and a finite certificate bound.
    Each trial terminates for every parameter and every input.
-/
theorem jumpTrialProgram_computes : UniformNumericalComputes jumpTrialProgram
    (fun ε z => if Term.oracleOutputCandidate ε z.unpair.1 z.unpair.1 z.unpair.2 then 1 else 0) := by
  simpa only [jumpTrialProgram,Nat.unpair_pair] using jointCandidateProgram_computes.reindex jumpTrialReindex_computes

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Fix an arbitrary parameter $\varepsilon:\NN\to\NN$ and put
    $$K^\varepsilon:=\{e:\exists m\;\LambdaInputSteps{\varepsilon}{P_eo\ChurchNumeral{e}}{\ChurchNumeral{m}}\}.$$
    For $A\IncludedIn\NN$, let $\chi_A$ be one on $A$ and zero outside $A$.
    Thus $K^\varepsilon$ records numerical halting on the program's own index. When $\varepsilon=\chi_A$, it is
    $A'$ from §{sec:hyperarithmetic-hierarchy}. Write $p_i:=\LambdaNumericProjection{i}$. With fresh binders, set
    $$\begin{aligned}
    T&:=\lambdaab{o}{\lambdaab{z}{\LambdaQueryOutputCandidate\,o\,(p_1z)\,(p_1z)\,(p_2z)}},\\
    J&:=\LambdaRelativeSearch{T}.
    \end{aligned}$$
    The paired input of $T$ is $\NatPair{e}{k}$, where $k$ codes an output candidate and a finite certificate bound.
    Each trial terminates for every parameter and every input.
-/
def jumpProgram : AlphaTerm := relativeSearchProgram jumpTrialProgram

theorem jumpProgram_closed : jumpProgram.Closed :=
  relativeSearchProgram_closed jumpTrialProgram_computes.1

theorem jumpProgram_runs_iff (ε : ℕ → ℕ) (e m : ℕ) :
    OracleRuns ε jumpProgram e m ↔ m = 1 ∧ e ∈ LambdaRelative.Jump ε := by
  have h : LambdaRelative.Computes ε jumpTrialProgram
      (fun z : ℕ => if Term.oracleOutputCandidate ε z.unpair.1 z.unpair.1 z.unpair.2 then 1 else 0) :=
    ⟨jumpTrialProgram_computes.1,jumpTrialProgram_computes.2 ε⟩
  rw [jumpProgram,relativeSearchProgram_runs_iff h,LambdaRelative.mem_jump_iff_candidates]
  simp only [Nat.unpair_pair,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not]

/-- On paired input (n,t), halt exactly when the nth parameter value is nonzero. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To recover the original parameter bits, use the closed terms
    $$\begin{aligned}
    Q&:=\lambdaab{o}{\lambdaab{z}{o(p_1(p_1z))}},\qquad P:=\LambdaRelativeSearch{Q},\\
    S_n&:=\lambdaab{o}{\lambdaab{t}{Po(\LambdaNumericPair\,\ChurchNumeral{n}\,t)}}.
    \end{aligned}$$
    On input $\NatPair{\NatPair{n}{t}}{k}$, the trial $Q$ returns $\varepsilon(n)$ independently of $t,k$.
    Apply the syntax-code construction in §{sec:lambda-pair-tree-programs} to this fixed $P$: it gives
    an index $f(n)$ for $S_n$ and a closed numerical lambda term $F$ computing $f$.
    The same code construction applies to a partial program; totality was needed for the decision conclusion,
    not for constructing the specialized syntax. Both $F$ and $f$ are independent of $\varepsilon$.
-/
def parameterBitTrial : AlphaTerm := queryOutputProgram
  (liftNumericalProgram (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true)))

theorem parameterBitTrial_computes : UniformNumericalComputes parameterBitTrial
    (fun ε z => ε z.unpair.1.unpair.1) :=
  ((projection_computes true).comp (projection_computes true)).uniform.query

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To recover the original parameter bits, use the closed terms
    $$\begin{aligned}
    Q&:=\lambdaab{o}{\lambdaab{z}{o(p_1(p_1z))}},\qquad P:=\LambdaRelativeSearch{Q},\\
    S_n&:=\lambdaab{o}{\lambdaab{t}{Po(\LambdaNumericPair\,\ChurchNumeral{n}\,t)}}.
    \end{aligned}$$
    On input $\NatPair{\NatPair{n}{t}}{k}$, the trial $Q$ returns $\varepsilon(n)$ independently of $t,k$.
    Apply the syntax-code construction in §{sec:lambda-pair-tree-programs} to this fixed $P$: it gives
    an index $f(n)$ for $S_n$ and a closed numerical lambda term $F$ computing $f$.
    The same code construction applies to a partial program; totality was needed for the decision conclusion,
    not for constructing the specialized syntax. Both $F$ and $f$ are independent of $\varepsilon$.
-/
def parameterBitProgram : AlphaTerm := relativeSearchProgram parameterBitTrial

theorem parameterBitProgram_closed : parameterBitProgram.Closed :=
  relativeSearchProgram_closed parameterBitTrial_computes.1

theorem parameterBitProgram_runs_iff (ε : ℕ → ℕ) (n t m : ℕ) :
    OracleRuns ε parameterBitProgram (Nat.pair n t) m ↔ m = 1 ∧ ε n ≠ 0 := by
  have h : LambdaRelative.Computes ε parameterBitTrial (fun z : ℕ => ε z.unpair.1.unpair.1) :=
    ⟨parameterBitTrial_computes.1,parameterBitTrial_computes.2 ε⟩
  simp only [parameterBitProgram,relativeSearchProgram_runs_iff h,Nat.unpair_pair,exists_const]

end NamedLambda.AlphaTerm
namespace LambdaRelative

theorem jump_semidecidable (ε : ℕ → ℕ) : SemidecidablePredicate ε (· ∈ Jump ε) :=
  ⟨jumpProgram,jumpProgram_closed,fun e => by simpa using (jumpProgram_runs_iff ε e 1).symm⟩

theorem jump_complement_not_semidecidable (ε : ℕ → ℕ) :
    ¬ SemidecidablePredicate ε (fun e => e ∉ Jump ε) := by
  intro h
  obtain ⟨P,hP,hdom⟩ := (semidecidable_iff_domain ε _).mp h
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP
  have hdiag : e ∉ Jump ε ↔ e ∈ Jump ε := by
    simpa only [Jump,Set.mem_ofPred_eq,he,Encodable.encode_nat] using hdom e
  by_cases hmem : e ∈ Jump ε
  · exact (hdiag.mpr hmem) hmem
  · exact hmem (hdiag.mp hmem)

theorem jump_not_decidable (ε : ℕ → ℕ) : ¬ DecidablePredicate ε (· ∈ Jump ε) := by
  intro h
  exact jump_complement_not_semidecidable ε h.not.semidecidable

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Exact search for the relative jump
  excerpt: |
    The term $J$ returns one on input $e$ exactly when $e\in K^\varepsilon$, and it has no numerical output otherwise.
    The complement of $K^\varepsilon$ is not semidecidable relative to $\varepsilon$.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Numerical projections supply $e,e,k$ to the total candidate checker. Its soundness and completeness identify
    existence of a successful trial with $e\in K^\varepsilon$. The exact relative search lemma gives the asserted
    output and excludes every numerical output if all trials fail.

    Suppose the complement had an accepting program. By the acceptance/domain equivalence, it would have a
    closed program $D$ whose numerical halting domain is exactly that complement. Choose an index $d$ for $D$.
    The definition of $K^\varepsilon$ then gives $d\notin K^\varepsilon$ if and only if $d\in K^\varepsilon$.
    Both cases contradict this equivalence. A decider for $K^\varepsilon$ would semidecide its complement by
    reversing the output bit, so no such decider exists either.
    \end{proof}
-/
theorem relative_jump_search : jumpProgram.Closed ∧ ∀ ε : ℕ → ℕ,
    (∀ e m, OracleRuns ε jumpProgram e m ↔ m = 1 ∧ e ∈ Jump ε) ∧
    ¬ SemidecidablePredicate ε (fun e => e ∉ Jump ε) :=
  ⟨jumpProgram_closed,fun ε => ⟨jumpProgram_runs_iff ε,jump_complement_not_semidecidable ε⟩⟩

/-- One numerical index map, independent of the oracle, reduces its nonzero bits
 to diagonal halting. Existence of representatives is only fixed template data. -/
theorem parameterBits_reduce_to_jump :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F f ∧
      ∀ ε n, f n ∈ Jump ε ↔ ε n ≠ 0 := by
  obtain ⟨P,hP⟩ := Quotient.exists_rep parameterBitProgram
  obtain ⟨B,hB⟩ := Quotient.exists_rep numericalPairTerm
  change mk P = parameterBitProgram at hP
  change mk B = numericalPairTerm at hB
  refine ⟨pairSpecializationCodeProgram P.code B.code,pairSpecializationCode P.code B.code,
    pairSpecializationCode_computes _ _,?_⟩
  intro ε n
  have hc : (mk P).Closed := hP.symm ▸ parameterBitProgram_closed
  rw [Jump,Set.mem_ofPred_eq,Term.closedProgram_pairSpecializationCode P B hc hB,hP]
  simp only [specializePairProgram_runs_iff parameterBitProgram_closed,parameterBitProgram_runs_iff]
  simp

/-- The characteristic name uses one for membership and zero otherwise. -/
noncomputable def characteristic (A : Set ℕ) : ℕ → ℕ := by
  classical
  exact fun n => if n ∈ A then 1 else 0

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Recovering parameter bits from the jump
  excerpt: |
    For every $\varepsilon,n$, one has $f(n)\in K^\varepsilon$ if and only if $\varepsilon(n)\ne0$.
    In particular, for every $A\IncludedIn\NN$, the closed term
    $$\lambdaab{o}{\lambdaab{n}{o(Fn)}}$$
    computes $\chi_A$ with input function $\chi_{A'}$.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Every trial for $P$ on input $\NatPair{n}{t}$ has the same value $\varepsilon(n)$. The exact search theorem
    therefore says that $P$ returns one exactly when this value is nonzero, and has no numerical output otherwise.
    Two beta contractions and numerical pairing reduce the specialized program $S_n$ on input $t$ to this
    computation. Conversely, confluence carries any numeral output of $S_n$ to the reduced computation, because
    numerals are terminal. Thus specialization preserves both outputs and numerical nontermination.
    Apply this equivalence with $t=f(n)$ to obtain the first assertion. For a characteristic function, being
    nonzero means being one, so $\chi_{A'}(f(n))=\chi_A(n)$. The computation of $F$ followed by one input query
    proves the second assertion. No test of emptiness or choice of a terminating index is used.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To recover the original parameter bits, use the closed terms
    $$\begin{aligned}
    Q&:=\lambdaab{o}{\lambdaab{z}{o(p_1(p_1z))}},\qquad P:=\LambdaRelativeSearch{Q},\\
    S_n&:=\lambdaab{o}{\lambdaab{t}{Po(\LambdaNumericPair\,\ChurchNumeral{n}\,t)}}.
    \end{aligned}$$
    On input $\NatPair{\NatPair{n}{t}}{k}$, the trial $Q$ returns $\varepsilon(n)$ independently of $t,k$.
    Apply the syntax-code construction in §{sec:lambda-pair-tree-programs} to this fixed $P$: it gives
    an index $f(n)$ for $S_n$ and a closed numerical lambda term $F$ computing $f$.
    The same code construction applies to a partial program; totality was needed for the decision conclusion,
    not for constructing the specialized syntax. Both $F$ and $f$ are independent of $\varepsilon$.
-/
theorem parameter_recovery :
    ∃ (F : AlphaTerm) (f : ℕ → ℕ), NumericalComputes F f ∧
      (∀ ε n, f n ∈ Jump ε ↔ ε n ≠ 0) ∧
      ∀ A : Set ℕ, Computes (characteristic (Jump (characteristic A)))
        (queryOutputProgram (liftNumericalProgram F)) (characteristic A) := by
  classical
  obtain ⟨F,f,hF,hf⟩ := parameterBits_reduce_to_jump
  refine ⟨F,f,hF,hf,fun A => ?_⟩
  have h := hF.uniform.query
  refine ⟨h.1,fun n => ?_⟩
  have he : characteristic (Jump (characteristic A)) (f n) = characteristic A n := by
    simp only [characteristic,hf]
    by_cases hn : n ∈ A <;> simp [hn]
  simpa only [Encodable.encode_nat,he] using h.2 (characteristic (Jump (characteristic A))) n

theorem characteristic_computable_from_jump (A : Set ℕ) :
    Computable (characteristic (Jump (characteristic A))) (characteristic A) := by
  obtain ⟨F,f,hF,hf,h⟩ := parameter_recovery
  exact ⟨_,h A⟩

theorem characteristic_jump_not_computable (A : Set ℕ) :
    ¬ Computable (characteristic A) (characteristic (Jump (characteristic A))) := by
  classical
  rintro ⟨P,hP⟩
  apply jump_not_decidable (characteristic A)
  refine ⟨P,hP.1,fun e => ⟨?_,?_⟩⟩ <;> intro he <;>
    simpa [characteristic,he] using hP.2 e

/-- Strict increase is expressed using the same lambda computation predicate
in both directions, together with the stronger complement obstruction. -/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Strict increase under the relative jump
  excerpt: |
    The set $A'$ is semidecidable relative to $A$, whereas its complement is not.
    Moreover, $\chi_A$ is computable relative to $\chi_{A'}$, but $\chi_{A'}$ is not computable relative to $\chi_A$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    To semidecide $A'$, search the finite reduction certificates for $P_e$ on input $e$, allowing every possible
    numerical output. The exact search construction returns one if a certificate exists and has no numerical
    output otherwise. If the complement were semidecidable, the equivalence between acceptance and numerical
    halting domains would give a closed program $D$ whose domain is that complement. At an index $d$ of $D$,
    its computation on $d$ would halt exactly when it did not halt, a contradiction. In particular, a decision
    program for $A'$ cannot exist.

    For the other direction, form a program that ignores its numerical input and searches for a nonzero answer
    to the fixed query $\chi_A(n)$. Its domain is all of $\NN$ if $n\in A$ and empty otherwise. Inserting
    $\ChurchNumeral{n}$ into this fixed template gives an index $f(n)$, and the syntax-code constructors compute
    $f$ by a closed numerical lambda term. Thus $f(n)\in A'$ exactly when $n\in A$. Querying $\chi_{A'}(f(n))$
    therefore computes $\chi_A(n)$. The explicit terms and the preservation of numerical nontermination under
    specialization are proved in §{sec:lambda-relative-jump}.
    \end{proof}
-/
theorem relative_jump_properties (A : Set ℕ) :
    SemidecidablePredicate (characteristic A) (· ∈ Jump (characteristic A)) ∧
    ¬ SemidecidablePredicate (characteristic A) (fun e => e ∉ Jump (characteristic A)) ∧
    Computable (characteristic (Jump (characteristic A))) (characteristic A) ∧
    ¬ Computable (characteristic A) (characteristic (Jump (characteristic A))) :=
  ⟨jump_semidecidable _,jump_complement_not_semidecidable _,
    characteristic_computable_from_jump A,characteristic_jump_not_computable A⟩

end LambdaRelative
end PolishSpaceBook
