module

public import PolishSpaceBook.LambdaRelativeEnumerations
public import PolishSpaceBook.LambdaInputParameters
public import PolishSpaceBook.LambdaInputStageBounds
public import PolishSpaceBook.LambdaBoundedPrefixTests
public import PolishSpaceBook.LambdaProjectionOperations

@[expose] public section

/-! # Computable Baire inverse images at one fixed parameter

Finite trials constrain the graph coordinate by coordinate. The program may
query the paired parameter and input without any prescribed modulus of use.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
local instance : Encodable (List ℕ) := NatListCode.encodable
local instance : Encodable (List ℕ × List ℕ) := wordPairEncodable

def graphClause (ε : ℕ → ℕ) (e i : ℕ) (s : List ℕ) : Prop :=
  Term.oracleOutputCandidate (fun j => Nat.pair (ε j) ((s.getD j 0).unpair.1))
    e i.unpair.1 i.unpair.2 = true →
    (s.getD i.unpair.1 0).unpair.2 = i.unpair.2.unpair.1

def graphInputAccessProgram : AlphaTerm := pairOutputProgram
  (queryOutputProgram (liftNumericalProgram (numericalProjectionTerm false)))
  (liftNumericalProgram (numericalCompose (numericalProjectionTerm true)
    (numericalCompose listGetTerm (pairNumerical
      (numericalCompose (numericalCompose (numericalProjectionTerm true)
        (numericalProjectionTerm false)) (numericalProjectionTerm true))
      (numericalProjectionTerm false)))))

theorem graphInputAccess_computes : UniformNumericalComputes graphInputAccessProgram
    (fun p z => Nat.pair (p z.unpair.2)
      (((NatListCode.decode z.unpair.1.unpair.2.unpair.1).getD z.unpair.2 0).unpair.1)) := by
  have hword := ((projection_computes true).comp (projection_computes false)).comp
    (projection_computes true)
  have hget := (projection_computes true).comp
    (listGet_computes.comp (hword.pair (projection_computes false)))
  simpa only [graphInputAccessProgram,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using
    (projection_computes false).uniform.query.pair hget.uniform

def graphCandidateProgram (e : ℕ) : AlphaTerm :=
  dataInputProgram (reindexProgram (candidateTestProgram e) (numericalProjectionTerm true))
    graphInputAccessProgram

theorem graphCandidate_computes (e : ℕ) : UniformNumericalComputes (graphCandidateProgram e)
    (fun p z => if Term.oracleOutputCandidate (fun j => Nat.pair (p j)
      (((NatListCode.decode z.unpair.2.unpair.1).getD j 0).unpair.1))
      e z.unpair.1.unpair.1 z.unpair.1.unpair.2 then 1 else 0) := by
  simpa only [graphCandidateProgram,candidateTest,Nat.unpair_pair,ite_true] using
    ((candidateTestProgram_computes e).reindex (projection_computes true)).dataInput
      graphInputAccess_computes

def graphEqualityTerm : AlphaTerm := numericalCombine equalityTerm
  (numericalCompose (numericalProjectionTerm false)
    (numericalCompose listGetTerm (pairNumerical
      (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))
      (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true)))))
  (numericalCompose (numericalCompose (numericalProjectionTerm true)
    (numericalProjectionTerm false)) (numericalProjectionTerm true))

theorem graphEquality_computes : NumericalComputes graphEqualityTerm (fun z => if
    ((NatListCode.decode z.unpair.2.unpair.1).getD z.unpair.1.unpair.1 0).unpair.2 =
      z.unpair.1.unpair.2.unpair.1 then 1 else 0) := by
  have hl := (projection_computes false).comp (listGet_computes.comp
    (((projection_computes true).comp (projection_computes false)).pair
      ((projection_computes true).comp (projection_computes true))))
  have hr := ((projection_computes true).comp (projection_computes false)).comp (projection_computes true)
  simpa only [graphEqualityTerm,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using
    hl.combine hr equalityTerm_closed (fun a b => if a = b then 1 else 0) equalityTerm_apply

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Here is the graph-row tester used in §{sec:edst-computable-preimages}.
    For the input
    $$z=\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}$$
    use numerical projections to
    recover $n,m,r$ from $i=\NatPair{n}{\NatPair{m}{r}}$ and put $a=\LambdaListCode{s}$.
    The second word $t$ is unused. In the preceding construction take the accessor body
    $$\LambdaTermName{digitProg}o(\LambdaNumericPair\,z\,k)=\LambdaNumericPair\,(ok)\,
     (\LambdaNumericProjection{1}(\LambdaListGet(\LambdaNumericPair\,a\,k))).$$
    This denotes the term obtained by substituting the projections for $a$ and abstracting the displayed
    inputs. It pairs the original parameter digit with the first component of the stored point digit,
    using zero beyond the word. Take the body of $\LambdaTermName{functionProg}$ to be
    $\LambdaQueryOutputCandidate\,o\,\ChurchNumeral{e}\,n\,(\LambdaNumericPair\,m\,r)$.
    Thus $\LambdaTermName{composeInput}$ returns one precisely when this finite computation test succeeds.
    The required row bit is
    $$\LambdaLeCase{\LambdaTermName{composeInput}oz}{\ChurchNumeral{0}}{\ChurchNumeral{1}}
     {\LambdaEqual\,(\LambdaNumericProjection{2}(\LambdaListGet(\LambdaNumericPair\,a\,n)))\,m}.$$
    Every component is total, so the row is decidable even on short words. At length $i+1$,
    the stage-address bound ensures that the zero padding cannot affect the answer.
    The bounded-prefix construction in §{sec:lambda-recursive-borel-separation}, with bound $i+1$,
    checks all rows without requiring an input-use modulus for the program with index $e$.
-/
theorem graphClause_decidable (ε : ℕ → ℕ) (e : ℕ) :
    LambdaRelative.DecidablePredicate ε
      (fun z : ℕ × PrefixPair => graphClause ε e z.1 z.2.1) := by
  have hc := graphCandidate_computes e
  have hc' : LambdaRelative.DecidablePredicate ε (fun z : ℕ =>
      Term.oracleOutputCandidate (fun j => Nat.pair (ε j)
        (((NatListCode.decode z.unpair.2.unpair.1).getD j 0).unpair.1))
        e z.unpair.1.unpair.1 z.unpair.1.unpair.2 = true) := by
    refine ⟨graphCandidateProgram e,hc.1,fun z => ⟨?_,?_⟩⟩ <;> intro hz
    · simpa only [Encodable.encode_nat,hz,ite_true] using hc.2 ε z
    · simpa only [Encodable.encode_nat,hz,ite_false] using hc.2 ε z
  have he' : LambdaRelative.DecidablePredicate ε (fun z : ℕ =>
      ((NatListCode.decode z.unpair.2.unpair.1).getD z.unpair.1.unpair.1 0).unpair.2 =
        z.unpair.1.unpair.2.unpair.1) := by
    apply numericalDecision graphEquality_computes ε
    · intro z hz; exact ite_eq_left hz
    · intro z hz; exact ite_eq_right hz
  simpa [graphClause,Encodable.encode,Encodable.encodeSigma] using (hc'.imp he').precompNumerical
    (g := fun z : ℕ × PrefixPair => Encodable.encode z) numericalIdentity_computes (fun _ => rfl)

private theorem prefix_getD (p : ℕ → ℕ) {n i : ℕ} (h : i < n) :
    (seqPrefix p n).getD i 0 = p i := by
  simp [seqPrefix,h,List.getD_eq_getElem?_getD]

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $e$ be the index of the supplied program. First construct a tree presentation of the coded graph
    $G_F:=\{\NamePair{x}{y}:y=F(x)\}$. A row $i=\NatPair{n}{\NatPair{m}{r}}$ proposes output $m$ at
    coordinate $n$ and tests all computation certificates below stage $r$.
    The list coding gives a useful bound: every address checked at stage $r$ is less than $r$,
    as proved in §{sec:lambda-stage-address-bound}. Both $n$ and $r$ are at most $i$.
    For a finite word $t$, let $\ZeroExtendedWord{t}$ denote its extension by zeros to an infinite sequence.
    For a prefix $s$ of the coded point, extend each of its coordinate projections in this way.
    Run the stage-$r$ test with input $\NamePair{\varepsilon}{\ZeroExtendedWord{s_1}}$;
    if it certifies output $m$ at coordinate $n$, require $s_2(n)=m$.
    For this row use exactly the prefix of length $i+1$. The test is finite and decidable relative to
    $\varepsilon$ by the explicit program in §{sec:lambda-graph-tests}.

    At length $N$, test every row $i<N$ on the prefix of length $i+1$, and impose these tests at all
    shorter prefixes as in §{sec:edst-finite-check-trees}. The stage bound ensures that each row has the
    same answer on this prefix as on the infinite input. Every certified output equals $F(x)(n)$ by
    uniqueness of numerical outputs. Conversely, totality supplies a finite certificate for each
    $F(x)(n)$, so the corresponding row forces $y(n)=F(x)(n)$. Thus all rows hold exactly on $G_F$.
    An unused second branch coordinate turns this recursive prefix condition into a pair-tree presentation.

    Intersect $G_F$ with $\NameProjection{2}{\cdot}^{-1}(A)$ and project onto the first coordinate.
    The constructions of §{sec:edst-coordinate-projections} give exactly $F^{-1}(A)$ and retain the same
    parameter. No bound on the running time or input use of $F$ is assumed. Totality is used to ensure
    that each output coordinate eventually has a certificate, not to decide when arbitrary programs halt.
    \end{proof}
-/
theorem graphClause_prefix (ε x y : ℕ → ℕ) (e i : ℕ) :
    graphClause ε e i (seqPrefix (pairBaire x y) (i+1)) ↔
      (Term.oracleOutputCandidate (pairBaire ε x) e i.unpair.1 i.unpair.2 = true →
        y i.unpair.1 = i.unpair.2.unpair.1) := by
  have hn : i.unpair.1 < i+1 := by have := Nat.unpair_left_le i; omega
  have hs : i.unpair.2.unpair.2 ≤ i :=
    (Nat.unpair_right_le i.unpair.2).trans (Nat.unpair_right_le i)
  have hc : Term.oracleOutputCandidate
      (fun j => Nat.pair (ε j) (((seqPrefix (pairBaire x y) (i+1)).getD j 0).unpair.1))
      e i.unpair.1 i.unpair.2 =
      Term.oracleOutputCandidate (pairBaire ε x) e i.unpair.1 i.unpair.2 := by
    apply Term.boundedInputTest_eq_of_stage_prefix
    intro j hj
    rw [prefix_getD _ (by omega)]
    simp [pairBaire]
  simp only [graphClause,hc,prefix_getD _ hn,pairBaire,Nat.unpair_pair]

/-- Totality is needed only at the single point whose graph fiber is tested. -/
theorem forall_graphClause_iff_at {ε : ℕ → ℕ} {e : ℕ} {x v : ℕ → ℕ}
    (hF : ∀ n, OracleRuns (pairBaire ε x) (Term.closedProgram e) n (v n))
    (y : ℕ → ℕ) :
    (∀ i, graphClause ε e i (seqPrefix (pairBaire x y) (i+1))) ↔ y = v := by
  simp only [graphClause_prefix]
  constructor
  · intro h
    funext n
    obtain ⟨s,hs⟩ := (oracle_outputTest_exists_iff _ e n (v n)).mpr (hF n)
    have hi := h (Nat.pair n (Nat.pair (v n) s))
    simpa [Term.oracleOutputCandidate,hs] using hi
  · rintro rfl i hi
    have hr := (oracle_outputTest_exists_iff _ e i.unpair.1 i.unpair.2.unpair.1).mp
      ⟨i.unpair.2.unpair.2,hi⟩
    exact ((hF i.unpair.1).output_unique hr)


/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $e$ be the index of the supplied program. First construct a tree presentation of the coded graph
    $G_F:=\{\NamePair{x}{y}:y=F(x)\}$. A row $i=\NatPair{n}{\NatPair{m}{r}}$ proposes output $m$ at
    coordinate $n$ and tests all computation certificates below stage $r$.
    The list coding gives a useful bound: every address checked at stage $r$ is less than $r$,
    as proved in §{sec:lambda-stage-address-bound}. Both $n$ and $r$ are at most $i$.
    For a finite word $t$, let $\ZeroExtendedWord{t}$ denote its extension by zeros to an infinite sequence.
    For a prefix $s$ of the coded point, extend each of its coordinate projections in this way.
    Run the stage-$r$ test with input $\NamePair{\varepsilon}{\ZeroExtendedWord{s_1}}$;
    if it certifies output $m$ at coordinate $n$, require $s_2(n)=m$.
    For this row use exactly the prefix of length $i+1$. The test is finite and decidable relative to
    $\varepsilon$ by the explicit program in §{sec:lambda-graph-tests}.

    At length $N$, test every row $i<N$ on the prefix of length $i+1$, and impose these tests at all
    shorter prefixes as in §{sec:edst-finite-check-trees}. The stage bound ensures that each row has the
    same answer on this prefix as on the infinite input. Every certified output equals $F(x)(n)$ by
    uniqueness of numerical outputs. Conversely, totality supplies a finite certificate for each
    $F(x)(n)$, so the corresponding row forces $y(n)=F(x)(n)$. Thus all rows hold exactly on $G_F$.
    An unused second branch coordinate turns this recursive prefix condition into a pair-tree presentation.

    Intersect $G_F$ with $\NameProjection{2}{\cdot}^{-1}(A)$ and project onto the first coordinate.
    The constructions of §{sec:edst-coordinate-projections} give exactly $F^{-1}(A)$ and retain the same
    parameter. No bound on the running time or input use of $F$ is assumed. Totality is used to ensure
    that each output coordinate eventually has a certificate, not to decide when arbitrary programs halt.
    \end{proof}
-/
theorem forall_graphClause_iff {ε : ℕ → ℕ} {e : ℕ} {F : (ℕ → ℕ) → (ℕ → ℕ)}
    (hF : ∀ x n, OracleRuns (pairBaire ε x) (Term.closedProgram e) n (F x n))
    (x y : ℕ → ℕ) :
    (∀ i, graphClause ε e i (seqPrefix (pairBaire x y) (i+1))) ↔ y = F x :=
  forall_graphClause_iff_at (hF x) y

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $e$ be the index of the supplied program. First construct a tree presentation of the coded graph
    $G_F:=\{\NamePair{x}{y}:y=F(x)\}$. A row $i=\NatPair{n}{\NatPair{m}{r}}$ proposes output $m$ at
    coordinate $n$ and tests all computation certificates below stage $r$.
    The list coding gives a useful bound: every address checked at stage $r$ is less than $r$,
    as proved in §{sec:lambda-stage-address-bound}. Both $n$ and $r$ are at most $i$.
    For a finite word $t$, let $\ZeroExtendedWord{t}$ denote its extension by zeros to an infinite sequence.
    For a prefix $s$ of the coded point, extend each of its coordinate projections in this way.
    Run the stage-$r$ test with input $\NamePair{\varepsilon}{\ZeroExtendedWord{s_1}}$;
    if it certifies output $m$ at coordinate $n$, require $s_2(n)=m$.
    For this row use exactly the prefix of length $i+1$. The test is finite and decidable relative to
    $\varepsilon$ by the explicit program in §{sec:lambda-graph-tests}.

    At length $N$, test every row $i<N$ on the prefix of length $i+1$, and impose these tests at all
    shorter prefixes as in §{sec:edst-finite-check-trees}. The stage bound ensures that each row has the
    same answer on this prefix as on the infinite input. Every certified output equals $F(x)(n)$ by
    uniqueness of numerical outputs. Conversely, totality supplies a finite certificate for each
    $F(x)(n)$, so the corresponding row forces $y(n)=F(x)(n)$. Thus all rows hold exactly on $G_F$.
    An unused second branch coordinate turns this recursive prefix condition into a pair-tree presentation.

    Intersect $G_F$ with $\NameProjection{2}{\cdot}^{-1}(A)$ and project onto the first coordinate.
    The constructions of §{sec:edst-coordinate-projections} give exactly $F^{-1}(A)$ and retain the same
    parameter. No bound on the running time or input use of $F$ is assumed. Totality is used to ensure
    that each output coordinate eventually has a certificate, not to decide when arbitrary programs halt.
    \end{proof}
-/
theorem projected_graph {ε : ℕ → ℕ} {e : ℕ} {F : (ℕ → ℕ) → (ℕ → ℕ)}
    (hF : ∀ x n, OracleRuns (pairBaire ε x) (Term.closedProgram e) n (F x n)) :
    Projected ε {p | rightBaire p = F (leftBaire p)} := by
  have h := projected_forall_finitePrefixTests (p := fun i z => graphClause ε e i z.1) (graphClause_decidable ε e) successor_computes
  have he : {p | ∃ (q : ℕ → ℕ), ∀ i, graphClause ε e i (seqPrefix p (i+1))} =
      {p | rightBaire p = F (leftBaire p)} := by
    ext p
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_,hp⟩
      apply (forall_graphClause_iff hF (leftBaire p) (rightBaire p)).mp
      simpa only [pairBaire_left_right] using hp
    · intro hp
      refine ⟨fun _ => 0,?_⟩
      simpa only [pairBaire_left_right] using
        (forall_graphClause_iff hF (leftBaire p) (rightBaire p)).mpr hp
  exact he ▸ h

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $e$ be the index of the supplied program. First construct a tree presentation of the coded graph
    $G_F:=\{\NamePair{x}{y}:y=F(x)\}$. A row $i=\NatPair{n}{\NatPair{m}{r}}$ proposes output $m$ at
    coordinate $n$ and tests all computation certificates below stage $r$.
    The list coding gives a useful bound: every address checked at stage $r$ is less than $r$,
    as proved in §{sec:lambda-stage-address-bound}. Both $n$ and $r$ are at most $i$.
    For a finite word $t$, let $\ZeroExtendedWord{t}$ denote its extension by zeros to an infinite sequence.
    For a prefix $s$ of the coded point, extend each of its coordinate projections in this way.
    Run the stage-$r$ test with input $\NamePair{\varepsilon}{\ZeroExtendedWord{s_1}}$;
    if it certifies output $m$ at coordinate $n$, require $s_2(n)=m$.
    For this row use exactly the prefix of length $i+1$. The test is finite and decidable relative to
    $\varepsilon$ by the explicit program in §{sec:lambda-graph-tests}.

    At length $N$, test every row $i<N$ on the prefix of length $i+1$, and impose these tests at all
    shorter prefixes as in §{sec:edst-finite-check-trees}. The stage bound ensures that each row has the
    same answer on this prefix as on the infinite input. Every certified output equals $F(x)(n)$ by
    uniqueness of numerical outputs. Conversely, totality supplies a finite certificate for each
    $F(x)(n)$, so the corresponding row forces $y(n)=F(x)(n)$. Thus all rows hold exactly on $G_F$.
    An unused second branch coordinate turns this recursive prefix condition into a pair-tree presentation.

    Intersect $G_F$ with $\NameProjection{2}{\cdot}^{-1}(A)$ and project onto the first coordinate.
    The constructions of §{sec:edst-coordinate-projections} give exactly $F^{-1}(A)$ and retain the same
    parameter. No bound on the running time or input use of $F$ is assumed. Totality is used to ensure
    that each output coordinate eventually has a certificate, not to decide when arbitrary programs halt.
    \end{proof}
-/
theorem Projected.computablePreimage_index {ε : ℕ → ℕ} {e : ℕ}
    {F : (ℕ → ℕ) → (ℕ → ℕ)} {A : Set (ℕ → ℕ)} (hA : Projected ε A)
    (hF : ∀ x n, OracleRuns (pairBaire ε x) (Term.closedProgram e) n (F x n)) :
    Projected ε (F ⁻¹' A) := by
  have h := ((projected_graph hF).inter hA.rightPreimage).projectLeft
  have he : leftBaire '' ({p | rightBaire p = F (leftBaire p)} ∩ rightBaire ⁻¹' A) =
      F ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨p,⟨hp,ha⟩,rfl⟩
      change rightBaire p = F (leftBaire p) at hp
      change rightBaire p ∈ A at ha
      change F (leftBaire p) ∈ A
      rwa [hp] at ha
    · intro hx
      exact ⟨pairBaire x (F x),⟨by simp,by simpa using hx⟩,by simp⟩
  exact he ▸ h

/-@ booklink:
  source: polish-space-book/effective-dst-lightface-hierarchies.md
  target: statement
  kind: proposition
  title: Computable inverse images at a fixed parameter
-/
theorem Projected.computablePreimage {ε : ℕ → ℕ} {P : AlphaTerm}
    {F : (ℕ → ℕ) → (ℕ → ℕ)} {A : Set (ℕ → ℕ)} (hA : Projected ε A)
    (hP : P.Closed) (hF : ∀ x n, OracleRuns (pairBaire ε x) P n (F x n)) :
    Projected ε (F ⁻¹' A) := by
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP
  exact hA.computablePreimage_index (e := e) (by simpa only [he] using hF)

end LambdaTree
end PolishSpaceBook
