module

public import PolishSpaceBook.LambdaPartialProgramCombinators
public import PolishSpaceBook.LambdaDelayedStageIndices

@[expose] public section

/-! # A guarded rank matrix with a dynamically selected lower input function -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm
namespace RankBound
open LambdaRelative
set_option maxRecDepth 4096
set_option maxHeartbeats 900000
attribute [local instance] Classical.propDecidable

def rankInput (q a s t b : ℕ) := Nat.pair q (Nat.pair a (Nat.pair (Nat.pair s t) b))
def stageField (z : ℕ) := z.unpair.2.unpair.1
def lowerField (z : ℕ) := z.unpair.2.unpair.2.unpair.2
def nodeField (z : ℕ) := z.unpair.2.unpair.2.unpair.1.unpair.2
def sourceField (z : ℕ) := z.unpair.2.unpair.2.unpair.1.unpair.1

def stageFieldProgram := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)
def payloadProgram := numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)
def lowerFieldProgram := numericalCompose (numericalProjectionTerm false) payloadProgram
def nodesProgram := numericalCompose (numericalProjectionTerm true) payloadProgram
def nodeFieldProgram := numericalCompose (numericalProjectionTerm false) nodesProgram
def sourceFieldProgram := numericalCompose (numericalProjectionTerm true) nodesProgram

theorem stageField_computes : NumericalComputes stageFieldProgram stageField :=
  (projection_computes true).comp (projection_computes false)
theorem lowerField_computes : NumericalComputes lowerFieldProgram lowerField :=
  (projection_computes false).comp ((projection_computes false).comp (projection_computes false))
theorem rankNodeField_computes : NumericalComputes nodeFieldProgram nodeField :=
  (projection_computes false).comp ((projection_computes true).comp
    ((projection_computes false).comp (projection_computes false)))
theorem sourceField_computes : NumericalComputes sourceFieldProgram sourceField :=
  (projection_computes true).comp ((projection_computes true).comp
    ((projection_computes false).comp (projection_computes false)))

def lowerCodeProgram := mapOutputProgram (uncurryNumerical outputSearchTerm)
  (liftNumericalProgram (pairNumerical (numericalProjectionTerm true) lowerFieldProgram))
def lowerEvalProgram := relativeComposeProgram uniformInterpreterProgram
  (pairOutputProgram lowerCodeProgram (liftNumericalProgram nodeFieldProgram))
def readerInputProgram (I : AlphaTerm) := pairNumerical
  (numericalCompose I (numericalCompose stageFieldProgram (numericalProjectionTerm true)))
  (pairNumerical (numericalCompose lowerFieldProgram (numericalProjectionTerm true)) (numericalProjectionTerm false))
def lowerReaderProgram (I : AlphaTerm) := reindexProgram uniformInterpreterProgram (readerInputProgram I)
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Here is the fixed template used for rank decisions. Let $\mathcal E$ decide $E(t,s)$ on
    $\NatPair{t}{s}$, let $K$ decide $b\in D$ and $bRa$ on $\NatPair{b}{a}$, and let $I$ compute the
    reader index $i(a)$. These are pure closed numerical terms. Decode the argument $w$ as
    $\NatPair{q}{\NatPair{a}{\NatPair{\NatPair{s}{t}}{b}}}$ by numerical projections, and abbreviate
    $$\begin{aligned}
    C(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,b\,k)},\\
    D(o,w)&:=\LambdaQueryOutputSearch\,(C(o,w))\,(\LambdaOutputSearch\,q\,b)\,t,\\
    J(w)&:=K(\LambdaNumericPair\,b\,a),\\
    V(o,w)&:=\LambdaZeroTest\,J(w)\,\ChurchNumeral{0}\,D(o,w),\\
    T&:=\lambdaab{o}{\lambdaab{w}{\LambdaZeroTest\,
     (\mathcal E(\LambdaNumericPair\,t\,s))\,\ChurchNumeral{1}\,V(o,w)}}.
    \end{aligned}$$
    Expand the field projections and abbreviations before abstraction, using a fresh binder $k$.
    This makes $T$ a single closed lambda term.
-/
def lowerRunProgram (I : AlphaTerm) := dataInputProgram lowerEvalProgram (lowerReaderProgram I)

theorem lowerCodeProgram_closed : lowerCodeProgram.Closed := mapOutputProgram_closed
  (uncurryNumerical_closed outputSearchTerm_closed)
  (((projection_computes true).pair lowerField_computes).uniform.1)
theorem lowerEvalProgram_closed : lowerEvalProgram.Closed := relativeComposeProgram_closed
  uniformInterpreterProgram_closed (pairOutputProgram_closed lowerCodeProgram_closed rankNodeField_computes.uniform.1)
theorem readerInputProgram_computes {I : AlphaTerm} {i : ℕ → ℕ} (hi : NumericalComputes I i) :
    NumericalComputes (readerInputProgram I)
      (fun z => Nat.pair (i (stageField z.unpair.1)) (Nat.pair (lowerField z.unpair.1) z.unpair.2)) :=
  (hi.comp (stageField_computes.comp (projection_computes true))).pair
    ((lowerField_computes.comp (projection_computes true)).pair (projection_computes false))
theorem lowerReaderProgram_closed {I : AlphaTerm} {i : ℕ → ℕ} (hi : NumericalComputes I i) :
    (lowerReaderProgram I).Closed := reindexProgram_closed uniformInterpreterProgram_closed
      (readerInputProgram_computes hi).1
theorem lowerRunProgram_closed {I : AlphaTerm} {i : ℕ → ℕ} (hi : NumericalComputes I i) :
    (lowerRunProgram I).Closed := dataInputProgram_closed lowerEvalProgram_closed (lowerReaderProgram_closed hi)

theorem lowerRunProgram_runs {I : AlphaTerm} {i : ℕ → ℕ} (hi : NumericalComputes I i)
    {q : ℕ} {r : ℕ → ℕ} (hq : NumericalComputes (Term.closedProgram q) r)
    {ε η : ℕ → ℕ} (a s t b m : ℕ)
    (hreader : ∀ k, OracleRuns ε (Term.closedProgram (i a)) (Nat.pair b k) (η k))
    (hvalue : OracleRuns η (Term.closedProgram (r b)) t m) :
    OracleRuns ε (lowerRunProgram I) (rankInput q a s t b) m := by
  let z := rankInput q a s t b
  have hc : OracleRuns η lowerCodeProgram z (r b) := by
    have hp := ((projection_computes true).pair lowerField_computes).uniform.2 η z
    have hstart := uncurryNumerical_start outputSearchTerm_closed (Nat.pair q b)
    simp only [Nat.unpair_pair] at hstart
    have hs := hstart.trans ((outputSearchTerm_runs_iff q b (r b)).mpr (hq.2 b))
    apply mapOutputProgram_runs (uncurryNumerical_closed outputSearchTerm_closed)
      (((projection_computes true).pair lowerField_computes).uniform.1) _ hs
    simpa only [z,rankInput,lowerField,Nat.unpair_pair,ite_true] using hp
  have hn : OracleRuns η (liftNumericalProgram nodeFieldProgram) z t := by
    simpa only [z,rankInput,nodeField,Nat.unpair_pair] using rankNodeField_computes.uniform.2 η z
  have he := relativeComposeProgram_runs uniformInterpreterProgram_closed
    (pairOutputProgram_closed lowerCodeProgram_closed rankNodeField_computes.uniform.1)
    (pairOutputProgram_runs lowerCodeProgram_closed rankNodeField_computes.uniform.1 hc hn)
    ((uniformInterpreterProgram_runs_iff η (r b) t m).mpr hvalue)
  apply dataInputProgram_runs_of lowerEvalProgram_closed (lowerReaderProgram_closed hi) he
  intro k
  have hinput := (readerInputProgram_computes hi).2 (Nat.pair z k)
  simp only [z,rankInput,stageField,lowerField,Nat.unpair_pair] at hinput
  exact reindexProgram_runs uniformInterpreterProgram_closed (readerInputProgram_computes hi).1
    ε (Nat.pair z k) _ _ hinput ((uniformInterpreterProgram_runs_iff ε (i a) (Nat.pair b k) (η k)).mpr (hreader k))

def edgeTestProgram (E : AlphaTerm) := numericalCompose E (pairNumerical nodeFieldProgram sourceFieldProgram)
def lowerTestProgram (C : AlphaTerm) := numericalCompose C (pairNumerical lowerFieldProgram stageFieldProgram)
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Here is the fixed template used for rank decisions. Let $\mathcal E$ decide $E(t,s)$ on
    $\NatPair{t}{s}$, let $K$ decide $b\in D$ and $bRa$ on $\NatPair{b}{a}$, and let $I$ compute the
    reader index $i(a)$. These are pure closed numerical terms. Decode the argument $w$ as
    $\NatPair{q}{\NatPair{a}{\NatPair{\NatPair{s}{t}}{b}}}$ by numerical projections, and abbreviate
    $$\begin{aligned}
    C(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,b\,k)},\\
    D(o,w)&:=\LambdaQueryOutputSearch\,(C(o,w))\,(\LambdaOutputSearch\,q\,b)\,t,\\
    J(w)&:=K(\LambdaNumericPair\,b\,a),\\
    V(o,w)&:=\LambdaZeroTest\,J(w)\,\ChurchNumeral{0}\,D(o,w),\\
    T&:=\lambdaab{o}{\lambdaab{w}{\LambdaZeroTest\,
     (\mathcal E(\LambdaNumericPair\,t\,s))\,\ChurchNumeral{1}\,V(o,w)}}.
    \end{aligned}$$
    Expand the field projections and abbreviations before abstraction, using a fresh binder $k$.
    This makes $T$ a single closed lambda term.
-/
def rankMatrixProgram (E C I : AlphaTerm) := ifZeroProgram (edgeTestProgram E) (constantProgram 1)
  (ifZeroProgram (lowerTestProgram C) (constantProgram 0) (lowerRunProgram I))

theorem edgeTest_computes {E : AlphaTerm} {e : ℕ → ℕ} (hE : NumericalComputes E e) :
    NumericalComputes (edgeTestProgram E) (fun z => e (Nat.pair (nodeField z) (sourceField z))) :=
  hE.comp (rankNodeField_computes.pair sourceField_computes)
theorem lowerTest_computes {C : AlphaTerm} {c : ℕ → ℕ} (hC : NumericalComputes C c) :
    NumericalComputes (lowerTestProgram C) (fun z => c (Nat.pair (lowerField z) (stageField z))) :=
  hC.comp (lowerField_computes.pair stageField_computes)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Here is the fixed template used for rank decisions. Let $\mathcal E$ decide $E(t,s)$ on
    $\NatPair{t}{s}$, let $K$ decide $b\in D$ and $bRa$ on $\NatPair{b}{a}$, and let $I$ compute the
    reader index $i(a)$. These are pure closed numerical terms. Decode the argument $w$ as
    $\NatPair{q}{\NatPair{a}{\NatPair{\NatPair{s}{t}}{b}}}$ by numerical projections, and abbreviate
    $$\begin{aligned}
    C(o,w)&:=\lambdaab{k}{\LambdaQueryOutputSearch\,o\,(Ia)\,(\LambdaNumericPair\,b\,k)},\\
    D(o,w)&:=\LambdaQueryOutputSearch\,(C(o,w))\,(\LambdaOutputSearch\,q\,b)\,t,\\
    J(w)&:=K(\LambdaNumericPair\,b\,a),\\
    V(o,w)&:=\LambdaZeroTest\,J(w)\,\ChurchNumeral{0}\,D(o,w),\\
    T&:=\lambdaab{o}{\lambdaab{w}{\LambdaZeroTest\,
     (\mathcal E(\LambdaNumericPair\,t\,s))\,\ChurchNumeral{1}\,V(o,w)}}.
    \end{aligned}$$
    Expand the field projections and abbreviations before abstraction, using a fresh binder $k$.
    This makes $T$ a single closed lambda term.
-/
theorem rankMatrixProgram_closed {E C I : AlphaTerm} {e c i : ℕ → ℕ}
    (hE : NumericalComputes E e) (hC : NumericalComputes C c) (hI : NumericalComputes I i) :
    (rankMatrixProgram E C I).Closed := ifZeroProgram_closed (edgeTest_computes hE).1
      (constantProgram_closed 1) (ifZeroProgram_closed (lowerTest_computes hC).1
        (constantProgram_closed 0) (lowerRunProgram_closed hI))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: lemma
  title: Guarded lower-rank evaluation
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    If the edge test returns zero, the outer zero test returns one without evaluating $V$. If it returns
    one but the predecessor test returns zero, the inner zero test returns zero without evaluating $D$.
    In the remaining case, pure universal evaluation of $P_q$ on $b$ supplies $d(b)$. For each queried
    numeral $k$, universal evaluation in $C$ simulates $P_{i(a)}$ on $\NatPair{b}{k}$ and returns
    $\eta_b(k)$. Substitute these finite computations for the queries in the lower decision program.
    The input-substitution theorem then gives the same output bit as $P_{d(b)}$ on $t$ at $\eta_b$.
    All calls in this case terminate by the hypotheses. This proves both totality and the matrix formula;
    no behavior at a nonpredecessor is needed. Two pair-specializations pass $q,a$ to the same term, so
    the conclusion holds for the compiled matrix code as well.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The hypothesis requires one decider jointly in $t,b$.
-/
theorem rankMatrixProgram_decides {E C I : AlphaTerm} {e c : ℕ → ℕ → Prop} {i : ℕ → ℕ}
    (hE : NumericalComputes E (fun z => if e z.unpair.1 z.unpair.2 then 1 else 0))
    (hC : NumericalComputes C (fun z => if c z.unpair.1 z.unpair.2 then 1 else 0))
    (hI : NumericalComputes I i) (q a : ℕ) (ε : ℕ → ℕ) (L : ℕ → ℕ → Prop)
    (hl : ∀ s t b, c b a → OracleRuns ε (lowerRunProgram I) (rankInput q a s t b)
      (if L b t then 1 else 0)) :
    Decides ε (specializePairProgram (specializePairProgram (rankMatrixProgram E C I) q) a)
      (fun z : ℕ => ¬ e z.unpair.1.unpair.2 z.unpair.1.unpair.1 ∨
        (c z.unpair.2 a ∧ L z.unpair.2 z.unpair.1.unpair.2)) := by
  have hP := rankMatrixProgram_closed hE hC hI
  have hY := ifZeroProgram_closed (lowerTest_computes hC).1 (constantProgram_closed 0) (lowerRunProgram_closed hI)
  have hm (s t b : ℕ) : OracleRuns ε (rankMatrixProgram E C I) (rankInput q a s t b)
      (if ¬ e t s ∨ (c b a ∧ L b t) then 1 else 0) := by
    have he := (edgeTest_computes hE).2 (rankInput q a s t b)
    have hc := (lowerTest_computes hC).2 (rankInput q a s t b)
    simp only [rankInput,nodeField,sourceField,lowerField,stageField,Nat.unpair_pair] at he hc
    by_cases het : e t s
    · apply ifZeroProgram_runs_one (edgeTest_computes hE).1 (constantProgram_closed 1) hY
        (by simpa only [rankInput,ite_eq_left het] using he)
      by_cases hcb : c b a
      · apply ifZeroProgram_runs_one (lowerTest_computes hC).1 (constantProgram_closed 0) (lowerRunProgram_closed hI)
          (by simpa only [rankInput,ite_eq_left hcb] using hc)
        simpa only [het,hcb,not_true_eq_false,false_or,true_and] using hl s t b hcb
      · apply ifZeroProgram_runs_zero (lowerTest_computes hC).1 (constantProgram_closed 0) (lowerRunProgram_closed hI)
          (by simpa only [rankInput,ite_eq_right hcb] using hc)
        simpa only [het,hcb,not_true_eq_false,false_and,or_self,ite_false] using
          constantProgram_runs 0 ε (rankInput q a s t b)
    · apply ifZeroProgram_runs_zero (edgeTest_computes hE).1 (constantProgram_closed 1) hY
        (by simpa only [rankInput,ite_eq_right het] using he)
      simpa only [het,not_false_eq_true,true_or,ite_true] using constantProgram_runs 1 ε (rankInput q a s t b)
  refine ⟨specializePairProgram_closed (specializePairProgram_closed hP q) a,fun z => ?_⟩
  have h := specializePairProgram_runs (specializePairProgram_closed hP q)
    (specializePairProgram_runs hP (hm z.unpair.1.unpair.1 z.unpair.1.unpair.2 z.unpair.2))
  simp only [Nat.pair_unpair] at h
  constructor <;> intro hz
  · simpa only [ite_eq_left hz,Encodable.encode_nat] using h
  · simpa only [ite_eq_right hz,Encodable.encode_nat] using h

end RankBound
end PolishSpaceBook
