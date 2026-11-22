module

public import PolishSpaceBook.RationalMetricEstimates
public import PolishSpaceBook.LambdaRationalCodes
public import PolishSpaceBook.LambdaNumericalQueries
public import PolishSpaceBook.LambdaSierpinski

@[expose] public section

/-! # Rational metric balls semidecided by closed lambda terms -/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
universe u
variable {X : Type u} [MetricSpace X]

/-- One numerical lambda program computes every coded distance approximation. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    To implement the metric searches, use the approximation form of the distance data. Fix a total computable
    rational-valued function $A$ such that
    $$
    \Abs{A(i,j,k)-d(q_i,q_j)}\le 2^{-k}.
    $$
    The same algorithm must work for all $i,j,k$. The rational operations from
    §{sec:tte-finite-data} implement each test below.
-/
structure LambdaMetricApproximation (q : ℕ → X) extends RationalMetricApproximation q where
  program : AlphaTerm
  computes : NumericalComputes program (fun z =>
    (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)

namespace NamedLambda.AlphaTerm

/-- The input is the paired ball code and stage: `pair (pair center radius) n`. -/
def metricStageNumber : AlphaTerm := liftNumericalProgram (numericalProjectionTerm false)
def metricStageCenter : AlphaTerm := liftNumericalProgram
  (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true))
def metricStageRadius : AlphaTerm := liftNumericalProgram
  (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm true))
def metricDistanceInput : AlphaTerm := pairOutputProgram (queryOutputProgram metricStageNumber)
  (pairOutputProgram metricStageCenter metricStageNumber)
def metricStageError : AlphaTerm := mapOutputProgram rationalDyadicTerm metricStageNumber

def metricStageApproximation (M : AlphaTerm) : AlphaTerm := mapOutputProgram M metricDistanceInput

def metricStageUpper (M : AlphaTerm) : AlphaTerm :=
  mapOutputProgram rationalAddTerm (pairOutputProgram
    (mapOutputProgram rationalAddTerm (pairOutputProgram (metricStageApproximation M) metricStageError))
    metricStageError)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The joint numerical input is $z=\NatPair{\NatPair{i}{c}}{n}$. In the following expressions, abbreviate
    $$\begin{aligned}
    n&:=\LambdaNumericProjection{2}z,\\
    i&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{1}z),\\
    c&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{1}z).
    \end{aligned}$$
    With $o$ the input-name variable, put
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,(on)\,(\LambdaNumericPair\,i\,n)),\\
    E&:=\LambdaDyadic\,n,\\
    U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,
     (\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E))\,E),\\
    T\,o\,z&\to_\beta^*\LambdaRationalLess\,(\LambdaNumericPair\,U\,c).
    \end{aligned}$$
    Here $T$ is the closed program assembled by composition and pairing of the component procedures. Expand the
    abbreviations before supplying its arguments; the helper beta-redexes then give the displayed reduction. All internal
    bound variables can be fixed fresh once. For a ball code $b=\NatPair{i}{c}$, define
    $$F_b:=\lambdaab{k}{\LambdaNumericPair\,\ChurchNumeral{b}\,k},\qquad
    \LambdaBallTest{b}:=\lambdaab{o}{\lambdaab{k}{T\,o\,(F_bk)}}.$$
    Thus the same stage term $T$ serves every center and radius.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Keep the preceding numerical convention for enumeration outputs: zero denotes an empty stage and $b+1$ denotes the ball
    encoded by $b$. Let $R_M$ be the fixed rational-ball stage term constructed in §{sec:lambda-rational-ball-programs}. Its
    inputs are the name argument and $\NatPair{b}{n}$, where $b$ is a center-radius code and $n$ the metric precision. Its
    output is zero or one, and it terminates on every name and every numerical input.
-/
def metricStageProgram (M : AlphaTerm) : AlphaTerm :=
  mapOutputProgram rationalLessTerm (pairOutputProgram (metricStageUpper M) metricStageRadius)

theorem metricStageNumber_computes : UniformNumericalComputes metricStageNumber
    (fun _ z => z.unpair.2) := by
  simpa [metricStageNumber] using (projection_computes false).uniform

theorem metricStageCenter_computes : UniformNumericalComputes metricStageCenter
    (fun _ z => z.unpair.1.unpair.1) := by
  simpa [metricStageCenter] using ((projection_computes true).comp (projection_computes true)).uniform

theorem metricStageRadius_computes : UniformNumericalComputes metricStageRadius
    (fun _ z => z.unpair.1.unpair.2) := by
  simpa [metricStageRadius] using ((projection_computes false).comp (projection_computes true)).uniform

theorem metricDistanceInput_computes : UniformNumericalComputes metricDistanceInput
    (fun p z => Nat.pair (p z.unpair.2) (Nat.pair z.unpair.1.unpair.1 z.unpair.2)) :=
  metricStageNumber_computes.query.pair (metricStageCenter_computes.pair metricStageNumber_computes)

theorem metricStageError_computes : UniformNumericalComputes metricStageError
    (fun _ z => (RationalCode.dyadic z.unpair.2).natCode) :=
  metricStageNumber_computes.map rationalDyadic_computes

/-- The stage construction uses only total coded arithmetic, without metric hypotheses. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Total rational stage test
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{RationalValue,LambdaBallTest,LambdaBallSemidecider}
    \end{mathmeta}
    We construct the numerical test used for rational balls. The construction itself needs no metric space. For a rational
    code $c=\RationalCode{a}{b}{d}$, write $\RationalValue{c}:=(a-b)/(d+1)$. Let $A:\NN^3\to\NN$ be a total function whose
    outputs are rational codes, and suppose one closed term $M$ satisfies
    $$M\,\ChurchNumeral{\NatPair{i}{\NatPair{j}{n}}}\to_\beta^*\ChurchNumeral{A(i,j,n)}$$
    for all $i,j,n$. Given an input name $p$, a center index $i$, a radius code $c$, and a stage $n$, the desired test is
    $$\RationalValue{A(p(n),i,n)}+2\cdot2^{-n}<\RationalValue{c}.$$
    It uses only a query to $p$, the supplied program $M$, and the arithmetic of §{sec:lambda-rational-arithmetic}.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The joint numerical input is $z=\NatPair{\NatPair{i}{c}}{n}$. In the following expressions, abbreviate
    $$\begin{aligned}
    n&:=\LambdaNumericProjection{2}z,\\
    i&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{1}z),\\
    c&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{1}z).
    \end{aligned}$$
    With $o$ the input-name variable, put
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,(on)\,(\LambdaNumericPair\,i\,n)),\\
    E&:=\LambdaDyadic\,n,\\
    U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,
     (\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E))\,E),\\
    T\,o\,z&\to_\beta^*\LambdaRationalLess\,(\LambdaNumericPair\,U\,c).
    \end{aligned}$$
    Here $T$ is the closed program assembled by composition and pairing of the component procedures. Expand the
    abbreviations before supplying its arguments; the helper beta-redexes then give the displayed reduction. All internal
    bound variables can be fixed fresh once. For a ball code $b=\NatPair{i}{c}$, define
    $$F_b:=\lambdaab{k}{\LambdaNumericPair\,\ChurchNumeral{b}\,k},\qquad
    \LambdaBallTest{b}:=\lambdaab{o}{\lambdaab{k}{T\,o\,(F_bk)}}.$$
    Thus the same stage term $T$ serves every center and radius.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Keep the preceding numerical convention for enumeration outputs: zero denotes an empty stage and $b+1$ denotes the ball
    encoded by $b$. Let $R_M$ be the fixed rational-ball stage term constructed in §{sec:lambda-rational-ball-programs}. Its
    inputs are the name argument and $\NatPair{b}{n}$, where $b$ is a center-radius code and $n$ the metric precision. Its
    output is zero or one, and it terminates on every name and every numerical input.
-/
theorem metricStageProgram_computes {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)) :
    UniformNumericalComputes (metricStageProgram M) (fun p z =>
      if (approx (p z.unpair.2,(z.unpair.1.unpair.1,z.unpair.2))).value +
        (1/2 : ℚ)^z.unpair.2 + (1/2 : ℚ)^z.unpair.2 <
        (RationalCode.ofNat z.unpair.1.unpair.2).value then 1 else 0) := by
  have ha : UniformNumericalComputes (metricStageApproximation M)
      (fun p z => (approx (p z.unpair.2,(z.unpair.1.unpair.1,z.unpair.2))).natCode) := by
    simpa [metricStageApproximation,Nat.unpair_pair] using metricDistanceInput_computes.map hM
  have hu := ((ha.pair metricStageError_computes).map rationalAdd_computes).pair metricStageError_computes
    |>.map rationalAdd_computes
  have h := (hu.pair metricStageRadius_computes).map rationalLess_computes
  simpa [metricStageProgram,metricStageUpper,Nat.unpair_pair] using h

theorem metricStageProgram_closed {M : AlphaTerm} (hM : M.Closed) :
    (metricStageProgram M).Closed := by
  have ha := mapOutputProgram_closed hM metricDistanceInput_computes.1
  have hu := mapOutputProgram_closed rationalAdd_computes.1
    (pairOutputProgram_closed (mapOutputProgram_closed rationalAdd_computes.1
      (pairOutputProgram_closed ha metricStageError_computes.1)) metricStageError_computes.1)
  exact mapOutputProgram_closed rationalLess_computes.1 (pairOutputProgram_closed hu metricStageRadius_computes.1)

/-- Insert a fixed ball code while leaving the stage as the numerical input. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The joint numerical input is $z=\NatPair{\NatPair{i}{c}}{n}$. In the following expressions, abbreviate
    $$\begin{aligned}
    n&:=\LambdaNumericProjection{2}z,\\
    i&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{1}z),\\
    c&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{1}z).
    \end{aligned}$$
    With $o$ the input-name variable, put
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,(on)\,(\LambdaNumericPair\,i\,n)),\\
    E&:=\LambdaDyadic\,n,\\
    U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,
     (\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E))\,E),\\
    T\,o\,z&\to_\beta^*\LambdaRationalLess\,(\LambdaNumericPair\,U\,c).
    \end{aligned}$$
    Here $T$ is the closed program assembled by composition and pairing of the component procedures. Expand the
    abbreviations before supplying its arguments; the helper beta-redexes then give the displayed reduction. All internal
    bound variables can be fixed fresh once. For a ball code $b=\NatPair{i}{c}$, define
    $$F_b:=\lambdaab{k}{\LambdaNumericPair\,\ChurchNumeral{b}\,k},\qquad
    \LambdaBallTest{b}:=\lambdaab{o}{\lambdaab{k}{T\,o\,(F_bk)}}.$$
    Thus the same stage term $T$ serves every center and radius.
-/
def insertBallCode (b : ℕ) : AlphaTerm :=
  lam 40 (app (app numericalPairTerm (numeral b)) (var 40))

theorem insertBallCode_computes (b : ℕ) : NumericalComputes (insertBallCode b) (Nat.pair b) :=
  by
    refine ⟨?_,fun n => ?_⟩
    · unfold insertBallCode Closed
      simp only [fv_lam,fv_app,fv_var]; rw [numericalPairTerm_closed,numeral_closed]; simp
    · have hb : Beta (app (insertBallCode b) (numeral n))
          (app (app numericalPairTerm (numeral b)) (numeral n)) := by
        simpa only [insertBallCode,subst_app,subst_var,ite_true,
          subst_closed _ _ _ numericalPairTerm_closed,subst_closed _ _ _ (numeral_closed b)] using
          Beta.contract 40 (app (app numericalPairTerm (numeral b)) (var 40)) (numeral n)
      exact (Relation.ReflTransGen.single hb).trans (numericalPairTerm_apply b n)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The joint numerical input is $z=\NatPair{\NatPair{i}{c}}{n}$. In the following expressions, abbreviate
    $$\begin{aligned}
    n&:=\LambdaNumericProjection{2}z,\\
    i&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{1}z),\\
    c&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{1}z).
    \end{aligned}$$
    With $o$ the input-name variable, put
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,(on)\,(\LambdaNumericPair\,i\,n)),\\
    E&:=\LambdaDyadic\,n,\\
    U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,
     (\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E))\,E),\\
    T\,o\,z&\to_\beta^*\LambdaRationalLess\,(\LambdaNumericPair\,U\,c).
    \end{aligned}$$
    Here $T$ is the closed program assembled by composition and pairing of the component procedures. Expand the
    abbreviations before supplying its arguments; the helper beta-redexes then give the displayed reduction. All internal
    bound variables can be fixed fresh once. For a ball code $b=\NatPair{i}{c}$, define
    $$F_b:=\lambdaab{k}{\LambdaNumericPair\,\ChurchNumeral{b}\,k},\qquad
    \LambdaBallTest{b}:=\lambdaab{o}{\lambdaab{k}{T\,o\,(F_bk)}}.$$
    Thus the same stage term $T$ serves every center and radius.
-/
def metricBallTestProgram (M : AlphaTerm) (b : ℕ) : AlphaTerm :=
  reindexProgram (metricStageProgram M) (insertBallCode b)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Put
    $$G_{b,o}:=\lambdaab{k}{\LambdaZeroTest\,(\LambdaBallTest{b}\,o\,k)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},
    \qquad I:=\lambdaab{x}{x},$$
    and define the closed semidecision program
    $$\LambdaBallSemidecider{b}:=\lambdaab{o}{\lambdaab{a}{\LambdaResultSearch\,G_{b,o}\,I}}.$$
    Its numerical argument $a$ is unused. The zero test reverses the answers so that the result-search term stops exactly on
    a successful stage.
-/
def metricBallSemidecider (M : AlphaTerm) (b : ℕ) : AlphaTerm :=
  digitSearchProgram (metricBallTestProgram M b)

def metricStageTest (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (p : ℕ → ℕ) (b n : ℕ) : Prop :=
  (approx (p n,(b.unpair.1,n))).value + (1/2 : ℚ)^n + (1/2 : ℚ)^n <
    (RationalCode.ofNat b.unpair.2).value

instance (approx : ℕ × (ℕ × ℕ) → RationalCode) (p : ℕ → ℕ) (b n : ℕ) :
    Decidable (metricStageTest approx p b n) := inferInstanceAs (Decidable (_ < _))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Contract the outer abstractions and compute $F_b\ChurchNumeral{n}$. Numerical projections recover $i,c,n$. One query supplies $p(n)$, and the two numerical pairings prepare the input for $M$. Its assumed reduction gives the code $A(p(n),i,n)$. The dyadic term gives a code of $2^{-n}$. Twice applying rational addition gives a code whose value is $\RationalValue{A(p(n),i,n)}+2\cdot2^{-n}$. The rational comparison term then gives the asserted answer. All these reductions are finite and may be performed inside application contexts. The outer abstractions bind the only free variables, and confluence excludes other numeral outputs.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    To make the program explicit, fix a code $c$ for the radius $r$ and put $b=\NatPair{i}{c}$. Queries, numerical pairing,
    the fixed distance-approximation term, and the rational arithmetic just constructed give a closed stage program
    $\LambdaBallTest{b}$. On every name and stage it returns one if the displayed inequality holds and zero otherwise. Put
    $$G_o:=\lambdaab{k}{\LambdaZeroTest\,(\LambdaBallTest{b}\,o\,k)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},
    \qquad I:=\lambdaab{x}{x}.$$
    The closed term
    $$\LambdaBallSemidecider{b}:=\lambdaab{o}{\lambdaab{a}{\LambdaResultSearch\,G_o\,I}}$$
    ignores $a$ and returns the least successful stage. If every stage fails, the result-search lemma excludes every numeral
    output, under any reduction order. Combined with the two estimates above, this proves exact semidecision on all valid
    Cauchy names. The Sierpi\'nski semidecision criterion gives the computable characteristic map.
-/
theorem metricBallTestProgram_computes {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)) (b : ℕ) :
    UniformNumericalComputes (metricBallTestProgram M b)
      (fun p n => if metricStageTest approx p b n then 1 else 0) := by
  simpa [metricBallTestProgram,metricStageTest,Nat.unpair_pair] using
    (metricStageProgram_computes approx hM).reindex (insertBallCode_computes b)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Exact semidecision and its code transformation
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Put
    $$G_{b,o}:=\lambdaab{k}{\LambdaZeroTest\,(\LambdaBallTest{b}\,o\,k)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},
    \qquad I:=\lambdaab{x}{x},$$
    and define the closed semidecision program
    $$\LambdaBallSemidecider{b}:=\lambdaab{o}{\lambdaab{a}{\LambdaResultSearch\,G_{b,o}\,I}}.$$
    Its numerical argument $a$ is unused. The zero test reverses the answers so that the result-search term stops exactly on
    a successful stage.
-/
theorem metricBallSemidecider_runs_iff {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode))
    (p : ℕ → ℕ) (b n m : ℕ) :
    OracleRuns p (metricBallSemidecider M b) n m ↔
      metricStageTest approx p b m ∧ ∀ k < m, ¬ metricStageTest approx p b k := by
  rw [metricBallSemidecider,digitSearchProgram_runs_iff (metricBallTestProgram_computes approx hM b).1
    p _ ((metricBallTestProgram_computes approx hM b).2 p)]
  simp

theorem metricBallSemidecider_domain {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode))
    (p : ℕ → ℕ) (b n : ℕ) :
    (∃ m, OracleRuns p (metricBallSemidecider M b) n m) ↔ ∃ k, metricStageTest approx p b k := by
  rw [metricBallSemidecider,digitSearchProgram_domain (metricBallTestProgram_computes approx hM b).1
    p _ ((metricBallTestProgram_computes approx hM b).2 p)]
  simp

theorem metricBallSemidecider_closed {M : AlphaTerm} (hM : M.Closed) (b : ℕ) :
    (metricBallSemidecider M b).Closed :=
  digitSearchProgram_closed (reindexProgram_closed (metricStageProgram_closed hM) (insertBallCode_computes b).1)

end NamedLambda.AlphaTerm

namespace LambdaMetricApproximation
variable {q : ℕ → X} (A : LambdaMetricApproximation q)

abbrev ballUpper := A.toRationalMetricApproximation.ballUpper
abbrev ballTest := A.toRationalMetricApproximation.ballTest

def stageValue (p : ℕ → ℕ) (z : ℕ) : ℕ :=
  if A.ballTest p ((z.unpair.1.unpair.1,RationalCode.ofNat z.unpair.1.unpair.2),z.unpair.2) then 1 else 0

theorem stageProgram_computes : UniformNumericalComputes (metricStageProgram A.program) A.stageValue := by
  unfold stageValue
  simpa [ballTest,RationalMetricApproximation.ballTest,RationalMetricApproximation.ballUpper,
    RationalCode.lt_iff] using metricStageProgram_computes A.approx A.computes

theorem ballTestProgram_computes (i : ℕ) (r : RationalCode) :
    UniformNumericalComputes (metricBallTestProgram A.program (Nat.pair i r.natCode))
      (fun p n => if A.ballTest p ((i,r),n) then 1 else 0) := by
  simpa [metricBallTestProgram,stageValue,Nat.unpair_pair] using
    A.stageProgram_computes.reindex (insertBallCode_computes (Nat.pair i r.natCode))

theorem ballSemidecider_closed (b : ℕ) : (metricBallSemidecider A.program b).Closed :=
  digitSearchProgram_closed (reindexProgram_closed A.stageProgram_computes.1 (insertBallCode_computes b).1)

theorem ballSemidecider_runs_iff (p : ℕ → ℕ) (i : ℕ) (r : RationalCode) (n m : ℕ) :
    OracleRuns p (metricBallSemidecider A.program (Nat.pair i r.natCode)) n m ↔
      A.ballTest p ((i,r),m) = true ∧ ∀ k < m, A.ballTest p ((i,r),k) = false := by
  rw [metricBallSemidecider,digitSearchProgram_runs_iff (A.ballTestProgram_computes i r).1
    p _ ((A.ballTestProgram_computes i r).2 p)]
  simp

variable [CompleteSpace X]

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Uniform semidecision of rational balls
-/
theorem ballSemidecider_domain (p : cauchyNameDomain q) (i : ℕ) (r : RationalCode) :
    (∃ m, OracleRuns p.val (metricBallSemidecider A.program (Nat.pair i r.natCode)) 0 m) ↔
      cauchyRepresentation q p ∈ Metric.ball (q i) (r.value : ℝ) := by
  rw [metricBallSemidecider,digitSearchProgram_domain (A.ballTestProgram_computes i r).1
    p.val _ ((A.ballTestProgram_computes i r).2 p.val)]
  simp only [ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not]
  exact ⟨fun ⟨n,hn⟩ => A.toRationalMetricApproximation.mem_ball_of_test p i r n hn,
    A.toRationalMetricApproximation.exists_ballTest_of_mem p i r⟩

include A in
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The associated Cauchy representation is the one already defined:
    $$p \in \DomainOf{\rho_X}
    \quad\Longleftrightarrow\quad
    d(q_{p(n)},q_{p(m)})\le 2^{-n}\quad(m\ge n),$$
    and
    $$\rho_X(p)=\lim_n q_{p(n)}.$$
    The representation is \termdefineas{effective Cauchy representation}{effective} because the Cauchy-name condition is a
    uniformly effectively closed condition on finite coordinates: failure is witnessed by rational bounds proving
    $d(q_{p(n)},q_{p(m)})>2^{-n}$ for some $m\ge n$. Metric balls around dense points can likewise be semidecided at
    rational precisions from the computable distance data.
-/
theorem semidecidable_ball (hq : DenseRange q) (i : ℕ) (r : RationalCode) :
    SemidecidableFromNames (cauchyRepresentationObject q hq) (Metric.ball (q i) (r.value : ℝ)) :=
  ⟨metricBallSemidecider A.program (Nat.pair i r.natCode),A.ballSemidecider_closed _,
    fun p => A.ballSemidecider_domain p i r⟩

include A in
theorem computable_ball_characteristic (hq : DenseRange q) (i : ℕ) (r : RationalCode) :
    HasComputableRealizer (cauchyRepresentationObject q hq) sierpinskiRepresentation
      (fun x => x ∈ Metric.ball (q i) (r.value : ℝ)) :=
  (lambda_computable_sierpinski_iff _ _).mpr (A.semidecidable_ball hq i r)

include A in
theorem semidecidable_rational_ball (hq : DenseRange q) (i : ℕ) (r : ℚ) :
    SemidecidableFromNames (cauchyRepresentationObject q hq) (Metric.ball (q i) (r : ℝ)) := by
  obtain ⟨c,hc⟩ := RationalCode.value_surjective r
  simpa only [hc] using A.semidecidable_ball hq i c

include A in
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Uniform semidecision of rational balls
-/
theorem computable_rational_ball_characteristic (hq : DenseRange q) (i : ℕ) (r : ℚ) :
    HasComputableRealizer (cauchyRepresentationObject q hq) sierpinskiRepresentation
      (fun x => x ∈ Metric.ball (q i) (r : ℝ)) :=
  (lambda_computable_sierpinski_iff _ _).mpr (A.semidecidable_rational_ball hq i r)

end LambdaMetricApproximation
end PolishSpaceBook
