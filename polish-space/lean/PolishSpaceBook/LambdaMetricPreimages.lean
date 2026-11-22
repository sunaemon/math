module

public import PolishSpaceBook.LambdaEnumeratedBallSemidecision
public import PolishSpaceBook.LambdaNumericalSearch

@[expose] public section

/-! # Effective inverse images using closed lambda programs

Uniform total enumeration of rational-ball preimages is equivalent to a lambda
realizer. Total metric tests, rather than partial computations, are composed
with the realizer before search. This makes the exact domain follow directly
from the existing search theorem.
-/
namespace PolishSpaceBook
open Set Filter Topology NamedLambda NamedLambda.AlphaTerm
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- One closed ordinary term enumerates every target ball's preimage. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For the criterion below, uniform enumeration means one total numerical lambda program computing $E(b,k)$ from
    $\NatPair{b}{k}$, where $b$ codes a basic ball in $Y$ and $k$ is a stage. Output zero denotes an empty stage, and
    output $c+1$ denotes the rational ball in $X$ coded by $c$. For each fixed $b$, the union of the emitted balls must be
    the preimage of the ball coded by $b$. The same closed term serves every target ball.
-/
def HasEnumerableBallPreimages {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (qX : ℕ → X) (qY : ℕ → Y) (f : X → Y) : Prop :=
  ∃ E : AlphaTerm, ∃ e : ℕ → ℕ, NumericalComputes E e ∧ ∀ b,
    (⋃ k, enumeratedRationalBall qX (e (Nat.pair b k))) =
      f ⁻¹' Metric.ball (qY b.unpair.1) ((RationalCode.ofNat b.unpair.2).value : ℝ)

/-- Pullback uses the total finite-trial name before searching for a nonzero digit. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Computable pullback of semidecidable sets
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Let $Q$ compute a realizer $F$ of $f$, and let $P_e$ semidecide membership in $V$. By the Sierpi\'nski semidecision
    criterion, the closed term
    $$C_e:=\lambdaab{o}{\LambdaFiniteTrial\,o\,\ChurchNumeral{e}\,\ChurchNumeral{0}}$$
    produces a total name whose $k$th digit is nonzero exactly when the $k$th finite trial succeeds. Compose $C_e$ with $Q$
    by lambda substitution. On a valid input name $p$, every digit of the composite is the corresponding finite-trial
    answer for $F(p)$. Search for a nonzero digit. The exact search theorem gives a numeral output precisely when some
    trial succeeds, equivalently when $P_e$ has an output on $F(p)$. Since $F(p)$ names $f(\delta_X(p))$, this is exactly
    $\delta_X(p)\in f^{-1}(V)$. All terms are fixed before the input name is supplied. For Cauchy representations, the
    effective-basis lemma identifies these semidecidable sets with the effectively open sets.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    A computable map
    $f:X\to Y$ pulls effectively open sets of $Y$ back to effectively open sets of $X$, because a realizer for $f$
    transforms Cauchy names before the semidecision procedure runs. Thus computable maps preserve effective openness under
    preimages,
-/
theorem SemidecidableFromNames.preimage {X Y : Type*}
    {δX : Representation X} {δY : Representation Y} {f : X → Y} {V : Set Y}
    (hV : SemidecidableFromNames δY V) (hf : HasComputableRealizer δX δY f) :
    SemidecidableFromNames δX (f ⁻¹' V) := by
  apply (lambda_computable_sierpinski_iff _ _).mp
  exact ((lambda_computable_sierpinski_iff δY V).mpr hV).comp hf

namespace LambdaFunction

/-- Insert a numerical parameter into one fixed total-test/search template. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Parameterized search compiler
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Fix named representatives of $\LambdaTermName{stagePredicate}$, numerical pairing, zero testing, result search
    and the identity. Construct the code
    of $\ChurchNumeral{b}$, then build $\LambdaTermName{paramStage}_b$, $\LambdaTermName{paramSearchTest}_{b,o}$ and
    $\LambdaTermName{paramSearch}_b$ using application and abstraction constructors. The
    coding identities identify the decoded term with the displayed closed term, so the program enumeration retains it.
    Every numerical operation in this recipe is primitive recursive and has a closed lambda implementation. Exactness of
    result search gives the assertion about outputs, because the test for that search is zero precisely at a nonzero
    answer of $\LambdaTermName{paramStage}_b$.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We record the uniform constructions used in the inverse-image criterion. All programs below use the same lambda
    syntax and numerical pairing as above. Fix a closed term $\LambdaTermName{stagePredicate}$ and define
    $$\begin{aligned}
    \LambdaTermName{paramStage}_b&:=\lambdaab{o}{\lambdaab{k}{\LambdaTermName{stagePredicate}\,o\,
     (\LambdaNumericPair\,\ChurchNumeral{b}\,k)}},\\
    \LambdaTermName{paramSearchTest}_{b,o}&:= \lambdaab{k}{ \LambdaZeroTest\,( \LambdaTermName{paramStage}_bok)\,
    \ChurchNumeral{1}\, \ChurchNumeral{0}},\\
    \LambdaTermName{identity}&:=\lambdaab{y}{y},\\
    \LambdaTermName{paramSearch}_b&:= \lambdaab{o}{ \lambdaab{a}{ \LambdaResultSearch\,
    \LambdaTermName{paramSearchTest}_{b,o}\, \LambdaTermName{identity}}}.
    \end{aligned}$$
    Choose the internal binders fresh and expand the abbreviations before supplying the arguments.
-/
theorem exists_parameter_search_compiler (P : AlphaTerm) (hP : P.Closed) :
    ∃ c : ℕ → ℕ, CodeTransform c ∧ ∀ b,
      Term.closedProgram (c b) = digitSearchProgram (reindexProgram P (insertBallCode b)) := by
  obtain ⟨K,hK⟩ := Quotient.exists_rep numericalPairTerm
  obtain ⟨T,hT⟩ := Quotient.exists_rep P
  obtain ⟨Z,hZ⟩ := Quotient.exists_rep zeroTestTerm
  obtain ⟨S,hS⟩ := Quotient.exists_rep resultSearchTerm
  obtain ⟨I,hI⟩ := Quotient.exists_rep identityProgram
  change mk K = numericalPairTerm at hK
  change mk T = P at hT
  change mk Z = zeroTestTerm at hZ
  change mk S = resultSearchTerm at hS
  change mk I = identityProgram at hI
  refine ⟨fun b => (ballSemideciderSyntax K T Z S I b).code,
    ballSemideciderSyntax_transform K T Z S I,fun b => ?_⟩
  apply closedProgram_eq_of_mk_decode
  · simp only [Term.decode_code,ballSemideciderSyntax,mk_digitSearchSyntax Z S I _ hZ hS hI,
      mk_reindexSyntax,mk_insertBallSyntax K hK,hT]
  · exact digitSearchProgram_closed (reindexProgram_closed hP (insertBallCode_computes b).1)

end LambdaFunction

namespace LambdaMetricApproximation
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
variable {qX : ℕ → X} {qY : ℕ → Y}
variable (A : LambdaMetricApproximation qX) (B : LambdaMetricApproximation qY)
/-- The stage test is total on each valid input name, because the realizer is total there. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $Q$ compute a realizer $F$ of $f$. Finite use and admissibility give continuity. For each target ball code $b$,
    compose the total rational-ball stage test with $Q$: on a valid input name $p$ and precision $k$, compute the stage
    answer using the name $F(p)$. Substitution of the name-producing term preserves this finite computation. Each stage
    therefore terminates and returns exactly the stage answer for the output name. Searching these zero-or-one answers
    for a nonzero digit yields a semidecider whose domain is exactly the preimage of the ball. This conclusion uses the
    exact search theorem for total tests, including exclusion of numeral outputs when every stage fails.
-/
theorem preimage_stage_runs {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)} {Q : AlphaTerm}
    (hQ : TypeTwoComputes Q F) (p : D) (b n : ℕ) :
    OracleRuns p.val
      (reindexProgram (compositionProgram (metricStageProgram B.program) Q) (insertBallCode b)) n
      (if metricStageTest B.approx (F p) b n then 1 else 0) := by
  apply reindexProgram_runs
    (compositionProgram_closed B.stageProgram_computes.1 hQ.1) (insertBallCode_computes b).1
    p.val n (Nat.pair b n) _ ((insertBallCode_computes b).2 n)
  apply compositionProgram_runs B.stageProgram_computes.1 hQ.1
  · simpa [metricStageTest,Nat.unpair_pair] using
      (metricStageProgram_computes B.approx B.computes).2 (F p) (Nat.pair b n)
  · intro k
    exact (hQ.2 p k _).mpr rfl

variable [CompleteSpace X] [CompleteSpace Y]
include A B

/-- The uniform semidecision compiler is a fixed syntax template with only the ball numeral varying. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    The construction in §{sec:lambda-metric-realizer-programs} inserts the numeral for $b$ into one fixed syntax template.
    Its code $c(b)$ is primitive recursive in $b$ and computed by a closed lambda term. Apply the source-space extraction
    program of §{sec:lambda-prefix-margin-programs} to $\NatPair{c(b)}{k}$. The resulting program is total on every pair
    $\NatPair{b}{k}$ and enumerates precisely the ball preimage, by the effective-basis lemma. Thus the enumeration is
    uniform in both the target ball and its stage.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the forward inverse-image construction, let $\LambdaTermName{nameRealizer}$ compute the output name and let
    $R_Y$ be the total rational-ball
    stage term for the target metric. Take
    $$\LambdaTermName{stagePredicate}:=\lambdaab{o}{\lambdaab{z}{R_Y\,(\LambdaTermName{nameRealizer}o)\,z}}.$$
    On every valid input name, lambda substitution gives exactly the stage answer for the output name. The preceding
    proposition therefore supplies a semidecider for each target-ball preimage and one numerical compiler $\chi$. Compose
    that compiler with the source-space extraction term:
    $$\LambdaTermName{forwardEnumeration}:=\lambdaab{z}{\LambdaExtractBall{M_X}\,
     (\LambdaNumericPair\,(\LambdaTermName{indexCompiler}(\LambdaNumericProjection{1}z))\,
     (\LambdaNumericProjection{2}z))},$$
    where $\LambdaTermName{indexCompiler}$ computes $\chi$. This ordinary closed term is total on every numerical
    input. At input $\NatPair{b}{k}$ it
    returns precisely the $k$th extraction output for the preimage semidecider $P_{\chi(b)}$. The extraction theorem proves
    that these outputs enumerate exactly the preimage, with zero representing an empty stage.
-/
theorem enumerableBallPreimages_of_realizer
    (hqX : DenseRange qX) (hqY : DenseRange qY) (f : X → Y)
    (hf : HasComputableRealizer (cauchyRepresentationObject qX hqX)
      (cauchyRepresentationObject qY hqY) f) : HasEnumerableBallPreimages qX qY f := by
  obtain ⟨F,⟨Q,hQ⟩,hF⟩ := hf
  let P := compositionProgram (metricStageProgram B.program) Q
  have hP : P.Closed := compositionProgram_closed B.stageProgram_computes.1 hQ.1
  obtain ⟨c,hc,hcode⟩ := LambdaFunction.exists_parameter_search_compiler P hP
  obtain ⟨C,hC⟩ := hc.2
  have hC : NumericalComputes C c := hC
  let E := numericalCompose (extractedBallProgram A.program)
    (pairNumerical (numericalCompose C (numericalProjectionTerm true)) (numericalProjectionTerm false))
  let e (z : ℕ) := extractedBallNumber A.approx (Nat.pair (c z.unpair.1) z.unpair.2)
  have hE : NumericalComputes E e :=
    (extractedBallProgram_computes A.approx A.computes).comp
      ((hC.comp (projection_computes true)).pair (projection_computes false))
  refine ⟨E,e,hE,fun b => ?_⟩
  have hs (p : cauchyNameDomain qX) :
      (∃ m, OracleRuns p.val (Term.closedProgram (c b)) 0 m) ↔
        cauchyRepresentation qX p ∈ f ⁻¹'
          Metric.ball (qY b.unpair.1) ((RationalCode.ofNat b.unpair.2).value : ℝ) := by
    rw [hcode]
    rw [digitSearchProgram_domain (reindexProgram_closed hP (insertBallCode_computes b).1)
      p.val _ (B.preimage_stage_runs hQ p b) 0]
    simp only [ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not]
    have hb := B.ballSemidecider_domain (F p) b.unpair.1 (RationalCode.ofNat b.unpair.2)
    rw [metricBallSemidecider_domain B.approx B.computes] at hb
    have hFp : cauchyRepresentation qY (F p) = f (cauchyRepresentation qX p) := hF p
    simpa only [RationalCode.natCode_ofNat,Nat.pair_unpair,hFp,Set.mem_preimage] using hb
  simpa [e] using (A.extractedBallNumber_cover hqX hs).symm

end LambdaMetricApproximation
end PolishSpaceBook
