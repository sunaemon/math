module

public import PolishSpaceBook.LambdaEffectiveBallEnumeration
public import PolishSpaceBook.LambdaMetricBallCodes

@[expose] public section

/-! # Compiling enumerated rational balls into a lambda semidecider

A trial proposes a positive enumeration output and a finite certificate bound.
No unbounded execution of the enumeration is performed inside a trial. This
keeps every trial total, even for an arbitrary or partial program index.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace NamedLambda.AlphaTerm
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

/-- The ordinary output-candidate tester with all three inputs numerically paired. -/
def jointOutputCandidateBody (Z : AlphaTerm) :=
  let E := app (numericalProjectionTerm true) Z
  let R := app (numericalProjectionTerm false) Z
  app (app (app outputCandidateTerm E) (app (numericalProjectionTerm true) R))
    (app (numericalProjectionTerm false) R)

def jointOutputCandidate := lam 40 (jointOutputCandidateBody (var 40))

theorem jointOutputCandidate_computes : NumericalComputes jointOutputCandidate
    (fun z => if Term.outputCandidate z.unpair.1 z.unpair.2.unpair.1 z.unpair.2.unpair.2 then 1 else 0) := by
  have hf (b : Bool) : (numericalProjectionTerm b).fv = ∅ := numericalProjectionTerm_closed b
  constructor
  · unfold jointOutputCandidate jointOutputCandidateBody Closed
    simp [fv_lam,fv_app,fv_var,hf,(show outputCandidateTerm.fv = ∅ from outputCandidateTerm_closed)]
  · intro z
    have he : (jointOutputCandidateBody (var 40)).subst 40 (numeral z) =
        jointOutputCandidateBody (numeral z) := by
      simp [jointOutputCandidateBody,subst_app,subst_var,
        subst_closed _ _ _ outputCandidateTerm_closed,
        subst_closed _ _ _ (numericalProjectionTerm_closed true),
        subst_closed _ _ _ (numericalProjectionTerm_closed false)]
    have hs : Beta (app jointOutputCandidate (numeral z)) (jointOutputCandidateBody (numeral z)) := by
      rw [← he]; exact Beta.contract 40 _ _
    apply (Relation.ReflTransGen.single hs).trans
    have hr := numericalProjectionTerm_apply false z
    have hn := (beta_steps_app_right (numericalProjectionTerm true) hr).trans
      (numericalProjectionTerm_apply true z.unpair.2)
    have hk := (beta_steps_app_right (numericalProjectionTerm false) hr).trans
      (numericalProjectionTerm_apply false z.unpair.2)
    exact (beta_steps_app (beta_steps_app (beta_steps_app_right outputCandidateTerm
      (numericalProjectionTerm_apply true z)) hn) hk).trans (outputCandidateTerm_apply _ _ _)

/-- Numerical input `pair e (pair j (pair b (pair t n)))`; proposed output is `b+1`. -/
def enumerationCertificateInputProgram :=
  let E := numericalProjectionTerm true
  let Y := numericalProjectionTerm false
  let J := firstOutput Y
  let B := firstOutput (secondOutput Y)
  let T := firstOutput (secondOutput (secondOutput Y))
  pairNumerical E (pairNumerical J (pairNumerical (numericalCompose successorTerm B) T))

def enumerationCertificateInput (z : ℕ) :=
  Nat.pair z.unpair.1 (Nat.pair z.unpair.2.unpair.1
    (Nat.pair (z.unpair.2.unpair.2.unpair.1 + 1) z.unpair.2.unpair.2.unpair.2.unpair.1))

theorem enumerationCertificateInput_computes :
    NumericalComputes enumerationCertificateInputProgram enumerationCertificateInput :=
  (projection_computes true).pair ((projection_computes false).first.pair
    ((successor_computes.comp (projection_computes false).second.first).pair
      (projection_computes false).second.second.first))

def enumerationMetricInputProgram :=
  let Y := numericalProjectionTerm false
  pairNumerical (firstOutput (secondOutput Y)) (secondOutput (secondOutput (secondOutput Y)))

def enumerationMetricInput (z : ℕ) :=
  Nat.pair z.unpair.2.unpair.2.unpair.1 z.unpair.2.unpair.2.unpair.2.unpair.2

theorem enumerationMetricInput_computes : NumericalComputes enumerationMetricInputProgram enumerationMetricInput :=
  (projection_computes false).second.first.pair (projection_computes false).second.second.second

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Encode a trial by $y:=\NatPair{j}{\NatPair{b}{\NatPair{h}{n}}}$ and the joint input by $z:=\NatPair{e}{y}$. Numerical
    projections recover $e,j,b,h,n$. With these letters abbreviating the projection terms, define the closed term
    $\LambdaEnumerationTrial{M}$ by
    $$\begin{aligned}
    \LambdaTermName{outputProof}&:=\LambdaOutputCandidate\,e\,j\,
     (\LambdaNumericPair\,(\LambdaSucc\,b)\,h),\\
    \LambdaTermName{ballTrial}&:=R_M\,o\,(\LambdaNumericPair\,b\,n),\\
    \LambdaEnumerationTrial{M}\,o\,z&\to_\beta^*\LambdaMul\,\LambdaTermName{outputProof}\,\LambdaTermName{ballTrial}.
    \end{aligned}$$
    The first factor uses the finite numerical-output test of §{sec:lambda-program-input-codes}: it checks whether a
    reduction certificate below bound $h$ witnesses output $b+1$ for program $P_e$ on input $j$. It does not run $P_e$ until
    termination. The second factor checks membership in the proposed ball at precision $n$.
-/
def enumerationTrialProgram (M : AlphaTerm) := combineOutputProgram multiplicationTerm
  (liftNumericalProgram (numericalCompose jointOutputCandidate enumerationCertificateInputProgram))
  (reindexProgram (metricStageProgram M) enumerationMetricInputProgram)

def enumerationTrialValue (approx : ℕ × (ℕ × ℕ) → RationalCode) (p : ℕ → ℕ) (z : ℕ) :=
  let e := z.unpair.1
  let y := z.unpair.2
  let j := y.unpair.1
  let b := y.unpair.2.unpair.1
  let t := y.unpair.2.unpair.2.unpair.1
  let n := y.unpair.2.unpair.2.unpair.2
  (if Term.outputCandidate e j (Nat.pair (b+1) t) then 1 else 0) *
    (if metricStageTest approx p b n then 1 else 0)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Total enumeration trial
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Pairing, successor and the numerical-output certificate checker are total ordinary lambda programs. The rational-ball
    stage is total with input queries. Their composition and numerical product therefore compute exactly the two zero-or-one
    factors displayed above. The proposed output is always positive, so no trial treats an empty enumeration stage as a
    ball.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For the reverse implication, encode a total ball enumeration by a numerical function $f$: output zero denotes an empty
    stage, and output $b+1$ denotes the ball whose center-radius code is $b$. Let $P_e$ compute $f$. Enumerate all
    quadruples $\Tuple{j,b,h,n}$. First apply the finite numerical-output test to the proposed computation
    $P_e\ChurchNumeral{j}\to_\beta^*\ChurchNumeral{b+1}$, searching only certificates below bound $h$. Also apply the
    rational-ball test at precision $n$ to ball $b$ and the input name. Multiply the two zero-or-one answers. Every trial
    terminates, even without assuming that $P_e$ is total.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Encode a trial by $y:=\NatPair{j}{\NatPair{b}{\NatPair{h}{n}}}$ and the joint input by $z:=\NatPair{e}{y}$. Numerical
    projections recover $e,j,b,h,n$. With these letters abbreviating the projection terms, define the closed term
    $\LambdaEnumerationTrial{M}$ by
    $$\begin{aligned}
    \LambdaTermName{outputProof}&:=\LambdaOutputCandidate\,e\,j\,
     (\LambdaNumericPair\,(\LambdaSucc\,b)\,h),\\
    \LambdaTermName{ballTrial}&:=R_M\,o\,(\LambdaNumericPair\,b\,n),\\
    \LambdaEnumerationTrial{M}\,o\,z&\to_\beta^*\LambdaMul\,\LambdaTermName{outputProof}\,\LambdaTermName{ballTrial}.
    \end{aligned}$$
    The first factor uses the finite numerical-output test of §{sec:lambda-program-input-codes}: it checks whether a
    reduction certificate below bound $h$ witnesses output $b+1$ for program $P_e$ on input $j$. It does not run $P_e$ until
    termination. The second factor checks membership in the proposed ball at precision $n$.
-/
theorem enumerationTrialProgram_computes {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)) :
    UniformNumericalComputes (enumerationTrialProgram M) (enumerationTrialValue approx) := by
  have hc := (jointOutputCandidate_computes.comp enumerationCertificateInput_computes).uniform
  have hm := (metricStageProgram_computes approx hM).reindex enumerationMetricInput_computes
  unfold enumerationTrialValue
  simpa [enumerationTrialProgram,enumerationCertificateInput,enumerationMetricInput,
    metricStageTest,Nat.unpair_pair] using
    hc.combine hm multiplicationTerm_closed (fun a b => a*b) multiplicationTerm_apply

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Total enumeration trial
-/
theorem enumerationTrialValue_success (approx : ℕ × (ℕ × ℕ) → RationalCode) (p : ℕ → ℕ) (e y : ℕ) :
    enumerationTrialValue approx p (Nat.pair e y) ≠ 0 ↔
      Term.outputCandidate e y.unpair.1
        (Nat.pair (y.unpair.2.unpair.1+1) y.unpair.2.unpair.2.unpair.1) = true ∧
      metricStageTest approx p y.unpair.2.unpair.1 y.unpair.2.unpair.2.unpair.2 := by
  simp [enumerationTrialValue,Nat.unpair_pair,and_comm]

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Insert the fixed index $e$ and reverse the answers for result search:
    $$\begin{aligned}
    \LambdaTermName{enumStage}_e&:=\lambdaab{o}{\lambdaab{y}{\LambdaEnumerationTrial{M}\,o\,
     (\LambdaNumericPair\,\ChurchNumeral{e}\,y)}},\\
    \LambdaTermName{enumSearch}_{e,o}&:= \lambdaab{y}{ \LambdaZeroTest\,( \LambdaTermName{enumStage}_eoy)\,
    \ChurchNumeral{1}\, \ChurchNumeral{0}},\\
    \LambdaTermName{identity}&:=\lambdaab{y}{y},\\
    \LambdaEnumerationSemidecider{M}{e}&:= \lambdaab{o}{ \lambdaab{a}{ \LambdaResultSearch\,
    \LambdaTermName{enumSearch}_{e,o}\, \LambdaTermName{identity}}}.
    \end{aligned}$$
    The numerical argument $a$ is unused. Choose all internal binders fresh once, and expand the abbreviations before
    supplying the arguments.
-/
def enumeratedBallSemidecider (M : AlphaTerm) (e : ℕ) :=
  digitSearchProgram (reindexProgram (enumerationTrialProgram M) (insertBallCode e))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Exact search and uniform compilation
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Each trial terminates, so the result-search theorem gives the least successful trial or excludes every numeral output
    when there is no successful trial. Soundness of the finite output test identifies a successful proposal with an actual
    output of $P_e$. Conversely, every finite numerical computation has a certificate below some finite bound. Pairing that
    bound with its input, output code and a successful ball precision produces a successful trial.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Insert the fixed index $e$ and reverse the answers for result search:
    $$\begin{aligned}
    \LambdaTermName{enumStage}_e&:=\lambdaab{o}{\lambdaab{y}{\LambdaEnumerationTrial{M}\,o\,
     (\LambdaNumericPair\,\ChurchNumeral{e}\,y)}},\\
    \LambdaTermName{enumSearch}_{e,o}&:= \lambdaab{y}{ \LambdaZeroTest\,( \LambdaTermName{enumStage}_eoy)\,
    \ChurchNumeral{1}\, \ChurchNumeral{0}},\\
    \LambdaTermName{identity}&:=\lambdaab{y}{y},\\
    \LambdaEnumerationSemidecider{M}{e}&:= \lambdaab{o}{ \lambdaab{a}{ \LambdaResultSearch\,
    \LambdaTermName{enumSearch}_{e,o}\, \LambdaTermName{identity}}}.
    \end{aligned}$$
    The numerical argument $a$ is unused. Choose all internal binders fresh once, and expand the abbreviations before
    supplying the arguments.
-/
theorem enumeratedBallSemidecider_runs_iff {M : AlphaTerm}
    (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode))
    (e : ℕ) (p : ℕ → ℕ) (a m : ℕ) :
    OracleRuns p (enumeratedBallSemidecider M e) a m ↔
      enumerationTrialValue approx p (Nat.pair e m) ≠ 0 ∧
      ∀ k < m, enumerationTrialValue approx p (Nat.pair e k) = 0 := by
  have hc := (enumerationTrialProgram_computes approx hM).reindex (insertBallCode_computes e)
  exact digitSearchProgram_runs_iff hc.1 p _ (hc.2 p) a m

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Exact search and uniform compilation
-/
theorem enumeratedBallSemidecider_domain {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode))
    (e : ℕ) (p : ℕ → ℕ) (a : ℕ) :
    (∃ m, OracleRuns p (enumeratedBallSemidecider M e) a m) ↔
      ∃ j b, Relation.ReflTransGen Beta (app (Term.closedProgram e) (numeral j)) (numeral (b+1)) ∧
        ∃ n, metricStageTest approx p b n := by
  have hc := (enumerationTrialProgram_computes approx hM).reindex (insertBallCode_computes e)
  rw [enumeratedBallSemidecider,digitSearchProgram_domain hc.1 p _ (hc.2 p) a]
  simp only [enumerationTrialValue_success]
  constructor
  · rintro ⟨y,hy,hm⟩
    exact ⟨y.unpair.1,y.unpair.2.unpair.1,
      (outputTest_exists_iff _ _ _).mp ⟨y.unpair.2.unpair.2.unpair.1,
        by simpa [Term.outputCandidate] using hy⟩,y.unpair.2.unpair.2.unpair.2,hm⟩
  · rintro ⟨j,b,hb,n,hn⟩
    obtain ⟨t,ht⟩ := (outputTest_exists_iff _ _ _).mpr hb
    refine ⟨Nat.pair j (Nat.pair b (Nat.pair t n)),?_,?_⟩
    · simpa [Term.outputCandidate] using ht
    · simpa using hn

end NamedLambda.AlphaTerm

namespace LambdaFunction

/-- One primitive-recursive, lambda-computed compiler for every enumeration index. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Exact search and uniform compilation
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For the compiler, fix named representatives of the trial term, pairing, zero testing, result search and the identity.
    Compute the syntax code of $\ChurchNumeral{e}$, insert it into the displayed template for
    $\LambdaTermName{enumStage}_e$, and form the two
    remaining templates. Only the numeral-code map and finitely many application and abstraction constructors are used.
    These numerical maps are primitive recursive and computed by closed lambda terms. The syntax coding identities show that
    decoding the result gives precisely the displayed closed semidecider; the program enumeration therefore retains it. No
    evaluation of $P_e$ and no digit of the input name is needed to compute this code.
-/
theorem exists_enumeration_semidecider_compiler (M : AlphaTerm)
    (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)) :
    ∃ f : ℕ → ℕ, CodeTransform f ∧
      ∀ e, Term.closedProgram (f e) = enumeratedBallSemidecider M e := by
  obtain ⟨K,hK⟩ := Quotient.exists_rep numericalPairTerm
  obtain ⟨P,hP⟩ := Quotient.exists_rep (enumerationTrialProgram M)
  obtain ⟨Z,hZ⟩ := Quotient.exists_rep zeroTestTerm
  obtain ⟨S,hS⟩ := Quotient.exists_rep resultSearchTerm
  obtain ⟨I,hI⟩ := Quotient.exists_rep identityProgram
  change mk K = numericalPairTerm at hK
  change mk P = enumerationTrialProgram M at hP
  change mk Z = zeroTestTerm at hZ
  change mk S = resultSearchTerm at hS
  change mk I = identityProgram at hI
  refine ⟨fun e => (ballSemideciderSyntax K P Z S I e).code,
    ballSemideciderSyntax_transform K P Z S I,fun e => ?_⟩
  apply closedProgram_eq_of_mk_decode
  · simp only [Term.decode_code,ballSemideciderSyntax,mk_digitSearchSyntax Z S I _ hZ hS hI,
      mk_reindexSyntax,mk_insertBallSyntax K hK,hP]
    rfl
  · exact digitSearchProgram_closed ((enumerationTrialProgram_computes approx hM).reindex
      (insertBallCode_computes e)).1

end LambdaFunction

namespace LambdaMetricApproximation
universe u
variable {X : Type u} [MetricSpace X] {q : ℕ → X} (A : LambdaMetricApproximation q)

theorem enumeratedBallSemidecider_closed (e : ℕ) : (enumeratedBallSemidecider A.program e).Closed :=
  digitSearchProgram_closed ((enumerationTrialProgram_computes A.approx A.computes).reindex
    (insertBallCode_computes e)).1

variable [CompleteSpace X]

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    On a valid name, a successful trial certifies both $f(j)=b+1$ and membership in the corresponding ball. Conversely, if
    the represented point belongs to the union, some $f(j)$ codes a ball containing it. The finite computation of that
    output has a certificate below some bound $h$, and the ball test succeeds at some precision $n$. Hence the corresponding
    quadruple succeeds. Result search therefore gives a semidecider with exactly the required domain; empty stages never
    cause acceptance.
-/
theorem enumeration_domain (e : ℕ) (f : ℕ → ℕ) (hf : NumericalComputes (Term.closedProgram e) f)
    (p : cauchyNameDomain q) :
    (∃ m, OracleRuns p.val (enumeratedBallSemidecider A.program e) 0 m) ↔
      cauchyRepresentation q p ∈ ⋃ j, enumeratedRationalBall q (f j) := by
  rw [enumeratedBallSemidecider_domain A.approx A.computes]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨j,b,hb,n,hn⟩
    have he := numeral_output_unique (hf.2 j) hb
    refine ⟨j,?_⟩
    rw [he]
    apply A.toRationalMetricApproximation.mem_ball_of_test p b.unpair.1
      (RationalCode.ofNat b.unpair.2) n
    simpa [RationalMetricApproximation.ballTest,RationalMetricApproximation.ballUpper,
      RationalCode.lt_iff,metricStageTest] using hn
  · rintro ⟨j,hj⟩
    cases hfj : f j with
    | zero => simp [hfj,enumeratedRationalBall] at hj
    | succ b =>
      refine ⟨j,b,by simpa [hfj] using hf.2 j,?_⟩
      have hm : cauchyRepresentation q p ∈ Metric.ball (q b.unpair.1)
          ((RationalCode.ofNat b.unpair.2).value : ℝ) := by
        simpa [hfj,enumeratedRationalBall] using hj
      obtain ⟨n,hn⟩ := A.toRationalMetricApproximation.exists_ballTest_of_mem p _ _ hm
      exact ⟨n,by simpa [RationalMetricApproximation.ballTest,RationalMetricApproximation.ballUpper,
        RationalCode.lt_iff,metricStageTest] using hn⟩

include A in
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    For uniformity, use the single trial term of §{sec:lambda-metric-realizer-programs}, whose numerical input pairs $e$ with the quadruple code. Insert $\ChurchNumeral{e}$ into this fixed template, reverse its zero-or-one answers, and apply result search. The same section constructs a primitive-recursive transformation of syntax codes, itself computed by a closed lambda term, which performs these operations. It does not need to decide whether the indexed enumeration is total. Under the stated totality assumption, the preceding argument proves that its output semidecides the enumerated union.
-/
theorem uniform_enumeration_semidecider_compiler :
    ∃ c : ℕ → ℕ, LambdaFunction.CodeTransform c ∧
      ∀ e f, NumericalComputes (Term.closedProgram e) f → ∀ p : cauchyNameDomain q,
        ((∃ m, OracleRuns p.val (Term.closedProgram (c e)) 0 m) ↔
          cauchyRepresentation q p ∈ ⋃ j, enumeratedRationalBall q (f j)) := by
  obtain ⟨c,hc,he⟩ := LambdaFunction.exists_enumeration_semidecider_compiler A.program A.approx A.computes
  refine ⟨c,hc,fun e f hf p => ?_⟩
  rw [he]
  exact A.enumeration_domain e f hf p

include A in
theorem semidecidable_of_ball_enumeration (hq : DenseRange q) {E : AlphaTerm} {f : ℕ → ℕ}
    (hf : NumericalComputes E f) :
    SemidecidableFromNames (cauchyRepresentationObject q hq)
      (⋃ j, enumeratedRationalBall q (f j)) := by
  obtain ⟨e,he⟩ := Term.closedProgram_surjective E hf.1
  have hfe : NumericalComputes (Term.closedProgram e) f := by rwa [he]
  exact ⟨enumeratedBallSemidecider A.program e,A.enumeratedBallSemidecider_closed e,
    fun p => A.enumeration_domain e f hfe p⟩

include A in
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Effective-basis lemma
-/
theorem semidecidable_iff_ball_enumeration (hq : DenseRange q) (U : Set X) :
    SemidecidableFromNames (cauchyRepresentationObject q hq) U ↔
      ∃ E : AlphaTerm, ∃ f : ℕ → ℕ, NumericalComputes E f ∧
        U = ⋃ j, enumeratedRationalBall q (f j) := by
  constructor
  · exact A.semidecidable_has_ball_enumeration hq
  · rintro ⟨E,f,hf,rfl⟩
    exact A.semidecidable_of_ball_enumeration hq hf

end LambdaMetricApproximation
end PolishSpaceBook
