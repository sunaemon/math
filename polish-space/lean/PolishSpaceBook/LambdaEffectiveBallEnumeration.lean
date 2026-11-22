module

public import PolishSpaceBook.LambdaPrefixCertificates
public import PolishSpaceBook.LambdaOracleOutputSearch

@[expose] public section

/-! # Uniform extraction of rational balls from ordinary lambda semideciders

A trial is `pair w (pair table (pair certificate output))`, where
`w = pair prefixCode (pair center (pair radiusExponent precision))`.
The numerical program takes `pair programIndex trial`. It returns zero at an
empty stage and `pair center rationalRadiusCode + 1` at a successful stage.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace NamedLambda.AlphaTerm
set_option maxHeartbeats 800000

/-- Prepare a prefix-supported certificate for the indexed program on input zero. -/
def extractionCertificateInput (z : ℕ) :=
  let a := z.unpair.2
  Nat.pair a.unpair.1.unpair.1
    (Nat.pair a.unpair.2.unpair.1 (Nat.pair a.unpair.2.unpair.2.unpair.1
      (Nat.pair (Term.oracleProgramInput z.unpair.1 0).code
        (Term.churchNumeral a.unpair.2.unpair.2.unpair.2).code)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We can now combine this test with the Cauchy-margin program. Fix the distance-approximation term $M$, retain the indexed
    programs $P_e$, and encode a trial by
    $$\begin{aligned}
    w&:=\NatPair{\LambdaListCode{s}}{\NatPair{i}{\NatPair{\ell}{k}}},\\
    a&:=\NatPair{w}{\NatPair{\LambdaAnswerTableCode{\theta}}{\NatPair{\LambdaCertificateCode{\gamma}}{m}}}.
    \end{aligned}$$
    On input $\NatPair{e}{a}$, construct the syntax codes of $P_eo\ChurchNumeral{0}$ and $\ChurchNumeral{m}$ using the
    programs of §{sec:lambda-input-universal-evaluation}. Prepare the five-component input to $\LambdaPrefixCertificate$
    with these endpoints. Multiply its result by $\LambdaPrefixMargins{M}\ChurchNumeral{w}$, obtaining a value
    $\beta\in\{0,1\}$. Define $\LambdaExtractBall{M}$ to return
    $$\beta\bigl(\NatPair{i}{\delta_\ell}+1\bigr).$$
    Here $\delta_ \ell$ is the rational code of $2^{- \ell}$. Output zero denotes an empty stage; output
    $\NatPair{i}{r}+1$ denotes
    the ball with center $q_i$ and radius given by rational code $r$.
-/
def extractionCertificateInputProgram :=
  let E := numericalProjectionTerm true
  let A := numericalProjectionTerm false
  let W := firstOutput A
  let T := firstOutput (secondOutput A)
  let C := firstOutput (secondOutput (secondOutput A))
  let O := secondOutput (secondOutput (secondOutput A))
  let S := numericalCombine oracleInputCodeTerm E (numericalConstant 0)
  pairNumerical (firstOutput W) (pairNumerical T (pairNumerical C
    (pairNumerical S (numericalCompose numeralCodeTerm O))))

theorem extractionCertificateInput_computes :
    NumericalComputes extractionCertificateInputProgram extractionCertificateInput := by
  have he := projection_computes true
  have ha := projection_computes false
  have hs := he.combine (numericalConstant_computes 0) oracleInputCodeTerm_closed
    (fun e n => (Term.oracleProgramInput e n).code) oracleInputCodeTerm_apply
  have hn : NumericalComputes numeralCodeTerm (fun n => (Term.churchNumeral n).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  exact ha.first.first.pair (ha.second.first.pair (ha.second.second.first.pair
    (hs.pair (hn.comp ha.second.second.second))))

def extractionCheck (approx : ℕ × (ℕ × ℕ) → RationalCode) (z : ℕ) :=
  prefixCertificateValue (extractionCertificateInput z) *
    allPrefixMarginsValue approx z.unpair.2.unpair.1

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We can now combine this test with the Cauchy-margin program. Fix the distance-approximation term $M$, retain the indexed
    programs $P_e$, and encode a trial by
    $$\begin{aligned}
    w&:=\NatPair{\LambdaListCode{s}}{\NatPair{i}{\NatPair{\ell}{k}}},\\
    a&:=\NatPair{w}{\NatPair{\LambdaAnswerTableCode{\theta}}{\NatPair{\LambdaCertificateCode{\gamma}}{m}}}.
    \end{aligned}$$
    On input $\NatPair{e}{a}$, construct the syntax codes of $P_eo\ChurchNumeral{0}$ and $\ChurchNumeral{m}$ using the
    programs of §{sec:lambda-input-universal-evaluation}. Prepare the five-component input to $\LambdaPrefixCertificate$
    with these endpoints. Multiply its result by $\LambdaPrefixMargins{M}\ChurchNumeral{w}$, obtaining a value
    $\beta\in\{0,1\}$. Define $\LambdaExtractBall{M}$ to return
    $$\beta\bigl(\NatPair{i}{\delta_\ell}+1\bigr).$$
    Here $\delta_ \ell$ is the rational code of $2^{- \ell}$. Output zero denotes an empty stage; output
    $\NatPair{i}{r}+1$ denotes
    the ball with center $q_i$ and radius given by rational code $r$.
-/
def extractionCheckProgram (M : AlphaTerm) := mulNumerical
  (numericalCompose prefixCertificateProgram extractionCertificateInputProgram)
  (numericalCompose (allPrefixMarginsProgram M) (firstOutput (numericalProjectionTerm false)))

theorem extractionCheck_computes {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)) :
    NumericalComputes (extractionCheckProgram M) (extractionCheck approx) :=
  (prefixCertificateProgram_computes.comp extractionCertificateInput_computes).mul
    ((allPrefixMarginsProgram_computes approx hM).comp (projection_computes false).first)

theorem extractionCheck_success (approx : ℕ × (ℕ × ℕ) → RationalCode) (z : ℕ) :
    extractionCheck approx z ≠ 0 ↔
      prefixCertificateValue (extractionCertificateInput z) ≠ 0 ∧
      allPrefixMarginsValue approx z.unpair.2.unpair.1 ≠ 0 := mul_ne_zero_iff

theorem extractionCheck_zero_or_one (approx : ℕ × (ℕ × ℕ) → RationalCode) (z : ℕ) :
    extractionCheck approx z = 0 ∨ extractionCheck approx z = 1 := by
  rcases prefixCertificateValue_zero_or_one (extractionCertificateInput z) with h | h <;>
    rcases allPrefixMarginsValue_zero_or_one approx z.unpair.2.unpair.1 with g | g <;>
    simp [extractionCheck,h,g]

/-- Decode the geometric data of a trial, independently of its acceptance. -/
def extractionCenter (a : ℕ) := a.unpair.1.unpair.2.unpair.1
def extractionExponent (a : ℕ) := a.unpair.1.unpair.2.unpair.2.unpair.1

def extractedBallNumber (approx : ℕ × (ℕ × ℕ) → RationalCode) (z : ℕ) :=
  extractionCheck approx z *
    (Nat.pair (extractionCenter z.unpair.2) (RationalCode.dyadic (extractionExponent z.unpair.2)).natCode + 1)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We can now combine this test with the Cauchy-margin program. Fix the distance-approximation term $M$, retain the indexed
    programs $P_e$, and encode a trial by
    $$\begin{aligned}
    w&:=\NatPair{\LambdaListCode{s}}{\NatPair{i}{\NatPair{\ell}{k}}},\\
    a&:=\NatPair{w}{\NatPair{\LambdaAnswerTableCode{\theta}}{\NatPair{\LambdaCertificateCode{\gamma}}{m}}}.
    \end{aligned}$$
    On input $\NatPair{e}{a}$, construct the syntax codes of $P_eo\ChurchNumeral{0}$ and $\ChurchNumeral{m}$ using the
    programs of §{sec:lambda-input-universal-evaluation}. Prepare the five-component input to $\LambdaPrefixCertificate$
    with these endpoints. Multiply its result by $\LambdaPrefixMargins{M}\ChurchNumeral{w}$, obtaining a value
    $\beta\in\{0,1\}$. Define $\LambdaExtractBall{M}$ to return
    $$\beta\bigl(\NatPair{i}{\delta_\ell}+1\bigr).$$
    Here $\delta_ \ell$ is the rational code of $2^{- \ell}$. Output zero denotes an empty stage; output
    $\NatPair{i}{r}+1$ denotes
    the ball with center $q_i$ and radius given by rational code $r$.
-/
def extractedBallProgram (M : AlphaTerm) :=
  let W := firstOutput (numericalProjectionTerm false)
  let I := firstOutput (secondOutput W)
  let L := firstOutput (secondOutput (secondOutput W))
  mulNumerical (extractionCheckProgram M) (numericalCompose successorTerm
    (pairNumerical I (numericalCompose rationalDyadicTerm L)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Uniform ball extraction program
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    All component terms are closed and total, including the syntax-code constructors. The two tests return zero or one, so
    their product is one exactly when both succeed. The final numerical pairing, successor and multiplication implement the
    stated output convention. The successor makes every ball output positive, even when the paired code is zero. This
    construction is independent of any assumption that $P_e$ semidecides a set. Under that additional assumption, the
    Cauchy-prefix margin lemma and the soundness and completeness just proved give exact coverage, as shown in
    §{sec:tte-polish-as-represented}.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Let $P_e$ semidecide membership in $U$ on every valid name. Enumerate all finite tuples $\Tuple{s, \theta,
    \gamma,m,i, \ell,k}$,
    where $s$
    is a finite prefix, $\theta$ an answer table, $\gamma$ a reduction certificate, and the other entries are
    natural numbers. Enumerate the natural-number codes of these tuples, using $\LambdaListCode{s}$,
    $\LambdaAnswerTableCode{ \theta}$, and $\LambdaCertificateCode{ \gamma}$ for the three finite objects. Check
    that every $\Pair{j}{v}\in \theta$ satisfies $j<\Length{s}$ and $s(j)=v$, and that $\gamma$ certifies a reduction from
    $P_eo\ChurchNumeral{0}$
    to $\ChurchNumeral{m}$ using $\theta$. Check also
    $$A(s(n),i,k)+2^{-k}+2^{-\ell}<2^{-(n+1)}\qquad(n<\Length{s}).$$
    If all tests succeed, emit $\Ball{q_i}{2^{-\ell}}$; otherwise emit nothing. The closed program constructed in
    §{sec:lambda-metric-realizer-programs} performs these tests and encodes either a ball or an empty stage. It
    terminates on
    every pair consisting of a program index and a trial code, so the enumeration is uniform in $e$.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    We can now combine this test with the Cauchy-margin program. Fix the distance-approximation term $M$, retain the indexed
    programs $P_e$, and encode a trial by
    $$\begin{aligned}
    w&:=\NatPair{\LambdaListCode{s}}{\NatPair{i}{\NatPair{\ell}{k}}},\\
    a&:=\NatPair{w}{\NatPair{\LambdaAnswerTableCode{\theta}}{\NatPair{\LambdaCertificateCode{\gamma}}{m}}}.
    \end{aligned}$$
    On input $\NatPair{e}{a}$, construct the syntax codes of $P_eo\ChurchNumeral{0}$ and $\ChurchNumeral{m}$ using the
    programs of §{sec:lambda-input-universal-evaluation}. Prepare the five-component input to $\LambdaPrefixCertificate$
    with these endpoints. Multiply its result by $\LambdaPrefixMargins{M}\ChurchNumeral{w}$, obtaining a value
    $\beta\in\{0,1\}$. Define $\LambdaExtractBall{M}$ to return
    $$\beta\bigl(\NatPair{i}{\delta_\ell}+1\bigr).$$
    Here $\delta_ \ell$ is the rational code of $2^{- \ell}$. Output zero denotes an empty stage; output
    $\NatPair{i}{r}+1$ denotes
    the ball with center $q_i$ and radius given by rational code $r$.
-/
theorem extractedBallProgram_computes {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)) :
    NumericalComputes (extractedBallProgram M) (extractedBallNumber approx) :=
  (extractionCheck_computes approx hM).mul
    (successor_computes.comp ((projection_computes false).first.second.first.pair
      (rationalDyadic_computes.comp (projection_computes false).first.second.second.first)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Uniform ball extraction program
-/
theorem extractedBallNumber_eq (approx : ℕ × (ℕ × ℕ) → RationalCode) (z : ℕ) :
    extractedBallNumber approx z =
      if extractionCheck approx z ≠ 0 then
        Nat.pair (extractionCenter z.unpair.2) (RationalCode.dyadic (extractionExponent z.unpair.2)).natCode + 1
      else 0 := by
  rcases extractionCheck_zero_or_one approx z with h | h <;> simp [extractedBallNumber,h]

theorem extractionCheck_runs {approx : ℕ × (ℕ × ℕ) → RationalCode} {e a : ℕ}
    (h : extractionCheck approx (Nat.pair e a) ≠ 0) {p : ℕ → ℕ}
    (hp : p ∈ cyl (NatListCode.decode a.unpair.1.unpair.1)) :
    OracleRuns p (Term.closedProgram e) 0 a.unpair.2.unpair.2.unpair.2 := by
  have hc := ((extractionCheck_success approx _).mp h).1
  have hc := prefixCertificateValue_sound hc (by simpa [extractionCertificateInput] using hp)
  simpa [extractionCertificateInput,Term.oracleProgramInput,← app_mk,Term.mk_programSyntax,
    Term.mk_churchNumeral,var,OracleRuns] using hc

end NamedLambda.AlphaTerm

/-- Numerical enumeration convention: zero is empty, successor codes are balls. -/
def enumeratedRationalBall {X : Type*} [MetricSpace X] (q : ℕ → X) : ℕ → Set X
  | 0 => ∅
  | n + 1 => Metric.ball (q n.unpair.1) ((RationalCode.ofNat n.unpair.2).value : ℝ)

namespace LambdaMetricApproximation
universe u
variable {X : Type u} [MetricSpace X] [CompleteSpace X] {q : ℕ → X}
variable (A : LambdaMetricApproximation q) (hq : DenseRange q)
include hq

/-- A successful trial emits a ball contained in the semidecided set. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Every emitted ball is contained in $U$. By the total finite Cauchy-margin test, each point of the ball has a valid name extending $s$. The checked answer table agrees with every such extension. Soundness of the finite reduction certificate therefore makes $P_e$ halt on that name, so the point belongs to $U$. No behavior on invalid names is used.
-/
theorem extractedBall_sound {U : Set X} {e a : ℕ}
    (he : ∀ p : cauchyNameDomain q,
      (∃ m, OracleRuns p.val (Term.closedProgram e) 0 m) ↔ cauchyRepresentation q p ∈ U)
    (ha : extractionCheck A.approx (Nat.pair e a) ≠ 0) :
    Metric.ball (q (extractionCenter a)) ((1/2 : ℝ)^extractionExponent a) ⊆ U := by
  intro x hx
  have hm := ((extractionCheck_success A.approx _).mp ha).2
  simp only [Nat.unpair_pair] at hm
  obtain ⟨p,hp,hpx⟩ := A.prefixMargins_ball_extends hq a.unpair.1 hm hx
  rw [← hpx]
  exact (he p).mp ⟨_,extractionCheck_runs ha hp⟩

omit [CompleteSpace X] in
/-- Every accepted strict name supplies a successful trial and a ball containing its point. -/
theorem extractedBall_complete {p : ℕ → ℕ} {x : X} {e m : ℕ}
    (hp : ∀ n, dist (q (p n)) x < (1/2 : ℝ)^(n+1))
    (hr : OracleRuns p (Term.closedProgram e) 0 m) :
    ∃ a, extractionCheck A.approx (Nat.pair e a) ≠ 0 ∧
      x ∈ Metric.ball (q (extractionCenter a)) ((1/2 : ℝ)^extractionExponent a) := by
  have hr' : Relation.ReflTransGen (OracleStep p)
      (AlphaTerm.mk (Term.oracleProgramInput e 0)) (AlphaTerm.mk (Term.churchNumeral m)) := by
    simpa [Term.oracleProgramInput,← app_mk,Term.mk_programSyntax,Term.mk_churchNumeral,var,OracleRuns] using hr
  obtain ⟨N,t,c,hc⟩ := prefixCertificateValue_complete hr'
  obtain ⟨i,l,hm,hx⟩ := A.exists_prefixMargins hq p x hp N
  let w := Nat.pair (NatListCode.encode (seqPrefix p N)) (Nat.pair i (Nat.pair l l))
  let a := Nat.pair w (Nat.pair t (Nat.pair c m))
  refine ⟨a,?_,?_⟩
  · apply (extractionCheck_success A.approx _).mpr
    constructor
    · simpa [extractionCertificateInput,a,w] using hc
    · simpa [a,w] using hm
  · simpa [extractionCenter,extractionExponent,a,w] using hx

/-- Exact coverage by the uniformly computable, possibly empty, enumeration stages. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Conversely, fix $x\in U$ and choose a name $p$ with $d(q_{p(n)},x)<2^{-(n+1)}$ at every coordinate, using density. The
    program $P_e$ returns some numeral on $p$. Finite-certificate completeness supplies an answer table $\theta$, a
    certificate
    $\gamma$ and a prefix $s$ of length $N$ containing every queried address. There are only finitely many positive gaps
    $2^{-(n+1)}-d(q_{p(n)},x)$ for $n<N$. Choose $\ell$ so large that
    $$d(q_{p(n)},x)+4\cdot2^{-\ell}<2^{-(n+1)}\qquad(n<N).$$
    For $N=0$ there are no constraints. Choose $i$ with $d(x,q_i)<2^{-\ell}$ and use precision $k=\ell$. The triangle
    inequality and the approximation error give
    $$A(s(n),i,\ell)+2\cdot2^{-\ell}
    \le d(q_{p(n)},q_i)+3\cdot2^{-\ell}
    <d(q_{p(n)},x)+4\cdot2^{-\ell}.$$
    Thus the corresponding tuple passes every test and emits a ball containing $x$. This proves that the emitted balls cover
    exactly $U$.
-/
theorem extractedBalls_cover {U : Set X} {e : ℕ}
    (he : ∀ p : cauchyNameDomain q,
      (∃ m, OracleRuns p.val (Term.closedProgram e) 0 m) ↔ cauchyRepresentation q p ∈ U) :
    U = {x | ∃ a, extractionCheck A.approx (Nat.pair e a) ≠ 0 ∧
      x ∈ Metric.ball (q (extractionCenter a)) ((1/2 : ℝ)^extractionExponent a)} := by
  ext x
  constructor
  · intro hx
    let p : cauchyNameDomain q := ⟨denseCauchyName q hq x,denseCauchyName_isCauchy q hq x⟩
    have hpx : cauchyRepresentation q p = x := cauchyRepresentation_denseCauchyName q hq x
    obtain ⟨m,hm⟩ := (he p).mpr (hpx.symm ▸ hx)
    apply A.extractedBall_complete hq (p := p.val) (m := m) _ hm
    intro n
    simpa [p,dist_comm] using denseCauchyName_approx q hq x n
  · rintro ⟨a,ha,hx⟩
    exact A.extractedBall_sound hq he ha hx

/-- Every semidecidable set has an index in this one fixed extraction program. -/
theorem semidecidable_extractedBalls {U : Set X}
    (hU : SemidecidableFromNames (cauchyRepresentationObject q hq) U) :
    ∃ e, U = {x | ∃ a, extractionCheck A.approx (Nat.pair e a) ≠ 0 ∧
      x ∈ Metric.ball (q (extractionCenter a)) ((1/2 : ℝ)^extractionExponent a)} := by
  obtain ⟨P,hP,hU⟩ := hU
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP
  refine ⟨e,A.extractedBalls_cover hq ?_⟩
  rw [he]
  exact hU

omit hq [CompleteSpace X] in
/-- The actual numerical outputs decode to precisely the certified balls. -/
theorem extractedBallNumber_decodes (e a : ℕ) :
    enumeratedRationalBall q (extractedBallNumber A.approx (Nat.pair e a)) =
      if extractionCheck A.approx (Nat.pair e a) ≠ 0 then
        Metric.ball (q (extractionCenter a)) ((1/2 : ℝ)^extractionExponent a) else ∅ := by
  rw [extractedBallNumber_eq]
  split_ifs <;> simp [enumeratedRationalBall]

/-- This is coverage by the outputs of the total closed lambda program itself. -/
theorem extractedBallNumber_cover {U : Set X} {e : ℕ}
    (he : ∀ p : cauchyNameDomain q,
      (∃ m, OracleRuns p.val (Term.closedProgram e) 0 m) ↔ cauchyRepresentation q p ∈ U) :
    U = ⋃ a, enumeratedRationalBall q (extractedBallNumber A.approx (Nat.pair e a)) := by
  rw [A.extractedBalls_cover hq he]
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_iUnion,A.extractedBallNumber_decodes]
  apply exists_congr
  intro a
  split_ifs <;> simp_all

include A in
/-- Forward effective-basis extraction, with the enumerating lambda term supplied. -/
theorem semidecidable_has_ball_enumeration {U : Set X}
    (hU : SemidecidableFromNames (cauchyRepresentationObject q hq) U) :
    ∃ E : AlphaTerm, ∃ f : ℕ → ℕ, NumericalComputes E f ∧
      U = ⋃ a, enumeratedRationalBall q (f a) := by
  obtain ⟨P,hP,hU⟩ := hU
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP
  have hs : ∀ p : cauchyNameDomain q,
      (∃ m, OracleRuns p.val (Term.closedProgram e) 0 m) ↔ cauchyRepresentation q p ∈ U := by
    rw [he]
    exact hU
  refine ⟨numericalCompose (extractedBallProgram A.program)
    (pairNumerical (numericalConstant e) numericalIdentity),
    (fun a => extractedBallNumber A.approx (Nat.pair e a)),?_,A.extractedBallNumber_cover hq hs⟩
  exact (extractedBallProgram_computes A.approx A.computes).comp
    ((numericalConstant_computes e).pair numericalIdentity_computes)

end LambdaMetricApproximation
end PolishSpaceBook
