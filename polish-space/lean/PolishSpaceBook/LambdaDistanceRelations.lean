module

public import PolishSpaceBook.LambdaMetricBalls
public import PolishSpaceBook.LambdaNumericalSearch
public import PolishSpaceBook.LambdaProgramCodes
public import PolishSpaceBook.RationalDistanceIntervals

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Effective distance data using only closed lambda programs

Forward search checks rational margins. Reverse search enumerates two rational
codes and a finite output-certificate candidate, returning the lower endpoint
of the first accepted narrow interval.
-/
namespace PolishSpaceBook
set_option maxHeartbeats 800000
open NamedLambda NamedLambda.AlphaTerm
namespace NamedLambda.AlphaTerm

def firstOutput (F : AlphaTerm) := numericalCompose (numericalProjectionTerm true) F
def secondOutput (F : AlphaTerm) := numericalCompose (numericalProjectionTerm false) F

theorem NumericalComputes.first {F : AlphaTerm} {f : ℕ → ℕ} (h : NumericalComputes F f) :
    NumericalComputes (firstOutput F) (fun n => (f n).unpair.1) := (projection_computes true).comp h

theorem NumericalComputes.second {F : AlphaTerm} {f : ℕ → ℕ} (h : NumericalComputes F f) :
    NumericalComputes (secondOutput F) (fun n => (f n).unpair.2) := (projection_computes false).comp h

/-- `pair (pair i j) (pair a b)` encodes an interval input. -/
def decodeDistanceInterval (z : ℕ) : DistanceIntervalInput :=
  (z.unpair.1.unpair,(RationalCode.ofNat z.unpair.2.unpair.1,RationalCode.ofNat z.unpair.2.unpair.2))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now let $\Sequence{q_i}{i\in\omega}$ be a sequence in a metric space and suppose a closed term $M$ computes rational
    codes $A(i,j,k)$ with
    distance error at most $2^{-k}$. Encode an interval input by $w=\NatPair{\NatPair{i}{j}}{\NatPair{a}{b}}$, where $a,b$
    now denote rational codes. On input $\NatPair{w}{k}$, numerical projections recover these components. Put
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,i\,(\LambdaNumericPair\,j\,k)),\\
    E&:=\LambdaDyadic\,k,\\
    L&:=\LambdaRationalAdd\,(\LambdaNumericPair\,a\,E),\\
    H&:=\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E).
    \end{aligned}$$
    Composition gives a closed stage term whose body reduces to
    $$\LambdaMul\,(\LambdaRationalLess\,(\LambdaNumericPair\,L\,V))\,
     (\LambdaRationalLess\,(\LambdaNumericPair\,H\,b)).$$
    It returns one exactly when both rational margin tests hold, and zero otherwise. The parameterized search just proved
    returns a numeral exactly when some precision succeeds. The error bound shows that success implies
    $\RationalValue{a}<d(q_i,q_j)<\RationalValue{b}$. Conversely, if these strict inequalities hold, choose $k$ so that
    $2\cdot2^{-k}$ is smaller than both endpoint gaps. Then both margin tests succeed. Thus this closed program semidecides
    the interval relation.
-/
def distanceIntervalStage (M : AlphaTerm) : AlphaTerm :=
  let W := numericalProjectionTerm true
  let K := numericalProjectionTerm false
  let D := numericalCompose M (pairNumerical (firstOutput (firstOutput W))
    (pairNumerical (secondOutput (firstOutput W)) K))
  let E := numericalCompose rationalDyadicTerm K
  let L := firstOutput (secondOutput W)
  let H := secondOutput (secondOutput W)
  mulNumerical
    (numericalCompose rationalLessTerm (pairNumerical
      (numericalCompose rationalAddTerm (pairNumerical L E)) D))
    (numericalCompose rationalLessTerm (pairNumerical
      (numericalCompose rationalAddTerm (pairNumerical D E)) H))

def distanceIntervalStageValue (approx : ℕ × (ℕ × ℕ) → RationalCode) (z : ℕ) : ℕ :=
  let w := decodeDistanceInterval z.unpair.1
  let a := (approx (w.1.1,(w.1.2,z.unpair.2))).value
  (if w.2.1.value + (1/2 : ℚ)^z.unpair.2 < a then 1 else 0) *
    (if a + (1/2 : ℚ)^z.unpair.2 < w.2.2.value then 1 else 0)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now let $\Sequence{q_i}{i\in\omega}$ be a sequence in a metric space and suppose a closed term $M$ computes rational
    codes $A(i,j,k)$ with
    distance error at most $2^{-k}$. Encode an interval input by $w=\NatPair{\NatPair{i}{j}}{\NatPair{a}{b}}$, where $a,b$
    now denote rational codes. On input $\NatPair{w}{k}$, numerical projections recover these components. Put
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,i\,(\LambdaNumericPair\,j\,k)),\\
    E&:=\LambdaDyadic\,k,\\
    L&:=\LambdaRationalAdd\,(\LambdaNumericPair\,a\,E),\\
    H&:=\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E).
    \end{aligned}$$
    Composition gives a closed stage term whose body reduces to
    $$\LambdaMul\,(\LambdaRationalLess\,(\LambdaNumericPair\,L\,V))\,
     (\LambdaRationalLess\,(\LambdaNumericPair\,H\,b)).$$
    It returns one exactly when both rational margin tests hold, and zero otherwise. The parameterized search just proved
    returns a numeral exactly when some precision succeeds. The error bound shows that success implies
    $\RationalValue{a}<d(q_i,q_j)<\RationalValue{b}$. Conversely, if these strict inequalities hold, choose $k$ so that
    $2\cdot2^{-k}$ is smaller than both endpoint gaps. Then both margin tests succeed. Thus this closed program semidecides
    the interval relation.
-/
theorem distanceIntervalStage_computes {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)) :
    NumericalComputes (distanceIntervalStage M) (distanceIntervalStageValue approx) := by
  have hw := projection_computes true
  have hk := projection_computes false
  have hd := hM.comp (hw.first.first.pair (hw.first.second.pair hk))
  have he := rationalDyadic_computes.comp hk
  have hl := hw.second.first
  have hh := hw.second.second
  have h₁ := rationalLess_computes.comp ((rationalAdd_computes.comp (hl.pair he)).pair hd)
  have h₂ := rationalLess_computes.comp ((rationalAdd_computes.comp (hd.pair he)).pair hh)
  unfold distanceIntervalStageValue
  simpa [distanceIntervalStage,decodeDistanceInterval,Nat.unpair_pair,
    RationalCode.ofNat_natCode,RationalCode.value_add,RationalCode.value_dyadic] using h₁.mul h₂

/-- Semidecision by ordinary beta reduction, with no oracle parameter. -/
def NumericallySemidecides (P : AlphaTerm) (U : Set ℕ) : Prop :=
  P.Closed ∧ ∀ n, (∃ m, Relation.ReflTransGen Beta (app P (numeral n)) (numeral m)) ↔ n ∈ U

def distanceIntervalSemidecider (M : AlphaTerm) := numericalSearch (distanceIntervalStage M)

/-- The finite candidate includes both a proposed output and its certificate bound. -/
def numericalCandidate (e : ℕ) := uncurryNumerical (app outputCandidateTerm (numeral e))

theorem numericalCandidate_computes (e : ℕ) : NumericalComputes (numericalCandidate e)
    (fun z => if Term.outputCandidate e z.unpair.1 z.unpair.2 then 1 else 0) :=
  uncurryNumerical_computes (closed_app outputCandidateTerm_closed (numeral_closed e))
    (fun n k => if Term.outputCandidate e n k then 1 else 0) (outputCandidateTerm_apply e)

/-- Input `pair (pair i (pair j k)) (pair a (pair b t))`. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the reverse construction, fix a closed term $P_e$ whose numeral-output domain is exactly that interval relation. Let
    $z=\NatPair{i}{\NatPair{j}{k}}$ be the approximation input and let $u=\NatPair{a}{\NatPair{b}{t}}$ enumerate two
    rational codes and an output-certificate candidate. Numerical projections recover every component. Put
    $$\begin{aligned}
    W&:=\LambdaNumericPair\,(\LambdaNumericPair\,i\,j)\,
     (\LambdaNumericPair\,a\,b),\\
    E&:=\LambdaDyadic\,k,\\
    H&:=\LambdaRationalAdd\,(\LambdaNumericPair\,a\,E),\\
    B&:=\LambdaRationalLess\,(\LambdaNumericPair\,b\,H),\\
    C&:=\LambdaOutputCandidate\,\ChurchNumeral{e}\,W\,t.
    \end{aligned}$$
    The closed stage term $T_e$ on input $\NatPair{z}{u}$ is assembled from these procedures and reduces to
    $\LambdaMul\,B\,C$. Define
    $$D_e:=\lambdaab{z}{\LambdaNumericProjection{1}(S_{T_e}z)}.$$
    Both stage tests are total: $B$ checks the interval width, and $C$ checks a bounded set of finite beta-reduction
    certificates. A failed candidate does not assert that $P_e$ diverges.
-/
def narrowIntervalStage (e : ℕ) : AlphaTerm :=
  let Z := numericalProjectionTerm true
  let T := numericalProjectionTerm false
  let A := firstOutput T
  let B := firstOutput (secondOutput T)
  let C := secondOutput (secondOutput T)
  let W := pairNumerical (pairNumerical (firstOutput Z) (firstOutput (secondOutput Z)))
    (pairNumerical A B)
  let E := numericalCompose rationalDyadicTerm (secondOutput (secondOutput Z))
  mulNumerical (numericalCompose rationalLessTerm
    (pairNumerical B (numericalCompose rationalAddTerm (pairNumerical A E))))
    (numericalCompose (numericalCandidate e) (pairNumerical W C))

def narrowIntervalInput (z t : ℕ) : ℕ :=
  Nat.pair (Nat.pair z.unpair.1 z.unpair.2.unpair.1)
    (Nat.pair t.unpair.1 t.unpair.2.unpair.1)

def narrowIntervalStageValue (e zt : ℕ) : ℕ :=
  let z := zt.unpair.1
  let t := zt.unpair.2
  (if (RationalCode.ofNat t.unpair.2.unpair.1).value <
      (RationalCode.ofNat t.unpair.1).value + (1/2 : ℚ)^z.unpair.2.unpair.2 then 1 else 0) *
    (if Term.outputCandidate e (narrowIntervalInput z t) t.unpair.2.unpair.2 then 1 else 0)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the reverse construction, fix a closed term $P_e$ whose numeral-output domain is exactly that interval relation. Let
    $z=\NatPair{i}{\NatPair{j}{k}}$ be the approximation input and let $u=\NatPair{a}{\NatPair{b}{t}}$ enumerate two
    rational codes and an output-certificate candidate. Numerical projections recover every component. Put
    $$\begin{aligned}
    W&:=\LambdaNumericPair\,(\LambdaNumericPair\,i\,j)\,
     (\LambdaNumericPair\,a\,b),\\
    E&:=\LambdaDyadic\,k,\\
    H&:=\LambdaRationalAdd\,(\LambdaNumericPair\,a\,E),\\
    B&:=\LambdaRationalLess\,(\LambdaNumericPair\,b\,H),\\
    C&:=\LambdaOutputCandidate\,\ChurchNumeral{e}\,W\,t.
    \end{aligned}$$
    The closed stage term $T_e$ on input $\NatPair{z}{u}$ is assembled from these procedures and reduces to
    $\LambdaMul\,B\,C$. Define
    $$D_e:=\lambdaab{z}{\LambdaNumericProjection{1}(S_{T_e}z)}.$$
    Both stage tests are total: $B$ checks the interval width, and $C$ checks a bounded set of finite beta-reduction
    certificates. A failed candidate does not assert that $P_e$ diverges.
-/
theorem narrowIntervalStage_computes (e : ℕ) :
    NumericalComputes (narrowIntervalStage e) (narrowIntervalStageValue e) := by
  have hz := projection_computes true
  have ht := projection_computes false
  have ha := ht.first
  have hb := ht.second.first
  have hc := ht.second.second
  have hw := (hz.first.pair hz.second.first).pair (ha.pair hb)
  have he := rationalDyadic_computes.comp hz.second.second
  have hwidth := rationalLess_computes.comp (hb.pair (rationalAdd_computes.comp (ha.pair he)))
  have htest := (numericalCandidate_computes e).comp (hw.pair hc)
  unfold narrowIntervalStageValue
  simpa [narrowIntervalStage,narrowIntervalInput,Nat.unpair_pair,
    RationalCode.ofNat_natCode,RationalCode.value_add,RationalCode.value_dyadic] using hwidth.mul htest

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the reverse construction, fix a closed term $P_e$ whose numeral-output domain is exactly that interval relation. Let
    $z=\NatPair{i}{\NatPair{j}{k}}$ be the approximation input and let $u=\NatPair{a}{\NatPair{b}{t}}$ enumerate two
    rational codes and an output-certificate candidate. Numerical projections recover every component. Put
    $$\begin{aligned}
    W&:=\LambdaNumericPair\,(\LambdaNumericPair\,i\,j)\,
     (\LambdaNumericPair\,a\,b),\\
    E&:=\LambdaDyadic\,k,\\
    H&:=\LambdaRationalAdd\,(\LambdaNumericPair\,a\,E),\\
    B&:=\LambdaRationalLess\,(\LambdaNumericPair\,b\,H),\\
    C&:=\LambdaOutputCandidate\,\ChurchNumeral{e}\,W\,t.
    \end{aligned}$$
    The closed stage term $T_e$ on input $\NatPair{z}{u}$ is assembled from these procedures and reduces to
    $\LambdaMul\,B\,C$. Define
    $$D_e:=\lambdaab{z}{\LambdaNumericProjection{1}(S_{T_e}z)}.$$
    Both stage tests are total: $B$ checks the interval width, and $C$ checks a bounded set of finite beta-reduction
    certificates. A failed candidate does not assert that $P_e$ diverges.
-/
def distanceApproximationProgram (e : ℕ) := firstOutput (numericalSearch (narrowIntervalStage e))

end NamedLambda.AlphaTerm

namespace LambdaMetricApproximation
universe u
variable {X : Type u} [MetricSpace X] {q : ℕ → X} (A : LambdaMetricApproximation q)

theorem distanceIntervalStage_success (z k : ℕ) :
    distanceIntervalStageValue A.approx (Nat.pair z k) ≠ 0 ↔
      A.toRationalMetricApproximation.intervalTest (decodeDistanceInterval z) k = true := by
  simp [distanceIntervalStageValue,RationalMetricApproximation.intervalTest,
    RationalCode.lt_iff,Nat.unpair_pair,and_comm]

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    First suppose that $A$ is given. On input $(i,j,a,b)$, put $\varepsilon_k=2^{-k}$ and test, for $k=0,1,\ldots$,
    $$a+\varepsilon_k<A(i,j,k)\quad\text{and}\quad A(i,j,k)+\varepsilon_k<b.$$
    These rational tests terminate. A successful test implies $a<d(q_i,q_j)<b$ by the error bound. Conversely, if the distance lies strictly between $a$ and $b$, choose $k$ so that $2\varepsilon_k$ is smaller than both gaps to the endpoints. Since $A(i,j,k)$ differs from the distance by at most $\varepsilon_k$, both inequalities then hold. Search through these total tests therefore semidecides the joint relation. Concretely, encode the input by $\NatPair{\NatPair{i}{j}}{\NatPair{c_a}{c_b}}$, where $c_a,c_b$ code the endpoints. Numerical projections, the approximation program, rational arithmetic and multiplication of zero-or-one answers give a total closed stage term. Result search returns the least successful precision and has no numeral output if every stage fails.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Now let $\Sequence{q_i}{i\in\omega}$ be a sequence in a metric space and suppose a closed term $M$ computes rational
    codes $A(i,j,k)$ with
    distance error at most $2^{-k}$. Encode an interval input by $w=\NatPair{\NatPair{i}{j}}{\NatPair{a}{b}}$, where $a,b$
    now denote rational codes. On input $\NatPair{w}{k}$, numerical projections recover these components. Put
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,i\,(\LambdaNumericPair\,j\,k)),\\
    E&:=\LambdaDyadic\,k,\\
    L&:=\LambdaRationalAdd\,(\LambdaNumericPair\,a\,E),\\
    H&:=\LambdaRationalAdd\,(\LambdaNumericPair\,V\,E).
    \end{aligned}$$
    Composition gives a closed stage term whose body reduces to
    $$\LambdaMul\,(\LambdaRationalLess\,(\LambdaNumericPair\,L\,V))\,
     (\LambdaRationalLess\,(\LambdaNumericPair\,H\,b)).$$
    It returns one exactly when both rational margin tests hold, and zero otherwise. The parameterized search just proved
    returns a numeral exactly when some precision succeeds. The error bound shows that success implies
    $\RationalValue{a}<d(q_i,q_j)<\RationalValue{b}$. Conversely, if these strict inequalities hold, choose $k$ so that
    $2\cdot2^{-k}$ is smaller than both endpoint gaps. Then both margin tests succeed. Thus this closed program semidecides
    the interval relation.
-/
theorem semidecides_distanceIntervals : NumericallySemidecides (distanceIntervalSemidecider A.program)
    {z | DistanceInterval q (decodeDistanceInterval z)} := by
  refine ⟨numericalSearch_closed (distanceIntervalStage_computes A.approx A.computes).1,fun z => ?_⟩
  rw [distanceIntervalSemidecider,numericalSearch_domain (distanceIntervalStage_computes A.approx A.computes)]
  simp only [A.distanceIntervalStage_success]
  exact A.toRationalMetricApproximation.exists_intervalTest_iff (decodeDistanceInterval z)

end LambdaMetricApproximation
namespace LambdaDistanceSearch
universe u
variable {X : Type u} [MetricSpace X] {q : ℕ → X}

theorem stage_success (e z t : ℕ) :
    narrowIntervalStageValue e (Nat.pair z t) ≠ 0 ↔
      (RationalCode.ofNat t.unpair.2.unpair.1).value <
        (RationalCode.ofNat t.unpair.1).value + (1/2 : ℚ)^z.unpair.2.unpair.2 ∧
      Term.outputCandidate e (narrowIntervalInput z t) t.unpair.2.unpair.2 = true := by
  simp [narrowIntervalStageValue,Nat.unpair_pair,and_comm]

theorem stage_error (e : ℕ)
    (hc : NumericallySemidecides (Term.closedProgram e) {z | DistanceInterval q (decodeDistanceInterval z)})
    (z t : ℕ) (ht : narrowIntervalStageValue e (Nat.pair z t) ≠ 0) :
    |((RationalCode.ofNat t.unpair.1).value : ℝ) - dist (q z.unpair.1) (q z.unpair.2.unpair.1)| ≤
      (1/2 : ℝ)^z.unpair.2.unpair.2 := by
  obtain ⟨hw,ht⟩ := (stage_success e z t).mp ht
  have hh := (outputTest_exists_iff e (narrowIntervalInput z t) t.unpair.2.unpair.2.unpair.1).mp
    ⟨t.unpair.2.unpair.2.unpair.2,ht⟩
  have hd := (hc.2 (narrowIntervalInput z t)).mp ⟨_,hh⟩
  have hw := (Rat.cast_lt (K := ℝ)).mpr hw
  push_cast at hw
  simp only [Set.mem_ofPred_eq,DistanceInterval,decodeDistanceInterval,narrowIntervalInput,Nat.unpair_pair] at hd
  rw [abs_le]
  constructor <;> linarith [pow_pos (by norm_num : (0 : ℝ) < 1/2) z.unpair.2.unpair.2]

theorem exists_stage (e : ℕ)
    (hc : NumericallySemidecides (Term.closedProgram e) {z | DistanceInterval q (decodeDistanceInterval z)})
    (z : ℕ) : ∃ t, narrowIntervalStageValue e (Nat.pair z t) ≠ 0 := by
  let d := dist (q z.unpair.1) (q z.unpair.2.unpair.1)
  let ε := (1/2 : ℝ)^z.unpair.2.unpair.2
  have he : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨a,ha,had⟩ := exists_rat_btwn (show d - ε < d by linarith)
  obtain ⟨b,hdb,hb⟩ := exists_rat_btwn (show d < (a : ℝ) + ε by linarith)
  obtain ⟨ac,hac⟩ := RationalCode.value_surjective a
  obtain ⟨bc,hbc⟩ := RationalCode.value_surjective b
  let w := Nat.pair (Nat.pair z.unpair.1 z.unpair.2.unpair.1) (Nat.pair ac.natCode bc.natCode)
  have hd : DistanceInterval q (decodeDistanceInterval w) := by
    simpa [DistanceInterval,decodeDistanceInterval,w,hac,hbc,d] using And.intro had hdb
  obtain ⟨m,hm⟩ := (hc.2 w).mpr hd
  obtain ⟨s,hs⟩ := (outputTest_exists_iff e w m).mpr hm
  let t := Nat.pair ac.natCode (Nat.pair bc.natCode (Nat.pair m s))
  refine ⟨t,(stage_success e z t).mpr ⟨?_,?_⟩⟩
  · simp only [t,Nat.unpair_pair,RationalCode.ofNat_natCode,hac,hbc]
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact hb
  · simpa only [t,narrowIntervalInput,Nat.unpair_pair,Term.outputCandidate,w] using hs

/-- Search all intervals and finite certificates, returning the first lower endpoint. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Distance approximation from interval semidecision
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Write $d=d(q_i,q_j)$ and $\varepsilon=2^{-k}>0$. Choose rational endpoints with
    $d-\varepsilon<\RationalValue{a}<d<\RationalValue{b}<\RationalValue{a}+\varepsilon$. Such endpoints exist by density of
    the rationals. The program $P_e$ returns a numeral on their encoded interval. Completeness of the finite candidate
    tester supplies a candidate $t$ which it accepts, so the triple $u=\NatPair{a}{\NatPair{b}{t}}$ passes both tests. Every
    stage terminates; hence parameterized search reaches the least successful stage. Soundness of its accepted candidate
    gives the interval inequalities, and the width test gives $\RationalValue{b}<\RationalValue{a}+\varepsilon$. Therefore
    $|\RationalValue{a}-d|<\varepsilon$. Finally, the first numerical projection extracts exactly the lower-endpoint code
    from the successful triple. This proves termination and the stated error bound. Different codes for the same rational
    cause no difficulty, since the tests and estimate use their values.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Conversely, fix one closed semideciding term $P_e$ for the joint relation. On input $(i,j,k)$, enumerate all triples
    $(c_a,c_b,t)$ of natural numbers, where $c_a,c_b$ are rational codes and $t=\NatPair{m}{s}$ is a proposed numeral output
    together with a finite certificate-search bound. Check $b<a+2^{-k}$ and apply the total numerical-output candidate
    tester to $e$, the encoded interval input, and $t$. If both tests succeed, output $c_a$. Each trial is finite.
    Enumerating certificate bounds together with the intervals ensures that a computation without an output cannot block the
    search.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    To prove termination, put $\delta=d(q_i,q_j)$ and $\varepsilon=2^{-k}$. By density of the rationals choose
    $$\delta-\varepsilon<a<\delta<b<a+\varepsilon.$$
    The semidecider returns a numeral on this interval. Its finite beta reduction has a certificate, so some pair
    $t=\NatPair{m}{s}$ is accepted by the candidate tester. The corresponding triple occurs in the enumeration. Every
    accepted interval satisfies $a<\delta<b<a+\varepsilon$, hence $\Abs{a-\delta}<\varepsilon$.
    Thus the search defines the required total computable approximation, uniformly in $i,j,k$.
    Numerical projections, the rational width test, the candidate tester and
    result search construct its closed lambda term. §{sec:lambda-rational-ball-programs} gives both programs and their
    reduction proofs.
-/
theorem approximation_of_semidecider (P : AlphaTerm)
    (hP : NumericallySemidecides P {z | DistanceInterval q (decodeDistanceInterval z)}) :
    Nonempty (LambdaMetricApproximation q) := by
  classical
  obtain ⟨e,he⟩ := Term.closedProgram_surjective P hP.1
  have hc : NumericallySemidecides (Term.closedProgram e)
      {z | DistanceInterval q (decodeDistanceInterval z)} := by simpa [he] using hP
  have hh := exists_stage e hc
  let f := firstNumericalHit (narrowIntervalStageValue e) hh
  have hf : NumericalComputes (distanceApproximationProgram e) (fun z => (f z).unpair.1) :=
    (numericalSearch_computes (narrowIntervalStage_computes e) hh).first
  let approx : ℕ × (ℕ × ℕ) → RationalCode := fun z =>
    RationalCode.ofNat (f (Nat.pair z.1 (Nat.pair z.2.1 z.2.2))).unpair.1
  refine ⟨{ approx := approx, program := distanceApproximationProgram e, computes := ?_, error := ?_ }⟩
  · intro i j k
    have ht : narrowIntervalStageValue e (Nat.pair (Nat.pair i (Nat.pair j k)) (f (Nat.pair i (Nat.pair j k)))) ≠ 0 :=
      Nat.find_spec (hh _)
    simpa only [approx,Nat.unpair_pair] using stage_error e hc (Nat.pair i (Nat.pair j k)) _ ht
  · simpa only [approx,RationalCode.natCode_ofNat,Nat.pair_unpair] using hf

end LambdaDistanceSearch

/-- Both sides use the same ordinary closed-lambda execution semantics. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Effective distance data equivalence
-/
theorem lambda_distance_data_equivalence {X : Type*} [MetricSpace X] (q : ℕ → X) :
    (∃ P, NumericallySemidecides P {z | DistanceInterval q (decodeDistanceInterval z)}) ↔
      Nonempty (LambdaMetricApproximation q) := by
  constructor
  · rintro ⟨P,hP⟩
    exact LambdaDistanceSearch.approximation_of_semidecider P hP
  · rintro ⟨A⟩
    exact ⟨distanceIntervalSemidecider A.program,A.semidecides_distanceIntervals⟩

end PolishSpaceBook
