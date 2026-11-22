module

public import PolishSpaceBook.LambdaMetricPreimages

@[expose] public section

/-! # Constructing a Cauchy-name realizer from ball preimage enumerations -/
namespace PolishSpaceBook
open Set Filter Topology NamedLambda NamedLambda.AlphaTerm
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace NamedLambda.AlphaTerm

/-- Input `pair n (pair j (pair k l))` prepares target ball and enumeration stage. -/
def preimageEnumerationArgument (z : ℕ) :=
  Nat.pair (Nat.pair z.unpair.2.unpair.1 (RationalCode.dyadic (z.unpair.1+2)).natCode)
    z.unpair.2.unpair.2.unpair.1

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the reverse construction, suppose a closed numerical term $\LambdaTermName{enumeration}$ computes a total
    enumeration function $\eta$.
    Fix a closed term $M$ computing the source-space distance approximations and let $R_M$ be its rational-ball stage
    term. At coordinate $n$, write $\rho(n,j)$ for the code of the target ball of center $q_j$ and radius $2^{-(n+2)}$.
    Its radius code is computed by $\LambdaDyadic\,\ChurchNumeral{n+2}$. Decode the joint input as
    $$z=\NatPair{n}{\NatPair{j}{\NatPair{k}{\ell}}},\qquad u=\eta(\NatPair{\rho(n,j)}{k}).$$
-/
def preimageEnumerationArgumentProgram :=
  pairNumerical
    (pairNumerical (firstOutput (numericalProjectionTerm false))
      (numericalCompose rationalDyadicTerm
        (addNumerical (numericalProjectionTerm true) (numericalConstant 2))))
    (firstOutput (secondOutput (numericalProjectionTerm false)))

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the reverse construction, suppose a closed numerical term $\LambdaTermName{enumeration}$ computes a total
    enumeration function $\eta$.
    Fix a closed term $M$ computing the source-space distance approximations and let $R_M$ be its rational-ball stage
    term. At coordinate $n$, write $\rho(n,j)$ for the code of the target ball of center $q_j$ and radius $2^{-(n+2)}$.
    Its radius code is computed by $\LambdaDyadic\,\ChurchNumeral{n+2}$. Decode the joint input as
    $$z=\NatPair{n}{\NatPair{j}{\NatPair{k}{\ell}}},\qquad u=\eta(\NatPair{\rho(n,j)}{k}).$$
-/
theorem preimageEnumerationArgument_computes :
    NumericalComputes preimageEnumerationArgumentProgram preimageEnumerationArgument :=
  ((projection_computes false).first.pair
    (rationalDyadic_computes.comp ((projection_computes true).add (numericalConstant_computes 2)))).pair
    (projection_computes false).second.first

def preimageTrialMetricInput (e : ℕ → ℕ) (z : ℕ) :=
  Nat.pair (e (preimageEnumerationArgument z)-1) z.unpair.2.unpair.2.unpair.2

def preimageTrialMetricInputProgram (E : AlphaTerm) :=
  pairNumerical (numericalCompose predecessorTerm (numericalCompose E preimageEnumerationArgumentProgram))
    (secondOutput (secondOutput (numericalProjectionTerm false)))

theorem preimageTrialMetricInput_computes {E : AlphaTerm} {e : ℕ → ℕ} (hE : NumericalComputes E e) :
    NumericalComputes (preimageTrialMetricInputProgram E) (preimageTrialMetricInput e) :=
  (predecessor_computes.comp (hE.comp preimageEnumerationArgument_computes)).pair
    (projection_computes false).second.second

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define $\LambdaPreimageTrial{M}{ \LambdaTermName{enumeration}}$ using projections, addition, the dyadic-code
    term, $\LambdaTermName{enumeration}$, and the rational-ball
    stage test. For $u=b+1$, let $\beta$ be the zero-or-one answer of the ball test for $b$ at precision $\ell$.
    The trial returns
    $$\begin{cases}
    0,&u=0,\\
    u,&u=b+1,\ \beta=1,\\
    0,&u=b+1,\ \beta=0.
    \end{cases}$$
    These are disjoint cases. For a positive output the predecessor term recovers $b$; an empty stage never succeeds.
-/
def preimageTrialProgram (M E : AlphaTerm) := combineOutputProgram multiplicationTerm
  (liftNumericalProgram (numericalCompose E preimageEnumerationArgumentProgram))
  (reindexProgram (metricStageProgram M) (preimageTrialMetricInputProgram E))

def preimageTrialValue (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (e : ℕ → ℕ) (p : ℕ → ℕ) (z : ℕ) :=
  e (preimageEnumerationArgument z) *
    if metricStageTest approx p (e (preimageEnumerationArgument z)-1) z.unpair.2.unpair.2.unpair.2
      then 1 else 0

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Total preimage trial
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Numerical projections recover the four inputs. Addition and the dyadic-code term compute the target-ball code, and
    $\LambdaTermName{enumeration}$ computes $u$. If $u=b+1$, predecessor recovers $b$ and the source-space stage
    test returns zero or one.
    Multiply this answer by $u$. If $u=0$, the result is zero regardless of the auxiliary test, which still terminates.
    All operations are total lambda computations; their composition gives the asserted closed term and answer.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define $\LambdaPreimageTrial{M}{ \LambdaTermName{enumeration}}$ using projections, addition, the dyadic-code
    term, $\LambdaTermName{enumeration}$, and the rational-ball
    stage test. For $u=b+1$, let $\beta$ be the zero-or-one answer of the ball test for $b$ at precision $\ell$.
    The trial returns
    $$\begin{cases}
    0,&u=0,\\
    u,&u=b+1,\ \beta=1,\\
    0,&u=b+1,\ \beta=0.
    \end{cases}$$
    These are disjoint cases. For a positive output the predecessor term recovers $b$; an empty stage never succeeds.
-/
theorem preimageTrialProgram_computes {M E : AlphaTerm}
    (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode))
    {e : ℕ → ℕ} (hE : NumericalComputes E e) :
    UniformNumericalComputes (preimageTrialProgram M E) (preimageTrialValue approx e) := by
  have he := (hE.comp preimageEnumerationArgument_computes).uniform
  have hm := (metricStageProgram_computes approx hM).reindex (preimageTrialMetricInput_computes hE)
  unfold preimageTrialValue
  simpa [preimageTrialProgram,preimageTrialMetricInput,metricStageTest] using
    he.combine hm multiplicationTerm_closed (fun a b => a*b) multiplicationTerm_apply

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Conversely, let $E$ be such a uniform enumeration and let $p$ name $x$. To compute output coordinate $n$, enumerate
    triples $(j,k,\ell)$ using codes $t=\NatPair{j}{\NatPair{k}{\ell}}$. Let $b$ code the target ball
    $$\Ball{q_j}{2^{-(n+2)}}.$$
    Compute $E(b,k)$. If its output is zero, this trial fails. If it is $c+1$, apply the input-space rational-ball test
    at precision $\ell$ to the ball coded by $c$ and the name $p$. On success, output $j$. Each trial terminates. The search
    tests all centers, enumeration stages and precisions, so failure to certify one candidate cannot obstruct another.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Define $\LambdaPreimageTrial{M}{ \LambdaTermName{enumeration}}$ using projections, addition, the dyadic-code
    term, $\LambdaTermName{enumeration}$, and the rational-ball
    stage test. For $u=b+1$, let $\beta$ be the zero-or-one answer of the ball test for $b$ at precision $\ell$.
    The trial returns
    $$\begin{cases}
    0,&u=0,\\
    u,&u=b+1,\ \beta=1,\\
    0,&u=b+1,\ \beta=0.
    \end{cases}$$
    These are disjoint cases. For a positive output the predecessor term recovers $b$; an empty stage never succeeds.
-/
theorem preimageTrialValue_success (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (e p : ℕ → ℕ) (z : ℕ) :
    preimageTrialValue approx e p z ≠ 0 ↔
      e (preimageEnumerationArgument z) ≠ 0 ∧
      metricStageTest approx p (e (preimageEnumerationArgument z)-1) z.unpair.2.unpair.2.unpair.2 := by
  simp [preimageTrialValue,and_comm]

/-- Curry the numerical pair while preserving the free input-name parameter. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Reverse the answers and curry the numerical input:
    $$\begin{aligned}
    \LambdaTermName{preimageSearchTest}&:=\lambdaab{o}{\lambdaab{n}{\lambdaab{y}{
     \LambdaZeroTest\,(\LambdaPreimageTrial{M}{\LambdaTermName{enumeration}}\,o\,(\LambdaNumericPair\,n\,y))
     \,\ChurchNumeral{1}\,\ChurchNumeral{0}}}},\\
    \LambdaPreimageRealizer{M}{\LambdaTermName{enumeration}}&:=\lambdaab{o}{\lambdaab{n}{
     \LambdaNumericProjection{1}(\LambdaSearchProgram{\LambdaTermName{preimageSearchTest}}\,o\,n)}}.
    \end{aligned}$$
-/
def curryInputProgram (P : AlphaTerm) := lam 40 (lam 41 (lam 42
  (app (app P (var 40)) (app (app numericalPairTerm (var 41)) (var 42)))))

theorem curryInputProgram_closed {P : AlphaTerm} (hP : P.Closed) : (curryInputProgram P).Closed := by
  unfold curryInputProgram Closed
  simp only [fv_lam,fv_app,fv_var]; rw [hP,numericalPairTerm_closed]; decide

theorem curryInputProgram_apply {P : AlphaTerm} (hP : P.Closed) (p : ℕ → ℕ) (n k : ℕ) :
    Relation.ReflTransGen (OracleStep p)
      (app (app (app (curryInputProgram P) (var 0)) (numeral n)) (numeral k))
      (app (app P (var 0)) (numeral (Nat.pair n k))) := by
  have h₁ : Beta (app (curryInputProgram P) (var 0))
      (lam 41 (lam 42 (app (app P (var 0)) (app (app numericalPairTerm (var 41)) (var 42))))) := by
    convert Beta.contract 40 _ (var 0) using 1 <;> try rfl
    simp [subst_lam_fresh,subst_app,subst_var,fv_var,subst_closed _ _ _ hP,
      subst_closed _ _ _ numericalPairTerm_closed]
  have h₂ : Beta (app (lam 41 (lam 42
      (app (app P (var 0)) (app (app numericalPairTerm (var 41)) (var 42))))) (numeral n))
      (lam 42 (app (app P (var 0)) (app (app numericalPairTerm (numeral n)) (var 42)))) := by
    convert Beta.contract 41 _ (numeral n) using 1
    rw [subst_lam_fresh _ _ 42 41 (by decide) (by rw [numeral_closed]; simp)]
    simp [subst_app,subst_var,subst_closed _ _ _ hP,
      subst_closed _ _ _ numericalPairTerm_closed]
  have h₃ : Beta (app (lam 42
      (app (app P (var 0)) (app (app numericalPairTerm (numeral n)) (var 42)))) (numeral k))
      (app (app P (var 0)) (app (app numericalPairTerm (numeral n)) (numeral k))) := by
    convert Beta.contract 42 _ (numeral k) using 1
    simp [subst_app,subst_var,subst_closed _ _ _ hP,
      subst_closed _ _ _ numericalPairTerm_closed,subst_closed _ _ _ (numeral_closed n)]
  apply (Relation.ReflTransGen.tail (.tail (.single (OracleStep.beta (.app_left _ (.app_left _ h₁))))
    (OracleStep.beta (.app_left _ h₂))) (OracleStep.beta h₃)).trans
  exact oracle_steps_app_right _ (beta_steps_oracle (numericalPairTerm_apply n k))

/-- Search all candidates for each numerical coordinate, then return its first component. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Reverse the answers and curry the numerical input:
    $$\begin{aligned}
    \LambdaTermName{preimageSearchTest}&:=\lambdaab{o}{\lambdaab{n}{\lambdaab{y}{
     \LambdaZeroTest\,(\LambdaPreimageTrial{M}{\LambdaTermName{enumeration}}\,o\,(\LambdaNumericPair\,n\,y))
     \,\ChurchNumeral{1}\,\ChurchNumeral{0}}}},\\
    \LambdaPreimageRealizer{M}{\LambdaTermName{enumeration}}&:=\lambdaab{o}{\lambdaab{n}{
     \LambdaNumericProjection{1}(\LambdaSearchProgram{\LambdaTermName{preimageSearchTest}}\,o\,n)}}.
    \end{aligned}$$
-/
def preimageRealizerProgram (M E : AlphaTerm) := mapOutputProgram (numericalProjectionTerm true)
  (searchProgram (curryInputProgram (mapOutputProgram reverseZeroTerm (preimageTrialProgram M E))))

end NamedLambda.AlphaTerm

namespace LambdaMetricApproximation
universe u v
variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
variable {qX : ℕ → X} {qY : ℕ → Y} (A : LambdaMetricApproximation qX)
variable [CompleteSpace X]

/-- A nonempty emitted ball and a successful metric stage give the strict output error. -/
theorem preimageTrial_sound (e : ℕ → ℕ) (f : X → Y)
    (he : ∀ b, (⋃ k, enumeratedRationalBall qX (e (Nat.pair b k))) =
      f ⁻¹' Metric.ball (qY b.unpair.1) ((RationalCode.ofNat b.unpair.2).value : ℝ))
    (p : cauchyNameDomain qX) (n t : ℕ)
    (h : preimageTrialValue A.approx e p.val (Nat.pair n t) ≠ 0) :
    dist (qY t.unpair.1) (f (cauchyRepresentation qX p)) < (1/2 : ℝ)^(n+2) := by
  obtain ⟨hne,ht⟩ := (preimageTrialValue_success A.approx e p.val _).mp h
  let b := Nat.pair t.unpair.1 (RationalCode.dyadic (n+2)).natCode
  have hx : cauchyRepresentation qX p ∈ ⋃ k, enumeratedRationalBall qX (e (Nat.pair b k)) := by
    refine Set.mem_iUnion.mpr ⟨t.unpair.2.unpair.1,?_⟩
    have hz : preimageEnumerationArgument (Nat.pair n t) = Nat.pair b t.unpair.2.unpair.1 := by
      simp [preimageEnumerationArgument,b]
    rw [hz] at hne ht
    cases heq : e (Nat.pair b t.unpair.2.unpair.1) with
    | zero => exact False.elim (hne heq)
    | succ a =>
      rw [heq] at ht
      apply A.toRationalMetricApproximation.mem_ball_of_test p a.unpair.1
        (RationalCode.ofNat a.unpair.2) t.unpair.2.unpair.2
      simpa [metricStageTest,RationalMetricApproximation.ballTest,RationalMetricApproximation.ballUpper,
        RationalCode.lt_iff] using ht
  rw [he b] at hx
  simpa [b,Set.mem_preimage,Metric.mem_ball,dist_comm] using hx

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    This search terminates for every valid input name and every $n$. Density supplies a target center whose ball contains
    $f(x)$. Exactness of its preimage enumeration supplies an emitted input ball containing $x$, and the rational-ball
    test succeeds at some precision. Conversely, every successful trial places $x$ in that preimage and hence $f(x)$ in
    the target ball. The closed trial term in §{sec:lambda-metric-realizer-programs} takes $\NatPair{n}{t}$ as its numerical
    input. Reverse its zero/nonzero answers and use the sequential-search term to find the first successful triple.
    Numerical projection returns its center index. Thus one closed term computes every output coordinate on every valid
    input name; no decision procedure for validity of names is used.
-/
theorem exists_preimageTrial (hqY : DenseRange qY) (e : ℕ → ℕ) (f : X → Y)
    (he : ∀ b, (⋃ k, enumeratedRationalBall qX (e (Nat.pair b k))) =
      f ⁻¹' Metric.ball (qY b.unpair.1) ((RationalCode.ofNat b.unpair.2).value : ℝ))
    (p : cauchyNameDomain qX) (n : ℕ) :
    ∃ t, preimageTrialValue A.approx e p.val (Nat.pair n t) ≠ 0 := by
  obtain ⟨j,hj⟩ := hqY.exists_dist_lt (f (cauchyRepresentation qX p))
    (by positivity : 0 < (1/2 : ℝ)^(n+2))
  let b := Nat.pair j (RationalCode.dyadic (n+2)).natCode
  have hx : cauchyRepresentation qX p ∈ ⋃ k, enumeratedRationalBall qX (e (Nat.pair b k)) := by
    rw [he b]
    simpa [b,Metric.mem_ball] using hj
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
  cases heq : e (Nat.pair b k) with
  | zero => simp [heq,enumeratedRationalBall] at hk
  | succ a =>
    have hm : cauchyRepresentation qX p ∈ Metric.ball (qX a.unpair.1)
        ((RationalCode.ofNat a.unpair.2).value : ℝ) := by simpa [heq,enumeratedRationalBall] using hk
    obtain ⟨l,hl⟩ := A.toRationalMetricApproximation.exists_ballTest_of_mem p _ _ hm
    refine ⟨Nat.pair j (Nat.pair k l),?_⟩
    rw [preimageTrialValue_success]
    have hz : preimageEnumerationArgument (Nat.pair n (Nat.pair j (Nat.pair k l))) = Nat.pair b k := by
      simp [preimageEnumerationArgument,b]
    rw [hz,heq]
    refine ⟨by omega,?_⟩
    simpa [metricStageTest,RationalMetricApproximation.ballTest,RationalMetricApproximation.ballUpper,
      RationalCode.lt_iff] using hl

variable [CompleteSpace Y]
include A in

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Realizer from preimage enumerations
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    For each $n$, density gives a target ball of the stated radius containing the image point. Its preimage enumeration
    emits a source ball containing the input point, and the metric test succeeds at some precision. Thus some triple
    succeeds. All earlier trials terminate, so sequential search returns the least successful triple and projection
    extracts its center $j_n$. Every successful trial certifies
    $$d(q_{j_n},f(x))<2^{-(n+2)}.$$
    For $m\ge n$, the triangle inequality bounds the distance between the two selected centers by
    $2^{-(n+2)}+2^{-(m+2)}\le2^{-n}$. The same error estimate implies convergence to $f(x)$. Hence the output is a valid
    fast Cauchy name of the image. The construction is one closed term for all valid names and coordinates, and confluence
    excludes all other numeral outputs.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Write $j_n$ for the index found at coordinate $n$ and $y=f(x)$.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Hence the search
    computes a Cauchy name of the image point. This constructs a computable realizer using only the uniform enumeration
    assumption; continuity follows from the already proved continuity of computably realizable maps.
-/
theorem realizer_of_enumerableBallPreimages (hqX : DenseRange qX) (hqY : DenseRange qY)
    (f : X → Y) (h : HasEnumerableBallPreimages qX qY f) :
    HasComputableRealizer (cauchyRepresentationObject qX hqX)
      (cauchyRepresentationObject qY hqY) f := by
  obtain ⟨E,e,hE,he⟩ := h
  let test (p : cauchyNameDomain qX) (n t : ℕ) :=
    if preimageTrialValue A.approx e p.val (Nat.pair n t) = 0 then 1 else 0
  have hex (p : cauchyNameDomain qX) (n : ℕ) : ∃ t, test p n t = 0 := by
    obtain ⟨t,ht⟩ := A.exists_preimageTrial hqY e f he p n
    exact ⟨t,by simp [test,ht]⟩
  let F (p : cauchyNameDomain qX) (n : ℕ) := (Nat.find (hex p n)).unpair.1
  have hclose (p : cauchyNameDomain qX) (n : ℕ) :
      dist (qY (F p n)) (f (cauchyRepresentation qX p)) < (1/2 : ℝ)^(n+2) := by
    apply A.preimageTrial_sound e f he p n
    have h := Nat.find_spec (hex p n)
    simpa [test] using h
  have hvalid (p : cauchyNameDomain qX) : IsCauchyName qY (F p) := fastCauchy_of_close (hclose p)
  have hlimit (p : cauchyNameDomain qX) :
      cauchyRepresentation qY ⟨F p,hvalid p⟩ = f (cauchyRepresentation qX p) := by
    apply tendsto_nhds_unique (tendsto_cauchyRepresentation qY ⟨F p,hvalid p⟩)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2 : ℝ) < 1)
    refine ⟨N,fun n hn => ?_⟩
    exact (hclose p n).trans_le ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)).trans hN.le)
  have hc := (preimageTrialProgram_computes A.approx A.computes hE).map reverseZero_computes
  have hh := curryInputProgram_closed hc.1
  have hs := searchProgram_least hh test (fun p n t =>
    (curryInputProgram_apply hc.1 p.val n t).trans (hc.2 p.val (Nat.pair n t))) hex
  refine ⟨fun p => ⟨F p,hvalid p⟩,⟨preimageRealizerProgram A.program E,?_⟩,hlimit⟩
  exact hs.map_output (projection_computes true).1 _ (projection_computes true).2

variable (B : LambdaMetricApproximation qY)
include A B

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Together with invariance under computable change of representation, the criterion gives an explicit test for
    independence from the dense sequence. It also preserves effectively open sets when both sequences give computable metric
    presentations. If the metric changes as well, one must instead verify computability of the identity in both directions
    between the two presentations. The inverse-image criterion can be used for that purpose. Equality of the induced
    topologies supplies continuity, but does not supply the required uniform enumerations of basic-ball preimages.
-/
theorem computable_iff_enumerableBallPreimages (hqX : DenseRange qX) (hqY : DenseRange qY)
    (f : X → Y) :
    HasComputableRealizer (cauchyRepresentationObject qX hqX)
      (cauchyRepresentationObject qY hqY) f ↔ HasEnumerableBallPreimages qX qY f :=
  ⟨A.enumerableBallPreimages_of_realizer B hqX hqY f,
    A.realizer_of_enumerableBallPreimages hqX hqY f⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Inverse-image criterion
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For computable Polish spaces with their effective Cauchy representations, the inverse-image criterion above
    proves the converse: uniform effective pullback of basic opens yields a computable realizer.
    Topological admissibility alone gives a continuous realizer; an effective version needs effective information
    about the representation as well.
-/
theorem computable_iff_continuous_enumerableBallPreimages
    (hqX : DenseRange qX) (hqY : DenseRange qY) (f : X → Y) :
    HasComputableRealizer (cauchyRepresentationObject qX hqX)
      (cauchyRepresentationObject qY hqY) f ↔
      Continuous f ∧ HasEnumerableBallPreimages qX qY f := by
  constructor
  · intro hf
    exact ⟨hf.continuous (cauchyRepresentationObject_isAdmissible qX hqX)
      (continuous_cauchyRepresentation qY),A.enumerableBallPreimages_of_realizer B hqX hqY f hf⟩
  · rintro ⟨_,he⟩
    exact A.realizer_of_enumerableBallPreimages hqX hqY f he

end LambdaMetricApproximation
end PolishSpaceBook
