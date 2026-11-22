module

public import PolishSpaceBook.LambdaMetricBalls
public import PolishSpaceBook.RationalCauchyEstimates
public import PolishSpaceBook.RepresentedBaireSpace

@[expose] public section

/-! # Semideciding invalid Cauchy names by closed lambda programs

A stage decodes one triple, reads two name digits, computes a rational distance
approximation and checks the positive-margin violation. Search has the exact
invalid-name domain, without assuming completeness or density.
-/
namespace PolishSpaceBook
open Set NamedLambda NamedLambda.AlphaTerm
namespace NamedLambda.AlphaTerm

/-- The stage index is `pair n (pair m k)`. -/
def cauchyStageFirst : AlphaTerm := liftNumericalProgram (numericalProjectionTerm true)
def cauchyStageSecond : AlphaTerm := liftNumericalProgram
  (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))
def cauchyStagePrecision : AlphaTerm := liftNumericalProgram
  (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))

def cauchyDistanceInput : AlphaTerm := pairOutputProgram (queryOutputProgram cauchyStageFirst)
  (pairOutputProgram (queryOutputProgram cauchyStageSecond) cauchyStagePrecision)

def cauchyStageBound : AlphaTerm := mapOutputProgram rationalAddTerm
  (pairOutputProgram (mapOutputProgram rationalDyadicTerm cauchyStageFirst)
    (mapOutputProgram rationalDyadicTerm cauchyStagePrecision))

def cauchyStageComparison (M : AlphaTerm) : AlphaTerm :=
  mapOutputProgram rationalLessTerm
    (pairOutputProgram cauchyStageBound (mapOutputProgram M cauchyDistanceInput))

def cauchyStageOrder : AlphaTerm :=
  combineOutputProgram lessOrEqualTerm cauchyStageFirst cauchyStageSecond

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In the term expressions below, abbreviate
    $$\begin{aligned}
    n&:=\LambdaNumericProjection{1}z,\\
    m&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
    k&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z).
    \end{aligned}$$
    Define the closed stage program $T$ by composition and pairing of the following component procedures:
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,(on)\,(\LambdaNumericPair\,(om)\,k)),\\
    U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,(\LambdaDyadic\,n)\,(\LambdaDyadic\,k)),\\
    B&:=\LambdaLeCase{n}{m}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
    T\,o\,z&\to_\beta^*\LambdaMul\,B\,
     (\LambdaRationalLess\,(\LambdaNumericPair\,U\,V)).
    \end{aligned}$$
    Expand the abbreviations before supplying the arguments. The helper beta-redexes give the displayed reduction, and all
    internal binders are chosen fresh once. Put
    $$\begin{aligned}
    G_o&:=\lambdaab{z}{\LambdaZeroTest\,(T\,o\,z)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
    I&:=\lambdaab{x}{x},\\
    S&:=\lambdaab{o}{\lambdaab{a}{\LambdaResultSearch\,G_o\,I}}.
    \end{aligned}$$
    The argument $a$ is unused.
-/
def invalidCauchyStageProgram (M : AlphaTerm) : AlphaTerm :=
  combineOutputProgram multiplicationTerm cauchyStageOrder (cauchyStageComparison M)

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In the term expressions below, abbreviate
    $$\begin{aligned}
    n&:=\LambdaNumericProjection{1}z,\\
    m&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
    k&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z).
    \end{aligned}$$
    Define the closed stage program $T$ by composition and pairing of the following component procedures:
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,(on)\,(\LambdaNumericPair\,(om)\,k)),\\
    U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,(\LambdaDyadic\,n)\,(\LambdaDyadic\,k)),\\
    B&:=\LambdaLeCase{n}{m}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
    T\,o\,z&\to_\beta^*\LambdaMul\,B\,
     (\LambdaRationalLess\,(\LambdaNumericPair\,U\,V)).
    \end{aligned}$$
    Expand the abbreviations before supplying the arguments. The helper beta-redexes give the displayed reduction, and all
    internal binders are chosen fresh once. Put
    $$\begin{aligned}
    G_o&:=\lambdaab{z}{\LambdaZeroTest\,(T\,o\,z)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
    I&:=\lambdaab{x}{x},\\
    S&:=\lambdaab{o}{\lambdaab{a}{\LambdaResultSearch\,G_o\,I}}.
    \end{aligned}$$
    The argument $a$ is unused.
-/
def invalidCauchySearchProgram (M : AlphaTerm) : AlphaTerm :=
  digitSearchProgram (invalidCauchyStageProgram M)

theorem cauchyStageFirst_computes : UniformNumericalComputes cauchyStageFirst
    (fun _ j => j.unpair.1) := by
  simpa [cauchyStageFirst] using (projection_computes true).uniform

theorem cauchyStageSecond_computes : UniformNumericalComputes cauchyStageSecond
    (fun _ j => j.unpair.2.unpair.1) := by
  simpa [cauchyStageSecond] using ((projection_computes true).comp (projection_computes false)).uniform

theorem cauchyStagePrecision_computes : UniformNumericalComputes cauchyStagePrecision
    (fun _ j => j.unpair.2.unpair.2) := by
  simpa [cauchyStagePrecision] using ((projection_computes false).comp (projection_computes false)).uniform

theorem cauchyDistanceInput_computes : UniformNumericalComputes cauchyDistanceInput
    (fun p j => Nat.pair (p j.unpair.1) (Nat.pair (p j.unpair.2.unpair.1) j.unpair.2.unpair.2)) :=
  cauchyStageFirst_computes.query.pair (cauchyStageSecond_computes.query.pair cauchyStagePrecision_computes)

theorem cauchyStageBound_computes : UniformNumericalComputes cauchyStageBound
    (fun _ j => ((RationalCode.dyadic j.unpair.1).add (RationalCode.dyadic j.unpair.2.unpair.2)).natCode) := by
  simpa [cauchyStageBound,Nat.unpair_pair] using
    ((cauchyStageFirst_computes.map rationalDyadic_computes).pair
      (cauchyStagePrecision_computes.map rationalDyadic_computes)).map rationalAdd_computes

theorem cauchyStageOrder_computes : UniformNumericalComputes cauchyStageOrder
    (fun _ j => if j.unpair.1 ≤ j.unpair.2.unpair.1 then 1 else 0) :=
  cauchyStageFirst_computes.combine cauchyStageSecond_computes lessOrEqualTerm_closed
    (fun n m => if n ≤ m then 1 else 0) lessOrEqualTerm_apply

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $A:\NN^3\to\NN$ be a total rational-code-valued function computed by a closed term $M$, so that
    $$M\,\ChurchNumeral{\NatPair{i}{\NatPair{j}{k}}}\to_\beta^*\ChurchNumeral{A(i,j,k)}.$$
    For a sequence $p$, the test at stage $z=\NatPair{n}{\NatPair{m}{k}}$ is
    $$n\le m\quad\text{and}\quad
    2^{-n}+2^{-k}<\RationalValue{A(p(n),p(m),k)}.$$
    This construction makes no metric assumption about $A$. It is a numerical test on two digits of an arbitrary sequence.
-/
def invalidCauchyTest (approx : ℕ × (ℕ × ℕ) → RationalCode) (p : ℕ → ℕ) (j : ℕ) : Prop :=
  j.unpair.1 ≤ j.unpair.2.unpair.1 ∧
    (1/2 : ℚ)^j.unpair.1 + (1/2 : ℚ)^j.unpair.2.unpair.2 <
      (approx (p j.unpair.1,(p j.unpair.2.unpair.1,j.unpair.2.unpair.2))).value

instance (approx : ℕ × (ℕ × ℕ) → RationalCode) (p : ℕ → ℕ) (j : ℕ) :
    Decidable (invalidCauchyTest approx p j) := inferInstanceAs (Decidable (_ ∧ _))

/-- The program is total for every input sequence, with no metric assumptions. -/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Total two-query test and exact search
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    Numerical projections recover the three indices. The two queries and numerical pairings supply the input to $M$, whose
    assumed computation gives $V$. Dyadic coding and rational addition give $U$ with value $2^{-n}+2^{-k}$. Natural-number
    comparison returns one exactly when $n\le m$, and rational comparison returns one exactly when the strict inequality
    holds. Multiplication therefore returns one exactly when both conditions hold. All component computations terminate, so
    the stage program is total on every sequence. Only the two stated queries occur; replacing the sequence by another with
    the same two answers leaves the result unchanged. The abstractions bind the only free variables, proving closedness.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For the actual program, use numerical projections to recover $n,m,k$. Compute the two tests as zero-or-one values and
    multiply them. Queries, the fixed distance-approximation term, dyadic rational codes, rational addition, and comparison
    give a closed stage term $T$ which returns one on success and zero on failure. Reverse its answers by zero testing and
    apply result search with the identity as its result function. This closed program returns the least successful stage
    index. If all stages fail, the no-output part of the result-search lemma excludes every numeral output, irrespective of
    reduction order. The Sierpi\'nski semidecision criterion now gives the characteristic map.
    §{sec:lambda-rational-ball-programs} constructs these terms explicitly. The error argument uses only the Cauchy
    inequalities and the distance-approximation bound; it requires neither completeness nor density.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $A:\NN^3\to\NN$ be a total rational-code-valued function computed by a closed term $M$, so that
    $$M\,\ChurchNumeral{\NatPair{i}{\NatPair{j}{k}}}\to_\beta^*\ChurchNumeral{A(i,j,k)}.$$
    For a sequence $p$, the test at stage $z=\NatPair{n}{\NatPair{m}{k}}$ is
    $$n\le m\quad\text{and}\quad
    2^{-n}+2^{-k}<\RationalValue{A(p(n),p(m),k)}.$$
    This construction makes no metric assumption about $A$. It is a numerical test on two digits of an arbitrary sequence.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In the term expressions below, abbreviate
    $$\begin{aligned}
    n&:=\LambdaNumericProjection{1}z,\\
    m&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
    k&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z).
    \end{aligned}$$
    Define the closed stage program $T$ by composition and pairing of the following component procedures:
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,(on)\,(\LambdaNumericPair\,(om)\,k)),\\
    U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,(\LambdaDyadic\,n)\,(\LambdaDyadic\,k)),\\
    B&:=\LambdaLeCase{n}{m}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
    T\,o\,z&\to_\beta^*\LambdaMul\,B\,
     (\LambdaRationalLess\,(\LambdaNumericPair\,U\,V)).
    \end{aligned}$$
    Expand the abbreviations before supplying the arguments. The helper beta-redexes give the displayed reduction, and all
    internal binders are chosen fresh once. Put
    $$\begin{aligned}
    G_o&:=\lambdaab{z}{\LambdaZeroTest\,(T\,o\,z)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
    I&:=\lambdaab{x}{x},\\
    S&:=\lambdaab{o}{\lambdaab{a}{\LambdaResultSearch\,G_o\,I}}.
    \end{aligned}$$
    The argument $a$ is unused.
-/
theorem invalidCauchyStageProgram_computes {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)) :
    UniformNumericalComputes (invalidCauchyStageProgram M)
      (fun p j => if invalidCauchyTest approx p j then 1 else 0) := by
  have ha : UniformNumericalComputes (mapOutputProgram M cauchyDistanceInput)
      (fun p j => (approx (p j.unpair.1,(p j.unpair.2.unpair.1,j.unpair.2.unpair.2))).natCode) := by
    simpa [Nat.unpair_pair] using cauchyDistanceInput_computes.map hM
  have hc := (cauchyStageBound_computes.pair ha).map rationalLess_computes
  have h := cauchyStageOrder_computes.combine hc multiplicationTerm_closed (· * ·) multiplicationTerm_apply
  refine ⟨h.1, fun p j => ?_⟩
  have hj := h.2 p j
  by_cases ho : j.unpair.1 ≤ j.unpair.2.unpair.1 <;>
    by_cases hc : (1/2 : ℚ)^j.unpair.1 + (1/2 : ℚ)^j.unpair.2.unpair.2 <
      (approx (p j.unpair.1,(p j.unpair.2.unpair.1,j.unpair.2.unpair.2))).value <;>
    simpa [invalidCauchyStageProgram,cauchyStageComparison,invalidCauchyTest,
      Nat.unpair_pair,ho,hc] using hj

theorem invalidCauchySearchProgram_closed {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)) :
    (invalidCauchySearchProgram M).Closed :=
  digitSearchProgram_closed (invalidCauchyStageProgram_computes approx hM).1

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Total two-query test and exact search
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: prose
  excerpt: |
    The zero test in $G_o$ returns zero exactly at successful stages. Since every stage terminates, the result-search lemma
    with input queries returns the least such stage, with $I$ returning its numeral unchanged. If no stage succeeds, the
    same lemma excludes every numeral output under any reduction order. This proves the exact domain assertion for $S$. When
    $A$ approximates distances with error at most $2^{-k}$, the two error estimates in §{sec:tte-polish-as-represented}
    identify this domain with the complement of the fast Cauchy-name domain.
-/
/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In the term expressions below, abbreviate
    $$\begin{aligned}
    n&:=\LambdaNumericProjection{1}z,\\
    m&:=\LambdaNumericProjection{1}(\LambdaNumericProjection{2}z),\\
    k&:=\LambdaNumericProjection{2}(\LambdaNumericProjection{2}z).
    \end{aligned}$$
    Define the closed stage program $T$ by composition and pairing of the following component procedures:
    $$\begin{aligned}
    V&:=M\,(\LambdaNumericPair\,(on)\,(\LambdaNumericPair\,(om)\,k)),\\
    U&:=\LambdaRationalAdd\,(\LambdaNumericPair\,(\LambdaDyadic\,n)\,(\LambdaDyadic\,k)),\\
    B&:=\LambdaLeCase{n}{m}{\ChurchNumeral{1}}{\ChurchNumeral{0}},\\
    T\,o\,z&\to_\beta^*\LambdaMul\,B\,
     (\LambdaRationalLess\,(\LambdaNumericPair\,U\,V)).
    \end{aligned}$$
    Expand the abbreviations before supplying the arguments. The helper beta-redexes give the displayed reduction, and all
    internal binders are chosen fresh once. Put
    $$\begin{aligned}
    G_o&:=\lambdaab{z}{\LambdaZeroTest\,(T\,o\,z)\,\ChurchNumeral{1}\,\ChurchNumeral{0}},\\
    I&:=\lambdaab{x}{x},\\
    S&:=\lambdaab{o}{\lambdaab{a}{\LambdaResultSearch\,G_o\,I}}.
    \end{aligned}$$
    The argument $a$ is unused.
-/
theorem invalidCauchySearchProgram_runs_iff {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode))
    (p : ℕ → ℕ) (a j : ℕ) :
    OracleRuns p (invalidCauchySearchProgram M) a j ↔
      invalidCauchyTest approx p j ∧ ∀ i < j, ¬ invalidCauchyTest approx p i := by
  rw [invalidCauchySearchProgram,digitSearchProgram_runs_iff
    (invalidCauchyStageProgram_computes approx hM).1 p _
    ((invalidCauchyStageProgram_computes approx hM).2 p)]
  simp

theorem invalidCauchySearchProgram_domain {M : AlphaTerm} (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode)) (p : ℕ → ℕ) (a : ℕ) :
    (∃ j, OracleRuns p (invalidCauchySearchProgram M) a j) ↔ ∃ j, invalidCauchyTest approx p j := by
  rw [invalidCauchySearchProgram,digitSearchProgram_domain
    (invalidCauchyStageProgram_computes approx hM).1 p _
    ((invalidCauchyStageProgram_computes approx hM).2 p)]
  simp

/-@ booklink:
  source: polish-space-book/appendix-effective-computational-constructions.md
  target: statement
  kind: proposition
  title: Total two-query test and exact search
-/
theorem invalidCauchyTest_iff_of_agree (approx : ℕ × (ℕ × ℕ) → RationalCode) (p r : ℕ → ℕ) (j : ℕ)
    (hn : p j.unpair.1 = r j.unpair.1) (hm : p j.unpair.2.unpair.1 = r j.unpair.2.unpair.1) :
    invalidCauchyTest approx p j ↔ invalidCauchyTest approx r j := by
  simp only [invalidCauchyTest,hn,hm]

end NamedLambda.AlphaTerm

namespace LambdaMetricApproximation
universe u
variable {X : Type u} [MetricSpace X] {q : ℕ → X} (A : LambdaMetricApproximation q)

theorem invalidCauchyTest_iff (p : ℕ → ℕ) (j : ℕ) :
    invalidCauchyTest A.approx p j ↔ A.toRationalMetricApproximation.invalidNameStage p j = true := by
  simp [invalidCauchyTest,RationalMetricApproximation.invalidNameStage,
    RationalMetricApproximation.invalidNameTest,RationalCode.lt_iff]

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Effective closedness of the Cauchy-name domain
-/
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
theorem invalidNameSemidecider_domain (p : ℕ → ℕ) (a : ℕ) :
    (∃ j, OracleRuns p (invalidCauchySearchProgram A.program) a j) ↔ ¬ IsCauchyName q p := by
  rw [invalidCauchySearchProgram_domain A.approx A.computes]
  simp only [A.invalidCauchyTest_iff]
  exact A.toRationalMetricApproximation.exists_invalidNameStage_iff p

include A in
theorem semidecidable_invalid_names :
    SemidecidableFromNames baireIdentityRepresentation (cauchyNameDomain q)ᶜ :=
  ⟨invalidCauchySearchProgram A.program,invalidCauchySearchProgram_closed A.approx A.computes,
    fun p => A.invalidNameSemidecider_domain p.val 0⟩

include A in
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: proposition
  title: Effective closedness of the Cauchy-name domain
-/
theorem computable_invalid_name_characteristic :
    HasComputableRealizer baireIdentityRepresentation sierpinskiRepresentation
      (fun p => p ∈ (cauchyNameDomain q)ᶜ) :=
  (lambda_computable_sierpinski_iff _ _).mpr A.semidecidable_invalid_names

end LambdaMetricApproximation
end PolishSpaceBook
