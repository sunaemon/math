module

public import PolishSpaceBook.LambdaMeasureBounds
public import PolishSpaceBook.LambdaEffectiveBallEnumeration

@[expose] public section

/-! # Effective finite unions of balls and exteriors of closed balls

The finite list is compiled structurally into a closed stage test. Every test
retains the supplied Cauchy name and numerical stage. No modulus for the final
strict inequalities is needed.
-/
namespace PolishSpaceBook
open Set Filter Topology Metric NamedLambda NamedLambda.AlphaTerm
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- A code denotes an actual ball, without the padding convention for open names. -/
def codedBall {X : Type*} [MetricSpace X] (q : ℕ → X) (b : ℕ) : Set X :=
  ball (q b.unpair.1) ((RationalCode.ofNat b.unpair.2).value : ℝ)

def codedClosedBall {X : Type*} [MetricSpace X] (q : ℕ → X) (b : ℕ) : Set X :=
  closedBall (q b.unpair.1) ((RationalCode.ofNat b.unpair.2).value : ℝ)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Fix a finite list $L=\Sequence{b_j}{j<\ell}$ of basic ball codes in $X$. Write
    $b_j=\NatPair{i_j}{\rho_j}$ and $r_j=\RationalValue{\rho_j}$ for their center indices and radii, and put
    $$\begin{aligned}
    U_L&:=\bigcup_{j<\ell}\Ball{q_{i_j}}{r_j},\\
    F_L&:=\bigcup_{j<\ell}\{x:d(x,q_{i_j})\le r_j\},\qquad V_L:=\SetDifference{X}{F_L}.
    \end{aligned}$$
    Here $F_L$ uses metric closed balls, which need not be the closures of the corresponding open balls.
-/
def finiteBallUnion {X : Type*} [MetricSpace X] (q : ℕ → X) (L : List ℕ) : Set X :=
  {x | ∃ b ∈ L, x ∈ codedBall q b}

def finiteClosedBallExterior {X : Type*} [MetricSpace X] (q : ℕ → X) (L : List ℕ) : Set X :=
  {x | ∀ b ∈ L, x ∉ codedClosedBall q b}

/-- The same total rational test is used for interior and exterior membership. -/
def metricSideBit (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (outside : Bool) (p : ℕ → ℕ) (b n : ℕ) : ℕ :=
  let a := (approx (p n,(b.unpair.1,n))).value
  let e := (1/2 : ℚ)^n
  let r := (RationalCode.ofNat b.unpair.2).value
  if outside then (if r < a-e-e then 1 else 0) else (if a+e+e < r then 1 else 0)

def metricExteriorStageProgram (M : AlphaTerm) : AlphaTerm :=
  let lower := mapOutputProgram rationalDifferenceProgram (pairOutputProgram
    (mapOutputProgram rationalDifferenceProgram
      (pairOutputProgram (metricStageApproximation M) metricStageError)) metricStageError)
  mapOutputProgram rationalLessTerm (pairOutputProgram metricStageRadius lower)

def metricSideTestProgram (M : AlphaTerm) (outside : Bool) (b : ℕ) : AlphaTerm :=
  reindexProgram (if outside then metricExteriorStageProgram M else metricStageProgram M) (insertBallCode b)

theorem metricSideTestProgram_computes {M : AlphaTerm}
    (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode))
    (outside : Bool) (b : ℕ) :
    UniformNumericalComputes (metricSideTestProgram M outside b)
      (fun p n => metricSideBit approx outside p b n) := by
  cases outside
  · simpa [metricSideTestProgram,metricSideBit,metricBallTestProgram,metricStageTest] using
      metricBallTestProgram_computes approx hM b
  · have ha := metricDistanceInput_computes.map hM
    have hl := (((ha.pair metricStageError_computes).map rationalDifferenceProgram_computes).pair
      metricStageError_computes).map rationalDifferenceProgram_computes
    have hc := (metricStageRadius_computes.pair hl).map rationalLess_computes
    have h := hc.reindex (insertBallCode_computes b)
    refine ⟨h.1,fun p n => ?_⟩
    simpa [metricSideTestProgram,metricExteriorStageProgram,metricSideBit,metricStageApproximation,
      Nat.unpair_pair,rationalDifferenceCode,RationalCode.value_add,
      RationalCode.value_neg,lt_sub_iff_add_lt] using h.2 p n

/-- Compile the finite list using multiplication for intersection and addition for union. -/
def finiteBallStageProgram (M : AlphaTerm) (outside : Bool) : List ℕ → AlphaTerm
  | [] => constantProgram (if outside then 1 else 0)
  | b :: L => combineOutputProgram (if outside then multiplicationTerm else additionTerm)
      (metricSideTestProgram M outside b) (finiteBallStageProgram M outside L)

def finiteBallStageValue (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (outside : Bool) (p : ℕ → ℕ) (n : ℕ) : List ℕ → ℕ
  | [] => if outside then 1 else 0
  | b :: L => if outside then
      metricSideBit approx outside p b n * finiteBallStageValue approx outside p n L
    else metricSideBit approx outside p b n + finiteBallStageValue approx outside p n L

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Finite ball unions and closed-ball exteriors
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Let $p$ be a Cauchy name of $x$, put $\varepsilon_t=2^{-t}$, and let $\zeta_{j,t}$ approximate
    $d(q_{p(t)},q_{i_j})$ with error at most $\varepsilon_t$. The two total rational tests are
    $$\zeta_{j,t}+2\varepsilon_t<r_j,\qquad r_j<\zeta_{j,t}-2\varepsilon_t.$$
    The first certifies $x\in\Ball{q_{i_j}}{r_j}$; the second certifies $d(x,q_{i_j})>r_j$.
    Indeed, the distance-approximation error and the Cauchy-name error give
    $$\zeta_{j,t}-2\varepsilon_t\le d(x,q_{i_j})\le \zeta_{j,t}+2\varepsilon_t.$$
    Conversely,
    $$\begin{aligned}
    \zeta_{j,t}+2\varepsilon_t&\le d(x,q_{i_j})+4\varepsilon_t,\\
     d(x,q_{i_j})-4\varepsilon_t&\le \zeta_{j,t}-2\varepsilon_t.
    \end{aligned}$$
    Each true strict inequality therefore passes its test at every sufficiently large stage.
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    For a single ball code $b$, let $I_b,E_b$ be the closed programs returning the acceptance bits of these tests
    on input name $o$ and stage $t$. Compile the finite list by
    $$\begin{aligned}
    I_{[]}&:=\lambdaab{o}{\lambdaab{t}{\ChurchNumeral{0}}},\\
    I_{b::L}&:=\lambdaab{o}{\lambdaab{t}{\LambdaAdd\,(I_b\,o\,t)\,(I_L\,o\,t)}},\\
    E_{[]}&:=\lambdaab{o}{\lambdaab{t}{\ChurchNumeral{1}}},\\
    E_{b::L}&:=\lambdaab{o}{\lambdaab{t}{\LambdaMul\,(E_b\,o\,t)\,(E_L\,o\,t)}}.
    \end{aligned}$$
    All stage computations terminate, including on streams that are not valid Cauchy names. Search for a nonzero
    output of $I_L$ to semidecide $U_L$, and of $E_L$ to semidecide $V_L$. For the latter search, every point of
    $V_L$ eventually satisfies all the finitely many tests at one common stage. The empty list gives the empty
    union and the whole-space exterior. The effective-basis construction turns these two semidecision programs
    into numerical enumerators of rational balls.
-/
theorem finiteBallStageProgram_computes {M : AlphaTerm}
    (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (hM : NumericalComputes M (fun z =>
      (approx (z.unpair.1,(z.unpair.2.unpair.1,z.unpair.2.unpair.2))).natCode))
    (outside : Bool) (L : List ℕ) :
    UniformNumericalComputes (finiteBallStageProgram M outside L)
      (fun p n => finiteBallStageValue approx outside p n L) := by
  induction L with
  | nil => exact uniform_constant _
  | cons b L ih =>
    have hb := metricSideTestProgram_computes approx hM outside b
    cases outside
    · exact hb.combine ih additionTerm_closed (· + ·) additionTerm_apply
    · exact hb.combine ih multiplicationTerm_closed (· * ·) multiplicationTerm_apply

theorem finiteBallStageValue_outside (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (p : ℕ → ℕ) (n : ℕ) (L : List ℕ) :
    finiteBallStageValue approx true p n L ≠ 0 ↔ ∀ b ∈ L, metricSideBit approx true p b n ≠ 0 := by
  induction L with
  | nil => simp [finiteBallStageValue]
  | cons b L ih => simp [finiteBallStageValue,ih]

theorem finiteBallStageValue_inside (approx : ℕ × (ℕ × ℕ) → RationalCode)
    (p : ℕ → ℕ) (n : ℕ) (L : List ℕ) :
    finiteBallStageValue approx false p n L ≠ 0 ↔ ∃ b ∈ L, metricSideBit approx false p b n ≠ 0 := by
  induction L with
  | nil => simp [finiteBallStageValue]
  | cons b L ih =>
    simp only [finiteBallStageValue,Bool.false_eq_true,ite_false,List.mem_cons,exists_eq_or_imp]
    rw [← ih]
    omega

namespace LambdaMetricApproximation
variable {X : Type*} [MetricSpace X] [CompleteSpace X] {q : ℕ → X}
variable (A : LambdaMetricApproximation q)

/-- Each successful stage is sound; for a true strict inequality, all sufficiently
late stages succeed. The common eventual stage is essential for intersections. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Finite ball unions and closed-ball exteriors
-/
theorem sideBit_sound (outside : Bool) (p : cauchyNameDomain q) (b n : ℕ)
    (h : metricSideBit A.approx outside p.val b n ≠ 0) :
    if outside then cauchyRepresentation q p ∉ codedClosedBall q b
    else cauchyRepresentation q p ∈ codedBall q b := by
  have ha := abs_le.mp (A.error (p.val n) b.unpair.1 n)
  have hx := cauchyRepresentation_dist_le q p n
  have htri₁ := dist_triangle_left (cauchyRepresentation q p) (q b.unpair.1) (q (p.val n))
  have htri₂ := dist_triangle (q (p.val n)) (cauchyRepresentation q p) (q b.unpair.1)
  cases outside <;> simp only [metricSideBit,Bool.false_eq_true,ite_false,ite_true,
    ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] at h
  · have ht := (Rat.cast_lt (K := ℝ)).mpr h
    simp only [Bool.false_eq_true,ite_false,codedBall,mem_ball]
    push_cast at ht
    linarith
  · have ht := (Rat.cast_lt (K := ℝ)).mpr h
    simp only [ite_true,codedClosedBall,mem_closedBall,not_le]
    push_cast at ht
    linarith

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Finite ball unions and closed-ball exteriors
-/
theorem sideBit_eventually (outside : Bool) (p : cauchyNameDomain q) (b : ℕ)
    (h : if outside then cauchyRepresentation q p ∉ codedClosedBall q b
      else cauchyRepresentation q p ∈ codedBall q b) :
    ∀ᶠ n in atTop, metricSideBit A.approx outside p.val b n ≠ 0 := by
  have hp : Tendsto (fun n => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let x := cauchyRepresentation q p
  let r : ℝ := (RationalCode.ofNat b.unpair.2).value
  cases outside
  · have hg : 0 < (r - dist x (q b.unpair.1))/4 := by
      simp only [Bool.false_eq_true,ite_false,codedBall,mem_ball] at h
      dsimp [r,x]; linarith
    filter_upwards [hp.eventually (eventually_lt_nhds hg)] with n hn
    have ha := (abs_le.mp (A.error (p.val n) b.unpair.1 n)).2
    have hx := cauchyRepresentation_dist_le q p n
    have ht := dist_triangle (q (p.val n)) x (q b.unpair.1)
    have he : ((A.approx (p.val n,(b.unpair.1,n))).value : ℝ) +
        (1/2:ℝ)^n+(1/2:ℝ)^n < r := by linarith
    have hr : (A.approx (p.val n,(b.unpair.1,n))).value +
        (1/2:ℚ)^n+(1/2:ℚ)^n < (RationalCode.ofNat b.unpair.2).value := by
      dsimp [r] at he
      apply (Rat.cast_lt (K := ℝ)).mp
      push_cast
      exact he
    simp only [metricSideBit,Bool.false_eq_true,ite_false,ite_true,hr,ne_eq,one_ne_zero,not_false_eq_true]
  · have hg : 0 < (dist x (q b.unpair.1) - r)/4 := by
      simp only [ite_true,codedClosedBall,mem_closedBall,not_le] at h
      dsimp [r,x]; linarith
    filter_upwards [hp.eventually (eventually_lt_nhds hg)] with n hn
    have ha := (abs_le.mp (A.error (p.val n) b.unpair.1 n)).1
    have hx := cauchyRepresentation_dist_le q p n
    have ht := dist_triangle_left x (q b.unpair.1) (q (p.val n))
    have he : r < ((A.approx (p.val n,(b.unpair.1,n))).value : ℝ) -
        (1/2:ℝ)^n-(1/2:ℝ)^n := by linarith
    have hr : (RationalCode.ofNat b.unpair.2).value <
        (A.approx (p.val n,(b.unpair.1,n))).value - (1/2:ℚ)^n-(1/2:ℚ)^n := by
      dsimp [r] at he
      apply (Rat.cast_lt (K := ℝ)).mp
      push_cast
      exact he
    simp only [metricSideBit,ite_true,hr,ne_eq,one_ne_zero,not_false_eq_true]

def finiteBallSemidecider (outside : Bool) (L : List ℕ) : AlphaTerm :=
  digitSearchProgram (finiteBallStageProgram A.program outside L)

theorem finiteBallSemidecider_domain (outside : Bool) (L : List ℕ) (p : cauchyNameDomain q) :
    (∃ m, OracleRuns p.val (A.finiteBallSemidecider outside L) 0 m) ↔
      if outside then cauchyRepresentation q p ∈ finiteClosedBallExterior q L
      else cauchyRepresentation q p ∈ finiteBallUnion q L := by
  have hc := finiteBallStageProgram_computes A.approx A.computes outside L
  rw [finiteBallSemidecider,digitSearchProgram_domain hc.1 p.val _ (hc.2 p.val)]
  cases outside
  · simp only [Bool.false_eq_true,ite_false,finiteBallStageValue_inside]
    constructor
    · rintro ⟨n,b,hb,hn⟩
      exact ⟨b,hb,A.sideBit_sound false p b n hn⟩
    · rintro ⟨b,hb,hn⟩
      obtain ⟨n,hn⟩ := (A.sideBit_eventually false p b hn).exists
      exact ⟨n,b,hb,hn⟩
  · simp only [ite_true,finiteBallStageValue_outside]
    constructor
    · rintro ⟨n,hn⟩ b hb
      exact A.sideBit_sound true p b n (hn b hb)
    · intro h
      clear hc
      have he : ∀ᶠ n in atTop, ∀ b ∈ L, metricSideBit A.approx true p.val b n ≠ 0 := by
        induction L with
        | nil => simp
        | cons b L ih =>
          have hb := A.sideBit_eventually true p b (h b (by simp))
          have ht := ih (fun c hc => h c (by simp [hc]))
          filter_upwards [hb,ht] with n hn ht
          simpa using And.intro hn ht
      exact he.exists

include A in
theorem finiteBall_semidecidable (hq : DenseRange q) (outside : Bool) (L : List ℕ) :
    SemidecidableFromNames (cauchyRepresentationObject q hq)
      (if outside then finiteClosedBallExterior q L else finiteBallUnion q L) := by
  refine ⟨A.finiteBallSemidecider outside L,
    digitSearchProgram_closed (finiteBallStageProgram_computes A.approx A.computes outside L).1,?_⟩
  intro p
  cases outside with
  | false => simpa only [Bool.false_eq_true,ite_false,cauchyRepresentationObject] using
      A.finiteBallSemidecider_domain false L p
  | true => simpa only [ite_true,cauchyRepresentationObject] using
      A.finiteBallSemidecider_domain true L p

include A in
/-- Both open sets have numerical enumerators, obtained from the actual semidecision programs. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: proposition
  title: Finite ball unions and closed-ball exteriors
-/
theorem finiteBall_has_enumeration (hq : DenseRange q) (outside : Bool) (L : List ℕ) :
    ∃ E f, NumericalComputes E f ∧
      (if outside then finiteClosedBallExterior q L else finiteBallUnion q L) =
        ⋃ n, enumeratedRationalBall q (f n) :=
  A.semidecidable_has_ball_enumeration hq (A.finiteBall_semidecidable hq outside L)

end LambdaMetricApproximation
end PolishSpaceBook
