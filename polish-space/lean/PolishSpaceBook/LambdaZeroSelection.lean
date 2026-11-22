module

public import PolishSpaceBook.LambdaRealAddition
public import PolishSpaceBook.LambdaRealMetric
public import PolishSpaceBook.LambdaFunctionSpaces
public import PolishSpaceBook.LambdaRealEquality
public import PolishSpaceBook.EffectiveDensePresentations
public import PolishSpaceBook.BinaryRepresentations

@[expose] public section

/-! # Finite-query obstruction to uniform zero selection

A fixed computable family has a flat zero interval at parameter zero.
Small positive and negative parameters force its zeros to opposite sides.
-/
namespace PolishSpaceBook
set_option maxHeartbeats 1000000
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA Filter Topology

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    The intermediate value theorem guarantees existence, but does not supply one procedure for selecting an exact zero
    from every named function. We prove this distinction with one explicit family. The input functions below are defined
    on $\R$, so their names provide even more information than their restrictions to $[0,1]$.
-/
noncomputable def plateauFunction (a x : ℝ) : ℝ := max (x-3/4) 0 - max (1/4-x) 0 + a

theorem plateauFunction_continuous (a : ℝ) : Continuous (plateauFunction a) := by
  unfold plateauFunction
  fun_prop

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: lemma
  title: A computable family with a flat zero interval
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Continuity follows from continuity of maximum, subtraction, and addition. The endpoints have values
    $-1/4+a$ and $1/4+a$. If $a>0$ and $x\ge1/4$, the second maximum vanishes and $f_a(x)\ge a>0$.
    If $a<0$ and $x\le3/4$, the first maximum vanishes and $f_a(x)\le a<0$. Also, since each maximum changes
    by at most $|x-y|$,
    $$|f_a(x)-f_b(y)|\le2|x-y|+|a-b|.$$
    Setting $a=b$ gives the stated modulus. In particular,
    $|x-y|\le2^{-(n+1)}$ implies $|f_a(x)-f_a(y)|\le2^{-n}$.
-/
theorem plateauFunction_endpoints {a : ℝ} (ha : |a| < 1/4) :
    plateauFunction a 0 < 0 ∧ 0 < plateauFunction a 1 := by
  obtain ⟨hl,hu⟩ := abs_lt.mp ha
  norm_num [plateauFunction]
  constructor <;> linarith

theorem plateauFunction_positive_root {a x : ℝ} (ha : 0 < a)
    (hx : plateauFunction a x = 0) : x < 1/4 := by
  by_contra h
  have hx' : 1/4-x ≤ 0 := by linarith
  have hm := le_max_right (x-3/4) (0:ℝ)
  simp only [plateauFunction,max_eq_right hx',sub_zero] at hx
  linarith

theorem plateauFunction_negative_root {a x : ℝ} (ha : a < 0)
    (hx : plateauFunction a x = 0) : 3/4 < x := by
  by_contra h
  have hx' : x-3/4 ≤ 0 := by linarith
  have hm := le_max_right (1/4-x) (0:ℝ)
  simp only [plateauFunction,max_eq_right hx',zero_sub] at hx
  linarith

theorem plateauFunction_dist (a b x y : ℝ) :
    dist (plateauFunction a x) (plateauFunction b y) ≤ 2*dist x y + dist a b := by
  have h₁ := abs_max_sub_max_le_abs (x-3/4) (y-3/4) (0:ℝ)
  have h₂ := abs_max_sub_max_le_abs (1/4-x) (1/4-y) (0:ℝ)
  have he₁ : x-3/4-(y-3/4) = x-y := by ring
  have he₂ : 1/4-x-(1/4-y) = -(x-y) := by ring
  rw [he₁] at h₁
  rw [he₂,abs_neg] at h₂
  calc
    _ ≤ dist (max (x-3/4) 0 - max (1/4-x) 0)
        (max (y-3/4) 0 - max (1/4-y) 0) + dist a b := dist_add_add_le _ _ _ _
    _ ≤ (dist (max (x-3/4) 0) (max (y-3/4) 0) +
        dist (max (1/4-x) 0) (max (1/4-y) 0)) + dist a b :=
      by
        have h := dist_sub_sub_le (max (x-3/4) 0) (max (1/4-x) 0)
          (max (y-3/4) 0) (max (1/4-y) 0)
        linarith
    _ ≤ _ := by simp only [Real.dist_eq]; linarith

theorem plateauFunction_modulus (a : ℝ) (n : ℕ) {x y : ℝ}
    (h : dist x y ≤ (1/2:ℝ)^(n+1)) :
    dist (plateauFunction a x) (plateauFunction a y) ≤ (1/2:ℝ)^n := by
  have hb := plateauFunction_dist a a x y
  simp only [dist_self,add_zero] at hb
  calc
    _ ≤ 2 * dist x y := hb
    _ ≤ 2 * (1/2:ℝ)^(n+1) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

def quarterCode : ℕ := Nat.pair (Nat.pair 1 0) 3
def threeQuarterCode : ℕ := Nat.pair (Nat.pair 3 0) 3

@[simp] theorem quarterCode_value : rationalPoint quarterCode = 1/4 := by
  norm_num [quarterCode,rationalPoint,RationalCode.ofNat,RationalCode.value]
@[simp] theorem threeQuarterCode_value : rationalPoint threeQuarterCode = 3/4 := by
  norm_num [threeQuarterCode,rationalPoint,RationalCode.ofNat,RationalCode.value]

def plateauCode (z : ℕ) : ℕ := rationalDifferenceCode (Nat.pair
  (rationalDifferenceCode (Nat.pair
    (rationalMaxCode (rationalDifferenceCode (Nat.pair z.unpair.2 threeQuarterCode)) 0)
    (rationalMaxCode (rationalDifferenceCode (Nat.pair quarterCode z.unpair.2)) 0)))
  (RationalCode.ofNat z.unpair.1).neg.natCode)

def plateauProgram : AlphaTerm :=
  let X := numericalProjectionTerm false
  let R := numericalCompose rationalMaxProgram (pairNumerical
    (numericalCompose rationalDifferenceProgram (pairNumerical X (numericalConstant threeQuarterCode)))
    (numericalConstant 0))
  let L := numericalCompose rationalMaxProgram (pairNumerical
    (numericalCompose rationalDifferenceProgram (pairNumerical (numericalConstant quarterCode) X))
    (numericalConstant 0))
  numericalCompose rationalDifferenceProgram (pairNumerical
    (numericalCompose rationalDifferenceProgram (pairNumerical R L))
    (numericalCompose rationalNegTerm (numericalProjectionTerm true)))

theorem plateauProgram_computes : NumericalComputes plateauProgram plateauCode := by
  have x := projection_computes false
  have r := rationalMaxProgram_computes.comp
    ((rationalDifferenceProgram_computes.comp (x.pair (numericalConstant_computes threeQuarterCode))).pair
      (numericalConstant_computes 0))
  have l := rationalMaxProgram_computes.comp
    ((rationalDifferenceProgram_computes.comp ((numericalConstant_computes quarterCode).pair x)).pair
      (numericalConstant_computes 0))
  have h := rationalDifferenceProgram_computes.comp
    ((rationalDifferenceProgram_computes.comp (r.pair l)).pair
      (rationalNeg_computes.comp (projection_computes true)))
  refine ⟨h.1,fun z => ?_⟩
  simpa only [plateauProgram,plateauCode,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using h.2 z

@[simp] theorem plateauCode_value (a x : ℕ) :
    rationalPoint (plateauCode (Nat.pair a x)) = plateauFunction (rationalPoint a) (rationalPoint x) := by
  have hz : rationalPoint 0 = 0 := by norm_num [rationalPoint,RationalCode.ofNat,RationalCode.value]
  simp [plateauCode,plateauFunction,hz,sub_eq_add_neg]

def plateauName (w : ℕ → ℕ) (n : ℕ) : ℕ := plateauCode (w (n+2))

def plateauEvaluationProgram : AlphaTerm := mapOutputProgram plateauProgram
  (queryOutputProgram (liftNumericalProgram (numericalCompose successorTerm successorTerm)))

theorem plateauEvaluationProgram_computes : UniformNumericalComputes plateauEvaluationProgram plateauName :=
  (successor_computes.comp successor_computes).uniform.query.map plateauProgram_computes

theorem plateauName_isCauchy (p q : realRepresentation.domain) :
    IsCauchyName rationalPoint (plateauName (typeTwoPairName p.val q.val)) := by
  intro n m hnm
  change dist (rationalPoint (plateauCode (Nat.pair (p.val (n+2)) (q.val (n+2)))))
    (rationalPoint (plateauCode (Nat.pair (p.val (m+2)) (q.val (m+2))))) ≤ _
  rw [plateauCode_value,plateauCode_value]
  have hb := plateauFunction_dist (rationalPoint (p.val (n+2))) (rationalPoint (p.val (m+2)))
    (rationalPoint (q.val (n+2))) (rationalPoint (q.val (m+2)))
  have hp := p.property (n+2) (m+2) (by omega)
  have hq := q.property (n+2) (m+2) (by omega)
  have hε : 0 ≤ (1/2:ℝ)^n := by positivity
  rw [pow_add] at hp hq
  norm_num at hp hq
  linarith

theorem plateauName_limit (p q : realRepresentation.domain) :
    realRepresentation.toFun ⟨plateauName (typeTwoPairName p.val q.val),plateauName_isCauchy p q⟩ =
      plateauFunction (realRepresentation.toFun p) (realRepresentation.toFun q) := by
  have hp := (tendsto_cauchyRepresentation rationalPoint p).comp (tendsto_add_atTop_nat 2)
  have hq := (tendsto_cauchyRepresentation rationalPoint q).comp (tendsto_add_atTop_nat 2)
  have hc : Continuous (fun z : ℝ × ℝ => plateauFunction z.1 z.2) := by
    unfold plateauFunction
    fun_prop
  have ht := (hc.tendsto _).comp (hp.prodMk_nhds hq)
  apply tendsto_nhds_unique (tendsto_cauchyRepresentation rationalPoint
    ⟨plateauName (typeTwoPairName p.val q.val),plateauName_isCauchy p q⟩)
  simpa only [Function.comp_def,plateauName,typeTwoPairName,plateauCode_value,
    realRepresentation,cauchyRepresentationObject] using ht

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: lemma
  title: A computable family with a flat zero interval
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    Here is a lambda realizer, including its precision bound. Let $Q$ be the closed numerical program obtained by
    composing the rational subtraction, maximum, and negation routines in the expression defining $f_a(x)$.
    It receives $\NatPair{i}{j}$ and returns a rational code for $f_{q_i}(q_j)$. The constants $1/4$ and $3/4$ have
    codes $\RationalCode{1}{0}{3}$ and $\RationalCode{3}{0}{3}$. For the final addition, subtract the negated parameter.
    The maximum routine compares the two rational codes and returns one of them, as in
    §{sec:tte-polish-as-represented}. All these numerical computations terminate by
    §{sec:lambda-rational-arithmetic}. On the paired name $w=\NamePair{p}{r}$, use
    $$E:=\lambdaab{o}{\lambdaab{n}{Q\bigl(o(\LambdaSucc(\LambdaSucc n))\bigr)}}.$$
    Thus its $n$-th output is a code for $f_{q_{p(n+2)}}(q_{r(n+2)})$. For $m\ge n$, the preceding estimate gives
    $$\bigl|f_{q_{p(n+2)}}(q_{r(n+2)})-f_{q_{p(m+2)}}(q_{r(m+2)})\bigr|
    \le3\cdot2^{-(n+2)}\le2^{-n}.$$
    The output is therefore a valid Cauchy name, and its limit is $f_a(x)$ when $p,r$ name $a,x$.
    Two beta contractions, the successor computations, one query, and the rational computation give each output of $E$.
    \end{proof}
-/
theorem plateau_hasComputableRealizer : HasComputableRealizer
    (typeTwoProductRepresentation realRepresentation realRepresentation) realRepresentation
    (fun z => plateauFunction z.1 z.2) := by
  let F : (typeTwoProductRepresentation realRepresentation realRepresentation).domain →
      realRepresentation.domain := fun p =>
    ⟨plateauName (typeTwoPairName (typeTwoLeftName p.val) (typeTwoRightName p.val)),
      plateauName_isCauchy ⟨_,p.property.1⟩ ⟨_,p.property.2⟩⟩
  refine ⟨F,⟨plateauEvaluationProgram,?_⟩,?_⟩
  · apply typeTwoComputes_iff_runs.mpr
    refine ⟨plateauEvaluationProgram_computes.1,fun p n => ?_⟩
    simpa only [F,typeTwoPair_projections] using plateauEvaluationProgram_computes.2 p.val n
  · intro p
    exact plateauName_limit ⟨_,p.property.1⟩ ⟨_,p.property.2⟩

/-- Every eventually constant test name is generated by a closed lambda term. -/
theorem switchedCauchyName_computable (i j N : ℕ) :
    LambdaFunction.ComputableName (switchedCauchyName i j N) := by
  have ht := numericalIdentity_computes.combine (numericalConstant_computes N)
    strictLessTerm_closed (fun a b => if a < b then 1 else 0) strictLessTerm_apply
  have h := numericalIfZero_computes ht (numericalConstant_computes j) (numericalConstant_computes i)
  refine ⟨_,h.1,fun n => ?_⟩
  by_cases hn : n < N <;> simpa [switchedCauchyName,hn] using h.2 n

/-- This assumption permits arbitrary dependence on the supplied name. -/
def SelectsPlateauZeros (P : AlphaTerm) : Prop :=
  ∀ p : realRepresentation.domain, LambdaFunction.ComputableName p.val →
    |realRepresentation.toFun p| < 1/4 →
    ∃ q : realRepresentation.domain,
      (∀ n, OracleRuns p.val P n (q.val n)) ∧
      plateauFunction (realRepresentation.toFun p) (realRepresentation.toFun q) = 0

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    First suppose that a fixed program $S$, given any computable Cauchy name $p$ of $a$ with $|a|<1/4$,
    outputs a Cauchy name of a zero of $f_a$. Run it on the constant-zero name $p_0(n)=0$ until output coordinate $3$
    returns a code $c$. By finite use, there is $N$ such that every input agreeing with $p_0$ below $N$ admits the
    same finite reduction to $\ChurchNumeral{c}$ at that coordinate.

    Put $\varepsilon:=2^{-(N+4)}$, and choose rational codes $j_+,j_-$ for $\varepsilon,-\varepsilon$.
    Define
    $$p_\pm(n):=\begin{cases}0,&n<N,\\j_\pm,&n\ge N.\end{cases}$$
    These are computable names: compare $n$ with the fixed numeral $N$ and return one of two fixed codes.
    They are valid Cauchy names because $\varepsilon\le2^{-N}$, and they represent $\pm\varepsilon$.
    Moreover, $0<\varepsilon\le1/16<1/4$. By finite use and confluence, both output names have code $c$ at coordinate $3$.
    If their represented zeros are $x_+,x_-$, the Cauchy error bound yields
    $$|x_+-q_c|\le1/8,\qquad |x_--q_c|\le1/8,\qquad |x_+-x_-|\le1/4.$$
    But the lemma gives $x_+<1/4$ and $x_->3/4$, contradicting this last bound.
-/
theorem no_uniform_plateau_zero_selection (P : AlphaTerm) : ¬ SelectsPlateauZeros P := by
  intro hP
  have hz : rationalPoint 0 = 0 := by norm_num [rationalPoint,RationalCode.ofNat,RationalCode.value]
  let p₀ : realRepresentation.domain := constantCauchyName rationalPoint 0
  have hp₀ : realRepresentation.toFun p₀ = 0 := by
    exact (cauchyRepresentation_constantName rationalPoint 0).trans hz
  have hc₀ : LambdaFunction.ComputableName p₀.val :=
    ⟨numericalConstant 0,numericalConstant_computes 0⟩
  obtain ⟨q₀,hq₀,_⟩ := hP p₀ hc₀ (by rw [hp₀]; norm_num)
  obtain ⟨N,hN⟩ := (hq₀ 3).finite_use
  let j := (RationalCode.dyadic (N+4)).natCode
  let k := (RationalCode.ofNat j).neg.natCode
  have hj : rationalPoint j = (1/2:ℝ)^(N+4) := by simp [j,rationalPoint]
  have hk : rationalPoint k = -(1/2:ℝ)^(N+4) := by rw [rationalPoint_neg,hj]
  have hpos : 0 < (1/2:ℝ)^(N+4) := by positivity
  have hsmall : (1/2:ℝ)^(N+4) ≤ (1/2:ℝ)^N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hquarter : (1/2:ℝ)^(N+4) < 1/4 := by
    have h := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
      (show 4 ≤ N+4 by omega)
    norm_num at h
    linarith
  have hdj : dist (rationalPoint 0) (rationalPoint j) ≤ (1/2:ℝ)^N := by
    simpa [Real.dist_eq,hz,hj,abs_of_pos hpos] using hsmall
  have hdk : dist (rationalPoint 0) (rationalPoint k) ≤ (1/2:ℝ)^N := by
    simpa [Real.dist_eq,hz,hk,abs_of_pos hpos] using hsmall
  let pPlus : realRepresentation.domain := ⟨switchedCauchyName 0 j N,switchedCauchyName_isCauchy rationalPoint hdj⟩
  let pMinus : realRepresentation.domain := ⟨switchedCauchyName 0 k N,switchedCauchyName_isCauchy rationalPoint hdk⟩
  have hvPlus : realRepresentation.toFun pPlus = (1/2:ℝ)^(N+4) :=
    (switchedCauchyName_limit rationalPoint hdj).trans hj
  have hvMinus : realRepresentation.toFun pMinus = -(1/2:ℝ)^(N+4) :=
    (switchedCauchyName_limit rationalPoint hdk).trans hk
  obtain ⟨qPlus,hrPlus,hzPlus⟩ := hP pPlus (switchedCauchyName_computable 0 j N)
    (by rw [hvPlus,abs_of_pos hpos]; exact hquarter)
  obtain ⟨qMinus,hrMinus,hzMinus⟩ := hP pMinus (switchedCauchyName_computable 0 k N)
    (by rw [hvMinus,abs_neg,abs_of_pos hpos]; exact hquarter)
  have hePlus : qPlus.val 3 = q₀.val 3 := (hrPlus 3).output_unique
    (hN pPlus.val (fun i hi => ite_eq_left hi))
  have heMinus : qMinus.val 3 = q₀.val 3 := (hrMinus 3).output_unique
    (hN pMinus.val (fun i hi => ite_eq_left hi))
  have hl := plateauFunction_positive_root (by rw [hvPlus]; exact hpos) hzPlus
  have hu := plateauFunction_negative_root (by rw [hvMinus]; linarith) hzMinus
  have hbPlus := cauchyRepresentation_dist_le rationalPoint qPlus 3
  have hbMinus := cauchyRepresentation_dist_le rationalPoint qMinus 3
  change dist (rationalPoint (qPlus.val 3)) (realRepresentation.toFun qPlus) ≤ _ at hbPlus
  change dist (rationalPoint (qMinus.val 3)) (realRepresentation.toFun qMinus) ≤ _ at hbMinus
  rw [hePlus,Real.dist_eq] at hbPlus
  rw [heMinus,Real.dist_eq] at hbMinus
  have hPlus := (abs_le.mp hbPlus).2
  have hMinus := (abs_le.mp hbMinus).1
  norm_num at hPlus hMinus
  linarith

theorem computableName_tagged {p : ℕ → ℕ} (hp : LambdaFunction.ComputableName p) (e : ℕ) :
    LambdaFunction.ComputableName (typeTwoTagName e p) := by
  obtain ⟨A,hA,hp⟩ := hp
  have h := numericalIfZero_computes numericalIdentity_computes (numericalConstant_computes e)
    ((show NumericalComputes A p from ⟨hA,hp⟩).comp predecessor_computes)
  refine ⟨_,h.1,fun n => ?_⟩
  cases n with
  | zero => simpa [typeTwoTagName] using h.2 0
  | succ n => simpa [typeTwoTagName] using h.2 (n+1)

/-- The input includes the fixed valid modulus n ↦ n+1 as a second name. -/
def SelectsIntervalZeros (P : AlphaTerm) : Prop :=
  ∀ (r : ℕ → ℕ) (f : ℝ → ℝ), LambdaFunction.ComputableName r →
    LambdaFunction.FunctionNameRealizes realRepresentation realRepresentation r f →
    f 0 < 0 → 0 < f 1 →
    (∀ n x y, dist x y ≤ (1/2:ℝ)^(n+1) → dist (f x) (f y) ≤ (1/2:ℝ)^n) →
    ∃ q : realRepresentation.domain,
      (∀ n, OracleRuns (typeTwoPairName r (fun k => k+1)) P n (q.val n)) ∧
      realRepresentation.toFun q ∈ Set.Icc (0:ℝ) 1 ∧ f (realRepresentation.toFun q) = 0

/-- Even computable names and a common supplied modulus do not allow uniform selection. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: theorem
  title: No uniform zero selection
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    Finally, let $e$ be the syntax index of the evaluation program $E$ in the lemma. The computable exponential law
    sends a name $p$ of $a$ to the function name $e\concat p$ of $f_a$. This name is computable whenever $p$ is.
    Let $M:=\lambdaab{o}{\LambdaSucc}$, which produces the fixed modulus name, and put
    $$T:=\LambdaPairOutputs{\LambdaNamePrefix{e}}{M}.$$
    If a closed program $P$ selected a zero from the paired function and modulus names, then $C_{P,T}$ would be the
    forbidden parameter-name program $S$. The prefixing, pairing, and input-substitution reductions establish this
    composition on every valid input. All names used in the contradiction are computable.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    A function name supplies information through queries, whereas a function tracker is a natural number on which a
    program can perform numerical computations. We keep the two selection problems separate: the first proof uses finite
    query dependence, and the second uses finite certificate search and self-reference. Both distinguish the existence of
    a zero from a uniform procedure that selects one from the specified input evidence.
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    The intermediate value theorem guarantees existence, but does not supply one procedure for selecting an exact zero
    from every named function. We prove this distinction with one explicit family. The input functions below are defined
    on $\R$, so their names provide even more information than their restrictions to $[0,1]$.
-/
theorem no_uniform_interval_zero_selection (P : AlphaTerm) (hP : P.Closed) :
    ¬ SelectsIntervalZeros P := by
  intro hS
  obtain ⟨F,⟨R,hR⟩,hF⟩ := plateau_hasComputableRealizer
  obtain ⟨e,he⟩ := Term.closedProgram_surjective R hR.1
  have hsection (p : realRepresentation.domain) :
      LambdaFunction.FunctionNameRealizes realRepresentation realRepresentation (typeTwoTagName e p.val)
        (plateauFunction (realRepresentation.toFun p)) := by
    apply LambdaFunction.functionNameRealizes_section (he.symm ▸ hR) hF p
  let T := pairOutputProgram (tagProgram e) (liftNumericalProgram successorTerm)
  have hT : UniformNumericalComputes T
      (fun p => typeTwoPairName (typeTwoTagName e p) (fun k => k+1)) := by
    exact (show UniformNumericalComputes (tagProgram e) (typeTwoTagName e) from
      ⟨tagProgram_closed e,fun p n => tagProgram_runs p e n⟩).pair successor_computes.uniform
  apply no_uniform_plateau_zero_selection (compositionProgram P T)
  intro p hp ha
  obtain ⟨hl,hu⟩ := plateauFunction_endpoints ha
  obtain ⟨q,hq,_,hz⟩ := hS (typeTwoTagName e p.val) (plateauFunction (realRepresentation.toFun p))
    (computableName_tagged hp e) (hsection p) hl hu
    (fun n x y h => plateauFunction_modulus _ n h)
  exact ⟨q,fun n => compositionProgram_runs hP hT.1 (hq n) (hT.2 p.val),hz⟩

end PolishSpaceBook
