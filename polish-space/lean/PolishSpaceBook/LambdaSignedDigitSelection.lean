module

public import PolishSpaceBook.LambdaSignedDigitSums
public import PolishSpaceBook.LambdaFourierCoefficients
public import PolishSpaceBook.LambdaNumericalResultSearch
public import PolishSpaceBook.LambdaUniformPredicates

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Selecting signed digits from dyadic Cauchy names by rational comparisons -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA Set Filter Topology

/-- Clamp the dyadic numerator before converting the index to a rational code. -/
def unitDyadicCode (i : ℕ) : ℕ :=
  RationalCode.natCode ((min i.unpair.1 (2^i.unpair.2),0),2^i.unpair.2-1)

theorem unitDyadicCode_value (i : ℕ) : rationalPoint (unitDyadicCode i) = (unitDyadicPoint i).val := by
  have hp : 1 ≤ 2^i.unpair.2 := Nat.one_le_pow _ _ (by decide)
  simp only [unitDyadicCode,rationalPoint,RationalCode.ofNat_natCode,RationalCode.value,
    unitDyadicPoint]
  push_cast
  rw [Nat.cast_sub hp]
  push_cast
  ring

def unitDyadicCodeProgram : AlphaTerm :=
  let a := numericalProjectionTerm true
  let b := numericalCompose powerTwoTerm (numericalProjectionTerm false)
  let m := numericalIfLe a b a b
  pairNumerical (pairNumerical m (numericalConstant 0)) (numericalCompose predecessorTerm b)

theorem unitDyadicCodeProgram_computes : NumericalComputes unitDyadicCodeProgram unitDyadicCode := by
  have a := projection_computes true
  have b := powerTwo_computes.comp (projection_computes false)
  have m := a.ifLe b a b
  have h := (m.pair (numericalConstant_computes 0)).pair (predecessor_computes.comp b)
  refine ⟨h.1,fun i => ?_⟩
  simpa only [unitDyadicCodeProgram,unitDyadicCode,RationalCode.natCode,ite_true,
    Bool.false_eq_true,ite_false,min_def] using h.2 i

private theorem numericalBranch {C A B : AlphaTerm} {c a b : ℕ → ℕ}
    (hc : NumericalComputes C c) (ha : NumericalComputes A a) (hb : NumericalComputes B b) :
    NumericalComputes (numericalApply3 zeroTestTerm C A B) (fun z => if c z = 0 then a z else b z) := by
  apply hc.apply3 ha hb zeroTestTerm_closed (fun c a b => if c=0 then a else b)
  intro c a b
  cases c with
  | zero => exact branch_zero _ _ (by rw [numeral_closed]; simp)
  | succ c => exact branch_succ c _ _

/-- The second argument is the positive threshold h/2. -/
def signedDigitChoiceCode (r t : ℕ) : ℕ :=
  if (RationalCode.ofNat r).value < -(RationalCode.ofNat t).value then 0
  else if (RationalCode.ofNat t).value < (RationalCode.ofNat r).value then 2 else 1

theorem signedDigitChoiceCode_lt (r t : ℕ) : signedDigitChoiceCode r t < 3 := by
  unfold signedDigitChoiceCode; split_ifs <;> decide

def signedDigitChoiceProgram : AlphaTerm :=
  let r := numericalProjectionTerm true
  let t := numericalProjectionTerm false
  let nt := numericalCompose rationalSubtractProgram (pairNumerical (numericalConstant 0) t)
  let lower := numericalCompose rationalLessTerm (pairNumerical r nt)
  let upper := numericalCompose rationalLessTerm (pairNumerical t r)
  numericalApply3 zeroTestTerm lower
    (numericalApply3 zeroTestTerm upper (numericalConstant 1) (numericalConstant 2)) (numericalConstant 0)

theorem signedDigitChoiceProgram_computes : NumericalComputes signedDigitChoiceProgram
    (fun z => signedDigitChoiceCode z.unpair.1 z.unpair.2) := by
  have r := projection_computes true
  have t := projection_computes false
  have nt := rationalSubtractProgram_computes.comp ((numericalConstant_computes 0).pair t)
  have lower := rationalLess_computes.comp (r.pair nt)
  have upper := rationalLess_computes.comp (t.pair r)
  have h := numericalBranch lower
    (numericalBranch upper (numericalConstant_computes 1) (numericalConstant_computes 2))
    (numericalConstant_computes 0)
  refine ⟨h.1,fun z => ?_⟩
  have hneg : (RationalCode.ofNat (rationalSubtractCode 0 z.unpair.2)).value =
      -(RationalCode.ofNat z.unpair.2).value := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_neg]
    change rationalPoint (rationalSubtractCode 0 z.unpair.2) = -rationalPoint z.unpair.2
    rw [rationalSubtractCode_value]
    have h0 : rationalPoint 0 = 0 := by norm_num [rationalPoint,RationalCode.ofNat,RationalCode.value]
    rw [h0,zero_sub]
  by_cases hl : (RationalCode.ofNat z.unpair.1).value < -(RationalCode.ofNat z.unpair.2).value <;>
    by_cases hu : (RationalCode.ofNat z.unpair.2).value < (RationalCode.ofNat z.unpair.1).value <;>
    simpa only [signedDigitChoiceProgram,signedDigitChoiceCode,Nat.unpair_pair,ite_true,
      Bool.false_eq_true,ite_false,hneg,hl,hu,one_ne_zero] using h.2 z

theorem signedDigitChoiceCode_select (r : ℕ) (n : ℕ) :
    signedDigitChoiceCode r (RationalCode.dyadic (n+3)).natCode =
      (selectSignedDigit ((1/2:ℝ)^(n+2)) (rationalPoint r)).val := by
  have ht : ((RationalCode.dyadic (n+3)).value : ℝ) = (1/2:ℝ)^(n+2)/2 := by
    simp only [RationalCode.value_dyadic]
    push_cast
    rw [show n+3=n+2+1 by omega,pow_succ]
    ring
  have hl : (RationalCode.ofNat r).value < -(RationalCode.dyadic (n+3)).value ↔
      rationalPoint r < -((1/2:ℝ)^(n+2))/2 := by
    rw [← Rat.cast_lt (K := ℝ)]
    simp only [Rat.cast_neg,ht,rationalPoint,neg_div]
  have hu : (RationalCode.dyadic (n+3)).value < (RationalCode.ofNat r).value ↔
      ((1/2:ℝ)^(n+2))/2 < rationalPoint r := by
    rw [← Rat.cast_lt (K := ℝ)]
    simp only [ht,rationalPoint]
  simp only [signedDigitChoiceCode,RationalCode.ofNat_natCode,selectSignedDigit,hl,hu]
  split_ifs <;> rfl

/-- State m is the numerator of the current center with denominator 2^(n+1). -/
@[irreducible] def cauchyDigitCode (p : ℕ → ℕ) (n m : ℕ) : ℕ :=
  signedDigitChoiceCode
    (rationalSubtractCode (unitDyadicCode (p (n+4))) (unitDyadicCode (Nat.pair m (n+1))))
    (RationalCode.dyadic (n+3)).natCode

theorem cauchyDigitCode_lt (p : ℕ → ℕ) (n m : ℕ) : cauchyDigitCode p n m < 3 := by
  unfold cauchyDigitCode
  exact signedDigitChoiceCode_lt _ _

theorem cauchyDigitCode_select (p : ℕ → ℕ) (n m : ℕ) (hm : m ≤ 2^(n+1)) :
    cauchyDigitCode p n m = (selectSignedDigit ((1/2:ℝ)^(n+2))
      ((unitDyadicPoint (p (n+4))).val-(m:ℝ)/(2:ℝ)^(n+1))).val := by
  rw [cauchyDigitCode,signedDigitChoiceCode_select,rationalSubtractCode_value,
    unitDyadicCode_value,unitDyadicCode_value,unitDyadicPoint_pair _ _ hm]

def cauchyDigitProgram : AlphaTerm :=
  let n := liftNumericalProgram (numericalProjectionTerm true)
  let m := liftNumericalProgram (numericalProjectionTerm false)
  let queryIndex := combineOutputProgram additionTerm n (constantProgram 4)
  let sample := mapOutputProgram unitDyadicCodeProgram (queryOutputProgram queryIndex)
  let center := mapOutputProgram unitDyadicCodeProgram
    (pairOutputProgram m (mapOutputProgram successorTerm n))
  let residual := mapOutputProgram rationalSubtractProgram (pairOutputProgram sample center)
  let threshold := mapOutputProgram rationalDyadicTerm
    (combineOutputProgram additionTerm n (constantProgram 3))
  mapOutputProgram signedDigitChoiceProgram (pairOutputProgram residual threshold)

theorem cauchyDigitProgram_computes : UniformNumericalComputes cauchyDigitProgram
    (fun p z => cauchyDigitCode p z.unpair.1 z.unpair.2) := by
  have n := (projection_computes true).uniform
  have m := (projection_computes false).uniform
  have qi := n.combine (uniform_constant 4) additionTerm_closed (·+·) additionTerm_apply
  have sample := qi.query.map unitDyadicCodeProgram_computes
  have center := (m.pair (n.map successor_computes)).map unitDyadicCodeProgram_computes
  have residual := (sample.pair center).map rationalSubtractProgram_computes
  have threshold := (n.combine (uniform_constant 3) additionTerm_closed (·+·) additionTerm_apply).map
    rationalDyadic_computes
  have h := (residual.pair threshold).map signedDigitChoiceProgram_computes
  refine ⟨h.1,fun p z => ?_⟩
  simpa only [cauchyDigitProgram,cauchyDigitCode,Nat.unpair_pair,ite_true,
    Bool.false_eq_true,ite_false,Nat.succ_eq_add_one] using h.2 p z

def cauchySignedNumerator (p : ℕ → ℕ) : ℕ → ℕ :=
  primitiveRec 1 (fun n m => 2*m+cauchyDigitCode p n m-1)

def cauchySignedName (p : ℕ → ℕ) (n : ℕ) : ℕ := cauchyDigitCode p n (cauchySignedNumerator p n)

def cauchySignedNameValid (p : ℕ → ℕ) : signedDigitNameDomain :=
  ⟨cauchySignedName p,fun n => cauchyDigitCode_lt p n _⟩

theorem cauchySignedNumerator_eq_partial (p : ℕ → ℕ) (n : ℕ) :
    cauchySignedNumerator p n = signedPartialNumerator (cauchySignedName p) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 2*cauchySignedNumerator p n+cauchySignedName p n-1 =
      2*signedPartialNumerator (cauchySignedName p) n+cauchySignedName p n-1
    rw [ih]

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Conversely, let $p$ be a $\rho_\nu$-name of $x$. Starting with $v_0(p)=1$, at stage $n$ compute the rational numbers
    $$c_n:=\frac{v_n(p)}{2^{n+1}},\qquad h_n:=2^{-(n+2)},\qquad e_n:=\nu_{p(n+4)}-c_n,$$
    choose the digit code
    $$d_n:=\begin{cases}0,&e_n<-h_n/2,\\2,&h_n/2<e_n,\\1,&-h_n/2\le e_n\le h_n/2,\end{cases}$$
    and put $v_{n+1}(p):=2v_n(p)+d_n-1$ and $\psi(p)(n):=d_n$. All comparisons are between rational numbers, including
    the equality cases at the thresholds. The bounds $1\le v_n(p)<2^{n+1}$ hold for every input stream, since
    $d_n\in\{0,1,2\}$ regardless of whether that stream is a valid Cauchy name.
-/
theorem cauchySignedNumerator_center (p : ℕ → ℕ) (n : ℕ) :
    (cauchySignedNumerator p n:ℝ)/(2:ℝ)^(n+1) =
      signedDigitCenter (fun k => (unitDyadicPoint (p (k+4))).val) n := by
  induction n with
  | zero => norm_num [cauchySignedNumerator,primitiveRec,signedDigitCenter]
  | succ n ih =>
    have hm := signedPartialNumerator_bounds (cauchySignedNameValid p) n
    change 1 ≤ signedPartialNumerator (cauchySignedName p) n ∧
      signedPartialNumerator (cauchySignedName p) n < 2^(n+1) at hm
    rw [← cauchySignedNumerator_eq_partial p n] at hm
    have hsub : 1 ≤ 2*cauchySignedNumerator p n+cauchyDigitCode p n (cauchySignedNumerator p n) := by omega
    change (((2*cauchySignedNumerator p n+cauchyDigitCode p n (cauchySignedNumerator p n)-1):ℕ):ℝ)/
      (2:ℝ)^(n+1+1) = _
    rw [Nat.cast_sub hsub]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,signedDigitCenter]
    rw [cauchyDigitCode_select _ _ _ hm.2.le,ih]
    simp only [signedDigitValue,one_div_pow]
    rw [← ih,show n+2=n+1+1 by omega,pow_succ]
    field_simp
    ring

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    To check the represented value, identify $\eta(n)=d_n-1$ and the center $c_n$ with those in
    §{sec:signed-digit-representation}. The displayed thresholds and the queried approximation $p(n+4)$ are
    exactly the recurrence proved there. Its invariant $\Abs{x-c_n}\le2^{-(n+1)}$ therefore gives
    $\rho_{\mathrm{sd}}(\psi(p))=x$. The $n$-th output uses only
    $p(4),\ldots,p(n+4)$ and finite rational arithmetic. The remaining task is to realize these numerical
    recurrences by closed lambda terms.
-/
theorem cauchySignedName_decode (p : ℕ → ℕ) :
    decodeSignedDigits (cauchySignedNameValid p) = cauchySignedDigits (fun i => (unitDyadicPoint i).val) p := by
  funext n
  apply Fin.ext
  have hm := (signedPartialNumerator_bounds (cauchySignedNameValid p) n).2.le
  change signedPartialNumerator (cauchySignedName p) n ≤ _ at hm
  rw [← cauchySignedNumerator_eq_partial] at hm
  change cauchyDigitCode p n (cauchySignedNumerator p n) = _
  rw [cauchyDigitCode_select _ _ _ hm,cauchySignedNumerator_center]
  rfl

def cauchySignedStepProgram : AlphaTerm := mapOutputProgram predecessorTerm
  (combineOutputProgram additionTerm
    (combineOutputProgram multiplicationTerm (constantProgram 2)
      (liftNumericalProgram (numericalProjectionTerm false))) cauchyDigitProgram)

theorem cauchySignedStepProgram_computes : UniformNumericalComputes cauchySignedStepProgram
    (fun p z => 2*z.unpair.2+cauchyDigitCode p z.unpair.1 z.unpair.2-1) := by
  have h := ((uniform_constant 2).combine (projection_computes false).uniform
    multiplicationTerm_closed (·*·) multiplicationTerm_apply).combine
    cauchyDigitProgram_computes additionTerm_closed (·+·) additionTerm_apply
  simpa only [cauchySignedStepProgram,ite_true,Bool.false_eq_true,ite_false] using h.map predecessor_computes

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Here are closed terms for these recurrences. Let $\LambdaTermName{signedBase}:= \lambdaab{o}{
    \ChurchNumeral{1}}$, and let $\LambdaTermName{signedStep}$ compute
    $\NatPair{m}{d}\mapsto2m+d-1$ when $m\ge1$. On the unused input $m=d=0$, let $\LambdaTermName{signedStep}$ return $0$.
    Multiplication, addition, and predecessor give such a total closed term. Let $\LambdaTermName{selectDigit}$ be
    the closed term that, on
    input $o,\ChurchNumeral{\NatPair{n}{m}}$, performs the rational comparisons defining $d_n$, using the center
    $\min(m,2^{n+1})/2^{n+1}$. It reads $o\ChurchNumeral{n+4}$, decodes the dyadic index, subtracts the center,
    and compares with $\pm2^{-(n+3)}$. The rational-code procedures in §{sec:lambda-rational-arithmetic} give
    $\LambdaTermName{selectDigit}$;
    the minimum is computed by comparing natural numbers and selecting the smaller one. Define
    $$\begin{aligned}
    \LambdaTermName{signedUpdate}&:= \lambdaab{o}{ \lambdaab{n}{ \lambdaab{m}{ \LambdaTermName{signedStep}(
    \LambdaNumericPair\,m\,(on))}}},\\
    \LambdaTermName{selectedUpdate}&:= \lambdaab{o}{ \lambdaab{n}{ \lambdaab{m}{ \LambdaTermName{signedStep}(
    \LambdaNumericPair\,m\,
    (\LambdaTermName{selectDigit}\,o\,(\LambdaNumericPair\,n\,m)))}}},\\
    \LambdaTermName{signedNumerator}&:= \LambdaParamRec{ \LambdaTermName{signedBase}}{
    \LambdaTermName{signedUpdate}}, \qquad \LambdaTermName{selectedNumerator}:= \LambdaParamRec{
    \LambdaTermName{signedBase}}{ \LambdaTermName{selectedUpdate}}.
    \end{aligned}$$
-/
def cauchySignedNumeratorProgram : AlphaTerm := nameRecursionProgram 1 cauchySignedStepProgram

theorem cauchySignedNumeratorProgram_computes : UniformNumericalComputes cauchySignedNumeratorProgram
    cauchySignedNumerator := by
  have h := cauchySignedStepProgram_computes.recursion 1
  refine ⟨h.1,fun p n => ?_⟩
  simpa only [cauchySignedNumeratorProgram,cauchySignedNumerator,Nat.unpair_pair] using h.2 p n

/-- Substitute the computed stage/state pair into the total selector, retaining the name. -/
def cauchySignedNameProgram : AlphaTerm :=
  relativeComposeProgram cauchyDigitProgram
    (pairOutputProgram (liftNumericalProgram numericalIdentity) cauchySignedNumeratorProgram)

theorem cauchySignedNameProgram_computes : UniformNumericalComputes cauchySignedNameProgram
    cauchySignedName := by
  have h := cauchyDigitProgram_computes.comp
    (numericalIdentity_computes.uniform.pair cauchySignedNumeratorProgram_computes)
  refine ⟨h.1,fun p n => ?_⟩
  simpa only [cauchySignedNameProgram,cauchySignedName,Nat.unpair_pair,id_eq] using h.2 p n

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    By recursion with an input name in §{sec:lambda-input-recursion}, $\LambdaTermName{signedNumerator}$ and
    $\LambdaTermName{selectedNumerator}$ compute the corresponding
    numerators $u_n(p)$ and $v_n(p)$, respectively. Thus, with the successor term $\LambdaSucc$, the required
    translators are
    $$\begin{aligned}
    \LambdaTermName{signedToCauchy}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaNumericPair\,(
    \LambdaTermName{signedNumerator}on)\,( \LambdaSucc\,n)}},\\
    \LambdaTermName{cauchyToSigned}&:= \lambdaab{o}{ \lambdaab{n}{ \LambdaTermName{selectDigit}\,o\,(
    \LambdaNumericPair\,n\,( \LambdaTermName{selectedNumerator}on))}}.
    \end{aligned}$$
    Every numerical subroutine terminates, and computing an output involves only finitely many recursion steps
    and queries. The displayed bounds on $v_n(p)$ ensure that the clamped center used by $\LambdaTermName{selectDigit}$
    equals $c_n$ throughout
    the recurrence. The value calculations above prove that these terms realize the identity in both directions.
-/
theorem dyadicCauchy_to_signedDigits_computable :
    HasComputableRealizer unitDyadicRepresentation signedDigitRepresentation id := by
  let F : cauchyNameDomain unitDyadicPoint → signedDigitNameDomain :=
    fun p => cauchySignedNameValid p.val
  refine ⟨F,⟨cauchySignedNameProgram,?_⟩,?_⟩
  · exact typeTwoComputes_iff_runs.mpr
      ⟨cauchySignedNameProgram_computes.1,fun p n => cauchySignedNameProgram_computes.2 p.val n⟩
  · intro p
    apply Subtype.ext
    change signedDigitExpansionValue (decodeSignedDigits (cauchySignedNameValid p.val)) =
      (cauchyRepresentation unitDyadicPoint p).val
    rw [cauchySignedName_decode]
    have hb : cauchyRepresentation (fun i => (unitDyadicPoint i).val)
        (intervalCauchyNameAsReal unitDyadicPoint p) ∈ Icc (0:ℝ) 1 := by
      rw [intervalCauchyNameAsReal_value]
      exact (cauchyRepresentation unitDyadicPoint p).property
    exact (cauchySignedDigits_value _ (intervalCauchyNameAsReal unitDyadicPoint p) hb).trans
      (intervalCauchyNameAsReal_value unitDyadicPoint p)

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Computable signed-digit equivalence
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Signed digits avoid this obstruction. Encode the signed digits $-1,0,1$ by $0,1,2$, respectively,
    and use the same dyadic enumeration $\nu$.
-/
theorem signedDigit_computable_equivalence :
    HasComputableRealizer signedDigitRepresentation unitDyadicRepresentation id ∧
    HasComputableRealizer unitDyadicRepresentation signedDigitRepresentation id :=
  ⟨signedDigits_to_dyadicCauchy_computable,dyadicCauchy_to_signedDigits_computable⟩

end PolishSpaceBook
