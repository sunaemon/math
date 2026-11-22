module

public import PolishSpaceBook.LambdaSignedDigitSums

@[expose] public section

/-! # Binary partial-sum programs and the shared topological obstruction -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA Set Filter Topology

def binaryNameDomain : Set baire_space := {p | ∀ n, p n < 2}

def encodeBinaryDigits (a : cantor_space) : binaryNameDomain :=
  ⟨fun n => if a n then 1 else 0,fun n => by dsimp; split_ifs <;> norm_num⟩

def decodeBinaryDigits (p : binaryNameDomain) : cantor_space := fun n => p.val n == 1

theorem decode_encodeBinaryDigits (a : cantor_space) :
    decodeBinaryDigits (encodeBinaryDigits a) = a := by
  funext n
  cases h : a n <;> simp [decodeBinaryDigits,encodeBinaryDigits,h]

theorem decodeBinaryDigits_value (p : binaryNameDomain) (n : ℕ) :
    (if decodeBinaryDigits p n then (1:ℝ) else 0) = (p.val n:ℝ) := by
  have hp := p.property n
  have hc : p.val n = 0 ∨ p.val n = 1 := by omega
  rcases hc with h | h <;> simp [decodeBinaryDigits,h]

noncomputable def binaryRepresentation : Representation unitInterval where
  domain := binaryNameDomain
  toFun p := ⟨binaryExpansionValue (decodeBinaryDigits p),binaryExpansionValue_bounds _⟩
  surjective := by
    intro x
    refine ⟨encodeBinaryDigits (binaryGreedyDigits x.val),?_⟩
    apply Subtype.ext
    change binaryExpansionValue (decodeBinaryDigits (encodeBinaryDigits (binaryGreedyDigits x.val))) = x.val
    rw [decode_encodeBinaryDigits]
    exact binaryExpansionValue_greedy x.property

def binaryPartialNumerator (p : ℕ → ℕ) : ℕ → ℕ := primitiveRec 0 (fun n m => 2*m+p n)

theorem continuous_decodeBinaryDigits : Continuous decodeBinaryDigits :=
  continuous_pi fun n =>
    (continuous_of_discreteTopology (f := fun k : ℕ => k == 1)).comp
      ((continuous_apply n).comp continuous_subtype_val)

theorem binaryRepresentation_isContinuous : binaryRepresentation.IsContinuous :=
  (continuous_binaryExpansionValue.comp continuous_decodeBinaryDigits).subtype_mk _

/-- The first-digit obstruction applies to the Baire-coded representation
objects, with interval values and inherited real values explicitly identified. -/
theorem cauchy_not_continuouslyReduces_binary (q : ℕ → unitInterval) (hq : DenseRange q)
    (hdyadic : EnumeratesUnitDyadics (fun n => (q n).val)) :
    ¬ ContinuouslyReduces (cauchyRepresentationObject q hq) binaryRepresentation := by
  rintro ⟨F, hF, hcomm⟩
  let lift : cauchyNameDomain (fun n => (q n).val) → cauchyNameDomain q :=
    fun p => ⟨p.val, p.property⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  apply no_continuous_binaryExpansion_translator _ hdyadic
  refine ⟨fun p => decodeBinaryDigits (F (lift p)),
    continuous_decodeBinaryDigits.comp (hF.comp hlift), ?_⟩
  intro p
  change binaryExpansionValue (decodeBinaryDigits (F (lift p))) =
    cauchyRepresentation _ (intervalCauchyNameAsReal q (lift p))
  rw [intervalCauchyNameAsReal_value]
  exact congrArg Subtype.val (hcomm (lift p))

theorem binaryRepresentation_not_admissible : ¬ binaryRepresentation.IsAdmissible := by
  intro h
  apply cauchy_not_continuouslyReduces_binary unitDyadicPoint unitDyadicPoint_dense
    unitDyadicPoint_enumerates
  exact h.2 _ (cauchyRepresentationObject_isAdmissible unitDyadicPoint unitDyadicPoint_dense).1

theorem binaryRepresentation_not_equivalent_cauchy (q : ℕ → unitInterval) (hq : DenseRange q) :
    ¬ ContinuouslyEquivalent binaryRepresentation (cauchyRepresentationObject q hq) := by
  intro h
  exact binaryRepresentation_not_admissible
    (admissible_of_continuouslyEquivalent (cauchyRepresentationObject_isAdmissible q hq) h)

/-@ booklink:
  source: polish-space-book/cauchy-names-polish-representations.md
  target: prose
  excerpt: |
    **The converse fails.** $\rho_{[0,1]} \NotContinuouslyReducesTo \rho_{\mathrm{bin}}$, so $\rho_{\mathrm{bin}}$ is not
    admissible. By the \termuseas{Kreitz--Weihrauch admissibility theorem}{Kreitz–Weihrauch theorem}, this is equivalent to
    $\rho_{[0,1]} \NotContinuouslyEquivalentTo \rho_{\mathrm{bin}}$. The obstruction sits at the dyadic rationals. Suppose
    a continuous $f : \DomainOf{\rho_{[0,1]}} \to \CantorSpace$ satisfied
    $\rho_{\mathrm{bin}} \circ f = \rho_{[0,1]}$. Any Cauchy name $p$ of
    a point in $(1/2, 1]$ would force the leading binary digit $f(p)(0) = 1$, and any Cauchy name of a point in $[0, 1/2)$
    would force the leading binary digit $f(p)(0) = 0$.
-/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    The \termuse{signed-digit representation} from §{sec:signed-digit-representation} illustrates why admissibility
    matters. The \termuse{binary expansion} is a representation of $[0,1]$, but it is not admissible because dyadic
    rationals force discontinuous choices of tails. Signed digits add redundancy, making enough room for continuous choices
    and restoring equivalence with the Cauchy representation.
-/
theorem binaryRepresentation_comparison (q : ℕ → unitInterval) (hq : DenseRange q)
    (hdyadic : EnumeratesUnitDyadics (fun n => (q n).val)) :
    ¬ ContinuouslyReduces (cauchyRepresentationObject q hq) binaryRepresentation ∧
      ¬ binaryRepresentation.IsAdmissible ∧
      ¬ ContinuouslyEquivalent (cauchyRepresentationObject q hq) binaryRepresentation :=
  ⟨cauchy_not_continuouslyReduces_binary q hq hdyadic, binaryRepresentation_not_admissible,
    fun h => binaryRepresentation_not_equivalent_cauchy q hq ⟨h.2, h.1⟩⟩

theorem binaryPartialNumerator_bounds (p : binaryNameDomain) (n : ℕ) :
    binaryPartialNumerator p.val n < 2^n := by
  induction n with
  | zero => norm_num [binaryPartialNumerator,primitiveRec]
  | succ n ih =>
    change 2*binaryPartialNumerator p.val n+p.val n < 2^(n+1)
    rw [pow_succ]
    have hp := p.property n
    omega

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    Given a binary name $p$, define the numerator of its finite binary expansion by
    $$t_0:=0,\qquad t_{n+1}:=2t_n+p(n),\qquad \beta(p)(n):=\NatPair{t_n}{n}.$$
    Induction gives $t_n<2^n$ and
    $$\nu_{\beta(p)(n)}=\frac{t_n}{2^n}=\sum_{k<n}p(k)2^{-(k+1)}.$$
    The tail estimate in §{sec:binary-expansion-example} shows that these partial sums form a fast Cauchy name
    of $\rho_{\mathrm{bin}}(p)$. Only the first $n$ input digits are needed for the $n$-th output coordinate.
-/
theorem binaryPartialNumerator_value (p : binaryNameDomain) (n : ℕ) :
    (binaryPartialNumerator p.val n:ℝ)/(2:ℝ)^n = binaryPartialSum (decodeBinaryDigits p) n := by
  induction n with
  | zero => norm_num [binaryPartialNumerator,primitiveRec,binaryPartialSum]
  | succ n ih =>
    have hs : binaryPartialSum (decodeBinaryDigits p) (n+1) =
        binaryPartialSum (decodeBinaryDigits p) n + (p.val n:ℝ)*(1/2:ℝ)^(n+1) := by
      simp only [binaryPartialSum,Finset.sum_range_succ,decodeBinaryDigits_value]
    change ((2*binaryPartialNumerator p.val n+p.val n:ℕ):ℝ)/(2:ℝ)^(n+1) = _
    rw [hs,← ih]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,pow_succ,one_div_pow]
    field_simp

def binaryPartialName (p : ℕ → ℕ) (n : ℕ) : ℕ := Nat.pair (binaryPartialNumerator p n) n

theorem binaryPartialName_value (p : binaryNameDomain) (n : ℕ) :
    (unitDyadicPoint (binaryPartialName p.val n)).val = binaryPartialSum (decodeBinaryDigits p) n := by
  rw [binaryPartialName,unitDyadicPoint_pair _ _ (binaryPartialNumerator_bounds p n).le,
    binaryPartialNumerator_value]

theorem binaryPartialName_isCauchy (p : binaryNameDomain) :
    IsCauchyName unitDyadicPoint (binaryPartialName p.val) := by
  intro n m hnm
  change dist (unitDyadicPoint (binaryPartialName p.val n)).val
    (unitDyadicPoint (binaryPartialName p.val m)).val ≤ _
  rw [binaryPartialName_value,binaryPartialName_value]
  exact binaryPartialSum_dist_le _ hnm

theorem binaryPartialName_limit (p : binaryNameDomain) :
    cauchyRepresentation unitDyadicPoint ⟨binaryPartialName p.val,binaryPartialName_isCauchy p⟩ =
      binaryRepresentation.toFun p := by
  apply Subtype.ext
  have h := (continuous_subtype_val.tendsto _).comp (tendsto_cauchyRepresentation unitDyadicPoint
    ⟨binaryPartialName p.val,binaryPartialName_isCauchy p⟩)
  simp only [Function.comp_def,binaryPartialName_value] at h
  exact tendsto_nhds_unique h (summable_binaryTerms (decodeBinaryDigits p)).hasSum.tendsto_sum_nat

def binaryPartialStepProgram : AlphaTerm :=
  combineOutputProgram additionTerm
    (combineOutputProgram multiplicationTerm (constantProgram 2)
      (liftNumericalProgram (numericalProjectionTerm false)))
    (queryOutputProgram (liftNumericalProgram (numericalProjectionTerm true)))

theorem binaryPartialStepProgram_computes : UniformNumericalComputes binaryPartialStepProgram
    (fun p z => 2*z.unpair.2+p z.unpair.1) := by
  have h := ((uniform_constant 2).combine (projection_computes false).uniform
    multiplicationTerm_closed (·*·) multiplicationTerm_apply).combine
      (projection_computes true).uniform.query additionTerm_closed (·+·) additionTerm_apply
  simpa only [binaryPartialStepProgram,ite_true,Bool.false_eq_true,ite_false] using h

def binaryPartialNumeratorProgram : AlphaTerm := nameRecursionProgram 0 binaryPartialStepProgram

theorem binaryPartialNumeratorProgram_computes : UniformNumericalComputes binaryPartialNumeratorProgram
    binaryPartialNumerator := by
  have h := binaryPartialStepProgram_computes.recursion 0
  refine ⟨h.1,fun p n => ?_⟩
  simpa only [binaryPartialNumeratorProgram,binaryPartialNumerator,Nat.unpair_pair] using h.2 p n

def binaryPartialNameProgram : AlphaTerm := pairOutputProgram binaryPartialNumeratorProgram
  (liftNumericalProgram numericalIdentity)

theorem binaryPartialNameProgram_computes : UniformNumericalComputes binaryPartialNameProgram binaryPartialName :=
  binaryPartialNumeratorProgram_computes.pair numericalIdentity_computes.uniform

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    For an explicit realizer, let $\LambdaTermName{binaryStep}$ be a closed numerical term computing
    $\NatPair{m}{d}\mapsto2m+d$, obtained from multiplication, addition, and numerical projections. Set
    $$\begin{aligned}
    \LambdaTermName{binaryBase}&:=\lambdaab{o}{\ChurchNumeral{0}},\\
    \LambdaTermName{binaryUpdate}&:= \lambdaab{o}{ \lambdaab{n}{ \lambdaab{m}{ \LambdaTermName{binaryStep}(
    \LambdaNumericPair\,m\,(on))}}},\\
    \LambdaTermName{binaryNumerator}&:=\LambdaParamRec{\LambdaTermName{binaryBase}}{\LambdaTermName{binaryUpdate}},\qquad
    \LambdaTermName{binaryToCauchy}:= \lambdaab{o}{ \lambdaab{n}{ \LambdaNumericPair\,(
    \LambdaTermName{binaryNumerator}on)\,n}}.
    \end{aligned}$$
    Recursion with an input name from §{sec:lambda-input-recursion} gives the numeral for $t_n$ from
    $\LambdaTermName{binaryNumerator}o \ChurchNumeral{n}$, after finitely many beta steps and queries. Pairing it
    with $n$ shows that $\LambdaTermName{binaryToCauchy}$
    realizes $\beta$. These terms are closed independently of the input name.
-/
theorem binary_to_dyadicCauchy_computable :
    HasComputableRealizer binaryRepresentation unitDyadicRepresentation id := by
  let F : binaryNameDomain → cauchyNameDomain unitDyadicPoint :=
    fun p => ⟨binaryPartialName p.val,binaryPartialName_isCauchy p⟩
  refine ⟨F,⟨binaryPartialNameProgram,?_⟩,fun p => binaryPartialName_limit p⟩
  exact typeTwoComputes_iff_runs.mpr
    ⟨binaryPartialNameProgram_computes.1,fun p n => binaryPartialNameProgram_computes.2 p.val n⟩

/-- Leading digits on opposite sides of the boundary must differ. -/
theorem binary_leading_digit (p : binaryNameDomain) :
    (binaryExpansionValue (decodeBinaryDigits p) < 1/2 → p.val 0 = 0) ∧
    (1/2 < binaryExpansionValue (decodeBinaryDigits p) → p.val 0 = 1) := by
  have ht := binaryExpansionValue_tail (decodeBinaryDigits p)
  rw [decodeBinaryDigits_value] at ht
  have hb := binaryExpansionValue_bounds (fun n => decodeBinaryDigits p (n+1))
  have hp := p.property 0
  have hc : p.val 0 = 0 ∨ p.val 0 = 1 := by omega
  constructor
  · intro h
    rcases hc with h0 | h1
    · exact h0
    · rw [h1] at ht
      norm_num at ht
      linarith
  · intro h
    rcases hc with h0 | h1
    · rw [h0] at ht
      norm_num at ht
      linarith
    · exact h1

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    For the reverse direction, §{sec:binary-expansion-example} proves that no continuous translator from Cauchy
    names to binary names exists for any enumeration of the unit dyadics. The explicit enumeration $\nu$ satisfies
    that hypothesis. A computable translator would be continuous by §{sec:type-two-lambda-continuity}, contradicting
    that result. Thus the obstruction already proved there rules out a uniform computable translator as well.
-/
theorem no_dyadicCauchy_to_binary_computable :
    ¬ HasComputableRealizer unitDyadicRepresentation binaryRepresentation id := by
  rintro ⟨F, ⟨P, hP⟩, hF⟩
  let lift : cauchyNameDomain (fun i => (unitDyadicPoint i).val) →
      cauchyNameDomain unitDyadicPoint := fun p => ⟨p.val, p.property⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  have hdecode : Continuous (fun p : cauchyNameDomain unitDyadicPoint => decodeBinaryDigits (F p)) := by
    apply continuous_pi
    intro n
    exact (continuous_of_discreteTopology (f := fun k : ℕ => k == 1)).comp
      ((continuous_apply n).comp hP.continuous)
  apply no_continuous_binaryExpansion_translator _ unitDyadicPoint_enumerates
  refine ⟨fun p => decodeBinaryDigits (F (lift p)), hdecode.comp hlift, ?_⟩
  intro p
  change binaryExpansionValue (decodeBinaryDigits (F (lift p))) =
    cauchyRepresentation _ (intervalCauchyNameAsReal unitDyadicPoint (lift p))
  rw [intervalCauchyNameAsReal_value]
  exact congrArg Subtype.val (hF (lift p))

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: statement
  kind: theorem
  title: Computable binary-to-Cauchy translation
-/
theorem binary_Cauchy_computable_asymmetry :
    HasComputableRealizer binaryRepresentation unitDyadicRepresentation id ∧
    ¬ HasComputableRealizer unitDyadicRepresentation binaryRepresentation id :=
  ⟨binary_to_dyadicCauchy_computable,no_dyadicCauchy_to_binary_computable⟩

end PolishSpaceBook
