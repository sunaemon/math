module

public import PolishSpaceBook.LambdaNameRecursion
public import PolishSpaceBook.SignedDigitRepresentations
public import PolishSpaceBook.LambdaRealRepresentation

@[expose] public section

/-! # Dyadic indices for signed-digit partial sums, computed by lambda terms -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA Set Filter Topology

/-- Every index decodes to a dyadic in the closed unit interval. -/
noncomputable def unitDyadicPoint (i : ℕ) : unitInterval :=
  ⟨(min i.unpair.1 (2^i.unpair.2) : ℕ) / (2:ℝ)^i.unpair.2,by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      exact_mod_cast min_le_right i.unpair.1 (2^i.unpair.2)⟩

theorem unitDyadicPoint_pair (m n : ℕ) (hm : m ≤ 2^n) :
    (unitDyadicPoint (Nat.pair m n)).val = (m:ℝ)/(2:ℝ)^n := by
  simp only [unitDyadicPoint,Nat.unpair_pair,min_eq_left hm]

theorem unitDyadicPoint_enumerates : EnumeratesUnitDyadics (fun i => (unitDyadicPoint i).val) :=
  fun m n hm => ⟨Nat.pair m n,unitDyadicPoint_pair m n hm⟩

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    Fix the following explicit enumeration of the dyadic points:
    $$\nu_{\NatPair{a}{b}}:=\frac{\min(a,2^b)}{2^b}\qquad a,b\in\NN.$$
    Every index names a point of $\ClosedInterval{0}{1}$, and every dyadic point of that interval occurs. The sequence is
    dense:
    the signed-digit partial sums in §{sec:signed-digit-representation} are dyadic and converge to every point.
    Let $\rho_\nu$ be its fast Cauchy representation. We regard a binary name as a Baire-space name whose entries
    all belong to $\{0,1\}$, with the same binary-expansion value as in §{sec:binary-expansion-example}.
-/
theorem unitDyadicPoint_dense : DenseRange unitDyadicPoint := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  have hx : x.val ∈ range signedDigitExpansionValue := by
    rw [range_signedDigitExpansionValue]; exact x.property
  obtain ⟨a,ha⟩ := hx
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2:ℝ)<1)
  obtain ⟨m,_,hm,hs⟩ := signedDigitPartialSum_dyadic a N
  refine ⟨Nat.pair m (N+1),?_⟩
  change dist x.val (unitDyadicPoint (Nat.pair m (N+1))).val < ε
  rw [unitDyadicPoint_pair m (N+1) hm.le,← hs,← ha,dist_comm]
  exact (signedDigitPartialSum_tail_bound a N).trans_lt
    ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ N)).trans_lt hN)

noncomputable def unitDyadicRepresentation : Representation unitInterval :=
  cauchyRepresentationObject unitDyadicPoint unitDyadicPoint_dense

/-- The numerator of the N-term partial sum has denominator 2^(N+1). -/
def signedPartialNumerator (p : ℕ → ℕ) : ℕ → ℕ :=
  primitiveRec 1 (fun n m => 2*m+p n-1)

theorem signedPartialNumerator_bounds (p : signedDigitNameDomain) (n : ℕ) :
    1 ≤ signedPartialNumerator p.val n ∧ signedPartialNumerator p.val n < 2^(n+1) := by
  induction n with
  | zero => norm_num [signedPartialNumerator,primitiveRec]
  | succ n ih =>
    change 1 ≤ 2*signedPartialNumerator p.val n+p.val n-1 ∧
      2*signedPartialNumerator p.val n+p.val n-1 < 2^(n+1+1)
    rw [pow_succ]
    have hp := p.property n
    omega

/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: proof
  excerpt: |
    For a coded signed-digit name $p$, set
    $$u_0(p):=1,\qquad u_{n+1}(p):=2u_n(p)+p(n)-1,\qquad \varphi(p)(n):=\NatPair{u_n(p)}{n+1}.$$
    Induction gives $1\le u_n(p)<2^{n+1}$, so every subtraction displayed here has a nonnegative result. Moreover,
    $$\nu_{\varphi(p)(n)}=\frac{u_n(p)}{2^{n+1}}
    =\frac12+\sum_{k<n}(p(k)-1)2^{-(k+2)}.$$
    These are exactly the signed-digit partial sums of §{sec:signed-digit-representation}, with digit
    $\zeta(k)=p(k)-1$. The tail estimate proved there makes $\varphi(p)$ a fast Cauchy name of $\rho_{\mathrm{sd}}(p)$.
    Its $n$-th coordinate uses only $p(0),\ldots,p(n-1)$.
-/
theorem signedPartialNumerator_value (p : signedDigitNameDomain) (n : ℕ) :
    (signedPartialNumerator p.val n:ℝ)/(2:ℝ)^(n+1) =
      signedDigitPartialSum (decodeSignedDigits p) n := by
  induction n with
  | zero => norm_num [signedPartialNumerator,primitiveRec,signedDigitPartialSum]
  | succ n ih =>
    have hm := (signedPartialNumerator_bounds p n).1
    have hsub : 1 ≤ 2*signedPartialNumerator p.val n+p.val n := by omega
    change ((2*signedPartialNumerator p.val n+p.val n-1:ℕ):ℝ)/(2:ℝ)^(n+1+1) = _
    rw [Nat.cast_sub hsub]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    have hs : signedDigitPartialSum (decodeSignedDigits p) (n+1) =
        signedDigitPartialSum (decodeSignedDigits p) n +
          ((p.val n:ℝ)-1)*(1/2:ℝ)^(n+2) := by
      simp only [signedDigitPartialSum,Finset.sum_range_succ,decodeSignedDigits,signedDigitValue]
      ring
    rw [hs,← ih,show n+2=n+1+1 by omega,pow_succ,one_div_pow]
    field_simp
    ring

def signedPartialName (p : ℕ → ℕ) (n : ℕ) : ℕ := Nat.pair (signedPartialNumerator p n) (n+1)

theorem signedPartialName_value (p : signedDigitNameDomain) (n : ℕ) :
    (unitDyadicPoint (signedPartialName p.val n)).val = signedDigitPartialSum (decodeSignedDigits p) n := by
  rw [signedPartialName,unitDyadicPoint_pair _ _ (signedPartialNumerator_bounds p n).2.le,
    signedPartialNumerator_value]

theorem signedPartialName_isCauchy (p : signedDigitNameDomain) :
    IsCauchyName unitDyadicPoint (signedPartialName p.val) := by
  intro n m hnm
  change dist (unitDyadicPoint (signedPartialName p.val n)).val
    (unitDyadicPoint (signedPartialName p.val m)).val ≤ _
  rw [signedPartialName_value,signedPartialName_value]
  exact signedDigitPartialSum_dist_le _ hnm

theorem signedPartialName_limit (p : signedDigitNameDomain) :
    cauchyRepresentation unitDyadicPoint ⟨signedPartialName p.val,signedPartialName_isCauchy p⟩ =
      signedDigitRepresentation.toFun p := by
  apply Subtype.ext
  have h := (continuous_subtype_val.tendsto _).comp (tendsto_cauchyRepresentation unitDyadicPoint
    ⟨signedPartialName p.val,signedPartialName_isCauchy p⟩)
  simp only [Function.comp_def,signedPartialName_value] at h
  exact tendsto_nhds_unique h (tendsto_signedDigitPartialSum _)

def signedPartialStepProgram : AlphaTerm := mapOutputProgram predecessorTerm
  (combineOutputProgram additionTerm
    (combineOutputProgram multiplicationTerm (constantProgram 2)
      (liftNumericalProgram (numericalProjectionTerm false)))
    (queryOutputProgram (liftNumericalProgram (numericalProjectionTerm true))))

theorem signedPartialStepProgram_computes : UniformNumericalComputes signedPartialStepProgram
    (fun p z => 2*z.unpair.2+p z.unpair.1-1) := by
  have h := ((uniform_constant 2).combine (projection_computes false).uniform
    multiplicationTerm_closed (·*·) multiplicationTerm_apply).combine
      (projection_computes true).uniform.query additionTerm_closed (·+·) additionTerm_apply
  simpa only [signedPartialStepProgram,ite_true,Bool.false_eq_true,ite_false] using h.map predecessor_computes

def signedPartialNumeratorProgram : AlphaTerm := nameRecursionProgram 1 signedPartialStepProgram

theorem signedPartialNumeratorProgram_computes : UniformNumericalComputes signedPartialNumeratorProgram
    signedPartialNumerator := by
  have h := signedPartialStepProgram_computes.recursion 1
  refine ⟨h.1,fun p n => ?_⟩
  simpa only [signedPartialNumeratorProgram,signedPartialNumerator,Nat.unpair_pair] using h.2 p n

def signedPartialNameProgram : AlphaTerm := pairOutputProgram signedPartialNumeratorProgram
  (liftNumericalProgram successorTerm)

theorem signedPartialNameProgram_computes : UniformNumericalComputes signedPartialNameProgram signedPartialName :=
  signedPartialNumeratorProgram_computes.pair successor_computes.uniform

theorem signedDigits_to_dyadicCauchy_computable :
    HasComputableRealizer signedDigitRepresentation unitDyadicRepresentation id := by
  let F : signedDigitNameDomain → cauchyNameDomain unitDyadicPoint :=
    fun p => ⟨signedPartialName p.val,signedPartialName_isCauchy p⟩
  refine ⟨F,⟨signedPartialNameProgram,?_⟩,fun p => signedPartialName_limit p⟩
  exact typeTwoComputes_iff_runs.mpr
    ⟨signedPartialNameProgram_computes.1,fun p n => signedPartialNameProgram_computes.2 p.val n⟩

end PolishSpaceBook
