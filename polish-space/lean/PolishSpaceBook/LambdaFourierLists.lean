module

public import PolishSpaceBook.LambdaFourierCoefficients
public import PolishSpaceBook.LambdaListTabulation
public import PolishSpaceBook.LambdaPolynomialIntegration

@[expose] public section

/-! # Finite lists of approximating Fourier coefficients

A step-function row is (left endpoint,(right endpoint,complex weight)).
The inner recursion adds weighted interval coefficients, retaining the row list,
precision and degree; the outer tabulation lists the degrees in increasing order.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA
set_option maxRecDepth 4096

def rationalAddCode (a b : ℕ) : ℕ :=
  (RationalCode.add (RationalCode.ofNat a) (RationalCode.ofNat b)).natCode

theorem rationalAddCode_value (a b : ℕ) :
    rationalPoint (rationalAddCode a b) = rationalPoint a + rationalPoint b := by
  simp [rationalAddCode,rationalPoint,RationalCode.value_add]

def complexAddCode (a b : ℕ) : ℕ :=
  Nat.pair (rationalAddCode a.unpair.1 b.unpair.1) (rationalAddCode a.unpair.2 b.unpair.2)

def complexMultiplyCode (a b : ℕ) : ℕ :=
  Nat.pair (rationalSubtractCode (rationalMultiplyCode a.unpair.1 b.unpair.1)
    (rationalMultiplyCode a.unpair.2 b.unpair.2))
    (rationalAddCode (rationalMultiplyCode a.unpair.1 b.unpair.2)
      (rationalMultiplyCode a.unpair.2 b.unpair.1))

@[simp] theorem complexRationalPoint_zero : complexRationalPoint 0 = 0 := by
  norm_num [complexRationalPoint,rationalPoint,RationalCode.ofNat,RationalCode.value]

theorem complexAddCode_value (a b : ℕ) :
    complexRationalPoint (complexAddCode a b) = complexRationalPoint a + complexRationalPoint b := by
  simp only [complexAddCode,complexRationalPoint,Nat.unpair_pair,rationalAddCode_value,Complex.ofReal_add]
  ring

theorem complexMultiplyCode_value (a b : ℕ) :
    complexRationalPoint (complexMultiplyCode a b) = complexRationalPoint a * complexRationalPoint b := by
  simp only [complexMultiplyCode,complexRationalPoint,Nat.unpair_pair,rationalAddCode_value,
    rationalSubtractCode_value,rationalMultiplyCode_value,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul]
  linear_combination (-(rationalPoint a.unpair.2:ℂ)*(rationalPoint b.unpair.2:ℂ))*Complex.I_sq

def complexAddProgram : AlphaTerm :=
  pairNumerical (numericalCompose rationalAddTerm (pairNumerical
    (onComponent (numericalProjectionTerm true) true) (onComponent (numericalProjectionTerm true) false)))
    (numericalCompose rationalAddTerm (pairNumerical
      (onComponent (numericalProjectionTerm false) true) (onComponent (numericalProjectionTerm false) false)))

theorem complexAddProgram_computes : NumericalComputes complexAddProgram
    (fun p => complexAddCode p.unpair.1 p.unpair.2) := by
  have h := (rationalAdd_computes.comp (((projection_computes true).onComponent true).pair
    ((projection_computes true).onComponent false))).pair
    (rationalAdd_computes.comp (((projection_computes false).onComponent true).pair
      ((projection_computes false).onComponent false)))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [complexAddProgram,complexAddCode,rationalAddCode,Nat.unpair_pair,
    ite_true,Bool.false_eq_true,ite_false] using h.2 p

def complexMultiplyProgram : AlphaTerm :=
  let ar := onComponent (numericalProjectionTerm true) true
  let ai := onComponent (numericalProjectionTerm false) true
  let br := onComponent (numericalProjectionTerm true) false
  let bi := onComponent (numericalProjectionTerm false) false
  let mul := fun x y => numericalCompose rationalMultiplyProgram (pairNumerical x y)
  pairNumerical (numericalCompose rationalSubtractProgram (pairNumerical (mul ar br) (mul ai bi)))
    (numericalCompose rationalAddTerm (pairNumerical (mul ar bi) (mul ai br)))

theorem complexMultiplyProgram_computes : NumericalComputes complexMultiplyProgram
    (fun p => complexMultiplyCode p.unpair.1 p.unpair.2) := by
  have ar := (projection_computes true).onComponent true
  have ai := (projection_computes false).onComponent true
  have br := (projection_computes true).onComponent false
  have bi := (projection_computes false).onComponent false
  have h := (rationalSubtractProgram_computes.comp
    ((rationalMultiplyProgram_computes.comp (ar.pair br)).pair
      (rationalMultiplyProgram_computes.comp (ai.pair bi)))).pair
    (rationalAdd_computes.comp ((rationalMultiplyProgram_computes.comp (ar.pair bi)).pair
      (rationalMultiplyProgram_computes.comp (ai.pair br))))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [complexMultiplyProgram,complexMultiplyCode,rationalAddCode,Nat.unpair_pair,
    ite_true,Bool.false_eq_true,ite_false] using h.2 p

/-- Sum the first n complex codes supplied by f, retaining parameter x. -/
def complexSumCode (f : ℕ → ℕ) (x : ℕ) : ℕ → ℕ :=
  primitiveRec 0 (fun i r => complexAddCode r (f (Nat.pair x i)))

def complexSumProgram (F : AlphaTerm) : AlphaTerm := numericalRecursion (numericalConstant 0)
  (numericalCompose complexAddProgram (pairNumerical piState
    (numericalCompose F (pairNumerical (numericalProjectionTerm true)
      (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))))))

theorem complexSumProgram_computes {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) :
    NumericalComputes (complexSumProgram F) (fun p => complexSumCode f p.unpair.1 p.unpair.2) := by
  have h := numericalRecursion_computes (numericalConstant_computes 0)
    (complexAddProgram_computes.comp (piState_computes.pair
      (hF.comp ((projection_computes true).pair
        ((projection_computes true).comp (projection_computes false))))))
  simpa only [complexSumProgram,complexSumCode,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using h

theorem complexSumCode_value (f : ℕ → ℕ) (x n : ℕ) :
    complexRationalPoint (complexSumCode f x n) =
      ∑ i ∈ Finset.range n, complexRationalPoint (f (Nat.pair x i)) := by
  induction n with
  | zero => simp [complexSumCode,primitiveRec]
  | succ n ih =>
    change complexRationalPoint (complexAddCode (complexSumCode f x n) (f (Nat.pair x n))) = _
    rw [complexAddCode_value,ih,Finset.sum_range_succ]

/-- The row at position i is a paired triple (a,(b,v)). -/
def stepRow (s i : ℕ) : ℕ := (NatListCode.decode s).getD i 0

def weightedIntervalCoefficient (s m j i : ℕ) : ℕ :=
  let row := stepRow s i
  complexMultiplyCode row.unpair.2.unpair.2
    (approximatedIntervalCoefficient row.unpair.1 row.unpair.2.unpair.1 j m)

/-- Input (((row-list,precision),degree),row-index). -/
def weightedIntervalCoefficientProgram : AlphaTerm :=
  let P := numericalProjectionTerm true
  let I := numericalProjectionTerm false
  let SM := numericalCompose (numericalProjectionTerm true) P
  let S := numericalCompose (numericalProjectionTerm true) SM
  let M := numericalCompose (numericalProjectionTerm false) SM
  let J := numericalCompose (numericalProjectionTerm false) P
  let row := numericalCompose listGetTerm (pairNumerical S I)
  let A := numericalCompose (numericalProjectionTerm true) row
  let tail := numericalCompose (numericalProjectionTerm false) row
  let B := numericalCompose (numericalProjectionTerm true) tail
  let V := numericalCompose (numericalProjectionTerm false) tail
  numericalCompose complexMultiplyProgram (pairNumerical V
    (numericalCompose approximatedIntervalCoefficientProgram (pairNumerical A (pairNumerical B (pairNumerical J M)))))

theorem weightedIntervalCoefficientProgram_computes : NumericalComputes weightedIntervalCoefficientProgram
    (fun p => weightedIntervalCoefficient p.unpair.1.unpair.1.unpair.1 p.unpair.1.unpair.1.unpair.2
      p.unpair.1.unpair.2 p.unpair.2) := by
  have hp := projection_computes true
  have hi := projection_computes false
  have hsm := (projection_computes true).comp hp
  have hs := (projection_computes true).comp hsm
  have hm := (projection_computes false).comp hsm
  have hj := (projection_computes false).comp hp
  have hrow := listGet_computes.comp (hs.pair hi)
  have ha := (projection_computes true).comp hrow
  have ht := (projection_computes false).comp hrow
  have hb := (projection_computes true).comp ht
  have hv := (projection_computes false).comp ht
  have h := complexMultiplyProgram_computes.comp (hv.pair
    (approximatedIntervalCoefficientProgram_computes.comp (ha.pair (hb.pair (hj.pair hm)))))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [weightedIntervalCoefficientProgram,weightedIntervalCoefficient,stepRow,Nat.unpair_pair,
    ite_true,Bool.false_eq_true,ite_false] using h.2 p

def stepCoefficientCode (s m j : ℕ) : ℕ :=
  complexSumCode (fun p => weightedIntervalCoefficient p.unpair.1.unpair.1.unpair.1
    p.unpair.1.unpair.1.unpair.2 p.unpair.1.unpair.2 p.unpair.2)
      (Nat.pair (Nat.pair s m) j) (NatListCode.decode s).length

/-- Input ((row-list,precision),degree); sum all rows, including an empty list. -/
def stepCoefficientProgram : AlphaTerm := numericalCompose
  (complexSumProgram weightedIntervalCoefficientProgram)
  (pairNumerical numericalIdentity (numericalCompose listLengthTerm
    (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true))))

theorem stepCoefficientProgram_computes : NumericalComputes stepCoefficientProgram
    (fun p => stepCoefficientCode p.unpair.1.unpair.1 p.unpair.1.unpair.2 p.unpair.2) := by
  have h := (complexSumProgram_computes weightedIntervalCoefficientProgram_computes).comp
    (numericalIdentity_computes.pair (listLength_computes.comp
      ((projection_computes true).comp (projection_computes true))))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [stepCoefficientProgram,stepCoefficientCode,Nat.unpair_pair,id_eq,
    ite_true,Bool.false_eq_true,ite_false,Nat.pair_unpair] using h.2 p

theorem stepCoefficientCode_value (s m j : ℕ) :
    complexRationalPoint (stepCoefficientCode s m j) =
      ∑ i ∈ Finset.range (NatListCode.decode s).length,
        complexRationalPoint (stepRow s i).unpair.2.unpair.2 *
          complexRationalPoint (approximatedIntervalCoefficient (stepRow s i).unpair.1
            (stepRow s i).unpair.2.unpair.1 j m) := by
  simp only [stepCoefficientCode,complexSumCode_value,Nat.unpair_pair,
    weightedIntervalCoefficient,complexMultiplyCode_value]

def stepPolynomialCode (s m N : ℕ) : ℕ := coefficientListCode N (stepCoefficientCode s m)

def stepPolynomialProgram : AlphaTerm := listTabulateTerm stepCoefficientProgram

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    We now assemble the finite coefficient list by closed terms. Encode row $\ell$ by
    $$d_\ell:=\NatPair{c^a_\ell}{\NatPair{c^b_\ell}{\NatPair{u_\ell}{w_\ell}}},\qquad
     c:=\LambdaListCode{[d_\ell]_{\ell<L}}.$$
    For fixed $m,j$, retain $c,m,j$ as the recursion parameter. At stage $\ell<L$, read the row with
    $\LambdaListGet$, project its entries, and apply the coefficient term $C$ to the endpoint codes and $j,m$.
    Multiply the result by the row's rational complex weight and add it to the accumulator, initially zero.
    The required complex arithmetic uses rational arithmetic on the two components:
    $$\begin{aligned}
     (u,v)+(r,t)&=(u+r,v+t),\\
     (u,v)(r,t)&=(ur-vt,ut+vr).
    \end{aligned}$$
    Induction on the number of processed rows shows that the accumulator denotes the sum of their weighted approximate
    coefficients. An empty row list returns zero. This gives a closed term $F$ computing the coefficient code
    $\gamma(c,m,j)$ on input $\NatPair{\NatPair{c}{m}}{j}$. Use $\LambdaListTabulate{F}$ with parameter $\NatPair{c}{m}$
    and length $N$ to append these codes in increasing degree. Its output is exactly
    $$\LambdaListCode{[\gamma(c,m,0),\ldots,\gamma(c,m,N-1)]}.$$
    The index $N-1$ is defined because $N\ge1$. This list denotes $P$; no test for a zero coefficient is needed.
-/
theorem stepPolynomialProgram_computes : NumericalComputes stepPolynomialProgram
    (fun p => stepPolynomialCode p.unpair.1.unpair.1 p.unpair.1.unpair.2 p.unpair.2) := by
  simpa only [stepPolynomialProgram,stepPolynomialCode,coefficientListCode,Nat.unpair_pair] using
    listTabulate_computes stepCoefficientProgram_computes

noncomputable def complexPolynomial (c : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (NatListCode.decode c).length,
    Polynomial.monomial j (complexRationalPoint ((NatListCode.decode c).getD j 0))

theorem complexPolynomial_eval (c : ℕ) (z : ℂ) :
    (complexPolynomial c).eval z = ∑ j ∈ Finset.range (NatListCode.decode c).length,
      complexRationalPoint ((NatListCode.decode c).getD j 0)*z^j := by
  simp [complexPolynomial,Polynomial.eval_finsetSum]

theorem stepPolynomialCode_eval (s m N : ℕ) (z : ℂ) :
    (complexPolynomial (stepPolynomialCode s m N)).eval z =
      ∑ j ∈ Finset.range N, complexRationalPoint (stepCoefficientCode s m j)*z^j := by
  rw [complexPolynomial_eval]
  simp only [stepPolynomialCode,coefficientListCode,NatListCode.decode_encode,List.length_map,List.length_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < ((List.range N).map (stepCoefficientCode s m)).length := by
    simpa using Finset.mem_range.mp hj
  rw [List.getD_eq_getElem _ _ hj']
  simp

/-- Exact finite Taylor polynomial of the coded rows, before rational approximation. -/
noncomputable def stepExactPolynomial (s N : ℕ) (ξ : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (NatListCode.decode s).length,
    complexRationalPoint (stepRow s i).unpair.2.unpair.2 *
      intervalExponentialPartial (rationalPoint (stepRow s i).unpair.1)
        (rationalPoint (stepRow s i).unpair.2.unpair.1) (fourierKernelScale ξ) N

theorem stepExactPolynomial_coefficients (s N : ℕ) (ξ : ℝ) :
    stepExactPolynomial s N ξ = ∑ j ∈ Finset.range N,
      (∑ i ∈ Finset.range (NatListCode.decode s).length,
        complexRationalPoint (stepRow s i).unpair.2.unpair.2 *
          intervalFourierCoefficient (rationalPoint (stepRow s i).unpair.1)
            (rationalPoint (stepRow s i).unpair.2.unpair.1) j)*(ξ:ℂ)^j := by
  simp only [stepExactPolynomial,intervalExponentialPartial_coefficients,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul,mul_assoc]

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Put
    $$Q:=N(R+1)^N,\qquad m:=n+V+Q,\qquad \delta:=\frac{2^{-(n+2)}}{Q}.$$
    Apply the preceding coefficient lemma at precision $m$ to every interval and degree $j<N$. Multiply the resulting
    rational complex approximations by $v_\ell$ and add them exactly. The error of each coefficient of $B$ is at most
    $$V2^{-(m+3)}\le2^{-(n+Q+3)}\le\delta,$$
    because $V\le2^V$ and $Q\le2^Q$. Include zero coefficients to form a list of length $N$, and let $P$ be the resulting
    rational complex polynomial. Since $R\ge1$ and $N\ge1$,
    $$\sup_{|\xi|\le R}|B(\xi)-P(\xi)|\le\sum_{j<N}\delta R^j\le2^{-(n+2)}.$$
-/
theorem stepPolynomialCode_error (s N R n V : ℕ) (hN : 0 < N)
    (hV : (∑ i ∈ Finset.range (NatListCode.decode s).length,
      ‖complexRationalPoint (stepRow s i).unpair.2.unpair.2‖) ≤ V)
    (ξ : ℝ) (hξ : |ξ| ≤ R) :
    ‖(complexPolynomial (stepPolynomialCode s (n+V+N*(R+1)^N) N)).eval (ξ:ℂ) -
      stepExactPolynomial s N ξ‖ ≤ (1/2:ℝ)^(n+2) := by
  rw [stepPolynomialCode_eval,stepExactPolynomial_coefficients]
  apply complexPolynomial_coefficient_error N R n hN _ _ (fun j _ => ?_) ξ hξ
  rw [stepCoefficientCode_value]
  exact finiteIntervalCoefficient_error _ _ _ _ V (N*(R+1)^N) n j hV (by positivity)

/-- A natural upper bound for the modulus of a rational complex code. -/
def complexMagnitudeBound (v : ℕ) : ℕ := rationalMagnitudeBound v.unpair.1 + rationalMagnitudeBound v.unpair.2

theorem complexRationalPoint_norm_le (v : ℕ) : ‖complexRationalPoint v‖ ≤ complexMagnitudeBound v := by
  unfold complexRationalPoint complexMagnitudeBound
  push_cast
  calc
    _ ≤ ‖(rationalPoint v.unpair.1:ℂ)‖ + ‖(rationalPoint v.unpair.2:ℂ)*Complex.I‖ := norm_add_le _ _
    _ = |rationalPoint v.unpair.1| + |rationalPoint v.unpair.2| := by
      simp [Complex.norm_real,Real.norm_eq_abs]
    _ ≤ _ := add_le_add (rationalPoint_abs_le_magnitude _) (rationalPoint_abs_le_magnitude _)

def complexMagnitudeProgram : AlphaTerm := addNumerical
  (onComponent rationalMagnitudeProgram true) (onComponent rationalMagnitudeProgram false)

theorem complexMagnitudeProgram_computes : NumericalComputes complexMagnitudeProgram complexMagnitudeBound :=
  (rationalMagnitudeProgram_computes.onComponent true).add (rationalMagnitudeProgram_computes.onComponent false)

/-- A bounded numerical sum over the decoded row list. -/
def naturalListSumPartial (f : ℕ → ℕ) (s : ℕ) : ℕ → ℕ :=
  primitiveRec 0 (fun i r => r+f (stepRow s i))

def naturalListSumCode (f : ℕ → ℕ) (s : ℕ) : ℕ :=
  naturalListSumPartial f s (NatListCode.decode s).length

def naturalListSumProgram (F : AlphaTerm) : AlphaTerm := numericalCompose
  (numericalRecursion (numericalConstant 0) (addNumerical piState
    (numericalCompose F (numericalCompose listGetTerm (pairNumerical (numericalProjectionTerm true)
      (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)))))))
  (pairNumerical numericalIdentity listLengthTerm)

theorem naturalListSumProgram_computes {F : AlphaTerm} {f : ℕ → ℕ} (hF : NumericalComputes F f) :
    NumericalComputes (naturalListSumProgram F) (naturalListSumCode f) := by
  have h := (numericalRecursion_computes (numericalConstant_computes 0)
    (piState_computes.add (hF.comp (listGet_computes.comp ((projection_computes true).pair
      ((projection_computes true).comp (projection_computes false))))))).comp
    (numericalIdentity_computes.pair listLength_computes)
  refine ⟨h.1,fun p => ?_⟩
  simpa only [naturalListSumProgram,naturalListSumCode,naturalListSumPartial,stepRow,Nat.unpair_pair,id_eq,
    ite_true,Bool.false_eq_true,ite_false] using h.2 p

theorem naturalListSumCode_value (f : ℕ → ℕ) (s : ℕ) :
    naturalListSumCode f s = ∑ i ∈ Finset.range (NatListCode.decode s).length, f (stepRow s i) := by
  have h (n : ℕ) : naturalListSumPartial f s n = ∑ i ∈ Finset.range n, f (stepRow s i) := by
    induction n with
    | zero => simp [naturalListSumPartial,primitiveRec]
    | succ n ih =>
      change naturalListSumPartial f s n + f (stepRow s n) = _
      rw [ih,Finset.sum_range_succ]
  exact h _

def stepWeightBound (s : ℕ) : ℕ := naturalListSumCode
  (fun row => complexMagnitudeBound row.unpair.2.unpair.2) s

def stepWeightProgram : AlphaTerm := naturalListSumProgram
  (numericalCompose complexMagnitudeProgram
    (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false)))

theorem stepWeightProgram_computes : NumericalComputes stepWeightProgram stepWeightBound :=
  naturalListSumProgram_computes (complexMagnitudeProgram_computes.comp
    ((projection_computes false).comp (projection_computes false)))

theorem stepWeightBound_valid (s : ℕ) :
    (∑ i ∈ Finset.range (NatListCode.decode s).length,
      ‖complexRationalPoint (stepRow s i).unpair.2.unpair.2‖) ≤ stepWeightBound s := by
  rw [stepWeightBound,naturalListSumCode_value,Nat.cast_sum]
  exact Finset.sum_le_sum (fun i _ => complexRationalPoint_norm_le _)

/-- Choose coefficient precision from the code, degree cutoff and frequency window. -/
def stepApproximationCode (s N R n : ℕ) : ℕ :=
  stepPolynomialCode s (n+stepWeightBound s+N*(R+1)^N) N

/-- Input (row-list,(degree-cutoff,(window-radius,output-precision))). -/
def stepApproximationProgram : AlphaTerm :=
  let S := numericalProjectionTerm true
  let T := numericalProjectionTerm false
  let N := numericalCompose (numericalProjectionTerm true) T
  let U := numericalCompose (numericalProjectionTerm false) T
  let R := numericalCompose (numericalProjectionTerm true) U
  let n := numericalCompose (numericalProjectionTerm false) U
  let Q := mulNumerical N (numericalCompose naturalPowerProgram
    (pairNumerical (numericalCompose successorTerm R) N))
  let m := addNumerical (addNumerical n (numericalCompose stepWeightProgram S)) Q
  numericalCompose stepPolynomialProgram (pairNumerical (pairNumerical S m) N)

theorem stepApproximationProgram_computes : NumericalComputes stepApproximationProgram
    (fun p => stepApproximationCode p.unpair.1 p.unpair.2.unpair.1
      p.unpair.2.unpair.2.unpair.1 p.unpair.2.unpair.2.unpair.2) := by
  have hs := projection_computes true
  have ht := projection_computes false
  have hN := (projection_computes true).comp ht
  have hu := (projection_computes false).comp ht
  have hR := (projection_computes true).comp hu
  have hn := (projection_computes false).comp hu
  have hQ := hN.mul (naturalPowerProgram_computes.comp ((successor_computes.comp hR).pair hN))
  have hm := (hn.add (stepWeightProgram_computes.comp hs)).add hQ
  have h := stepPolynomialProgram_computes.comp ((hs.pair hm).pair hN)
  refine ⟨h.1,fun p => ?_⟩
  simpa only [stepApproximationProgram,stepApproximationCode,Nat.unpair_pair,Nat.succ_eq_add_one,
    ite_true,Bool.false_eq_true,ite_false] using h.2 p

theorem stepApproximationCode_length (s N R n : ℕ) :
    (NatListCode.decode (stepApproximationCode s N R n)).length = N := by
  simp [stepApproximationCode,stepPolynomialCode,coefficientListCode]

theorem stepApproximationCode_error (s N R n : ℕ) (hN : 0 < N) (ξ : ℝ) (hξ : |ξ| ≤ R) :
    ‖(complexPolynomial (stepApproximationCode s N R n)).eval (ξ:ℂ) - stepExactPolynomial s N ξ‖ ≤
      (1/2:ℝ)^(n+2) :=
  stepPolynomialCode_error s N R n (stepWeightBound s) hN (stepWeightBound_valid s) ξ hξ

/-- Unsigned endpoint bounds also bound each interval length. -/
def rowEndpointBound (row : ℕ) : ℕ :=
  rationalMagnitudeBound row.unpair.1 + rationalMagnitudeBound row.unpair.2.unpair.1

def rowEndpointProgram : AlphaTerm := addNumerical
  (onComponent rationalMagnitudeProgram true)
  (numericalCompose rationalMagnitudeProgram
    (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)))

theorem rowEndpointProgram_computes : NumericalComputes rowEndpointProgram rowEndpointBound :=
  (rationalMagnitudeProgram_computes.onComponent true).add (rationalMagnitudeProgram_computes.comp
    ((projection_computes true).comp (projection_computes false)))

def stepEndpointBound (s : ℕ) : ℕ := naturalListSumCode rowEndpointBound s

def stepMassBound (s : ℕ) : ℕ := naturalListSumCode
  (fun row => complexMagnitudeBound row.unpair.2.unpair.2 * rowEndpointBound row) s

def stepEndpointProgram : AlphaTerm := naturalListSumProgram rowEndpointProgram

def stepMassProgram : AlphaTerm := naturalListSumProgram (mulNumerical
  (numericalCompose complexMagnitudeProgram
    (numericalCompose (numericalProjectionTerm false) (numericalProjectionTerm false))) rowEndpointProgram)

theorem stepEndpointProgram_computes : NumericalComputes stepEndpointProgram stepEndpointBound :=
  naturalListSumProgram_computes rowEndpointProgram_computes

theorem stepMassProgram_computes : NumericalComputes stepMassProgram stepMassBound :=
  naturalListSumProgram_computes ((complexMagnitudeProgram_computes.comp
    ((projection_computes false).comp (projection_computes false))).mul rowEndpointProgram_computes)

theorem rowEndpointBound_le (s i : ℕ) (hi : i < (NatListCode.decode s).length) :
    rowEndpointBound (stepRow s i) ≤ stepEndpointBound s := by
  rw [stepEndpointBound,naturalListSumCode_value]
  exact Finset.single_le_sum (f := fun j => rowEndpointBound (stepRow s j))
    (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr hi)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Set
    $$N:=\FourierSeriesCutoff{M}{n+A},\qquad
     B(\xi):=\sum_{\ell<L}v_\ell\IntervalFourierPolynomial{a_\ell}{b_\ell}{N}{\xi}.
-/
theorem stepEndpointBound_valid (s R i : ℕ) (hi : i < (NatListCode.decode s).length) :
    2*Real.pi*(R:ℝ)*max |rationalPoint (stepRow s i).unpair.1|
      |rationalPoint (stepRow s i).unpair.2.unpair.1| ≤ (8*R*stepEndpointBound s:ℕ) := by
  have h := fourierRadiusBound_valid R (stepRow s i).unpair.1 (stepRow s i).unpair.2.unpair.1
  apply h.trans
  change ((8*R*rowEndpointBound (stepRow s i):ℕ):ℝ) ≤ ((8*R*stepEndpointBound s:ℕ):ℝ)
  exact_mod_cast Nat.mul_le_mul_left (8*R) (rowEndpointBound_le s i hi)

theorem rowLength_le (row : ℕ) :
    rationalPoint row.unpair.2.unpair.1-rationalPoint row.unpair.1 ≤ rowEndpointBound row := by
  have ha := rationalPoint_abs_le_magnitude row.unpair.1
  have hb := rationalPoint_abs_le_magnitude row.unpair.2.unpair.1
  unfold rowEndpointBound
  push_cast
  linarith [le_abs_self (rationalPoint row.unpair.2.unpair.1),neg_le_abs (rationalPoint row.unpair.1)]

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Here are explicit integer bounds computable from the finite input. For a rational code
    $c=\RationalCode{p}{q}{d}$, put $h(c):=p+q$, so that $|\RationalValue{c}|\le h(c)$. Write
    $$a_\ell=\RationalValue{c^a_\ell},\quad b_\ell=\RationalValue{c^b_\ell},\quad
     v_\ell=\RationalValue{u_\ell}+\mathrm i\RationalValue{w_\ell}.$$
    Set
    $$\begin{aligned}
     E_\ell&:=h(c^a_\ell)+h(c^b_\ell),& W_\ell&:=h(u_\ell)+h(w_\ell),\\
     M&:=8R\sum_{\ell<L}E_\ell,& A&:=\sum_{\ell<L}W_\ell E_\ell,\\
     V&:=\sum_{\ell<L}W_\ell.
    \end{aligned}$$
    The endpoint estimate and $\pi\le4$ show that $M$ satisfies the
    \termuseas{Uniform truncation for interval Fourier transforms}{uniform truncation lemma} for every interval.
    Moreover, $b_\ell-a_\ell\le E_\ell$ and $|v_\ell|\le W_\ell$, so
    $$\sum_{\ell<L}|v_\ell|(b_\ell-a_\ell)\le A,\qquad \sum_{\ell<L}|v_\ell|\le V.$$
    These are bounded sums of natural numbers; the empty list gives $M=A=V=0$.
-/
theorem stepMassBound_valid (s : ℕ) :
    (∑ i ∈ Finset.range (NatListCode.decode s).length,
      ‖complexRationalPoint (stepRow s i).unpair.2.unpair.2‖ *
        (rationalPoint (stepRow s i).unpair.2.unpair.1-rationalPoint (stepRow s i).unpair.1)) ≤
          stepMassBound s := by
  rw [stepMassBound,naturalListSumCode_value,Nat.cast_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Nat.cast_mul]
  exact (mul_le_mul_of_nonneg_left (rowLength_le _) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (complexRationalPoint_norm_le _) (by positivity))

/-- The cutoff and all precision parameters are chosen from the finite input code. -/
def stepFourierCutoff (s R n : ℕ) : ℕ :=
  fourierCutoff (8*R*stepEndpointBound s) (n+stepMassBound s)

def stepFourierApproximationCode (s R n : ℕ) : ℕ :=
  stepApproximationCode s (stepFourierCutoff s R n) R n

def stepFourierApproximationProgram : AlphaTerm :=
  let S := numericalProjectionTerm true
  let T := numericalProjectionTerm false
  let R := numericalCompose (numericalProjectionTerm true) T
  let n := numericalCompose (numericalProjectionTerm false) T
  let M := mulNumerical (mulNumerical (numericalConstant 8) R) (numericalCompose stepEndpointProgram S)
  let A := numericalCompose stepMassProgram S
  let N := numericalCompose fourierCutoffProgram (pairNumerical M (addNumerical n A))
  numericalCompose stepApproximationProgram (pairNumerical S (pairNumerical N (pairNumerical R n)))

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    The bounds $M,A,V$ are also computed by bounded recursions over the same row list. The cutoff term and natural
    power term then compute $N,Q,m$. Composing these operations with the tabulation gives a closed numerical term $K$
    which, on input $\NatPair{c}{\NatPair{R}{n}}$, returns the code $k(c,R,n)$ of $P$. All recursion lengths are
    computed natural numbers. Every rational code has a positive denominator, so the numerical program terminates on
    all inputs; ordered endpoints are needed for the integral estimate, not for termination.
-/
theorem stepFourierApproximationProgram_computes : NumericalComputes stepFourierApproximationProgram
    (fun p => stepFourierApproximationCode p.unpair.1 p.unpair.2.unpair.1 p.unpair.2.unpair.2) := by
  have hs := projection_computes true
  have ht := projection_computes false
  have hR := (projection_computes true).comp ht
  have hn := (projection_computes false).comp ht
  have hM := ((numericalConstant_computes 8).mul hR).mul (stepEndpointProgram_computes.comp hs)
  have hA := stepMassProgram_computes.comp hs
  have hN := fourierCutoffProgram_computes.comp (hM.pair (hn.add hA))
  have h := stepApproximationProgram_computes.comp (hs.pair (hN.pair (hR.pair hn)))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [stepFourierApproximationProgram,stepFourierApproximationCode,stepFourierCutoff,Nat.unpair_pair,
    ite_true,Bool.false_eq_true,ite_false] using h.2 p

noncomputable def stepFourierValue (s : ℕ) (ξ : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (NatListCode.decode s).length,
    complexRationalPoint (stepRow s i).unpair.2.unpair.2 *
      (∫ x in (rationalPoint (stepRow s i).unpair.1)..(rationalPoint (stepRow s i).unpair.2.unpair.1),
        Complex.exp (fourierKernelScale ξ*(x:ℂ)))

theorem stepFourierApproximation_error (s R n : ℕ)
    (hab : ∀ i < (NatListCode.decode s).length,
      rationalPoint (stepRow s i).unpair.1 ≤ rationalPoint (stepRow s i).unpair.2.unpair.1)
    (ξ : ℝ) (hξ : |ξ| ≤ R) :
    ‖stepFourierValue s ξ - (complexPolynomial (stepFourierApproximationCode s R n)).eval (ξ:ℂ)‖ ≤
      (1/2:ℝ)^(n+1) := by
  have hN : 0 < stepFourierCutoff s R n := by unfold stepFourierCutoff fourierCutoff; omega
  have ht := finiteFourierPartial_error (NatListCode.decode s).length
    (fun i => rationalPoint (stepRow s i).unpair.1)
    (fun i => rationalPoint (stepRow s i).unpair.2.unpair.1)
    (fun i => complexRationalPoint (stepRow s i).unpair.2.unpair.2)
    hab R (8*R*stepEndpointBound s) (stepMassBound s) n
    (fun i hi => stepEndpointBound_valid s R i hi) (stepMassBound_valid s) ξ hξ
  have hc := stepApproximationCode_error s (stepFourierCutoff s R n) R n hN ξ hξ
  change ‖stepFourierValue s ξ - stepExactPolynomial s (stepFourierCutoff s R n) ξ‖ ≤ _ at ht
  change ‖(complexPolynomial (stepFourierApproximationCode s R n)).eval (ξ:ℂ) -
    stepExactPolynomial s (stepFourierCutoff s R n) ξ‖ ≤ _ at hc
  calc
    _ ≤ ‖stepFourierValue s ξ - stepExactPolynomial s (stepFourierCutoff s R n) ξ‖ +
        ‖stepExactPolynomial s (stepFourierCutoff s R n) ξ -
          (complexPolynomial (stepFourierApproximationCode s R n)).eval (ξ:ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1/2:ℝ)^(n+2)+(1/2:ℝ)^(n+2) := add_le_add ht (by rwa [norm_sub_rev])
    _ = _ := by rw [show n+2 = (n+1)+1 by omega,pow_succ]; ring

/-- The output query encodes (radius,precision); only input precision n+2 is read. -/
def fourierNameTransform (p : ℕ → ℕ) (z : ℕ) : ℕ :=
  stepFourierApproximationCode (p (z.unpair.2+2)) z.unpair.1 z.unpair.2

def fourierQueryProgram : AlphaTerm := addNumerical (numericalProjectionTerm false) (numericalConstant 2)

theorem fourierQueryProgram_computes : NumericalComputes fourierQueryProgram (fun z => z.unpair.2+2) :=
  (projection_computes false).add (numericalConstant_computes 2)

/-- A single closed term for all names; pairing retains the original output query. -/
def fourierNameProgram : AlphaTerm := mapOutputProgram stepFourierApproximationProgram
  (pairOutputProgram (queryOutputProgram (liftNumericalProgram fourierQueryProgram))
    (liftNumericalProgram numericalIdentity))

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    To obtain a single term acting on names, let $p(t)$ be the code of $s_t$ and encode the output request by
    $z=\NatPair{R}{n}$. Let $U$ compute $z\mapsto n+2$. First lift $U$ to a program that ignores its name argument,
    then query the input at the returned index. Pair this answer with the unchanged output request and apply $K$.
    The query, pairing, and output-composition constructions give a closed term $\Phi$. After the elementary beta
    reductions that expose these compositions, its computation is
    $$\Phi\,o\,\ChurchNumeral{z}\to_\beta^*
     K\bigl(\LambdaNumericPair\,(o\,(U\ChurchNumeral{z}))\,\ChurchNumeral{z}\bigr).$$
    The numerical computation of $U$ returns $n+2$, one query returns $p(n+2)$, and pairing followed by $K$ gives
    $$\LambdaInputSteps{p}{\Phi\,o\,\ChurchNumeral{z}}{\ChurchNumeral{k(p(n+2),R,n)}}.$$
-/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    Combining the input error, the series tail, and the coefficient error gives
    $$\sup_{|\xi|\le R}|\FourierTransform{f}(\xi)-P(\xi)|\le3\cdot2^{-(n+2)}<2^{-n}.
-/
theorem fourierNameProgram_computes : UniformNumericalComputes fourierNameProgram fourierNameTransform := by
  have h := (fourierQueryProgram_computes.uniform.query.pair numericalIdentity_computes.uniform).map
    stepFourierApproximationProgram_computes
  refine ⟨h.1,fun p z => ?_⟩
  simpa only [fourierNameProgram,fourierNameTransform,Nat.unpair_pair,id_eq] using h.2 p z

theorem fourierNameProgram_typeTwoComputes (D : Set (ℕ → ℕ)) :
    TypeTwoComputes fourierNameProgram (fun p : D => fourierNameTransform p.val) :=
  typeTwoComputes_iff_runs.mpr ⟨fourierNameProgram_computes.1,
    fun p z => fourierNameProgram_computes.2 p.val z⟩

/-- Transfer a bound on the input approximant's transform to the computed polynomial.
The L1-to-Fourier norm estimate supplies this hypothesis for L1 names. -/
theorem fourierNameTransform_error (p : ℕ → ℕ) (g : ℝ → ℂ) (R n : ℕ)
    (hab : ∀ i < (NatListCode.decode (p (n+2))).length,
      rationalPoint (stepRow (p (n+2)) i).unpair.1 ≤ rationalPoint (stepRow (p (n+2)) i).unpair.2.unpair.1)
    (hinput : ∀ ξ : ℝ, ‖g ξ - stepFourierValue (p (n+2)) ξ‖ ≤ (1/2:ℝ)^(n+2))
    (ξ : ℝ) (hξ : |ξ| ≤ R) :
    ‖g ξ - (complexPolynomial (fourierNameTransform p (Nat.pair R n))).eval (ξ:ℂ)‖ ≤ (1/2:ℝ)^n := by
  simp only [fourierNameTransform,Nat.unpair_pair]
  calc
    _ ≤ ‖g ξ - stepFourierValue (p (n+2)) ξ‖ +
        ‖stepFourierValue (p (n+2)) ξ -
          (complexPolynomial (stepFourierApproximationCode (p (n+2)) R n)).eval (ξ:ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1/2:ℝ)^(n+2)+(1/2:ℝ)^(n+1) :=
      add_le_add (hinput ξ) (stepFourierApproximation_error _ _ _ hab ξ hξ)
    _ ≤ _ := by
      rw [show n+2 = (n+1)+1 by omega,pow_succ,pow_succ]
      nlinarith [show 0 ≤ (1/2:ℝ)^n by positivity]

end PolishSpaceBook
