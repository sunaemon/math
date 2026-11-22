module

public import PolishSpaceBook.LambdaFourierL1

@[expose] public section

/-! # Closed lambda programs for finite complex polynomial arithmetic

The list representation retains trailing zero coefficients. Addition tabulates
coefficients and multiplication uses the finite convolution, so every output
is again a concrete finite list rather than an existential polynomial code.
-/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA

/-- Out-of-range coefficients are zero by the list representation's default. -/
theorem complexPolynomial_coeff (c k : ℕ) :
    (complexPolynomial c).coeff k = complexRationalPoint ((NatListCode.decode c).getD k 0) := by
  unfold complexPolynomial
  rw [Polynomial.finsetSum_coeff]
  by_cases hk : k < (NatListCode.decode c).length
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Polynomial.coeff_monomial,hj]
    · intro h; exact (h (Finset.mem_range.mpr hk)).elim
  · rw [Finset.sum_eq_zero]
    · rw [List.getD_eq_default (NatListCode.decode c) 0 (by omega)]
      simp
    · intro j hj
      have hne : j ≠ k := by have := Finset.mem_range.mp hj; omega
      simp [Polynomial.coeff_monomial,hne]

theorem complexPolynomial_coeff_zero {c k : ℕ} (hk : (NatListCode.decode c).length ≤ k) :
    (complexPolynomial c).coeff k = 0 := by
  rw [complexPolynomial_coeff,List.getD_eq_default _ _ hk,complexRationalPoint_zero]

theorem complexCoefficientList_coeff (N : ℕ) (a : ℕ → ℕ) (k : ℕ) :
    (complexPolynomial (coefficientListCode N a)).coeff k = if k<N then complexRationalPoint (a k) else 0 := by
  rw [complexPolynomial_coeff]
  simp only [coefficientListCode,NatListCode.decode_encode]
  by_cases hk : k<N
  · have hk' : k < ((List.range N).map a).length := by simpa using hk
    rw [List.getD_eq_getElem _ _ hk']
    simp [hk]
  · rw [List.getD_eq_default _ _ (by simpa using (le_of_not_gt hk))]
    simp [hk]

def polynomialAddCoefficientCode (a b k : ℕ) : ℕ :=
  complexAddCode ((NatListCode.decode a).getD k 0) ((NatListCode.decode b).getD k 0)

def polynomialAddCoefficientProgram : AlphaTerm :=
  let A := onComponent (numericalProjectionTerm true) true
  let B := onComponent (numericalProjectionTerm false) true
  let K := numericalProjectionTerm false
  numericalCompose complexAddProgram (pairNumerical
    (numericalCompose listGetTerm (pairNumerical A K)) (numericalCompose listGetTerm (pairNumerical B K)))

theorem polynomialAddCoefficientProgram_computes : NumericalComputes polynomialAddCoefficientProgram
    (fun p => polynomialAddCoefficientCode p.unpair.1.unpair.1 p.unpair.1.unpair.2 p.unpair.2) := by
  have a := (projection_computes true).onComponent true
  have b := (projection_computes false).onComponent true
  have k := projection_computes false
  have h := complexAddProgram_computes.comp ((listGet_computes.comp (a.pair k)).pair (listGet_computes.comp (b.pair k)))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [polynomialAddCoefficientProgram,polynomialAddCoefficientCode,Nat.unpair_pair,
    ite_true,Bool.false_eq_true,ite_false] using h.2 p

@[irreducible] def polynomialAddCode (a b : ℕ) : ℕ :=
  coefficientListCode ((NatListCode.decode a).length+(NatListCode.decode b).length) (polynomialAddCoefficientCode a b)

def polynomialPairLengthProgram : AlphaTerm := addNumerical
  (onComponent listLengthTerm true) (onComponent listLengthTerm false)

theorem polynomialPairLengthProgram_computes : NumericalComputes polynomialPairLengthProgram
    (fun p => (NatListCode.decode p.unpair.1).length+(NatListCode.decode p.unpair.2).length) :=
  (listLength_computes.onComponent true).add (listLength_computes.onComponent false)

def polynomialAddProgram : AlphaTerm := numericalCompose (listTabulateTerm polynomialAddCoefficientProgram)
  (pairNumerical numericalIdentity polynomialPairLengthProgram)

theorem polynomialAddProgram_computes : NumericalComputes polynomialAddProgram
    (fun p => polynomialAddCode p.unpair.1 p.unpair.2) := by
  have h := (listTabulate_computes polynomialAddCoefficientProgram_computes).comp
    (numericalIdentity_computes.pair polynomialPairLengthProgram_computes)
  refine ⟨h.1,fun p => ?_⟩
  simpa only [polynomialAddProgram,polynomialAddCode,coefficientListCode,Nat.unpair_pair,id_eq] using h.2 p

theorem polynomialAddCode_value (a b : ℕ) :
    complexPolynomial (polynomialAddCode a b) = complexPolynomial a+complexPolynomial b := by
  ext k
  rw [polynomialAddCode,complexCoefficientList_coeff,Polynomial.coeff_add]
  split_ifs with hk
  · simp only [polynomialAddCoefficientCode,complexAddCode_value,complexPolynomial_coeff]
  · rw [complexPolynomial_coeff_zero (by omega),complexPolynomial_coeff_zero (by omega),add_zero]

/-- The input is (((a,b),k),i), retaining both polynomial codes and the output degree. -/
def polynomialProductSummandCode (a b k i : ℕ) : ℕ :=
  complexMultiplyCode ((NatListCode.decode a).getD i 0) ((NatListCode.decode b).getD (k-i) 0)

def polynomialProductSummandProgram : AlphaTerm :=
  let AB := numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm true)
  let A := numericalCompose (numericalProjectionTerm true) AB
  let B := numericalCompose (numericalProjectionTerm false) AB
  let K := onComponent (numericalProjectionTerm false) true
  let I := numericalProjectionTerm false
  numericalCompose complexMultiplyProgram (pairNumerical (numericalCompose listGetTerm (pairNumerical A I))
    (numericalCompose listGetTerm (pairNumerical B (numericalCombine subtractionTerm K I))))

theorem polynomialProductSummandProgram_computes : NumericalComputes polynomialProductSummandProgram
    (fun p => polynomialProductSummandCode p.unpair.1.unpair.1.unpair.1 p.unpair.1.unpair.1.unpair.2
      p.unpair.1.unpair.2 p.unpair.2) := by
  have ab := (projection_computes true).comp (projection_computes true)
  have a := (projection_computes true).comp ab
  have b := (projection_computes false).comp ab
  have k := (projection_computes false).onComponent true
  have i := projection_computes false
  have h := complexMultiplyProgram_computes.comp ((listGet_computes.comp (a.pair i)).pair
    (listGet_computes.comp (b.pair (k.combine i subtractionTerm_closed (fun k i => k-i) subtractionTerm_apply))))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [polynomialProductSummandProgram,polynomialProductSummandCode,Nat.unpair_pair,
    ite_true,Bool.false_eq_true,ite_false,onComponent] using h.2 p

@[irreducible] def polynomialProductCoefficientCode (a b k : ℕ) : ℕ :=
  complexSumCode (fun p => polynomialProductSummandCode p.unpair.1.unpair.1.unpair.1
    p.unpair.1.unpair.1.unpair.2 p.unpair.1.unpair.2 p.unpair.2) (Nat.pair (Nat.pair a b) k) (k+1)

def polynomialProductCoefficientProgram : AlphaTerm := numericalCompose
  (complexSumProgram polynomialProductSummandProgram)
  (pairNumerical numericalIdentity (numericalCompose successorTerm (numericalProjectionTerm false)))

theorem polynomialProductCoefficientProgram_computes : NumericalComputes polynomialProductCoefficientProgram
    (fun p => polynomialProductCoefficientCode p.unpair.1.unpair.1 p.unpair.1.unpair.2 p.unpair.2) := by
  have h := (complexSumProgram_computes polynomialProductSummandProgram_computes).comp
    (numericalIdentity_computes.pair (successor_computes.comp (projection_computes false)))
  refine ⟨h.1,fun p => ?_⟩
  simpa only [polynomialProductCoefficientProgram,polynomialProductCoefficientCode,Nat.unpair_pair,
    Nat.pair_unpair,id_eq,ite_false,Bool.false_eq_true] using h.2 p

theorem polynomialProductCoefficientCode_value (a b k : ℕ) :
    complexRationalPoint (polynomialProductCoefficientCode a b k) =
      (complexPolynomial a*complexPolynomial b).coeff k := by
  rw [polynomialProductCoefficientCode,complexSumCode_value,Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (complexPolynomial a).coeff i*(complexPolynomial b).coeff j) k]
  simp only [Nat.unpair_pair,polynomialProductSummandCode,complexMultiplyCode_value,complexPolynomial_coeff]

@[irreducible] def polynomialProductCode (a b : ℕ) : ℕ :=
  coefficientListCode ((NatListCode.decode a).length+(NatListCode.decode b).length) (polynomialProductCoefficientCode a b)

def polynomialProductProgram : AlphaTerm := numericalCompose (listTabulateTerm polynomialProductCoefficientProgram)
  (pairNumerical numericalIdentity polynomialPairLengthProgram)

theorem polynomialProductProgram_computes : NumericalComputes polynomialProductProgram
    (fun p => polynomialProductCode p.unpair.1 p.unpair.2) := by
  have h := (listTabulate_computes polynomialProductCoefficientProgram_computes).comp
    (numericalIdentity_computes.pair polynomialPairLengthProgram_computes)
  refine ⟨h.1,fun p => ?_⟩
  simpa only [polynomialProductProgram,polynomialProductCode,coefficientListCode,Nat.unpair_pair,id_eq] using h.2 p

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: prose
  excerpt: |
    For completeness, polynomial arithmetic on these lists is also explicit. If the input lists have lengths $m$ and $r$,
    interpret coefficients outside the lists as zero. Tabulate $m+r$ coefficients. Addition uses $a_k+b_k$, while
    multiplication uses
    $$c_k:=\sum_{i=0}^{k}a_i b_{k-i}\qquad(0\le k<m+r).$$
    The finite sum retains both lists and $k$ as parameters; its indices satisfy $i\le k$, so $k-i$ is nonnegative.
    The convolution formula proves that the decoded output is the product polynomial. Trailing zeros are harmless.
-/
theorem polynomialProductCode_value (a b : ℕ) :
    complexPolynomial (polynomialProductCode a b) = complexPolynomial a*complexPolynomial b := by
  ext k
  rw [polynomialProductCode,complexCoefficientList_coeff]
  split_ifs with hk
  · exact polynomialProductCoefficientCode_value a b k
  · rw [Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (complexPolynomial a).coeff i*(complexPolynomial b).coeff j) k]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    by_cases ha : i < (NatListCode.decode a).length
    · rw [complexPolynomial_coeff_zero (c := b) (by omega),mul_zero]
    · rw [complexPolynomial_coeff_zero (c := a) (by omega),zero_mul]

@[irreducible] def polynomialConstantCode (c : ℕ) : ℕ := coefficientListCode 1 (fun _ => c)

def polynomialConstantProgram : AlphaTerm := numericalCompose (listTabulateTerm (numericalProjectionTerm true))
  (pairNumerical numericalIdentity (numericalConstant 1))

theorem polynomialConstantProgram_computes : NumericalComputes polynomialConstantProgram polynomialConstantCode := by
  have h := (listTabulate_computes (projection_computes true)).comp
    (numericalIdentity_computes.pair (numericalConstant_computes 1))
  refine ⟨h.1,fun c => ?_⟩
  simpa only [polynomialConstantProgram,polynomialConstantCode,coefficientListCode,Nat.unpair_pair,ite_true,id_eq] using h.2 c

theorem polynomialConstantCode_value (c : ℕ) :
    complexPolynomial (polynomialConstantCode c) = Polynomial.C (complexRationalPoint c) := by
  ext k
  rw [polynomialConstantCode,complexCoefficientList_coeff,Polynomial.coeff_C]
  cases k <;> simp

def polynomialOneCode : ℕ := polynomialConstantCode (Nat.pair rationalOneCode 0)

theorem polynomialOneCode_value : complexPolynomial polynomialOneCode = 1 := by
  rw [polynomialOneCode,polynomialConstantCode_value]
  have h0 : rationalPoint 0 = 0 := by norm_num [rationalPoint,RationalCode.ofNat,RationalCode.value]
  simp [complexRationalPoint,h0]

@[simp] theorem complexPolynomial_zero : complexPolynomial 0 = 0 := by
  simp [complexPolynomial,NatListCode.decode]

@[irreducible] def polynomialPowerCode (c : ℕ) : ℕ → ℕ :=
  primitiveRec polynomialOneCode (fun _ r => polynomialProductCode r c)

def polynomialPowerProgram : AlphaTerm := numericalRecursion (numericalConstant polynomialOneCode)
  (numericalCompose polynomialProductProgram (pairNumerical piState (numericalProjectionTerm true)))

theorem polynomialPowerProgram_computes : NumericalComputes polynomialPowerProgram
    (fun p => polynomialPowerCode p.unpair.1 p.unpair.2) := by
  have h := numericalRecursion_computes (numericalConstant_computes polynomialOneCode)
    (polynomialProductProgram_computes.comp (piState_computes.pair (projection_computes true)))
  simpa only [polynomialPowerProgram,polynomialPowerCode,Nat.unpair_pair,ite_true] using h

theorem polynomialPowerCode_value (c n : ℕ) :
    complexPolynomial (polynomialPowerCode c n) = complexPolynomial c^n := by
  induction n with
  | zero => simp [polynomialPowerCode,primitiveRec,polynomialOneCode_value]
  | succ n ih =>
    have h : polynomialPowerCode c (n+1) = polynomialProductCode (polynomialPowerCode c n) c := by
      rw [polynomialPowerCode,primitiveRec]
    rw [h,polynomialProductCode_value,ih,pow_succ]

@[irreducible] def polynomialSumCode (f : ℕ → ℕ) (x : ℕ) : ℕ → ℕ :=
  primitiveRec 0 (fun i r => polynomialAddCode r (f (Nat.pair x i)))

def polynomialSumProgram (F : AlphaTerm) : AlphaTerm := numericalRecursion (numericalConstant 0)
  (numericalCompose polynomialAddProgram (pairNumerical piState
    (numericalCompose F (pairNumerical (numericalProjectionTerm true)
      (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false))))))

theorem polynomialSumProgram_computes {F : AlphaTerm} {f : ℕ → ℕ} (hf : NumericalComputes F f) :
    NumericalComputes (polynomialSumProgram F) (fun p => polynomialSumCode f p.unpair.1 p.unpair.2) := by
  have h := numericalRecursion_computes (numericalConstant_computes 0)
    (polynomialAddProgram_computes.comp (piState_computes.pair
      (hf.comp ((projection_computes true).pair
        ((projection_computes true).comp (projection_computes false))))))
  simpa only [polynomialSumProgram,polynomialSumCode,Nat.unpair_pair,ite_true,Bool.false_eq_true,ite_false] using h

theorem polynomialSumCode_value (f : ℕ → ℕ) (x n : ℕ) :
    complexPolynomial (polynomialSumCode f x n) = ∑ i ∈ Finset.range n, complexPolynomial (f (Nat.pair x i)) := by
  induction n with
  | zero => simp [polynomialSumCode,primitiveRec]
  | succ n ih =>
    have h : polynomialSumCode f x (n+1) = polynomialAddCode (polynomialSumCode f x n) (f (Nat.pair x n)) := by
      rw [polynomialSumCode,primitiveRec]
    rw [h,polynomialAddCode_value,ih,Finset.sum_range_succ]

end PolishSpaceBook
