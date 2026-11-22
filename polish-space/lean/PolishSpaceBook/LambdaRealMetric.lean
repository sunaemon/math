module

public import PolishSpaceBook.LambdaRationalOrder
public import PolishSpaceBook.LambdaRealRepresentation
public import PolishSpaceBook.LambdaMetricBalls

@[expose] public section

/-! # Exact rational distances for the computable real-line presentation -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA

@[simp] theorem rationalPoint_max (a b : ℕ) :
    rationalPoint (rationalMaxCode a b) = max (rationalPoint a) (rationalPoint b) := by
  exact rationalMaxCode_value a b

def rationalDifferenceCode (z : ℕ) : ℕ :=
  ((RationalCode.ofNat z.unpair.1).add (RationalCode.ofNat z.unpair.2).neg).natCode

def rationalDifferenceProgram : AlphaTerm :=
  numericalCompose rationalAddTerm (pairNumerical (numericalProjectionTerm true)
    (numericalCompose rationalNegTerm (numericalProjectionTerm false)))

theorem rationalDifferenceProgram_computes :
    NumericalComputes rationalDifferenceProgram rationalDifferenceCode := by
  have h := rationalAdd_computes.comp ((projection_computes true).pair
    (rationalNeg_computes.comp (projection_computes false)))
  refine ⟨h.1,fun z => ?_⟩
  simpa [rationalDifferenceProgram,rationalDifferenceCode] using h.2 z

@[simp] theorem rationalPoint_difference (a b : ℕ) :
    rationalPoint (rationalDifferenceCode (Nat.pair a b)) = rationalPoint a - rationalPoint b := by
  simp [rationalDifferenceCode,rationalPoint,sub_eq_add_neg]

def rationalDistanceCode (z : ℕ) : ℕ :=
  rationalMaxCode (rationalDifferenceCode z)
    (RationalCode.ofNat (rationalDifferenceCode z)).neg.natCode

def rationalDistanceProgram : AlphaTerm :=
  numericalCompose rationalMaxProgram (pairNumerical rationalDifferenceProgram
    (numericalCompose rationalNegTerm rationalDifferenceProgram))

theorem rationalDistanceProgram_computes :
    NumericalComputes rationalDistanceProgram rationalDistanceCode := by
  have h := rationalMaxProgram_computes.comp (rationalDifferenceProgram_computes.pair
    (rationalNeg_computes.comp rationalDifferenceProgram_computes))
  refine ⟨h.1,fun z => ?_⟩
  simpa only [rationalDistanceCode,rationalDistanceProgram,Nat.unpair_pair] using h.2 z

@[simp] theorem rationalPoint_neg (a : ℕ) :
    rationalPoint (RationalCode.ofNat a).neg.natCode = -rationalPoint a := by
  simp [rationalPoint]

@[simp] theorem rationalPoint_distance (a b : ℕ) :
    rationalPoint (rationalDistanceCode (Nat.pair a b)) = dist (rationalPoint a) (rationalPoint b) := by
  simp only [rationalDistanceCode,rationalPoint_max,rationalPoint_neg,rationalPoint_difference,
    Real.dist_eq,abs_eq_max_neg]

/-- The rational distances are exact, so the precision input can be ignored. -/
/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: statement
  kind: lemma
  title: Rational maxima and real distances
-/
def realMetricApproximation : LambdaMetricApproximation rationalPoint where
  approx z := RationalCode.ofNat (rationalDistanceCode (Nat.pair z.1 z.2.1))
  error i j n := by
    change |rationalPoint (rationalDistanceCode (Nat.pair i j)) - dist (rationalPoint i) (rationalPoint j)| ≤ _
    rw [rationalPoint_distance,sub_self,abs_zero]
    positivity
  program := numericalCompose rationalDistanceProgram (pairNumerical (numericalProjectionTerm true)
    (numericalCompose (numericalProjectionTerm true) (numericalProjectionTerm false)))
  computes := by
    simpa using rationalDistanceProgram_computes.comp
      ((projection_computes true).pair ((projection_computes true).comp (projection_computes false)))

end PolishSpaceBook
