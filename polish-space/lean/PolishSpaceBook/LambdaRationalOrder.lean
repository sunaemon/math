module

public import PolishSpaceBook.LambdaRationalCodes
public import PolishSpaceBook.LambdaNumericalResultSearch

@[expose] public section

/-! # Exact rational negation and maximum by closed lambda terms -/
namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm

namespace RationalCode
/-- Negation swaps the two natural numerator components; no truncated subtraction is used. -/
def neg (a : RationalCode) : RationalCode := ((a.1.2,a.1.1),a.2)
@[simp] theorem value_neg (a : RationalCode) : (neg a).value = -a.value := by
  simp only [neg,value]; ring
end RationalCode

def rationalNegTerm : AlphaTerm :=
  pairNumerical (pairNumerical (rationalNumeratorTerm false) (rationalNumeratorTerm true))
    (numericalProjectionTerm false)

theorem rationalNeg_computes : NumericalComputes rationalNegTerm
    (fun z => (RationalCode.ofNat z).neg.natCode) := by
  simpa [rationalNegTerm,RationalCode.neg,RationalCode.natCode,RationalCode.ofNat] using
    ((rationalNumerator_computes false).pair (rationalNumerator_computes true)).pair
      (projection_computes false)

/-- Select the larger rational without requiring a canonical rational code. -/
def rationalMaxCode (a b : ℕ) : ℕ :=
  if (RationalCode.ofNat a).value < (RationalCode.ofNat b).value then b else a

def rationalMaxProgram : AlphaTerm := numericalApply3 zeroTestTerm rationalLessTerm
  (numericalProjectionTerm true) (numericalProjectionTerm false)

/-@ booklink:
  source: polish-space-book/computable-analysis.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Let $s_c$ be the rational represented by code $c$. Write $\pi_a:=\LambdaNumericProjection{a}$ and
    $C:=\LambdaRationalLess$. The term
    $$V:=\lambdaab{z}{\LambdaZeroTest\,(Cz)\,(\pi_1z)\,(\pi_2z)}$$
    returns the second code if its value is larger and the first code otherwise. Indeed, the comparison returns
    $1$ or $0$, and the zero test selects the first code on zero and the second on one. Thus its output represents
    $\max(s_a,s_b)$ on input $\NatPair{a}{b}$, including when both rationals are negative.
    Using the rational negation term $J$ from the preceding proof, define
    $$\begin{aligned}
    D&:=\lambdaab{z}{\LambdaRationalAdd(\LambdaNumericPair\,(\pi_1z)\,(J(\pi_2z)))},\\
    A&:=\lambdaab{z}{V(\LambdaNumericPair\,(Dz)\,(J(Dz)))},\\
    M&:=\lambdaab{z}{A(\LambdaNumericPair\,(\pi_1z)\,(\pi_1(\pi_2z)))}.
    \end{aligned}$$
    The first term computes a code for $s_a-s_b$, and the second computes a code for
    $\max(s_a-s_b,-(s_a-s_b))=|s_a-s_b|$. The third accepts $\NatPair{a}{\NatPair{b}{n}}$ and ignores the
    precision coordinate, since its answer is exact. Composition of the terminating beta computations proves
    these assertions. Every rational has a code, so the basic sequence is dense; the usual real metric is complete.
    \end{proof}
-/
theorem rationalMaxProgram_computes : NumericalComputes rationalMaxProgram
    (fun z => rationalMaxCode z.unpair.1 z.unpair.2) := by
  have h := rationalLess_computes.apply3 (projection_computes true) (projection_computes false)
    zeroTestTerm_closed (fun c a b => if c = 0 then a else b) (by
      intro c a b
      cases c with
      | zero => exact branch_zero _ _ (by rw [numeral_closed]; simp)
      | succ c => exact branch_succ c _ _)
  refine ⟨h.1,fun z => ?_⟩
  by_cases hz : (RationalCode.ofNat z.unpair.1).value < (RationalCode.ofNat z.unpair.2).value <;>
    simpa only [rationalMaxProgram,rationalMaxCode,hz,ite_true,ite_false,one_ne_zero,Bool.false_eq_true] using h.2 z

theorem rationalMaxCode_value (a b : ℕ) :
    ((RationalCode.ofNat (rationalMaxCode a b)).value : ℝ) =
      max ((RationalCode.ofNat a).value : ℝ) ((RationalCode.ofNat b).value : ℝ) := by
  unfold rationalMaxCode
  split_ifs with h
  · exact (max_eq_right (by exact_mod_cast h.le)).symm
  · exact (max_eq_left (by exact_mod_cast le_of_not_gt h)).symm

end PolishSpaceBook
