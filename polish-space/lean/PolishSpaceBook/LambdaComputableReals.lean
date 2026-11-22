module

public import PolishSpaceBook.LambdaRealMetric
public import PolishSpaceBook.EffectiveDensePresentations

@[expose] public section

namespace PolishSpaceBook
open NamedLambda NamedLambda.AlphaTerm LambdaIndexPCA

/-- The book's two-coordinate shift converts rational approximations to the
same fast Cauchy representation used by its real-number programs. -/
/-@ booklink:
  source: polish-space-book/computable-polish-spaces-tte.md
  target: prose
  excerpt: |
    For real numbers, computability means that one algorithm produces, from $n\in\NN$, a rational $q_n$ with
    $|x-q_n|\le2^{-n}$. This is equivalent to having a computable fast Cauchy name: shifting the approximation index by two
    gives the required pairwise Cauchy bounds. An exact finite expression for a number and an algorithm for its
    approximations are different kinds of information.
-/
theorem computableReal_iff_rationalApproximation (x : ℝ) :
    IsComputablePoint realRepresentation x ↔
      ∃ (a : ℕ → ℕ) (A : AlphaTerm), NumericalComputes A a ∧
        ∀ n, |rationalPoint (a n) - x| ≤ (1 / 2 : ℝ)^n := by
  constructor
  · rintro ⟨p, ⟨A, hA⟩, hx⟩
    refine ⟨p.val, A, hA, fun n => ?_⟩
    have he : cauchyRepresentation rationalPoint p = x := hx
    simpa only [Real.dist_eq, he] using cauchyRepresentation_dist_le rationalPoint p n
  · rintro ⟨a, A, hA, ha⟩
    let p : ℕ → ℕ := fun n => a (n + 2)
    have hhalf (n : ℕ) : dist (rationalPoint (p n)) x ≤ (1 / 2 : ℝ)^(n + 1) := by
      calc
        dist (rationalPoint (p n)) x ≤ (1 / 2 : ℝ)^(n + 2) := by
          simpa only [p, Real.dist_eq] using ha (n + 2)
        _ ≤ (1 / 2 : ℝ)^(n + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hshift : NumericalComputes (numericalCompose successorTerm successorTerm)
        (fun n => n + 2) := by
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using successor_computes.comp successor_computes
    exact ⟨⟨p, isCauchyName_of_halfError_le hhalf⟩, ⟨_, hA.comp hshift⟩,
      cauchyRepresentation_eq_of_halfError_le p x hhalf⟩

end PolishSpaceBook
