module

public import PolishSpaceBook.RationalMetricEstimates

@[expose] public section

/-! # Rational margins for distance intervals

These metric estimates have no dependency on an execution model.
-/
namespace PolishSpaceBook
universe u
variable {X : Type u} [MetricSpace X]

abbrev DistanceIntervalInput := (ℕ × ℕ) × (RationalCode × RationalCode)

def DistanceInterval (q : ℕ → X) (z : DistanceIntervalInput) : Prop :=
  (z.2.1.value : ℝ) < dist (q z.1.1) (q z.1.2) ∧
    dist (q z.1.1) (q z.1.2) < (z.2.2.value : ℝ)

namespace RationalMetricApproximation
variable {q : ℕ → X} (A : RationalMetricApproximation q)

def intervalTest (z : DistanceIntervalInput) (k : ℕ) : Bool :=
  decide ((z.2.1.add (RationalCode.dyadic k)).lt (A.approx (z.1.1, (z.1.2, k)))) &&
    decide (((A.approx (z.1.1, (z.1.2, k))).add (RationalCode.dyadic k)).lt z.2.2)


theorem intervalTest_iff (z : DistanceIntervalInput) (k : ℕ) :
    A.intervalTest z k = true ↔
      (z.2.1.value : ℝ) + (1 / 2 : ℝ)^k < (A.approx (z.1.1, (z.1.2, k))).value ∧
      ((A.approx (z.1.1, (z.1.2, k))).value : ℝ) + (1 / 2 : ℝ)^k < z.2.2.value := by
  simp only [intervalTest, Bool.and_eq_true, decide_eq_true_eq, RationalCode.lt_iff]
  rw [← Rat.cast_lt (K := ℝ), ← Rat.cast_lt (K := ℝ)]
  simp


theorem exists_intervalTest_iff (z : DistanceIntervalInput) :
    (∃ k, A.intervalTest z k = true) ↔ DistanceInterval q z := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨hl, hr⟩ := (A.intervalTest_iff z k).mp hk
    obtain ⟨ha, hb⟩ := abs_le.mp (A.error z.1.1 z.1.2 k)
    constructor <;> linarith
  · rintro ⟨hl, hr⟩
    let g := min (dist (q z.1.1) (q z.1.2) - z.2.1.value)
      ((z.2.2.value : ℝ) - dist (q z.1.1) (q z.1.2))
    have hg : 0 < g / 2 := by dsimp [g]; positivity
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hg (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨k, (A.intervalTest_iff z k).mpr ?_⟩
    have hg₁ := min_le_left (dist (q z.1.1) (q z.1.2) - (z.2.1.value : ℝ))
      ((z.2.2.value : ℝ) - dist (q z.1.1) (q z.1.2))
    have hg₂ := min_le_right (dist (q z.1.1) (q z.1.2) - (z.2.1.value : ℝ))
      ((z.2.2.value : ℝ) - dist (q z.1.1) (q z.1.2))
    obtain ⟨ha, hb⟩ := abs_le.mp (A.error z.1.1 z.1.2 k)
    dsimp [g] at hk
    constructor <;> linarith

end RationalMetricApproximation
end PolishSpaceBook
