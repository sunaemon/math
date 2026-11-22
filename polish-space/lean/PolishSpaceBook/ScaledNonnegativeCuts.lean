module

public import PolishSpaceBook.CantorInternalMeasureCutValue

@[expose] public section

/-! # Scaled comparisons from nonnegative rational lower cuts -/

namespace PolishSpaceBook.CantorTreeMeasure

lemma scaled_fraction_lt_iff (a b m n : ℕ) (hb : 0 < b) (hn : 0 < n) (y : ℝ) :
    ((m * a : ℕ) : ℝ) / (n * b : ℕ) < y ↔ (m : ℝ) * ((a : ℝ) / b) < (n : ℝ) * y := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have he : ((m * a : ℕ) : ℝ) / (n * b : ℕ) = ((m : ℝ) * ((a : ℝ) / b)) / n := by
    push_cast
    field_simp
  rw [he, div_lt_iff₀ hnR]
  rw [mul_comm y]

/-- A strict scaled comparison has one nonnegative rational margin.
Its left query is excluded from the lower cut and its right query belongs to it. -/
theorem scaled_lt_iff_fraction (x y : ℝ) (hx : 0 ≤ x) (m n : ℕ) (hn : 0 < n) :
    (m : ℝ) * x < (n : ℝ) * y ↔
      ∃ a b : ℕ, 0 < b ∧ ¬ (a : ℝ) / b < x ∧ ((m * a : ℕ) : ℝ) / (n * b : ℕ) < y := by
  constructor
  · intro h
    by_cases hm : m = 0
    · obtain ⟨a, b, hb, ha, _⟩ := (lt_iff_nat_fraction_margin x (x + 1) hx).mp (by linarith)
      refine ⟨a, b, hb, not_lt_of_ge ha.le, ?_⟩
      rw [scaled_fraction_lt_iff a b m n hb hn]
      simpa only [hm, Nat.cast_zero, zero_mul] using h
    · have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
      have hxR : x < ((n : ℝ) * y) / m := (lt_div_iff₀ hmR).mpr (by nlinarith)
      obtain ⟨a, b, hb, ha, hq⟩ :=
        (lt_iff_nat_fraction_margin x ((x + ((n : ℝ) * y) / m) / 2) hx).mp (by linarith)
      refine ⟨a, b, hb, not_lt_of_ge ha.le, ?_⟩
      rw [scaled_fraction_lt_iff a b m n hb hn]
      have hq' : (a : ℝ) / b < ((n : ℝ) * y) / m := by linarith
      have hmul := (lt_div_iff₀ hmR).mp hq'
      nlinarith
  · rintro ⟨a, b, hb, ha, hq⟩
    rw [scaled_fraction_lt_iff a b m n hb hn] at hq
    exact (mul_le_mul_of_nonneg_left (le_of_not_gt ha) (Nat.cast_nonneg m)).trans_lt hq

lemma reciprocal_le_density_dist_zero (ν δ : ℝ) (hν : 0 ≤ ν) (hδ : 0 ≤ δ) (hνδ : ν ≤ δ) (k : ℕ) :
    1 / (k + 1 : ℝ) ≤ dist (ν / δ) 0 ↔
      0 < δ ∧ ¬ ((k + 1 : ℝ) * ν < δ) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  by_cases hz : δ = 0
  · have hνz : ν = 0 := by linarith
    simp only [hz, hνz, zero_div, dist_self, lt_self_iff_false, false_and, iff_false]
    exact not_le.mpr (one_div_pos.mpr hk)
  · have hδp : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hz)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hν hδ), div_le_div_iff₀ hk hδp]
    simp only [hδp, true_and, not_lt, one_mul]
    rw [mul_comm ν]

lemma reciprocal_le_density_dist_one (ν δ : ℝ) (hν : 0 ≤ ν) (hδ : 0 ≤ δ) (hνδ : ν ≤ δ) (k : ℕ) :
    1 / (k + 1 : ℝ) ≤ dist (ν / δ) 1 ↔
      ¬ ((k : ℝ) * δ < (k + 1 : ℝ) * ν) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  by_cases hz : δ = 0
  · have hνz : ν = 0 := by linarith
    simp only [hz, hνz, zero_div, Real.dist_eq, zero_sub, abs_neg, abs_one, mul_zero,
      lt_self_iff_false, not_false_eq_true, iff_true]
    exact (div_le_one hk).mpr (by norm_num)
  · have hδp : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hz)
    have hdist : dist (ν / δ) 1 = 1 - ν / δ := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ((div_le_one hδp).mpr hνδ)), neg_sub]
    have hadd : 1 / (k + 1 : ℝ) + ν / δ =
        (δ + (k + 1 : ℝ) * ν) / ((k + 1 : ℝ) * δ) := by
      field_simp
    rw [hdist, le_sub_iff_add_le, hadd, div_le_one (mul_pos hk hδp), not_lt]
    constructor <;> intro h <;> nlinarith

end PolishSpaceBook.CantorTreeMeasure
