module

public import PolishSpaceBook.HilbertMinMax
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

@[expose] public section

/-! # Dimension bounds for Hilbert space min–max coordinates -/

noncomputable section

open Set

namespace PolishSpaceBook.HilbertMinMaxBounds

open HilbertMinMax

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A finite-dimensional space of larger dimension meets the orthogonal
complement of a smaller finite-dimensional space in a unit vector. -/
theorem exists_unit_mem_orthogonal (V K : Submodule 𝕜 H)
    [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 K]
    (hd : Module.finrank 𝕜 K < Module.finrank 𝕜 V) :
    ∃ x : H, x ∈ V ∧ x ∈ Kᗮ ∧ ‖x‖ = 1 := by
  let f : V →L[𝕜] K := K.orthogonalProjectionOnto.comp V.subtypeL
  have hf : f.ker ≠ ⊥ := by
    intro h
    have hi := LinearMap.ker_eq_bot.mp h
    exact (not_le_of_gt hd) (LinearMap.finrank_le_finrank_of_injective hi)
  obtain ⟨x, hx, hx0⟩ := f.ker.ne_bot_iff.mp hf
  have hnorm : ‖(x : H)‖ ≠ 0 := by
    simpa only [Submodule.norm_coe, norm_ne_zero_iff] using hx0
  have hxK : (x : H) ∈ Kᗮ :=
    K.orthogonalProjectionOnto_eq_zero_iff.mp (show K.orthogonalProjectionOnto (x : H) = 0 from hx)
  let c : 𝕜 := (‖(x : H)‖⁻¹ : ℝ)
  refine ⟨c • (x : H), V.smul_mem c x.2, Kᗮ.smul_mem c hxK, ?_⟩
  simp [c, norm_smul, inv_mul_cancel₀ hnorm]

/-- Any Rayleigh value on the unit ball is bounded by the Rayleigh supremum. -/
theorem rayleigh_le_sup (A : H →L[𝕜] H) (K : Submodule 𝕜 H)
    (x : H) (hx : x ∈ K) (hn : ‖x‖ ≤ 1) :
    RCLike.re (inner 𝕜 x (A x)) ≤ rayleighSup A K := by
  apply le_ciSup (f := fun y : UnitBall K => RCLike.re (inner 𝕜 (y.1 : H) (A y.1))) _
    (⟨⟨x, hx⟩, hn⟩ : UnitBall K)
  refine ⟨‖A‖, ?_⟩
  rintro _ ⟨y, rfl⟩
  calc
    RCLike.re (inner 𝕜 (y.1 : H) (A y.1)) ≤ ‖inner 𝕜 (y.1 : H) (A y.1)‖ :=
      RCLike.re_le_norm _
    _ ≤ ‖(y.1 : H)‖ * ‖A y.1‖ := norm_inner_le_norm _ _
    _ ≤ 1 * (‖A‖ * 1) := mul_le_mul y.2
      ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left y.2 (norm_nonneg _)))
      (norm_nonneg _) zero_le_one
    _ = ‖A‖ := by ring

/-- A quadratic lower bound on a space of dimension larger than `n` bounds
the `n`th min–max coordinate from below. -/
theorem le_minMax_of_subspace (A : H →L[𝕜] H) (V : Submodule 𝕜 H)
    [FiniteDimensional 𝕜 V] {n : ℕ} {r : ℝ}
    (hd : n < Module.finrank 𝕜 V)
    (hV : ∀ x ∈ V, r * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 x (A x))) :
    r ≤ minMax A n := by
  apply le_ciInf
  intro K
  have : FiniteDimensional 𝕜 K.1 := K.2.1
  obtain ⟨x, hxV, hxK, hxnorm⟩ := exists_unit_mem_orthogonal V K.1 (K.2.2.trans_lt hd)
  have h := hV x hxV
  simp only [hxnorm, one_pow, mul_one] at h
  exact h.trans (rayleigh_le_sup A K.1ᗮ x hxK hxnorm.le)

end PolishSpaceBook.HilbertMinMaxBounds
