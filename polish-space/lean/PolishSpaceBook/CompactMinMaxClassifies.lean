module

public import PolishSpaceBook.CompactMinMaxCounting
public import PolishSpaceBook.SpectralCountRecovery
public import PolishSpaceBook.EigenbasisMultiplicity

@[expose] public section

/-! # Compact self-adjoint classification by signed min–max lists and kernel dimension -/

noncomputable section

open Set TopologicalSpace
open scoped ENNReal

namespace PolishSpaceBook.CompactMinMaxClassifies

open HilbertMinMax HilbertProjectionTrace CompactSpectralUnitary CompactEigenbasis
  CompactMinMaxCounting SpectralCountRecovery EigenbasisMultiplicity

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Positive threshold comparisons determine a nonnegative real number. -/
theorem nonneg_eq_of_positive_cuts {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ r > 0, r < a ↔ r < b) : a = b := by
  apply le_antisymm
  · by_contra hn
    obtain ⟨r, hbr, hra⟩ := exists_between (lt_of_not_ge hn)
    exact (not_lt_of_ge hbr.le) ((h r (hb.trans_lt hbr)).mp hra)
  · by_contra hn
    obtain ⟨r, har, hrb⟩ := exists_between (lt_of_not_ge hn)
    exact (not_lt_of_ge har.le) ((h r (ha.trans_lt har)).mpr hrb)

/-- Intertwining unitaries preserve the min–max sequence. -/
theorem minMax_eq_of_unitarilyEquivalent
    (A B : H →L[𝕜] H) (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hBc : IsCompactOperator B) (hBs : IsSelfAdjoint B)
    (h : UnitarilyEquivalent A B) : minMax A = minMax B := by
  classical
  obtain ⟨U, hU⟩ := h
  obtain ⟨ι, b, ev, he⟩ := exists_eigenbasis A hAc hAs
  let c : HilbertBasis ι 𝕜 H := HilbertBasis.ofRepr (U.symm.trans b.repr)
  have hc (i : ι) : c i = U (b i) := by
    change U (b.repr.symm (lp.single 2 i (1 : 𝕜))) = U (b i)
    rw [b.repr_symm_single]
  have hBe (i : ι) : B (c i) = (ev i : 𝕜) • c i := by
    rw [hc, ← hU, he, map_smul]
  funext n
  apply nonneg_eq_of_positive_cuts (minMax_nonneg A n) (minMax_nonneg B n)
  intro r hr
  rw [minMax_gt_iff_count A hAc hAs b ev he hr,
    minMax_gt_iff_count B hBc hBs c ev hBe hr]

/-- Equality of positive min–max lists recovers each positive eigenspace dimension. -/
theorem positive_eigen_dimensions_eq_of_minMax_eq
    (A B : H →L[𝕜] H) (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hBc : IsCompactOperator B) (hBs : IsSelfAdjoint B)
    (h : minMax A = minMax B) {μ : ℝ} (hμ : 0 < μ) :
    hilbertDimension 𝕜 (Eigen A (μ : 𝕜)) = hilbertDimension 𝕜 (Eigen B (μ : 𝕜)) := by
  classical
  obtain ⟨ι, b, ev, he⟩ := exists_eigenbasis A hAc hAs
  obtain ⟨κ, c, ew, hf⟩ := exists_eigenbasis B hBc hBs
  have hcounts (r : ℝ) (hr : 0 < r) :
      {i | r < ev i}.ncard = {j | r < ew j}.ncard := by
    apply eq_of_forall_lt_iff
    intro n
    rw [← minMax_gt_iff_count A hAc hAs b ev he hr,
      ← minMax_gt_iff_count B hBc hBs c ew hf hr, h]
  have hcard := positive_fiber_ncard_eq ev ew
    (fun r hr => finite_eigenvalue_ge A hAc hAs b ev he hr)
    (fun r hr => finite_eigenvalue_ge B hBc hBs c ew hf hr) hcounts hμ
  have hfinA : {i | ev i = μ}.Finite :=
    (finite_eigenvalue_ge A hAc hAs b ev he hμ).subset (by intro i hi; exact hi.ge)
  have hfinB : {j | ew j = μ}.Finite :=
    (finite_eigenvalue_ge B hBc hBs c ew hf hμ).subset (by intro j hj; exact hj.ge)
  rw [dimension_eigen_eq_ncard_fiber A hAs b ev he μ hfinA,
    dimension_eigen_eq_ncard_fiber B hBs c ew hf μ hfinB, hcard]

omit [CompleteSpace H] in
theorem eigen_neg (A : H →L[𝕜] H) (μ : 𝕜) : Eigen (-A) μ = Eigen A (-μ) := by
  ext x
  simp only [Eigen, Module.End.mem_eigenspace_iff, ContinuousLinearMap.toLinearMap_neg,
    LinearMap.neg_apply, neg_smul]
  exact neg_eq_iff_eq_neg

omit [CompleteSpace H] in
theorem eigen_zero (A : H →L[𝕜] H) : Eigen A 0 = A.ker :=
  Module.End.eigenspace_zero A.toLinearMap

omit [CompleteSpace H] in
/-- Negation preserves an intertwining unitary. -/
theorem unitarilyEquivalent_neg {A B : H →L[𝕜] H}
    (h : UnitarilyEquivalent A B) : UnitarilyEquivalent (-A) (-B) := by
  obtain ⟨U, hU⟩ := h
  exact ⟨U, fun x => by simpa using congrArg Neg.neg (hU x)⟩

variable [SeparableSpace H]

/-- Both signed min–max lists and the kernel dimension are a complete invariant. -/
theorem unitarilyEquivalent_iff_signed_minMax_kernel
    (A B : H →L[𝕜] H) (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hBc : IsCompactOperator B) (hBs : IsSelfAdjoint B) :
    UnitarilyEquivalent A B ↔
      minMax A = minMax B ∧ minMax (-A) = minMax (-B) ∧ kernelDimension A = kernelDimension B := by
  constructor
  · intro h
    refine ⟨minMax_eq_of_unitarilyEquivalent A B hAc hAs hBc hBs h,
      minMax_eq_of_unitarilyEquivalent (-A) (-B) hAc.neg hAs.neg hBc.neg hBs.neg (unitarilyEquivalent_neg h), ?_⟩
    have hd := eigenspace_dimensions_eq_of_unitarilyEquivalent A B h (0 : 𝕜)
    rw [eigen_zero, eigen_zero] at hd
    exact hd
  · rintro ⟨hp, hn, hk⟩
    apply unitarilyEquivalent_of_eigenspace_dimensions A B hAc hAs hBc hBs
    intro μ
    by_cases hreal : (RCLike.re μ : 𝕜) = μ
    · rw [← hreal]
      rcases lt_trichotomy (RCLike.re μ) 0 with hneg | hz | hpos
      · have hd := positive_eigen_dimensions_eq_of_minMax_eq (-A) (-B)
          hAc.neg hAs.neg hBc.neg hBs.neg hn (neg_pos.mpr hneg)
        rw [eigen_neg, eigen_neg, RCLike.ofReal_neg, neg_neg] at hd
        exact hd
      · rw [hz, RCLike.ofReal_zero, eigen_zero, eigen_zero]
        exact hk
      · exact positive_eigen_dimensions_eq_of_minMax_eq A B hAc hAs hBc hBs hp hpos
    · rw [eigen_eq_bot_of_nonreal A hAs hreal, eigen_eq_bot_of_nonreal B hBs hreal]

end PolishSpaceBook.CompactMinMaxClassifies
