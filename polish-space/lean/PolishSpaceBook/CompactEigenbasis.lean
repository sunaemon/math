module

public import PolishSpaceBook.CompactSpectralUnitary

@[expose] public section

/-! # A Hilbert basis of eigenvectors for a compact self-adjoint operator -/

noncomputable section

open Set Filter TopologicalSpace
open scoped ENNReal Topology

namespace PolishSpaceBook.CompactEigenbasis

open CompactSpectralUnitary

universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Choosing bases in the closed eigenspaces and taking their disjoint union
gives a Hilbert basis of genuine eigenvectors, including vectors in the kernel. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Choose an orthonormal eigenbasis for $A$, including a basis of its kernel.
-/
theorem exists_eigenbasis (A : H →L[𝕜] H)
    (hc : IsCompactOperator A) (hs : IsSelfAdjoint A) :
    ∃ (ι : Type (max u v)) (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ),
      ∀ i, A (b i) = (ev i : 𝕜) • b i := by
  classical
  have hb (μ : 𝕜) := exists_hilbertBasis 𝕜 (Eigen A μ)
  choose I b hb using hb
  let ι := Σ μ : 𝕜, I μ
  let w : ι → H := fun i => (b i.1 i.2 : H)
  have hw : Orthonormal 𝕜 w :=
    hs.isSymmetric.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
      (fun μ => (b μ).orthonormal)
  let W := Submodule.span 𝕜 (range w)
  have heig : ∀ μ, Eigen A μ ≤ W.topologicalClosure := by
    intro μ x hx
    have hsum := (Eigen A μ).subtypeL.hasSum ((b μ).hasSum_repr ⟨x, hx⟩)
    apply W.isClosed_topologicalClosure.mem_of_tendsto hsum
    filter_upwards [] with s
    apply Submodule.sum_mem
    intro i _
    change (b μ).repr ⟨x, hx⟩ i • (b μ i : H) ∈ W.topologicalClosure
    apply Submodule.smul_mem
    apply W.le_topologicalClosure
    exact Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩
  have htotal : ⊤ ≤ W.topologicalClosure := by
    have hle := iSup_le heig
    have hclose := Submodule.topologicalClosure_mono hle
    rw [W.isClosed_topologicalClosure.submodule_topologicalClosure_eq] at hclose
    have hspec : (⨆ μ, Eigen A μ).topologicalClosure = ⊤ :=
      Submodule.topologicalClosure_eq_top_iff.mpr
        (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs.isSymmetric)
    rwa [hspec] at hclose
  let e := HilbertBasis.mk hw htotal
  refine ⟨ι, e, fun i => RCLike.re i.1, ?_⟩
  intro i
  have hAi : A (w i) = i.1 • w i := Module.End.mem_eigenspace_iff.mp (b i.1 i.2).2
  have hne : w i ≠ 0 := by
    intro hz
    have hn := hw.norm_eq_one i
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hreal : (RCLike.re i.1 : 𝕜) = i.1 :=
    RCLike.conj_eq_iff_re.mp (hs.isSymmetric.conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hAi, hne⟩))
  simpa only [e, HilbertBasis.coe_mk, hreal] using hAi

end PolishSpaceBook.CompactEigenbasis
