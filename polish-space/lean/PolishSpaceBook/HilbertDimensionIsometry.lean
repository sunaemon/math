module

public import PolishSpaceBook.HilbertKernelBorel

@[expose] public section

/-!
# Hilbert dimension and linear isometries

For separable real or complex Hilbert spaces the finite-or-infinite dimension
is a complete invariant for linear isometric isomorphism. The infinite case
uses countability of orthonormal bases, rather than algebraic `finrank`.
-/

noncomputable section

open Set TopologicalSpace
open scoped ENNReal

namespace PolishSpaceBook.HilbertDimensionIsometry

open HilbertProjectionTrace HilbertKernelBorel

universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H G : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- Linear isomorphisms preserve finite-or-infinite dimension. -/
theorem hilbertDimension_eq_of_linearEquiv (e : H ≃ₗ[𝕜] G) :
    hilbertDimension 𝕜 H = hilbertDimension 𝕜 G := by
  classical
  have hf : FiniteDimensional 𝕜 H ↔ FiniteDimensional 𝕜 G := by
    constructor
    · intro h
      let := h
      exact e.finiteDimensional
    · intro h
      let := h
      exact e.symm.finiteDimensional
  simp only [hilbertDimension, hf, e.finrank_eq]

variable [CompleteSpace H] [CompleteSpace G] [SeparableSpace H] [SeparableSpace G]

/-- Equal extended Hilbert dimensions give a unitary or orthogonal isomorphism. -/
theorem nonempty_linearIsometryEquiv_of_dimension_eq
    (h : hilbertDimension 𝕜 H = hilbertDimension 𝕜 G) : Nonempty (H ≃ₗᵢ[𝕜] G) := by
  classical
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis 𝕜 H
  obtain ⟨κ, c, _⟩ := exists_hilbertBasis 𝕜 G
  have : Countable ι := countable_orthonormal b.orthonormal
  have : Countable κ := countable_orthonormal c.orthonormal
  rw [hilbertDimension_eq_card b, hilbertDimension_eq_card c, ENat.toENNReal_inj] at h
  have hcard : Cardinal.mk ι = Cardinal.mk κ :=
    (Cardinal.toENat_eq_iff_of_le_aleph0 Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0).mp h
  obtain ⟨e⟩ := Cardinal.eq.mp hcard
  have htotal : ⊤ ≤ (Submodule.span 𝕜 (range (c ∘ e))).topologicalClosure := by
    rw [e.surjective.range_comp, c.dense_span]
  let c' := HilbertBasis.mk (c.orthonormal.comp e e.injective) htotal
  exact ⟨b.repr.trans c'.repr.symm⟩

/-- Finite-or-infinite Hilbert dimension classifies separable Hilbert spaces. -/
theorem nonempty_linearIsometryEquiv_iff_dimension_eq :
    Nonempty (H ≃ₗᵢ[𝕜] G) ↔ hilbertDimension 𝕜 H = hilbertDimension 𝕜 G := by
  constructor
  · rintro ⟨e⟩
    exact hilbertDimension_eq_of_linearEquiv e.toLinearEquiv
  · exact nonempty_linearIsometryEquiv_of_dimension_eq

end PolishSpaceBook.HilbertDimensionIsometry
