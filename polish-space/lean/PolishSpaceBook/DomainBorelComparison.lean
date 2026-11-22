module

public import PolishSpaceBook.DomainTheoryQuasiPolishSpaces
public import PolishSpaceBook.BorelStructure
public import Mathlib.Topology.GDelta.MetrizableSpace

@[expose] public section

namespace PolishSpaceBook
open Set TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [PseudoMetrizableSpace X]

/-- On a metrizable space the generalized second multiplicative class is exactly Gδ. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    On metrizable spaces this agrees with the classical Borel hierarchy used in §{sec:borel-hierarchy}.
-/
theorem generalizedPi02_iff_isGdelta (A : Set X) : GeneralizedPi02 A ↔ IsGδ A := by
  constructor
  · intro h
    obtain ⟨U, V, hU, hV, rfl⟩ := (generalizedPi02_iff A).mp h
    exact IsGδ.iInter (fun n => (hU n).isClosed_compl.isGδ.union (hV n).isGδ)
  · intro h
    obtain ⟨V, hV, hA⟩ := h.eq_iInter_nat
    apply (generalizedPi02_iff A).mpr
    exact ⟨fun _ => univ, V, fun _ => isOpen_univ, hV, by simpa using hA⟩

/-- The dual generalized additive class is the ordinary countable union of closed sets. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    On metrizable spaces this agrees with the classical Borel hierarchy used in §{sec:borel-hierarchy}.
-/
theorem generalizedSigma02_iff_isFsigma (A : Set X) : GeneralizedSigma02 A ↔ IsFsigma A := by
  rw [isFsigma_iff_isGδ_compl]
  simpa only [GeneralizedPi02, compl_compl] using generalizedPi02_iff_isGdelta Aᶜ

end PolishSpaceBook
