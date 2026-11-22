module

public import PolishSpaceBook.LambdaRationalCodes
public import PolishSpaceBook.CauchyNamesPolishRepresentations
public import Mathlib.Topology.Instances.Rat

@[expose] public section

/-! # The rational-code Cauchy representation of the real line -/
namespace PolishSpaceBook.LambdaIndexPCA

/-- Enumerate all rationals by the existing noncanonical signed-numerator codes. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: construction
  title: Doubling computable reals
-/
def rationalPoint (n : ℕ) : ℝ := (RationalCode.ofNat n).value

theorem rationalPoint_dense : DenseRange rationalPoint := by
  apply Rat.denseRange_cast.mono
  rintro x ⟨q,rfl⟩
  obtain ⟨c,hc⟩ := RationalCode.value_surjective q
  exact ⟨c.natCode,by simp [rationalPoint,hc]⟩

/-- This is the Cauchy representation already used in the book, for the explicit rational enumeration. -/
noncomputable def realRepresentation : Representation ℝ :=
  cauchyRepresentationObject rationalPoint rationalPoint_dense


end PolishSpaceBook.LambdaIndexPCA
