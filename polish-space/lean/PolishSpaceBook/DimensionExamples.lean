module

public import PolishSpaceBook.SmallInductiveDimension
public import PolishSpaceBook.LargeInductiveDimension
public import PolishSpaceBook.CoveringDimension
public import Mathlib.Topology.Connected.Clopen

@[expose] public section

/-! # The dimension examples from clopen cylinders and connectedness -/
namespace PolishSpaceBook
open Set TopologicalSpace

/-- A nonempty second-countable T1 space with a clopen basis has value zero
for each of the three dimensions. -/
theorem dimensions_zero_of_clopen_basis (X : Type) [TopologicalSpace X]
    [T1Space X] [SecondCountableTopology X] [Nonempty X] (h : IsZeroDimensional X) :
    smallInductiveDimension X = (0 : ℕ∞) ∧
      largeInductiveDimension X = (0 : ℤ) ∧ coveringDimension X = (0 : ℤ) := by
  have hs := (zero_dimensional_iff_small_inductive X).mp h
  have hl := (zero_dimensional_iff_big_inductive X).mp h
  have hc : HasCoveringDimensionLEZero X := (zero_dimensional_iff_lebesgue_covering_dimension X).mp h
  refine ⟨smallInductiveDimension_zero_of_bound X hs,
    largeInductiveDimension_zero_of_bound X hl, ?_⟩
  apply coveringDimension_eq_of_least X
    ((coveringDimensionBound_zero_iff X).mpr hc)
  intro k hk
  omega

/-@ booklink:
  source: polish-space-book/appendix-metric-spaces.md
  exclude-books: polish-space-ch1
  target: statement
  kind: remark
  title: Reading the examples in the main text
-/
/-- The existing clopen-cylinder basis gives all three numeric dimensions of Cantor space. -/
theorem cantor_space_dimensions_zero :
    smallInductiveDimension cantor_space = (0 : ℕ∞) ∧
      largeInductiveDimension cantor_space = (0 : ℤ) ∧
      coveringDimension cantor_space = (0 : ℤ) :=
  dimensions_zero_of_clopen_basis cantor_space cantor_space_zero_dimensional

/-- The same cylinder argument applies to Baire space. -/
theorem baire_space_dimensions_zero :
    smallInductiveDimension baire_space = (0 : ℕ∞) ∧
      largeInductiveDimension baire_space = (0 : ℤ) ∧
      coveringDimension baire_space = (0 : ℤ) :=
  dimensions_zero_of_clopen_basis baire_space baire_space_zero_dimensional

/-- Connectedness forces a clopen subset of the real line to be empty or universal. -/
theorem real_clopen_iff (V : Set ℝ) : IsClopen V ↔ V = ∅ ∨ V = univ :=
  isClopen_iff

/-- A clopen basis would refine a proper open neighborhood by a nonempty clopen set,
contradicting connectedness. -/
theorem real_not_zero_dimensional : ¬IsZeroDimensional ℝ := by
  intro h
  obtain ⟨V, hV, hx, hVU⟩ := h.exists_subset_of_mem_open
    (show (0 : ℝ) ∈ Iio 1 by norm_num) isOpen_Iio
  rcases (real_clopen_iff V).mp hV with he | he
  · simp [he] at hx
  · have hbad : (1 : ℝ) ∈ Iio 1 := hVU (he ▸ mem_univ 1)
    exact lt_irrefl (1 : ℝ) hbad

end PolishSpaceBook
