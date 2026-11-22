module

public import PolishSpaceBook.E0Nonsmooth
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

namespace PolishSpaceBook
open MeasureTheory MeasurableSpace Set Filter

universe u v

/-- The full-measure sides of a countable separating family have a common
point, and separation makes the function constant on their intersection. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To see this, take a countable point-separating Borel family in the target and
    intersect the full-measure side of each inverse image; all points in this conull intersection have the same value.
-/
theorem measurable_zero_one_ae_constant
    {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    [CountablySeparated Y] (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → Y} (hf : Measurable f)
    (hzero : ∀ B : Set Y, MeasurableSet B → μ (f ⁻¹' B) = 0 ∨ μ (f ⁻¹' B) = 1) :
    ∃ c : Y, ∀ᵐ x ∂μ, f x = c := by
  obtain ⟨S, hS, hsep⟩ := exists_seq_separating Y (p := MeasurableSet)
    MeasurableSet.univ Set.univ
  have hsides : ∀ n, ∀ᵐ x ∂μ, (f x ∈ S n ↔ μ (f ⁻¹' S n) = 1) := by
    intro n
    rcases hzero (S n) (hS n) with hz | ho
    · have hnot : ∀ᵐ x ∂μ, f x ∉ S n := by
        apply ae_iff.mpr
        change μ {x | ¬ ¬ f x ∈ S n} = 0
        convert hz using 2
        ext x
        simp
      filter_upwards [hnot] with x hx
      simp [hx, hz]
    · have hmem : ∀ᵐ x ∂μ, f x ∈ S n := by
        apply ae_iff.mpr
        rw [show {x | ¬ f x ∈ S n} = (f ⁻¹' S n)ᶜ from rfl,
          measure_compl (hf (hS n)) (measure_ne_top μ _), measure_univ, ho, tsub_self]
      filter_upwards [hmem] with x hx
      simp [hx, ho]
  have hall := ae_all_iff.mpr hsides
  obtain ⟨x₀, hx₀⟩ := hall.exists
  refine ⟨f x₀, ?_⟩
  filter_upwards [hall] with x hx
  exact hsep _ (mem_univ _) _ (mem_univ _) (fun n => (hx n).trans (hx₀ n).symm)

/-- An eventual-equality invariant set is invariant under every finite-support
coordinate permutation. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    These three theorems explain several facts used elsewhere in the text. The non-smoothness of $\EventualEqualityER$
    in §{sec:e0-glimm-effros} reduces to \termuseas{Hewitt--Savage 0-1 law}{Hewitt--Savage}: every
    $\EventualEqualityER$-invariant Borel set is invariant under finite-support permutations for the fair-coin product.
-/
theorem e0_invariant_finite_permutation {A : Set (ℕ → Bool)}
    (hinv : ∀ x y, E0 x y → (x ∈ A ↔ y ∈ A))
    (σ : Equiv.Perm ℕ) (hσ : {n | σ n ≠ n}.Finite) (x : ℕ → Bool) :
    x ∘ σ ∈ A ↔ x ∈ A :=
  (hinv x (x ∘ σ) (e0_finite_permutation σ hσ x)).symm

/-- Specialization to the actual fair-coin product and eventual equality,
using the finite-permutation Hewitt--Savage corollary. -/
/-@ booklink:
  source: polish-space-book/borel-measures-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Hence any $\EventualEqualityER$-invariant Borel function with values in a standard Borel space is
    $\mu$-almost everywhere constant.
-/
theorem e0_invariant_standardBorel_ae_constant
    {Y : Type v} [MeasurableSpace Y] [StandardBorelSpace Y]
    {f : (ℕ → Bool) → Y} (hf : Measurable f)
    (hinv : ∀ x y, E0 x y → f x = f y) :
    ∃ c : Y, ∀ᵐ x ∂fairCoinProduct, f x = c := by
  apply measurable_zero_one_ae_constant fairCoinProduct hf
  intro B hB
  apply e0_saturated_zero_one (hf hB)
  intro x y hxy
  change f x ∈ B ↔ f y ∈ B
  rw [hinv x y hxy]

end PolishSpaceBook
