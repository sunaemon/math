module

public import PolishSpaceBook.LambdaInvariantClosure

@[expose] public section

/-! # The actual invariant-test kernel and its Borel properties -/

namespace PolishSpaceBook
open Set MeasureTheory NamedLambda NamedLambda.AlphaTerm
namespace LambdaTree
local instance kernelListEncoding : Encodable (List ℕ) := NatListCode.encodable
local instance kernelPairEncoding : Encodable (List ℕ × List ℕ) := wordPairEncodable

theorem projected_empty_set (ε : ℕ → ℕ) : Projected ε (∅ : Set (ℕ → ℕ)) := by
  have ht : LambdaRelative.DecidablePredicate ε (fun _ : List ℕ × List ℕ => False) := by
    apply numericalDecision (numericalConstant_computes 0) ε
    · intro z h; exact False.elim h
    · intro z h; rfl
  simpa using projected_finiteChecks ht

theorem projected_univ (ε : ℕ → ℕ) : Projected ε (univ : Set (ℕ → ℕ)) := by
  simpa using projected_cyl ε []

/-- This is a classical enumeration, with no claim of recursive uniformity. -/
theorem exists_invariantTests (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ)) :
    ∃ W : ℕ → Set (ℕ → ℕ),
      (∀ n, Complemented ε (W n) ∧ ERInvariant E (W n)) ∧
      ∀ x y, (invariantSetoid ε E).r x y ↔ (invariantTestSetoid W).r x y := by
  let tests := {C : Set (ℕ → ℕ) | Complemented ε C ∧ ERInvariant E C}
  have hc : tests.Countable :=
    (countable_projected ε).mono (fun _ h => h.1.1)
  have he : (∅ : Set (ℕ → ℕ)) ∈ tests := by
    refine ⟨⟨projected_empty_set _, ?_⟩, ?_⟩
    · simpa using projected_univ ε
    · intro x y _
      rfl
  obtain ⟨W, hW⟩ := hc.exists_eq_range ⟨∅, he⟩
  have hw (n : ℕ) : W n ∈ tests := by rw [hW]; exact mem_range_self n
  refine ⟨W, hw, ?_⟩
  intro x y
  constructor
  · intro h n
    exact h (W n) (hw n).1 (hw n).2
  · intro h C hc hi
    obtain ⟨n, rfl⟩ := hW ▸ (show C ∈ tests from ⟨hc, hi⟩)
    exact h n

theorem invariantSetoid_measurable (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ)) :
    MeasurableSet {p : (ℕ → ℕ) × (ℕ → ℕ) | (invariantSetoid ε E).r p.1 p.2} := by
  obtain ⟨W, hW, heq⟩ := exists_invariantTests ε E
  simpa only [heq] using invariantTestSetoid_measurable W (fun n => (hW n).1.measurableSet)

theorem smooth_of_eq_invariantSetoid (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ))
    (heq : ∀ x y, E.r x y ↔ (invariantSetoid ε E).r x y) : Smooth E.r := by
  obtain ⟨W, hW, htests⟩ := exists_invariantTests ε E
  exact smooth_of_invariant_tests_complete E W (fun n => (hW n).1.measurableSet)
    (fun x y => (heq x y).trans (htests x y))

theorem invariantKernel_nonempty (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ))
    (hns : ¬ Smooth E.r) : (equivalenceGapKernel E (invariantSetoid ε E)).Nonempty := by
  classical
  by_contra hn
  apply hns
  apply smooth_of_eq_invariantSetoid ε E
  intro x y
  refine ⟨relation_le_invariantSetoid ε E, ?_⟩
  intro hxy
  by_contra hne
  exact hn ⟨x, y, hxy, hne⟩

/-- The actual kernel is ordinarily analytic for Borel E. No new parameter is
chosen to turn this ordinary assertion into an effective one. -/
theorem invariantKernel_analytic (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ))
    (hE : MeasurableSet {p : (ℕ → ℕ) × (ℕ → ℕ) | E.r p.1 p.2}) :
    AnalyticSet (equivalenceGapKernel E (invariantSetoid ε E)) := by
  obtain ⟨W, hW, heq⟩ := exists_invariantTests ε E
  have heqKernel : equivalenceGapKernel E (invariantSetoid ε E) =
      equivalenceGapKernel E (invariantTestSetoid W) := by
    ext x
    simp only [equivalenceGapKernel, mem_ofPred_eq, heq]
  rw [heqKernel]
  exact hkl_gap_kernel_analytic E hE W (fun n => (hW n).1.measurableSet)

/-- Projecting the F-but-not-E relation gives a kernel code in the same
parameter. `projected_hklKernel` supplies the graph code explicitly. -/
theorem projected_invariantKernel (ε : ℕ → ℕ) (E : Setoid (ℕ → ℕ))
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (hF : ProjectedRelation ε (invariantSetoid ε E).r) :
    Projected ε (equivalenceGapKernel E (invariantSetoid ε E)) := by
  have hgap := projected_relationGapImage E (invariantSetoid ε E)
    hF hneE (projected_univ ε)
  have heq : relationGapImage E (invariantSetoid ε E) univ =
      equivalenceGapKernel E (invariantSetoid ε E) := by
    ext x
    constructor
    · rintro ⟨y, _, hyx, hn⟩
      exact ⟨y, (invariantSetoid ε E).symm hyx, fun hxy => hn (E.symm hxy)⟩
    · rintro ⟨y, hxy, hn⟩
      exact ⟨y, mem_univ _, (invariantSetoid ε E).symm hxy, fun hyx => hn (E.symm hyx)⟩
  exact heq ▸ hgap

end LambdaTree
end PolishSpaceBook
