module

public import PolishSpaceBook.BorelStructure

@[expose] public section

/-! # Measurability and countable unions in the Borel hierarchy

These helpers expose the union and complement clauses used in rank inductions.
-/
namespace PolishSpaceBook
open Set

/-- Each set in an additive Borel level is measurable for the Borel sigma algebra. -/
theorem measurableSet_of_mem_borelSigma {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (α : Ordinal) {A : Set X}
    (hA : A ∈ borelSigma α) : MeasurableSet A := by
  revert A
  induction α using WellFoundedLT.induction with
  | _ α ih =>
    intro A hA
    by_cases hα : α ≤ 1
    · rw [borelSigma, ite_eq_left hα] at hA
      exact hA.measurableSet
    · rw [borelSigma, ite_eq_right hα] at hA
      obtain ⟨f, hf, rfl⟩ := hA
      apply MeasurableSet.iUnion
      intro n
      obtain ⟨β, hβ⟩ := hf n
      simpa only [compl_compl] using (ih β.1 β.2.2 hβ).compl

/-- The multiplicative version follows by complementation. -/
theorem measurableSet_of_mem_borelPi {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (α : Ordinal) {A : Set X}
    (hA : A ∈ borelPi α) : MeasurableSet A := by
  simpa only [compl_compl] using (measurableSet_of_mem_borelSigma α hA).compl

/-- Countable unions may be indexed by any countable type, including an empty one. -/
theorem borelSigma_iUnion_countable {X I : Type*} [MetricSpace X] [Countable I]
    {α : Ordinal} (hα : 1 ≤ α) {A : I → Set X} (hA : ∀ i, A i ∈ borelSigma α) :
    (⋃ i, A i) ∈ borelSigma α := by
  cases isEmpty_or_nonempty I with
  | inl hI =>
    simp only [iUnion_of_empty]
    exact borelSigma_mono le_rfl hα (by rw [borelSigma_one]; exact isOpen_empty)
  | inr hI =>
    obtain ⟨f, hf⟩ := exists_surjective_nat I
    have he : (⋃ n, A (f n)) = ⋃ i, A i := iUnion_congr_of_surjective f hf (fun _ => rfl)
    rw [← he]
    exact borelSigma_iUnion fun n => hA (f n)

end PolishSpaceBook
