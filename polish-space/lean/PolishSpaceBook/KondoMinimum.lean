module

public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Order.WellFounded

@[expose] public section

/-! # Successive ordinal minima

Keep all candidates realizing the preceding minima; at each step minimize one
more key. This is the finite-history construction used for Kondo uniformization.
-/
namespace PolishSpaceBook.Kondo
noncomputable section
open Set
universe u v

variable {Y : Type u} (key : ℕ → Y → Ordinal.{v})

def refine (n : ℕ) (S : {S : Set Y // S.Nonempty}) : {S : Set Y // S.Nonempty} := by
  classical
  let a := wellFounded_lt.min (key n '' S.val) (S.property.image _)
  have ha : a ∈ key n '' S.val := wellFounded_lt.min_mem _ _
  exact ⟨{y ∈ S.val | key n y = a}, by
    obtain ⟨y, hy, he⟩ := ha
    exact ⟨y, hy, he⟩⟩

def candidates (S : {S : Set Y // S.Nonempty}) : ℕ → {S : Set Y // S.Nonempty}
  | 0 => S
  | n + 1 => refine key n (candidates S n)

def sample (S : {S : Set Y // S.Nonempty}) (n : ℕ) : Y :=
  (candidates key S (n + 1)).property.choose

def minimum (S : {S : Set Y // S.Nonempty}) (n : ℕ) : Ordinal.{v} :=
  key n (sample key S n)

theorem refine_subset (n : ℕ) (S : {S : Set Y // S.Nonempty}) :
    (refine key n S).val ⊆ S.val := fun _ h => h.1

theorem sample_mem (S : {S : Set Y // S.Nonempty}) (n : ℕ) :
    sample key S n ∈ (candidates key S (n + 1)).val :=
  (candidates key S (n + 1)).property.choose_spec

theorem mem_refine_iff (n : ℕ) (S : {S : Set Y // S.Nonempty})
    {z : Y} (hz : z ∈ (refine key n S).val) (y : Y) :
    y ∈ (refine key n S).val ↔ y ∈ S.val ∧ key n y = key n z := by
  change y ∈ S.val ∧ _ = _ ↔ _
  change z ∈ S.val ∧ _ = _ at hz
  rw [hz.2]

theorem minimum_le (n : ℕ) (S : {S : Set Y // S.Nonempty})
    {z : Y} (hz : z ∈ (refine key n S).val) {y : Y} (hy : y ∈ S.val) :
    key n z ≤ key n y := by
  change z ∈ S.val ∧ _ = _ at hz
  rw [hz.2]
  exact le_of_not_gt (wellFounded_lt.not_lt_min (s := key n '' S.val) ⟨y, hy, rfl⟩)

theorem mem_candidates_iff (S : {S : Set Y // S.Nonempty}) (n : ℕ) (y : Y) :
    y ∈ (candidates key S n).val ↔
      y ∈ S.val ∧ ∀ i < n, key i y = minimum key S i := by
  induction n with
  | zero => simp [candidates]
  | succ n ih =>
    rw [candidates, mem_refine_iff key n _ (sample_mem key S n), ih]
    change (_ ∧ ∀ i < n, _) ∧ key n y = minimum key S n ↔ _
    constructor
    · rintro ⟨⟨hy, hh⟩, hn⟩
      refine ⟨hy, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hh i hi
      · exact hn
    · rintro ⟨hy, hh⟩
      exact ⟨⟨hy, fun i hi => hh i (Nat.lt_succ_of_lt hi)⟩, hh n (Nat.lt_succ_self n)⟩

theorem sample_spec (S : {S : Set Y // S.Nonempty}) (n : ℕ) :
    sample key S n ∈ S.val ∧
      ∀ i ≤ n, key i (sample key S n) = minimum key S i := by
  simpa only [Nat.lt_succ_iff] using
    (mem_candidates_iff key S (n + 1) _).mp (sample_mem key S n)

theorem minimum_le_of_history (S : {S : Set Y // S.Nonempty}) (n : ℕ)
    {y : Y} (hy : y ∈ S.val) (hh : ∀ i < n, key i y = minimum key S i) :
    minimum key S n ≤ key n y :=
  minimum_le key n _ (sample_mem key S n)
    ((mem_candidates_iff key S n y).mpr ⟨hy, hh⟩)

end
end PolishSpaceBook.Kondo
