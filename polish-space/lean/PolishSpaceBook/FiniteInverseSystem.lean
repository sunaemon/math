module

public import PolishSpaceBook.EventuallyBijectiveSystem
public import Mathlib.Order.KonigLemma

@[expose] public section

/-! # Coherent branches through finite levels

Kőnig's lemma supplies the compatible choices needed when locally finite
families of neighborhoods are read along a fixed ambient point.
-/
noncomputable section
namespace PolishSpaceBook.NatInverseSystem
universe u
variable (S : NatInverseSystem.{u})

/-- Finite projections compose, without any surjectivity assumption. -/
theorem down_down (n : ℕ) (a : S.Obj n) (j i : ℕ) (hj : j ≤ n) (hi : i ≤ j) :
    S.down j (S.down n a j hj) i hi = S.down n a i (hi.trans hj) := by
  induction n generalizing j i with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    simp only [S.down_self]
  | succ n ih =>
    by_cases h : j = n+1
    · subst j
      rw [S.down_self]
    · have hii : i ≠ n+1 := by omega
      simp only [down, dite_eq_right h, dite_eq_right hii]
      exact ih (S.step n a) j i (by omega) hi

/-- Every nonempty finite tower has a coherent branch. Bonding maps need not
be surjective; infinitely extendable choices are obtained by Kőnig's lemma. -/
theorem nonempty_limit_of_finite [∀ i, Finite (S.Obj i)] [∀ i, Nonempty (S.Obj i)] :
    Nonempty S.Limit := by
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite
    (fun {i j} hij a => S.down j a i hij) (fun _ _ => S.down_self _ _)
    (fun i j k hij hjk a => S.down_down k a j i hjk hij)
    (fun i _ => Set.toFinite _)
  refine ⟨⟨f, ?_⟩⟩
  intro i
  have h := hf (Nat.le_succ i)
  simpa only [down, dite_eq_right (show i ≠ i+1 by omega), S.down_self] using h

end PolishSpaceBook.NatInverseSystem
