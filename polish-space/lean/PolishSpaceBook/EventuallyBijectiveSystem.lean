module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic

@[expose] public section

/-! # Inverse systems with eventually bijective bonding maps

A stable coordinate determines a compatible family uniquely. Earlier coordinates
are obtained by finite projection; later ones are obtained by the unique inverse
of each bijective bonding map. These are ordinary set-theoretic constructions,
with no claim of effective selection of inverse images.
-/
noncomputable section
namespace PolishSpaceBook
universe u

structure NatInverseSystem where
  Obj : ℕ → Type u
  step : ∀ i, Obj (i+1) → Obj i

namespace NatInverseSystem
variable (S : NatInverseSystem.{u})

/-- Finite projection to any earlier coordinate. -/
def down : (n : ℕ) → S.Obj n → (i : ℕ) → i ≤ n → S.Obj i
  | 0, a, i, hi => (Nat.eq_zero_of_le_zero hi).symm ▸ a
  | n+1, a, i, hi => if h : i = n+1 then h.symm ▸ a
    else down n (S.step n a) i (by omega)

@[simp] theorem down_self (n : ℕ) (a : S.Obj n) : S.down n a n le_rfl = a := by
  cases n <;> simp [down]

/-- A family satisfying every bonding equation. -/
abbrev Limit := {x : ∀ i, S.Obj i // ∀ i, S.step i (x (i+1)) = x i}

/-- Finite projections of a compatible family recover its earlier coordinates. -/
theorem down_eq (x : S.Limit) (n i : ℕ) (hi : i ≤ n) : S.down n (x.val n) i hi = x.val i := by
  induction n generalizing i with
  | zero =>
    have h : i = 0 := by omega
    subst i
    rfl
  | succ n ih =>
    by_cases h : i = n+1
    · subst i; exact S.down_self _ _
    · simp only [down, dite_eq_right h]
      rw [x.property n]
      exact ih i (by omega)

/-- Adjacent finite projections satisfy the same bonding equation. -/
theorem step_down (n : ℕ) (a : S.Obj n) (i : ℕ) (hi : i+1 ≤ n) :
    S.step i (S.down n a (i+1) hi) = S.down n a i (by omega) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    by_cases h : i = n
    · subst i
      simp [down]
    · have h₁ : i+1 ≠ n+1 := by omega
      have h₂ : i ≠ n+1 := by omega
      simp only [down,dite_eq_right h₁,dite_eq_right h₂]
      exact ih (S.step n a) i (by omega)

variable {S} {K : ℕ}

/-- Recursive extension along the unique inverses after the stable stage. -/
def tail (h : ∀ i ≥ K, Function.Bijective (S.step i)) (a : S.Obj K) :
    (t : ℕ) → S.Obj (K+t)
  | 0 => a
  | t+1 => (Equiv.ofBijective (S.step (K+t)) (h (K+t) (by omega))).symm (tail h a t)

@[simp] theorem step_tail (h : ∀ i ≥ K, Function.Bijective (S.step i)) (a : S.Obj K) (t : ℕ) :
    S.step (K+t) (tail h a (t+1)) = tail h a t := by
  exact (Equiv.ofBijective (S.step (K+t)) (h (K+t) (by omega))).apply_symm_apply _

/-- Join finite downward projection and recursive upward extension at K. -/
def extend (h : ∀ i ≥ K, Function.Bijective (S.step i)) (a : S.Obj K) (i : ℕ) : S.Obj i :=
  if hi : i ≤ K then S.down K a i hi
  else (show K + (i-K) = i by omega) ▸ tail h a (i-K)

@[simp] theorem extend_at_add (h : ∀ i ≥ K, Function.Bijective (S.step i))
    (a : S.Obj K) (t : ℕ) : extend h a (K+t) = tail h a t := by
  cases t with
  | zero => simp [extend,tail]
  | succ t =>
    simp only [extend, dite_eq_right (show ¬ K+(t+1) ≤ K by omega)]
    apply eq_of_heq
    have ht : HEq (tail h a (K+(t+1)-K)) (tail h a (t+1)) := by
      rw [Nat.add_sub_cancel_left]
    exact (eqRec_heq _ _).trans ht

/-- The joined family satisfies all bonding equations, including the seam at K. -/
theorem extend_compatible (h : ∀ i ≥ K, Function.Bijective (S.step i)) (a : S.Obj K) (i : ℕ) :
    S.step i (extend h a (i+1)) = extend h a i := by
  by_cases hi : i < K
  · simp only [extend,dite_eq_left (show i+1 ≤ K by omega),dite_eq_left (show i ≤ K by omega)]
    exact S.step_down K a i (by omega)
  · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le (show K ≤ i by omega)
    change S.step (K+t) (extend h a (K+(t+1))) = extend h a (K+t)
    rw [extend_at_add,extend_at_add]
    exact step_tail h a t

/-- A point at a stable stage extends to a compatible family. -/
def lift (h : ∀ i ≥ K, Function.Bijective (S.step i)) (a : S.Obj K) : S.Limit :=
  ⟨extend h a,extend_compatible h a⟩

@[simp] theorem lift_at (h : ∀ i ≥ K, Function.Bijective (S.step i)) (a : S.Obj K) :
    (lift h a).val K = a := by
  simpa only [lift, Nat.add_zero,tail] using extend_at_add h a 0

/-- No additional choices remain once a stable coordinate is fixed. -/
theorem limit_ext (h : ∀ i ≥ K, Function.Bijective (S.step i))
    {x y : S.Limit} (hK : x.val K = y.val K) : x = y := by
  apply Subtype.ext
  funext i
  by_cases hi : i ≤ K
  · rw [← S.down_eq x K i hi, ← S.down_eq y K i hi,hK]
  · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le (show K ≤ i by omega)
    clear hi
    induction t with
    | zero => exact hK
    | succ t ih =>
      apply (h (K+t) (by omega)).injective
      change S.step (K+t) (x.val ((K+t)+1)) = S.step (K+t) (y.val ((K+t)+1))
      rw [x.property,y.property]
      exact ih

/-- Evaluation at a stable coordinate is a bijection with the inverse limit. -/
theorem evaluation_bijective (h : ∀ i ≥ K, Function.Bijective (S.step i)) :
    Function.Bijective (fun x : S.Limit => x.val K) := by
  exact ⟨fun _ _ he => limit_ext h he, fun a => ⟨lift h a,lift_at h a⟩⟩

end NatInverseSystem
end PolishSpaceBook
