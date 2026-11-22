module

public import PolishSpaceBook.BorelExpressionEvaluation

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # A shared fold for valid, externally labelled Borel trees

The algebra sees exactly the present children. A single homomorphism theorem
transports this recursion to sets, code levels, and tree ranks.
-/

namespace PolishSpaceBook.BorelExpression
open Set

/-- The nonempty set of child numbers at a union or complement node. -/
def Children (c : BorelExpression) (s : List ℕ) := {k : ℕ // c (s ++ [k]) ≠ 0}

structure Algebra (A : Type*) where
  leaf : ℕ → A
  union : (S : Set ℕ) → Nonempty S → (S → A) → A
  complement : A → A

theorem union_nonempty (c : BorelExpression) (hc : c.Valid)
    (s : List ℕ) (hs : c s = 1) : Nonempty (Children c s) := by
  obtain ⟨k, hk⟩ := hc.2.2.2.1 s hs
  exact ⟨⟨k, hk⟩⟩

noncomputable def complementChild (c : BorelExpression) (hc : c.Valid)
    (s : List ℕ) (hs : c s = 2) : Children c s :=
  ⟨(hc.2.2.2.2.1 s hs).exists.choose, (hc.2.2.2.2.1 s hs).exists.choose_spec⟩

theorem complementChild_unique (c : BorelExpression) (hc : c.Valid)
    (s : List ℕ) (hs : c s = 2) (k : Children c s) : k = complementChild c hc s hs := by
  apply Subtype.ext
  exact (hc.2.2.2.2.1 s hs).unique k.2 (complementChild c hc s hs).2

noncomputable def foldStep {A : Type*} (c : BorelExpression) (hc : c.Valid) (a : Algebra A)
    (s : List ℕ) (rec : ∀ t, c.Child t s → A) : A := by
  classical
  exact if h1 : c s = 1 then
    a.union {k | c (s ++ [k]) ≠ 0} (union_nonempty c hc s h1)
      (fun k => rec (s ++ [k.1]) ⟨by omega, k.1, rfl, k.2⟩)
  else if h2 : c s = 2 then
    let k := complementChild c hc s h2
    a.complement (rec (s ++ [k.1]) ⟨by omega, k.1, rfl, k.2⟩)
  else a.leaf (c s - 3)

/-- The value at absent nodes is immaterial: recursive calls only visit present children. -/
noncomputable def fold {A : Type*} (c : BorelExpression) (hc : c.Valid) (a : Algebra A) : List ℕ → A :=
  hc.2.2.2.2.2.fix (foldStep c hc a)

theorem fold_eq {A : Type*} (c : BorelExpression) (hc : c.Valid) (a : Algebra A) (s : List ℕ) :
    c.fold hc a s = foldStep c hc a s (fun t _ => c.fold hc a t) :=
  hc.2.2.2.2.2.fix_eq _ s

/-- Prove correctness of a shared operation once, then transport the fold through it. -/
theorem map_fold {A B : Type*} (c : BorelExpression) (hc : c.Valid)
    (a : Algebra A) (b : Algebra B) (f : A → B)
    (hleaf : ∀ n, f (a.leaf n) = b.leaf n)
    (hunion : ∀ S hn g, f (a.union S hn g) = b.union S hn (fun i => f (g i)))
    (hcomp : ∀ x, f (a.complement x) = b.complement (f x)) (s : List ℕ) :
    f (c.fold hc a s) = c.fold hc b s := by
  induction s using hc.2.2.2.2.2.induction with
  | h s ih =>
    calc
      f (c.fold hc a s) = f (foldStep c hc a s (fun t _ => c.fold hc a t)) :=
        congrArg f (fold_eq c hc a s)
      _ = foldStep c hc b s (fun t _ => c.fold hc b t) := by
        unfold foldStep
        split_ifs with h1 h2
        · rw [hunion]
          congr 1
          funext k
          exact ih (s ++ [k.1]) ⟨by omega, k.1, rfl, k.2⟩
        · rw [hcomp]
          congr 1
          exact ih _ ⟨by omega, _, rfl, (complementChild c hc s h2).2⟩
        · exact hleaf _
      _ = c.fold hc b s := (fold_eq c hc b s).symm

/-- The three equations at present nodes uniquely determine the fold. -/
theorem fold_unique {A : Type*} (c : BorelExpression) (hc : c.Valid) (a : Algebra A)
    (v : List ℕ → A)
    (hv : ∀ s, c s ≠ 0 → v s = foldStep c hc a s (fun t _ => v t))
    (s : List ℕ) (hs : c s ≠ 0) : c.fold hc a s = v s := by
  induction s using hc.2.2.2.2.2.induction with
  | h s ih =>
    rw [hv s hs, fold_eq]
    unfold foldStep
    split_ifs with h1 h2
    · congr 1
      funext k
      exact ih _ ⟨by omega, k.1, rfl, k.2⟩ k.2
    · dsimp only
      congr 1
      exact ih _ ⟨by omega, _, rfl, (complementChild c hc s h2).2⟩ (complementChild c hc s h2).2
    · rfl

end PolishSpaceBook.BorelExpression
