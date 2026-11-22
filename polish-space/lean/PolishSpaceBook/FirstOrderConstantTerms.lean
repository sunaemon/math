module

public import PolishSpaceBook.FirstOrderFreshBinders

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Turning added constant symbols into a free variable

The term operation uses mathlib's constants-to-variables conversion. Only the
new constants are changed; the old language symbols and old variables remain.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v w
variable {L : Language.{u,v}} {A : Type w}

def dropConstantTerm (y : ℕ) (t : L[[A]].Term ℕ) : L.Term ℕ :=
  t.constantsToVars.relabel (Sum.elim (fun _ => y) id)

@[simp] theorem dropConstantTerm_var (y x : ℕ) :
    dropConstantTerm (L := L) (A := A) y (.var x) = .var x := rfl

@[simp] theorem dropConstantTerm_old (y : ℕ) {n : ℕ} (f : L.Functions n)
    (ts : Fin n → L[[A]].Term ℕ) :
    dropConstantTerm y (.func (Sum.inl f) ts) = .func f (fun i => dropConstantTerm y (ts i)) := by
  cases n <;> rfl

@[simp] theorem dropConstantTerm_new (y : ℕ) (a : A) (ts : Fin 0 → L[[A]].Term ℕ) :
    dropConstantTerm (L := L) (A := A) y (.func (l := 0) (Sum.inr a) ts) = (.var y : L.Term ℕ) := rfl

@[simp] theorem dropConstantTerm_inclusion (y : ℕ) (t : L.Term ℕ) :
    dropConstantTerm y ((L.lhomWithConstants A).onTerm t) = t := by
  induction t with
  | var => rfl
  | func f ts ih =>
    change dropConstantTerm y (.func (Sum.inl f) _) = .func f ts
    rw [dropConstantTerm_old]
    congr 1
    funext i
    exact ih i

/-- Replacing a constant only adds the chosen free variable. -/
theorem fv_dropConstantTerm (y : ℕ) (t : L[[A]].Term ℕ) :
    (dropConstantTerm y t).varFinset ⊆ t.varFinset ∪ {y} := by
  induction t with
  | var x => simp
  | @func n f ts ih =>
    cases n with
    | zero =>
      cases f with
      | inl f => simp [Term.varFinset]
      | inr a => simp [Term.varFinset]
    | succ n =>
      cases f with
      | inr e => exact e.elim
      | inl f =>
        intro z hz
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
        rcases Finset.mem_union.mp (ih i hi) with hm | he
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hm⟩)
        · exact Finset.mem_union_right _ he

theorem dropConstantTerm_subst (y x : ℕ) (hyx : y ≠ x) (t r : L[[A]].Term ℕ) :
    dropConstantTerm y (termSubst t x r) = termSubst (dropConstantTerm y t) x (dropConstantTerm y r) := by
  induction t with
  | var z => by_cases hz : z = x <;> simp [termSubst, Term.subst, hz]
  | @func n f ts ih =>
    cases n with
    | zero =>
      cases f with
      | inl f =>
        simp only [termSubst, Term.subst, dropConstantTerm_old]
        congr 1
        funext i
        exact Fin.elim0 i
      | inr a => simp [termSubst, Term.subst, hyx]
    | succ n =>
      cases f with
      | inr e => exact e.elim
      | inl f =>
        simp only [termSubst, Term.subst, dropConstantTerm_old]
        congr 1
        funext i
        exact ih i

/-- Name comparison survives constant replacement when the replacement name corresponds to itself. -/
theorem TermRel.dropConstants {R : ℕ → ℕ → Prop} {t r : L[[A]].Term ℕ} (h : TermRel R t r)
    (y : ℕ) (hy : R y y) : TermRel R (dropConstantTerm y t) (dropConstantTerm y r) := by
  induction h with
  | var h => exact .var h
  | @func n f ts us h ih =>
    cases n with
    | zero =>
      cases f with
      | inl f => exact .func f ih
      | inr a => exact .var hy
    | succ n =>
      cases f with
      | inl f => exact .func f ih
      | inr e => exact e.elim

end PolishSpaceBook.NamedFirstOrder
