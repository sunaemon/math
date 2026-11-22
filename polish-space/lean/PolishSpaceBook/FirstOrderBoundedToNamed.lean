module

public import PolishSpaceBook.FirstOrderTheoryConsequence

@[expose] public section

/-! # Translating finite bound-variable contexts into the book's named syntax -/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

/-- Context slots become names below the context length. -/
def boundedTermToNamed {n : ℕ} (t : L.Term (Empty ⊕ Fin n)) : L.Term ℕ :=
  t.relabel (Sum.elim Empty.elim Fin.val)

/-- Each new universal binder uses the next unused context name. -/
def boundedToNamed : {n : ℕ} → L.BoundedFormula Empty n → Formula L
  | _, .falsum => .falsum
  | _, .equal t r => .equal (boundedTermToNamed t) (boundedTermToNamed r)
  | _, .rel R ts => .rel R (fun i => boundedTermToNamed (ts i))
  | _, .imp φ ψ => .binary .imp (boundedToNamed φ) (boundedToNamed ψ)
  | n, .all φ => .quant .all n (boundedToNamed φ)

lemma realize_boundedTermToNamed {n : ℕ} (t : L.Term (Empty ⊕ Fin n)) (s : ℕ → M) :
    (boundedTermToNamed t).realize s = t.realize (Sum.elim Empty.elim (fun i => s i.val)) := by
  rw [boundedTermToNamed, Term.realize_relabel]
  congr 1
  funext i
  cases i with
  | inl x => exact Empty.elim x
  | inr i => rfl

private lemma update_context (s : ℕ → M) (n : ℕ) (a : M) :
    (fun i : Fin (n + 1) => Function.update s n a i.val) =
      Fin.snoc (fun i : Fin n => s i.val) a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.val_castSucc, Fin.snoc_castSucc, Function.update_of_ne (Nat.ne_of_lt j.isLt)]

/-- The translation preserves actual satisfaction in every structure, not just in set models. -/
theorem realize_boundedToNamed {n : ℕ} (φ : L.BoundedFormula Empty n) (s : ℕ → M) :
    (boundedToNamed φ).Realize s ↔ φ.Realize Empty.elim (fun i => s i.val) := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t r =>
    simp only [boundedToNamed, Formula.Realize, BoundedFormula.Realize, realize_boundedTermToNamed]
  | rel R ts =>
    simp only [boundedToNamed, Formula.Realize, BoundedFormula.Realize, realize_boundedTermToNamed]
  | imp φ ψ ihφ ihψ =>
    simp only [boundedToNamed, Formula.Realize, Connective.eval, BoundedFormula.realize_imp,
      ihφ, ihψ]
  | @all n φ ih =>
    simp only [boundedToNamed, Formula.Realize, Quantifier.eval, BoundedFormula.realize_all,
      ih, update_context]

lemma boundedTermToNamed_fv {n : ℕ} (t : L.Term (Empty ⊕ Fin n)) :
    (boundedTermToNamed t).varFinset ⊆ Finset.range n := by
  induction t with
  | var i =>
    cases i with
    | inl x => exact Empty.elim x
    | inr i => simp [boundedTermToNamed, Term.relabel, Term.varFinset]
  | func f ts ih =>
    intro x hx
    simp only [boundedTermToNamed, Term.relabel, Term.varFinset, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hi⟩ := hx
    exact ih i hi

/-- The binder name is genuinely fresh for the preceding context. -/
theorem boundedToNamed_fv {n : ℕ} (φ : L.BoundedFormula Empty n) :
    (boundedToNamed φ).fv ⊆ Finset.range n := by
  induction φ with
  | falsum => simp [boundedToNamed, Formula.fv]
  | equal t r => exact Finset.union_subset (boundedTermToNamed_fv t) (boundedTermToNamed_fv r)
  | rel R ts =>
    intro x hx
    simp only [boundedToNamed, Formula.fv, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hi⟩ := hx
    exact boundedTermToNamed_fv (ts i) hi
  | imp φ ψ ihφ ihψ => exact Finset.union_subset ihφ ihψ
  | @all n φ ih =>
    intro x hx
    obtain ⟨hxn, hx⟩ := Finset.mem_erase.mp hx
    have hx' := Finset.mem_range.mp (ih hx)
    exact Finset.mem_range.mpr (by omega)

/-- A closed mathlib sentence becomes a closed named formula. -/
theorem boundedToNamed_sentence (φ : L.Sentence) : (boundedToNamed φ).fv = ∅ := by
  exact Finset.subset_empty.mp (by simpa only [Finset.range_zero] using boundedToNamed_fv φ)

/-- For a sentence, the translated truth is exactly ordinary sentence satisfaction. -/
theorem realize_boundedToNamed_sentence (φ : L.Sentence) (s : ℕ → M) :
    (boundedToNamed φ).Realize s ↔ M ⊨ φ := by
  rw [realize_boundedToNamed]
  unfold Sentence.Realize FirstOrder.Language.Formula.Realize
  rw [Subsingleton.elim (default : Empty → M) Empty.elim,
    Subsingleton.elim (default : Fin 0 → M) (fun i => s i.val)]

end PolishSpaceBook.NamedFirstOrder
