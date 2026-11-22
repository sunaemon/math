module

public import PolishSpaceBook.FirstOrderRelationConservativity

@[expose] public section

/-!
# Finite conjunctions and blocks of existential witnesses

The assignment characterization keeps every parameter outside the quantified
block fixed. These operations package the children of a function application.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v w
variable {L : Language.{u,v}}
namespace AlphaFormula

def conjoin : (n : ℕ) → (Fin n → AlphaFormula L) → AlphaFormula L
  | 0, _ => binary .imp falsum falsum
  | n + 1, φ => binary .conj (φ 0) (conjoin n (fun i => φ i.succ))

def existsBlock : ℕ → ℕ → AlphaFormula L → AlphaFormula L
  | 0, _, φ => φ
  | n + 1, B, φ => quant .ex (B + n) (existsBlock n B φ)

@[simp] theorem temporaryNames_succ (n B : ℕ) :
    temporaryNames (n + 1) B = insert (B + n) (temporaryNames n B) := by
  simp only [temporaryNames, Finset.range_add_one, Finset.image_insert]

theorem mem_temporaryNames_iff (n B x : ℕ) : x ∈ temporaryNames n B ↔ B ≤ x ∧ x < B+n := by
  simp only [temporaryNames, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩; omega
  · rintro ⟨hlo,hhi⟩; exact ⟨x-B, by omega, by omega⟩

/-- Assign a finite tuple to a consecutive block and retain every other value. -/
def blockAssignment {M : Type*} {n : ℕ} (s : ℕ → M) (B : ℕ) (a : Fin n → M) : ℕ → M :=
  fun x => if h : B ≤ x ∧ x < B+n then a ⟨x-B, by omega⟩ else s x

@[simp] theorem blockAssignment_inside {M : Type*} {n : ℕ} (s : ℕ → M) (B : ℕ)
    (a : Fin n → M) (i : Fin n) : blockAssignment s B a (B+i.val) = a i := by
  have h : B ≤ B+i.val ∧ B+i.val < B+n := by have := i.isLt; omega
  simp only [blockAssignment, dite_eq_left h, Nat.add_sub_cancel_left]

theorem blockAssignment_outside {M : Type*} {n : ℕ} (s : ℕ → M) (B : ℕ)
    (a : Fin n → M) (x : ℕ) (hx : x ∉ temporaryNames n B) : blockAssignment s B a x = s x := by
  exact dite_eq_right (fun h => hx ((mem_temporaryNames_iff n B x).mpr h))

@[simp] theorem fv_conjoin (n : ℕ) (φ : Fin n → AlphaFormula L) :
    (conjoin n φ).fv = Finset.univ.biUnion (fun i => (φ i).fv) := by
  induction n with
  | zero => simp [conjoin, fv_binary, fv_falsum]
  | succ n ih =>
    rw [conjoin, fv_binary, ih]
    ext x
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro (h | ⟨i,h⟩)
      · exact ⟨0,h⟩
      · exact ⟨i.succ,h⟩
    · rintro ⟨i,h⟩
      exact Fin.cases (fun h => Or.inl h) (fun i h => Or.inr ⟨i,h⟩) i h

@[simp] theorem fv_existsBlock (n B : ℕ) (φ : AlphaFormula L) :
    (existsBlock n B φ).fv = φ.fv \ temporaryNames n B := by
  induction n with
  | zero => simp [existsBlock, temporaryNames]
  | succ n ih =>
    rw [existsBlock, fv_quant, ih, temporaryNames_succ]
    ext x
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert, not_or]
    tauto

section Semantics
variable {M : Type w} [L.Structure M]

theorem realize_conjoin (n : ℕ) (φ : Fin n → AlphaFormula L) (s : ℕ → M) :
    (conjoin n φ).Realize s ↔ ∀ i, (φ i).Realize s := by
  induction n with
  | zero => simp [conjoin]
  | succ n ih =>
    rw [conjoin, realize_conj, ih]
    exact ⟨fun h i => Fin.cases h.1 h.2 i, fun h => ⟨h 0, fun i => h i.succ⟩⟩

/-- Existentially binding a block changes exactly its assigned names. -/
theorem realize_existsBlock (n B : ℕ) (φ : AlphaFormula L) (s : ℕ → M) :
    (existsBlock n B φ).Realize s ↔
      ∃ s' : ℕ → M, (∀ x, x ∉ temporaryNames n B → s' x = s x) ∧ φ.Realize s' := by
  induction n generalizing s with
  | zero =>
    constructor
    · intro h; exact ⟨s, fun _ _ => rfl, h⟩
    · rintro ⟨s',he,h⟩
      have hh : s' = s := funext (fun x => he x (by simp [temporaryNames]))
      simpa only [hh, existsBlock] using h
  | succ n ih =>
    rw [existsBlock, realize_ex]
    constructor
    · rintro ⟨a,ha⟩
      obtain ⟨s',he,h⟩ := (ih (Function.update s (B+n) a)).mp ha
      refine ⟨s', ?_, h⟩
      intro x hx
      have hx' : x ≠ B+n ∧ x ∉ temporaryNames n B := by
        simpa only [temporaryNames_succ, Finset.mem_insert, not_or] using hx
      rw [he x hx'.2, Function.update_of_ne hx'.1]
    · rintro ⟨s',he,h⟩
      refine ⟨s' (B+n), (ih _).mpr ⟨s', ?_, h⟩⟩
      intro x hx
      by_cases hx' : x = B+n
      · subst x; simp
      · rw [Function.update_of_ne hx']
        apply he
        simpa only [temporaryNames_succ, Finset.mem_insert, not_or] using And.intro hx' hx

end Semantics
end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
