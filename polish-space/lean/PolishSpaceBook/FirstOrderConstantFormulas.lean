module

public import PolishSpaceBook.FirstOrderConstantTerms

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Literal constant replacement in formulas with fresh binders

The raw operation is used only after its replacement variable has been excluded
from bound names. Comparison of names proves independence of this representative.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
open NamedLambda.Term (bindNames)
universe u v w
variable {L : Language.{u,v}} {A : Type w}
namespace Formula

def dropConstants (y : ℕ) : Formula L[[A]] → Formula L
  | .falsum => .falsum
  | .equal t r => .equal (dropConstantTerm y t) (dropConstantTerm y r)
  | .rel (.inl R) ts => .rel R (fun i => dropConstantTerm y (ts i))
  | .rel (.inr e) _ => nomatch e
  | .binary c φ ψ => .binary c (dropConstants y φ) (dropConstants y ψ)
  | .quant q x φ => .quant q x (dropConstants y φ)

@[simp] theorem boundNames_dropConstants (y : ℕ) (φ : Formula L[[A]]) :
    (φ.dropConstants y).boundNames = φ.boundNames := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel R ts => cases R with | inl R => rfl | inr e => exact e.elim
  | binary c φ ψ ihφ ihψ => simp [dropConstants, boundNames, ihφ, ihψ]
  | quant q x φ ih => simp [dropConstants, boundNames, ih]

@[simp] theorem boundNames_mapLanguage {K : Language} (f : L →ᴸ K) (φ : Formula L) :
    (φ.mapLanguage f).boundNames = φ.boundNames := by
  induction φ <;> simp_all [mapLanguage, boundNames]

@[simp] theorem dropConstants_inclusion (y : ℕ) (φ : Formula L) :
    (φ.mapLanguage (L.lhomWithConstants A)).dropConstants y = φ := by
  induction φ with
  | falsum => rfl
  | equal t r => simp [mapLanguage, dropConstants]
  | rel R ts =>
    change Formula.rel R (fun i => dropConstantTerm y ((L.lhomWithConstants A).onTerm (ts i))) = _
    simp
  | binary c φ ψ ihφ ihψ => simp [mapLanguage, dropConstants, ihφ, ihψ]
  | quant q x φ ih => simp [mapLanguage, dropConstants, ih]

theorem fv_dropConstants (y : ℕ) (φ : Formula L[[A]]) :
    (φ.dropConstants y).fv ⊆ φ.fv ∪ {y} := by
  induction φ with
  | falsum => simp [dropConstants, fv]
  | equal t r =>
    intro z hz
    rcases Finset.mem_union.mp hz with ht | hr
    · rcases Finset.mem_union.mp (fv_dropConstantTerm y t ht) with hm | he
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
      · exact Finset.mem_union_right _ he
    · rcases Finset.mem_union.mp (fv_dropConstantTerm y r hr) with hm | he
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
      · exact Finset.mem_union_right _ he
  | rel R ts =>
    cases R with
    | inr e => exact e.elim
    | inl R =>
      intro z hz
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
      rcases Finset.mem_union.mp (fv_dropConstantTerm y (ts i) hi) with hm | he
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hm⟩)
      · exact Finset.mem_union_right _ he
  | binary c φ ψ ihφ ihψ =>
    intro z hz
    rcases Finset.mem_union.mp hz with hφ | hψ
    · rcases Finset.mem_union.mp (ihφ hφ) with hm | he
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
      · exact Finset.mem_union_right _ he
    · rcases Finset.mem_union.mp (ihψ hψ) with hm | he
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
      · exact Finset.mem_union_right _ he
  | quant q x φ ih =>
    intro z hz
    obtain ⟨hzx, hz⟩ := Finset.mem_erase.mp hz
    rcases Finset.mem_union.mp (ih hz) with hm | he
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hzx, hm⟩)
    · exact Finset.mem_union_right _ he

theorem NameRel.dropConstants {R : ℕ → ℕ → Prop} {φ ψ : Formula L[[A]]} (h : NameRel R φ ψ)
    (y : ℕ) (hy : R y y) (hφ : y ∉ φ.boundNames) (hψ : y ∉ ψ.boundNames) :
    NameRel R (φ.dropConstants y) (ψ.dropConstants y) := by
  induction h with
  | falsum => exact .falsum _
  | equal ht hr => exact .equal (ht.dropConstants y hy) (hr.dropConstants y hy)
  | rel R ht => cases R with
    | inl R => exact .rel R (fun i => (ht i).dropConstants y hy)
    | inr e => exact e.elim
  | binary c h₁ h₂ ih₁ ih₂ =>
    simp only [boundNames, Finset.mem_union, not_or] at hφ hψ
    exact .binary c (ih₁ hy hφ.1 hψ.1) (ih₂ hy hφ.2 hψ.2)
  | @quant q R x z φ ψ h ih =>
    have hf : y ≠ x ∧ y ∉ φ.boundNames := by simpa [boundNames] using hφ
    have hg : y ≠ z ∧ y ∉ ψ.boundNames := by simpa [boundNames] using hψ
    exact .quant q (ih (Or.inr ⟨hf.1, hg.1, hy⟩) hf.2 hg.2)

theorem Alpha.dropConstants {φ ψ : Formula L[[A]]} (h : Alpha φ ψ) (y : ℕ)
    (hφ : y ∉ φ.boundNames) (hψ : y ∉ ψ.boundNames) :
    Alpha (φ.dropConstants y) (ψ.dropConstants y) :=
  (h.nameRel.dropConstants y rfl hφ hψ).eq_alpha

/-- Fresh binders make both substitutions literal, avoiding any choice of fresh name. -/
theorem dropConstants_subst_of_fresh (y x : ℕ) (hyx : y ≠ x) (φ : Formula L[[A]]) (t : L[[A]].Term ℕ)
    (hf : Disjoint φ.boundNames (t.varFinset ∪ {y})) :
    (φ.subst x t).dropConstants y = (φ.dropConstants y).subst x (dropConstantTerm y t) := by
  induction φ with
  | falsum => rfl
  | equal a b => simp [subst_equal, dropConstants, dropConstantTerm_subst y x hyx]
  | rel R ts => cases R with
    | inl R => simp [subst_rel, dropConstants, dropConstantTerm_subst y x hyx]
    | inr e => exact e.elim
  | binary c φ ψ ihφ ihψ =>
    have h : Disjoint φ.boundNames (t.varFinset ∪ {y}) ∧
        Disjoint ψ.boundNames (t.varFinset ∪ {y}) := Finset.disjoint_union_left.mp hf
    simp [subst_binary, dropConstants, ihφ h.1, ihψ h.2]
  | quant q z φ ih =>
    have h : z ∉ t.varFinset ∪ {y} ∧ Disjoint φ.boundNames (t.varFinset ∪ {y}) :=
      Finset.disjoint_insert_left.mp hf
    have hz : z ∉ t.varFinset := fun hm => h.1 (Finset.mem_union_left _ hm)
    have hz' : z ∉ (dropConstantTerm y t).varFinset := fun hm => h.1 (fv_dropConstantTerm y t hm)
    rw [subst_quant]
    by_cases hzx : z = x
    · simp [hzx, dropConstants, subst_quant]
    · simp [hzx, hz, hz', dropConstants, subst_quant, ih h.2]

end Formula
end PolishSpaceBook.NamedFirstOrder
