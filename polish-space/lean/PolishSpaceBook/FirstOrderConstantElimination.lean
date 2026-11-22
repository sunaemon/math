module

public import PolishSpaceBook.FirstOrderConstantClasses

@[expose] public section

/-!
# Eliminating newly adjoined constants from derivations

A finite derivation excludes only finitely many replacement-variable names.
The implementation expresses this as eventual validity for large natural-number
variable names, avoiding elimination of a proof in Prop into a computed bound.
No completeness theorem or model-existence assumption is used.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula Filter
universe u v w
variable {L : Language.{u,v}} {A : Type w}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
local instance : DecidableEq (AlphaFormula L[[A]]) := Classical.decEq _

namespace Context

def dropConstants (y : ℕ) (Γ : Context L[[A]]) : Context L := Γ.image (AlphaFormula.dropConstants y)

@[simp] theorem dropConstants_insert (y : ℕ) (Γ : Context L[[A]]) (φ : AlphaFormula L[[A]]) :
    (insert φ Γ).dropConstants y = insert (φ.dropConstants y) (Γ.dropConstants y) := by
  simp [dropConstants]

theorem fv_dropConstants (y : ℕ) (Γ : Context L[[A]]) : (Γ.dropConstants y).fv ⊆ Γ.fv ∪ {y} := by
  intro x hx
  obtain ⟨ψ, hψ, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hψ
  rcases Finset.mem_union.mp (AlphaFormula.fv_dropConstants y φ hx) with hm | he
  · exact Finset.mem_union_left _ (mem_fv_of_mem hφ hm)
  · exact Finset.mem_union_right _ he

@[simp] theorem dropConstants_inclusion (y : ℕ) (Γ : Context L) :
    (Γ.mapLanguage (L.lhomWithConstants A)).dropConstants y = Γ := by
  simp [dropConstants, mapLanguage, Finset.image_image, Function.comp_def]

end Context
namespace Derives

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Given a finite derivation in the expanded language, choose the replacement name outside the finitely many
    names used as quantifier binders, eigenvariables, or substitution variables in its rule instances.
    Induction on the derivation replaces it by a derivation in the old language. Assumptions and propositional rules
    are immediate. Quantifier instantiation and equality elimination use commutation with substitution.
    For the two eigenvariable rules, a newly introduced free variable cannot equal the eigenvariable by the choice
    of the replacement name, so the side conditions remain valid. When the assumptions and conclusion belong to
    the old language, replacement leaves them unchanged. Applying this to a putative derivation of falsity proves
    preservation of consistency. The reverse transport of old derivations is the \termuse{language inclusion lemma}.
    \end{proof}
-/
theorem dropConstants_eventually {Γ : Context L[[A]]} {φ : AlphaFormula L[[A]]} (h : Derives Γ φ) :
    ∀ᶠ y : ℕ in atTop, Derives (Γ.dropConstants y) (φ.dropConstants y) := by
  induction h with
  | hyp Γ φ => exact Eventually.of_forall (fun y => by simpa using hyp (Γ.dropConstants y) (φ.dropConstants y))
  | andIntro hφ hψ ihφ ihψ =>
    filter_upwards [ihφ, ihψ] with y hφ hψ
    simpa using andIntro hφ hψ
  | andLeft h ih =>
    filter_upwards [ih] with y h
    exact andLeft (by simpa using h)
  | andRight h ih =>
    filter_upwards [ih] with y h
    exact andRight (by simpa using h)
  | orLeft ψ h ih =>
    filter_upwards [ih] with y h
    simpa using orLeft (ψ.dropConstants y) h
  | orRight φ h ih =>
    filter_upwards [ih] with y h
    simpa using orRight (φ.dropConstants y) h
  | orElim hd hl hr ihd ihl ihr =>
    filter_upwards [ihd, ihl, ihr] with y hd hl hr
    exact orElim (by simpa using hd) (by simpa using hl) (by simpa using hr)
  | impIntro h ih =>
    filter_upwards [ih] with y h
    simpa using impIntro (by simpa using h)
  | impElim hf ha ihf iha =>
    filter_upwards [ihf, iha] with y hf ha
    exact impElim (by simpa using hf) ha
  | falseElim φ h ih =>
    filter_upwards [ih] with y h
    exact falseElim _ (by simpa using h)
  | @allIntro Γ φ x h hx ih =>
    filter_upwards [ih, eventually_gt_atTop x] with y h hy
    have hyx : y ≠ x := ne_of_gt hy
    rw [dropConstants_quant y .all x φ hyx]
    apply allIntro x h
    intro hm
    rcases Finset.mem_union.mp (Context.fv_dropConstants y Γ hm) with ho | he
    · exact hx ho
    · exact hyx (Finset.mem_singleton.mp he).symm
  | allElim x φ t h ih =>
    filter_upwards [ih, eventually_gt_atTop x] with y h hy
    have hyx : y ≠ x := ne_of_gt hy
    rw [dropConstants_subst y x hyx]
    exact allElim x (φ.dropConstants y) (dropConstantTerm y t)
      (by simpa [dropConstants_quant, hyx] using h)
  | exIntro x φ t h ih =>
    filter_upwards [ih, eventually_gt_atTop x] with y h hy
    have hyx : y ≠ x := ne_of_gt hy
    rw [dropConstants_quant y .ex x φ hyx]
    exact exIntro x (φ.dropConstants y) (dropConstantTerm y t)
      (by simpa [dropConstants_subst, hyx] using h)
  | @exElim Γ x z φ χ he hc hz ihe ihc =>
    filter_upwards [ihe, ihc, eventually_gt_atTop x, eventually_gt_atTop z] with y he hc hyx hyz
    have hxy : y ≠ x := ne_of_gt hyx
    have hzy : y ≠ z := ne_of_gt hyz
    apply exElim x z (φ.dropConstants y) (χ.dropConstants y)
      (by simpa [dropConstants_quant, hxy] using he)
      (by simpa [dropConstants_subst, hxy] using hc)
    have hz' : z ∉ Γ.fv ∧ z ∉ χ.fv ∧ z ∉ (quant .ex x φ).fv := by
      simpa only [Finset.mem_union, not_or, and_assoc] using hz
    have fresh {S T : Finset ℕ} (hST : S ⊆ T ∪ {y}) (hzT : z ∉ T) : z ∉ S := by
      intro hm
      rcases Finset.mem_union.mp (hST hm) with ho | he
      · exact hzT ho
      · exact hzy (Finset.mem_singleton.mp he).symm
    simp only [Finset.mem_union, not_or]
    refine ⟨⟨fresh (Context.fv_dropConstants y Γ) hz'.1,
      fresh (AlphaFormula.fv_dropConstants y χ) hz'.2.1⟩, ?_⟩
    rw [← dropConstants_quant y .ex x φ hxy]
    exact fresh (AlphaFormula.fv_dropConstants y (quant .ex x φ)) hz'.2.2
  | eqIntro Γ t => exact Eventually.of_forall (fun y => by simpa using eqIntro (Γ.dropConstants y) (dropConstantTerm y t))
  | eqElim φ x t r ht he iht ihe =>
    filter_upwards [iht, ihe, eventually_gt_atTop x] with y ht he hy
    have hyx : y ≠ x := ne_of_gt hy
    rw [dropConstants_subst y x hyx]
    exact eqElim (φ.dropConstants y) x (dropConstantTerm y t) (dropConstantTerm y r)
      (by simpa [dropConstants_subst, hyx] using ht) (by simpa using he)
  | excludedMiddle Γ φ =>
    exact Eventually.of_forall (fun y => by simpa [neg] using excludedMiddle (Γ.dropConstants y) (φ.dropConstants y))

theorem withConstants_iff (Γ : Context L) (φ : AlphaFormula L) :
    Derives (Γ.mapLanguage (L.lhomWithConstants A)) (φ.mapLanguage (L.lhomWithConstants A)) ↔ Derives Γ φ := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h.dropConstants_eventually.exists
    simpa using hy
  · intro h
    exact h.mapLanguage _

end Derives

theorem ProvesFrom.dropConstants_eventually {T : Set (AlphaFormula L)} {φ : AlphaFormula L[[A]]}
    (h : ProvesFrom (AlphaFormula.mapLanguage (L.lhomWithConstants A) '' T) φ) :
    ∀ᶠ y : ℕ in atTop, ProvesFrom T (φ.dropConstants y) := by
  obtain ⟨Γ, hΓ, hd⟩ := h
  filter_upwards [hd.dropConstants_eventually] with y hy
  refine ⟨Γ.dropConstants y, ?_, hy⟩
  intro ψ hψ
  obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hψ
  obtain ⟨θ, hθ, rfl⟩ := hΓ χ hχ
  simpa using hθ

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Adjoining constants is conservative
-/
theorem ProvesFrom.withConstants_iff (T : Set (AlphaFormula L)) (φ : AlphaFormula L) :
    ProvesFrom (AlphaFormula.mapLanguage (L.lhomWithConstants A) '' T)
      (φ.mapLanguage (L.lhomWithConstants A)) ↔ ProvesFrom T φ := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h.dropConstants_eventually.exists
    simpa using hy
  · intro h
    exact h.mapLanguage _

theorem Consistent.withConstants {T : Set (AlphaFormula L)} (hT : Consistent T) :
    Consistent (AlphaFormula.mapLanguage (L.lhomWithConstants A) '' T) := by
  intro h
  exact hT ((ProvesFrom.withConstants_iff T falsum).mp (by simpa using h))

end PolishSpaceBook.NamedFirstOrder
