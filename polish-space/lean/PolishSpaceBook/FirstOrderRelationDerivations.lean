module

public import PolishSpaceBook.FirstOrderRelationSubstitution

@[expose] public section

/-!
# Translation of derivations under relation elimination

The image context can lose free names but cannot gain them. Thus each original
eigenvariable remains fresh. Instantiation and equality elimination use the
substitution identity; all other rules retain their constructors.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
local instance : DecidableEq (AlphaFormula (L.sum (relationSymbols ι))) := Classical.decEq _
namespace RelationDefinitions
variable (D : RelationDefinitions L ι)

@[simp] theorem eliminate_falsum : D.eliminate falsum = falsum := rfl

@[simp] theorem eliminate_equal (t r : (L.sum (relationSymbols ι)).Term ℕ) :
    D.eliminate (equal t r) = equal (eraseTerm t) (eraseTerm r) := rfl

def eliminateContext (Γ : Context (L.sum (relationSymbols ι))) : Context L := Γ.image D.eliminate

@[simp] theorem eliminateContext_insert (Γ : Context (L.sum (relationSymbols ι)))
    (φ : AlphaFormula (L.sum (relationSymbols ι))) :
    D.eliminateContext (insert φ Γ) = insert (D.eliminate φ) (D.eliminateContext Γ) := by
  simp [eliminateContext]

theorem fv_eliminateContext_subset (Γ : Context (L.sum (relationSymbols ι))) :
    (D.eliminateContext Γ).fv ⊆ Γ.fv := by
  intro x hx
  obtain ⟨ψ, hψ, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hψ
  exact Context.mem_fv_of_mem hφ (D.fv_eliminate_subset φ hx)

/-- Every natural-deduction rule survives recursive relation elimination. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Now induct on the derivation. Translate each finite context by taking its image under elimination.
    Adding a hypothesis commutes with this operation, so discharged hypotheses remain the required hypotheses.
    The quantifier-instantiation and equality-elimination rules use the substitution identity. The free-variable
    bound for elimination implies the same bound for the union of the context's free-variable sets. Thus a fresh
    eigenvariable remains fresh for the translated context and conclusions, including all three sets in the
    existential-elimination condition. Every remaining rule preserves its displayed constructors directly.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Proof translation for relation definitions
-/
theorem eliminate_derivation {Γ : Context (L.sum (relationSymbols ι))}
    {φ : AlphaFormula (L.sum (relationSymbols ι))} (h : Derives Γ φ) :
    Derives (D.eliminateContext Γ) (D.eliminate φ) := by
  induction h with
  | hyp Γ φ => simpa using Derives.hyp (D.eliminateContext Γ) (D.eliminate φ)
  | andIntro hφ hψ ihφ ihψ => simpa using Derives.andIntro ihφ ihψ
  | andLeft h ih => exact Derives.andLeft (by simpa using ih)
  | andRight h ih => exact Derives.andRight (by simpa using ih)
  | orLeft ψ h ih => simpa using Derives.orLeft (D.eliminate ψ) ih
  | orRight φ h ih => simpa using Derives.orRight (D.eliminate φ) ih
  | orElim hd hl hr ihd ihl ihr =>
    exact Derives.orElim (by simpa using ihd) (by simpa using ihl) (by simpa using ihr)
  | impIntro h ih => simpa using Derives.impIntro (by simpa using ih)
  | impElim hf ha ihf iha => exact Derives.impElim (by simpa using ihf) iha
  | falseElim φ h ih => exact Derives.falseElim _ (by simpa using ih)
  | allIntro x h hx ih =>
    simpa using Derives.allIntro x ih (fun hm => hx (D.fv_eliminateContext_subset _ hm))
  | allElim x φ t h ih =>
    simpa only [eliminate_subst] using
      Derives.allElim x (D.eliminate φ) (eraseTerm t) (by simpa using ih)
  | exIntro x φ t h ih =>
    simpa using Derives.exIntro x (D.eliminate φ) (eraseTerm t)
      (by simpa only [eliminate_subst] using ih)
  | @exElim Γ x y φ χ he hc hy ihe ihc =>
    have hs := Finset.union_subset_union
      (Finset.union_subset_union (D.fv_eliminateContext_subset Γ) (D.fv_eliminate_subset χ))
      (D.fv_eliminate_subset (quant .ex x φ))
    have hy' : y ∉ (D.eliminateContext Γ).fv ∪ (D.eliminate χ).fv ∪
        (quant .ex x (D.eliminate φ)).fv := by
      intro hm; apply hy; apply hs; simpa using hm
    exact Derives.exElim x y (D.eliminate φ) (D.eliminate χ) (by simpa using ihe)
      (by simpa only [eliminateContext_insert, eliminate_subst, eraseTerm] using ihc) hy'
  | eqIntro Γ t => simpa using Derives.eqIntro (D.eliminateContext Γ) (eraseTerm t)
  | eqElim φ x t r ht he iht ihe =>
    simpa only [eliminate_subst] using Derives.eqElim (D.eliminate φ) x (eraseTerm t) (eraseTerm r)
      (by simpa only [eliminate_subst] using iht) (by simpa using ihe)
  | excludedMiddle Γ φ =>
    simpa [neg] using Derives.excludedMiddle (D.eliminateContext Γ) (D.eliminate φ)

/-- Finite proof support is carried to the image theory. -/
theorem eliminate_proof {T : Set (AlphaFormula (L.sum (relationSymbols ι)))}
    {φ : AlphaFormula (L.sum (relationSymbols ι))} (h : ProvesFrom T φ) :
    ProvesFrom (D.eliminate '' T) (D.eliminate φ) := by
  obtain ⟨Γ, hΓ, hd⟩ := h
  refine ⟨D.eliminateContext Γ, ?_, D.eliminate_derivation hd⟩
  intro ψ hψ
  obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hψ
  exact ⟨χ, hΓ χ hχ, rfl⟩

end RelationDefinitions
end PolishSpaceBook.NamedFirstOrder
