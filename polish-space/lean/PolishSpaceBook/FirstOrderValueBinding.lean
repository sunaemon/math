module

public import PolishSpaceBook.FirstOrderGraphProofs

@[expose] public section

/-!
# Binding an intermediate value in a proof

Two implications under a value assumption and existence of that value suffice
to bind it. The result is reusable for term graphs and atomic translations.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance valueBindingDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace ProvesFrom

/-- Bind an intermediate value, keeping the conclusion independent of its name. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Both conditional implications now hold under the same replacement-value graph. Existence supplies such a
    value. From the left side of the displayed equivalence, the conditional implication gives the translated atom
    at that value, and existential introduction gives the right side. In the other direction, open the value and
    apply the other implication. The free-variable bound for translation shows that the value's name is not free
    in the left side. It is also not free in the sentence assumptions, so both existential eliminations are valid.
    These are the same value-binding steps used in \termuse{substitution in term graphs}.
-/
theorem bind_value_equivalence {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (ρ ψ χ : AlphaFormula L) (y : ℕ) (hyχ : y ∉ χ.fv)
    (hex : ProvesFrom T (quant .ex y ρ))
    (hf : ProvesFrom T (binary .imp (binary .conj ρ ψ) χ))
    (hb : ProvesFrom T (binary .imp (binary .conj ρ χ) ψ)) :
    ProvesFrom T (binary .conj
      (binary .imp χ (quant .ex y (binary .conj ρ ψ)))
      (binary .imp (quant .ex y (binary .conj ρ ψ)) χ)) := by
  let E := quant .ex y (binary .conj ρ ψ)
  have hp := map₂_sentences hT hf hb (fun _ hf hb => Derives.andIntro hf hb)
  apply map₂_sentences hT hex hp
  intro Γ hΓ he hp
  have hyE : y ∉ E.fv := by simp only [E,fv_quant,Finset.notMem_erase,not_false_eq_true]
  have hforward : Derives Γ (binary .imp χ E) := by
    apply Derives.impIntro
    let Δ := insert χ Γ
    have hbody : Derives (insert ρ Δ) E := by
      have hwΓ : Γ ⊆ insert ρ Δ := by intro φ hφ; simp [Δ,hφ]
      have hs : Derives (insert ρ Δ) ψ := .impElim ((Derives.andRight hp).weaken hwΓ)
        (.andIntro (.hyp Δ ρ) (.assumption (by simp [Δ])))
      exact .exIntro y _ (.var y) (by simpa only [subst_self] using Derives.andIntro (.hyp Δ ρ) hs)
    refine Derives.exElim y y ρ E (he.weaken (Finset.subset_insert _ _))
      (by simpa only [subst_self] using hbody) ?_
    simp only [Context.fv_insert,hΓ,Finset.union_empty,Finset.mem_union,fv_quant,Finset.mem_erase,
      ne_eq,not_true_eq_false,false_and,or_false,not_or]
    exact ⟨hyχ,hyE⟩
  have hbackward : Derives Γ (binary .imp E χ) := by
    apply Derives.impIntro
    let Δ := insert E Γ
    have hwΓ : Γ ⊆ insert (binary .conj ρ ψ) Δ := by intro φ hφ; simp [Δ,hφ]
    have hbody : Derives (insert (binary .conj ρ ψ) Δ) χ :=
      .impElim ((Derives.andLeft hp).weaken hwΓ) (.hyp Δ _)
    refine Derives.exElim y y (binary .conj ρ ψ) χ (.hyp Γ E)
      (by simpa only [subst_self] using hbody) ?_
    simp only [Context.fv_insert,hΓ,Finset.union_empty,Finset.mem_union,fv_quant,Finset.mem_erase,
      ne_eq,not_true_eq_false,false_and,or_false,not_or]
    exact ⟨hyE,hyχ⟩
  exact .andIntro hforward hbackward

end ProvesFrom
end PolishSpaceBook.NamedFirstOrder
