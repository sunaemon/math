module

public import PolishSpaceBook.FirstOrderFunctionSubstitution
public import PolishSpaceBook.FirstOrderFunctionReflexivity

@[expose] public section

/-!
# Quantifier instantiation after function elimination

A translated term instance binds its value. Universal elimination supplies the
body at that value; existential introduction binds that value as the witness.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance functionQuantifierRulesDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- A fresh value name and an admissible internal bound always exist together. -/
theorem exists_value_name (φ : AlphaFormula (L.sum (functionSymbols ι)))
    (t : (L.sum (functionSymbols ι)).Term ℕ) :
    ∃ y B : ℕ, y < B ∧ y ∉ φ.fv ∧ y ∉ t.varFinset ∧ (∀ a ∈ t.varFinset, a < B) := by
  let S := φ.fv ∪ t.varFinset
  let y := S.sup id + 1
  have hab (a : ℕ) (ha : a ∈ S) : a < y := Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
  exact ⟨y,y+1,by omega,
    (fun hm => by have := hab y (Finset.mem_union_left _ hm); omega),
    (fun hm => by have := hab y (Finset.mem_union_right _ hm); omega),
    (fun a ha => by have := hab a (Finset.mem_union_right _ ha); omega)⟩

/-- No fresh name is gained by a translated instance. -/
theorem not_free_eliminate_subst (φ : AlphaFormula (L.sum (functionSymbols ι)))
    (t : (L.sum (functionSymbols ι)).Term ℕ) (x y : ℕ)
    (hyφ : y ∉ φ.fv) (hyt : y ∉ t.varFinset) : y ∉ (D.eliminate (φ.subst x t)).fv := by
  intro hm
  have hm' := D.fv_eliminate_subset (φ.subst x t) hm
  rw [fv_subst] at hm'
  rcases Finset.mem_union.mp hm' with hm' | hm'
  · exact hyφ (Finset.mem_erase.mp hm').2
  · split_ifs at hm'
    · exact hyt hm'
    · exact Finset.notMem_empty y hm'

/-- A universal premise yields every translated term instance. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For the rules with a term instance, write $\theta$ for the body and $\eta$ for its translation.
    For universal elimination at $t$, choose a value name $y$ fresh for the body and the term and an admissible
    starting index $B$. Existence gives the graph $\FirstOrderTermGraph{t}{y}{B}$ at some value.
    Under that graph, instantiate $\forall x\,\eta$ at the variable $y$ to obtain $\eta\subst{x}{y}$.
    Introduce the existential value quantifier and apply \termuse{relational substitution for function elimination}
    to obtain the translation of $\theta\subst{x}{t}$. The temporary value name is not free in the universally
    quantified premise or the sentence assumptions, so its graph assumption can be discharged.
-/
theorem proves_eliminate_allElim {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (φ : AlphaFormula (L.sum (functionSymbols ι))) (x : ℕ)
    (t : (L.sum (functionSymbols ι)).Term ℕ) :
    ProvesFrom T (binary .imp (quant .all x (D.eliminate φ)) (D.eliminate (φ.subst x t))) := by
  obtain ⟨y,B,hy,hyφ,hyt,ht⟩ := exists_value_name φ t
  let ψ := D.eliminate φ
  let ρ := D.termGraph t y B
  let E := quant .ex y (binary .conj ρ (ψ.subst x (.var y)))
  let A := quant .all x ψ
  have hs := D.proves_eliminate_substitution hT hu φ t x y B hy hyt hyφ ht
  have he := D.proves_termGraph_exists hT hu t y B hy hyt ht
  apply ProvesFrom.map₂_sentences hT hs he
  intro Γ hΓ hs he
  have hyψ : y ∉ ψ.fv := fun hm => hyφ (D.fv_eliminate_subset φ hm)
  have hyA : y ∉ A.fv := by
    intro hm
    rw [fv_quant] at hm
    exact hyψ (Finset.mem_erase.mp hm).2
  have hyE : y ∉ E.fv := by simp only [E,fv_quant,Finset.notMem_erase,not_false_eq_true]
  apply Derives.impIntro
  have hE : Derives (insert A Γ) E := by
    let Δ := insert A Γ
    have hb : Derives (insert ρ Δ) E := by
      have hψ : Derives (insert ρ Δ) (ψ.subst x (.var y)) :=
        Derives.allElim x ψ (.var y) (Derives.assumption (φ := A) (by simp [Δ]))
      exact .exIntro y _ (.var y) (by simpa only [subst_self] using Derives.andIntro (.hyp Δ ρ) hψ)
    refine Derives.exElim y y ρ E (he.weaken (Finset.subset_insert _ _))
      (by simpa only [subst_self] using hb) ?_
    simp only [Context.fv_insert,hΓ,Finset.union_empty,Finset.mem_union,fv_quant,Finset.mem_erase,
      ne_eq,not_true_eq_false,false_and,or_false,not_or]
    exact ⟨hyA,hyE⟩
  exact .impElim ((Derives.andRight hs).weaken (Finset.subset_insert _ _)) hE

/-- A translated term instance yields the translated existential conclusion. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For existential introduction, relational substitution turns the translated instance into existence of a value
    whose graph and body instance both hold. Open this value, use it as the witness for the original existential
    quantifier, and discharge the graph-and-body assumption. The temporary value name is not free in the translated
    instance, the existential conclusion, or the sentence assumptions. These two quantifier implications are proved
    from the old theory and then applied to the translated premises of the derivation.
-/
theorem proves_eliminate_exIntro {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (φ : AlphaFormula (L.sum (functionSymbols ι))) (x : ℕ)
    (t : (L.sum (functionSymbols ι)).Term ℕ) :
    ProvesFrom T (binary .imp (D.eliminate (φ.subst x t)) (quant .ex x (D.eliminate φ))) := by
  obtain ⟨y,B,hy,hyφ,hyt,ht⟩ := exists_value_name φ t
  let ψ := D.eliminate φ
  let ρ := D.termGraph t y B
  let A := D.eliminate (φ.subst x t)
  let M := binary .conj ρ (ψ.subst x (.var y))
  let χ := quant .ex x ψ
  obtain ⟨Γ,hΓ,hs⟩ := D.proves_eliminate_substitution hT hu φ t x y B hy hyt hyφ ht
  have hΓfv := Context.fv_eq_empty_of_sentences hT Γ hΓ
  have hyA := D.not_free_eliminate_subst φ t x y hyφ hyt
  have hyχ : y ∉ χ.fv := by
    intro hm
    rw [fv_quant] at hm
    exact hyφ (D.fv_eliminate_subset φ (Finset.mem_erase.mp hm).2)
  refine ⟨Γ,hΓ,Derives.impIntro ?_⟩
  have hE : Derives (insert A Γ) (quant .ex y M) :=
    .impElim ((Derives.andLeft hs).weaken (Finset.subset_insert _ _)) (.hyp Γ A)
  have hb : Derives (insert M (insert A Γ)) χ := .exIntro x ψ (.var y) (.andRight (.hyp _ M))
  refine Derives.exElim y y M χ hE (by simpa only [subst_self] using hb) ?_
  simp only [Context.fv_insert,hΓfv,Finset.union_empty,Finset.mem_union,fv_quant,Finset.mem_erase,
    ne_eq,not_true_eq_false,false_and,or_false,not_or]
  exact ⟨hyA,hyχ⟩

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
