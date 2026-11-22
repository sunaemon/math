module

public import PolishSpaceBook.FirstOrderFunctionQuantifierRules

@[expose] public section

/-!
# Equality elimination after function elimination

Open the two value graphs in the translated equality, pass each term instance
through its value, and apply ordinary equality elimination between those values.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance functionEqualityRuleDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- Bounds on original parameters bound every free name in a translated term instance. -/
theorem eliminate_subst_fv_below (φ : AlphaFormula (L.sum (functionSymbols ι)))
    (t : (L.sum (functionSymbols ι)).Term ℕ) (x B : ℕ)
    (hφ : ∀ a ∈ φ.fv, a < B) (ht : ∀ a ∈ t.varFinset, a < B) :
    ∀ a ∈ (D.eliminate (φ.subst x t)).fv, a < B := by
  intro a ha
  have hm := D.fv_eliminate_subset (φ.subst x t) ha
  rw [fv_subst] at hm
  rcases Finset.mem_union.mp hm with hm | hm
  · exact hφ a (Finset.mem_erase.mp hm).2
  · split_ifs at hm
    · exact ht a hm
    · exact False.elim (Finset.notMem_empty a hm)

/-- The old theory derives the translated equality-elimination rule. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For equality elimination, choose $B$ above all free-variable indices in $\theta$ and all variable indices in
    $t,r$. By bound-name invariance, the translated equality can use the value names $u=v_B$ and $v=v_{B+1}$,
    with internal graph indices $B+2$. Open its two value graphs and their final equality $u=v$.
    The conditional substitution lemma for the first graph turns the translated $\theta\subst{x}{t}$ into
    $\eta\subst{x}{u}$. Ordinary equality elimination gives $\eta\subst{x}{v}$, and the conditional lemma for the
    second graph gives the translation of $\theta\subst{x}{r}$. Discharge the two value assumptions
    by existential elimination.
    Their names are not free in either original translated premise or in the final conclusion: all such free-variable
    indices are below $B$. This proves the equality-elimination implication in the old theory, ready to be applied
    to the translated premises.
-/
theorem proves_eliminate_eqElim {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (φ : AlphaFormula (L.sum (functionSymbols ι))) (x : ℕ)
    (t r : (L.sum (functionSymbols ι)).Term ℕ) :
    ProvesFrom T (binary .imp
      (binary .conj (D.eliminate (φ.subst x t)) (D.eliminate (equal t r)))
      (D.eliminate (φ.subst x r))) := by
  let S := φ.fv ∪ t.varFinset ∪ r.varFinset
  let B := S.sup id + 1
  have hS (a : ℕ) (ha : a ∈ S) : a < B := Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
  have hφ (a : ℕ) (ha : a ∈ φ.fv) : a < B := hS a (Finset.mem_union_left _ (Finset.mem_union_left _ ha))
  have ht (a : ℕ) (ha : a ∈ t.varFinset) : a < B := hS a (Finset.mem_union_left _ (Finset.mem_union_right _ ha))
  have hr (a : ℕ) (ha : a ∈ r.varFinset) : a < B := hS a (Finset.mem_union_right _ ha)
  let ψ := D.eliminate φ
  let A := binary .conj (D.eliminate (φ.subst x t)) (D.eliminate (equal t r))
  let χ := D.eliminate (φ.subst x r)
  let ρ := D.termGraph t B (B+2)
  let σ := D.termGraph r (B+1) (B+2)
  let M := binary .conj (binary .conj ρ (binary .conj σ (binary .imp falsum falsum)))
    (equal (.var B) (.var (B+1)))
  have hct := D.proves_eliminate_subst_conditional hT hu φ t x B (B+2) (by omega)
    (fun hm => by have := ht B hm; omega) (fun a ha => by have := ht a ha; omega)
  have hcr := D.proves_eliminate_subst_conditional hT hu φ r x (B+1) (B+2) (by omega)
    (fun hm => by have := hr (B+1) hm; omega) (fun a ha => by have := hr a ha; omega)
  apply ProvesFrom.map₂_sentences hT hct hcr
  intro Γ hΓ hct hcr
  have hA (a : ℕ) (ha : a ∈ A.fv) : a < B := by
    rw [fv_binary] at ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact D.eliminate_subst_fv_below φ t x B hφ ht a ha
    · have hm := D.fv_eliminate_subset (equal t r) ha
      change a ∈ t.varFinset ∪ r.varFinset at hm
      exact (Finset.mem_union.mp hm).elim (ht a) (hr a)
  have hχ := D.eliminate_subst_fv_below φ r x B hφ hr
  let Δ := insert A Γ
  have hb : Derives (insert M Δ) χ := by
    have hwΓ : Γ ⊆ insert M Δ := by intro θ hθ; simp [Δ,hθ]
    have hp : Derives (insert M Δ) (D.eliminate (φ.subst x t)) :=
      .andLeft (.assumption (φ := A) (by simp [Δ]))
    have hv : Derives (insert M Δ) (ψ.subst x (.var B)) :=
      .impElim (.andLeft (.impElim (hct.weaken hwΓ) (.andLeft (.andLeft (.hyp Δ M))))) hp
    have hw : Derives (insert M Δ) (ψ.subst x (.var (B+1))) :=
      .eqElim ψ x (.var B) (.var (B+1)) hv (.andRight (.hyp Δ M))
    exact .impElim (.andRight (.impElim (hcr.weaken hwΓ) (.andLeft (.andRight (.andLeft (.hyp Δ M)))))) hw
  apply Derives.impIntro
  have he : Derives Δ (existsBlock 2 B M) := by
    have h := Derives.andRight (Derives.hyp Γ A)
    rw [D.eliminate_equal_at t r B ht hr] at h
    exact h
  exact Derives.existsBlock_elim_self 2 B M χ
    (fun i hm => by
      have hm' : B+i.val ∈ A.fv := by simpa only [Δ,Context.fv_insert,hΓ,Finset.union_empty] using hm
      have := hA _ hm'; omega)
    (fun i hm => by have := hχ _ hm; omega) he hb

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
