module

public import PolishSpaceBook.FirstOrderTermGraphFunctionality

@[expose] public section

/-!
# Unique existence of recursive term values

Changing the fresh output name is capture-avoiding substitution. Combine the
separately constructed existence and functionality proofs to obtain the actual
unique-existence abbreviation in the original theory.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z
variable {L : Language.{u,v}} {ι : ℕ → Type z}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace AlphaFormula

theorem subst_absent (φ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) (hx : x ∉ φ.fv) :
    φ.subst x t = φ := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact Quotient.sound (Formula.alpha_subst_not_free φ x t hx)

/-- A substitution between names below a bound block commutes with all its quantifiers. -/
theorem subst_existsBlock_below (n B : ℕ) (φ : AlphaFormula L) (x y : ℕ)
    (hx : x < B) (hy : y < B) :
    (existsBlock n B φ).subst x (.var y) = existsBlock n B (φ.subst x (.var y)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [existsBlock, subst_quant_fresh .ex (B+n) _ x (.var y)
      (by omega) (by simpa only [Term.varFinset, Finset.mem_singleton] using (show B+n ≠ y by omega)), ih]
    rfl

end AlphaFormula
namespace Derives

/-- Existence and pairwise equality build the full unique-existence abbreviation. -/
theorem uniqueAt_of_exists_functional {Γ : Context L} (ρ : AlphaFormula L) (x y : ℕ)
    (hxΓ : x ∉ Γ.fv) (hyΓ : y ∉ Γ.fv) (hyρ : y ∉ ρ.fv)
    (hex : Derives Γ (quant .ex x ρ))
    (hf : Derives Γ (binary .imp (binary .conj ρ (ρ.subst x (.var y))) (equal (.var x) (.var y)))) :
    Derives Γ (uniqueAt x y ρ) := by
  have hall : Derives (insert ρ Γ)
      (quant .all y (binary .imp (ρ.subst x (.var y)) (equal (.var y) (.var x)))) := by
    apply Derives.allIntro y
    · apply Derives.impIntro
      apply Derives.eq_symm
      apply Derives.impElim (hf.weaken (by intro φ hφ; simp [hφ]))
      exact .andIntro (.assumption (by simp)) (.hyp _ _)
    · simpa only [Context.fv_insert, Finset.mem_union, not_or] using And.intro hyρ hyΓ
  have hbody : Derives (insert ρ Γ) (uniqueAt x y ρ) :=
    .exIntro x _ (.var x) (by simpa only [subst_self] using Derives.andIntro (Derives.hyp Γ ρ) hall)
  apply Derives.exElim x x ρ (uniqueAt x y ρ) hex (by simpa only [subst_self] using hbody)
  have hxU : x ∉ (uniqueAt x y ρ).fv := fun hm => (Finset.mem_erase.mp (fv_uniqueAt_subset x y ρ hm)).1 rfl
  simp only [Finset.mem_union, fv_quant, Finset.mem_erase, ne_eq, not_true_eq_false,
    false_and, or_false, not_or]
  exact ⟨hxΓ,hxU⟩

end Derives
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- Renaming a fresh output does not alter the child graphs or their parameters. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    The output variable of a recursive graph can also be replaced directly:
    $$\bigl(\FirstOrderTermGraph{t}{y}{B}\bigr)\subst{y}{z}
    \equiv_\alpha\FirstOrderTermGraph{t}{z}{B}.$$
    For a variable term this is substitution into equality. At an application, the child graphs contain no free
    occurrence of the output: their free variables are original parameters or their own child outputs. Substitution
    therefore leaves them unchanged. It passes through the child quantifiers because their names have indices at
    least $B$, and it changes only the output of the final operation graph.
-/
theorem termGraph_subst_output (t : (L.sum (functionSymbols ι)).Term ℕ) (x y B : ℕ)
    (hx : x < B) (hy : y < B) (hxt : x ∉ t.varFinset) :
    (D.termGraph t x B).subst x (.var y) = D.termGraph t y B := by
  cases t with
  | var a =>
    have hax : a ≠ x := by simpa only [Term.varFinset, Finset.mem_singleton, ne_eq, eq_comm] using hxt
    simp only [termGraph, subst_equal, termSubst, Term.subst, ite_eq_right hax, ite_true]
  | @func n f ts =>
    have hc : x ∉ (conjoin n (fun i => D.termGraph (ts i) (B+i.val) (B+n))).fv := by
      rw [fv_conjoin]
      intro hm
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
      rcases Finset.mem_insert.mp (D.fv_termGraph_subset (ts i) _ _ hi) with he | hi
      · omega
      · exact hxt (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩)
    simp only [termGraph]
    rw [subst_existsBlock_below n B _ x y hx hy, subst_binary, subst_absent _ x (.var y) hc,
      D.operationGraph_subst_output f _ x y (by intro i; simp only [Term.varFinset, Finset.mem_singleton]; omega)]

/-- Every recursive term graph has a unique value, proved within the old theory. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Finally combine pairwise equality with the previously proved existence of a term value. Under the graph
    assumption for the output, assume the graph at the comparison variable and derive their equality. Reverse its
    orientation, discharge the comparison assumption, and universally quantify the comparison variable, which is
    fresh for the output graph. Conjoin this uniqueness clause with the output graph and introduce the existential
    output quantifier. Existential elimination using the existence proof discharges the temporary output
    assumption. The substitution identity above identifies the comparison instance with the graph at the second
    output, so the result is exactly the displayed unique-existence abbreviation.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Derivable uniqueness of term values
-/
theorem proves_termGraph_unique {T : Set (AlphaFormula L)} (hT : T ⊆ Sentences L)
    (hu : ∀ n (f : ι n), ProvesFrom T (D.uniqueExistence f))
    (t : (L.sum (functionSymbols ι)).Term ℕ) (x y B : ℕ)
    (hx : x < B) (hy : y < B) (hxy : x ≠ y)
    (hxt : x ∉ t.varFinset) (hyt : y ∉ t.varFinset)
    (ht : ∀ a ∈ t.varFinset, a < B) : ProvesFrom T (uniqueAt x y (D.termGraph t x B)) := by
  have he := D.proves_termGraph_exists hT hu t x B hx hxt ht
  have hf := D.proves_termGraph_functional hT hu t x y B hx hy hxt hyt ht
  apply ProvesFrom.map₂_sentences hT he hf
  intro Γ hΓ he hf
  refine Derives.uniqueAt_of_exists_functional (D.termGraph t x B) x y
    (by rw [hΓ]; simp) (by rw [hΓ]; simp) ?_ he ?_
  · intro hm
    exact (Finset.mem_insert.mp (D.fv_termGraph_subset t x B hm)).elim (Ne.symm hxy) hyt
  · simpa only [D.termGraph_subst_output t x y B hx hy hxt] using hf

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
