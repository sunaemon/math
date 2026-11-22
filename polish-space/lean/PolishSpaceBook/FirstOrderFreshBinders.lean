module

public import PolishSpaceBook.FirstOrderLanguageDerivations

@[expose] public section

/-!
# Representatives with fresh bound names

Every alpha-class has a representative whose bound names avoid a prescribed
finite set. This permits literal symbol replacement without variable capture.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v
variable {L : Language.{u,v}}
namespace Formula

def boundNames : Formula L → Finset ℕ
  | .falsum | .equal .. | .rel .. => ∅
  | .binary _ φ ψ => φ.boundNames ∪ ψ.boundNames
  | .quant _ x φ => insert x φ.boundNames

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Fresh bound names
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Use strong induction on the number of formula constructors. Atomic formulas have no binders, and binary
    connectives follow by applying induction to both subformulas. At a quantifier with bound name $x$ and body
    $\psi$, choose $z\notin\FreeVars{\psi}\cup S$ and rename the binder to $z$. Apply induction to
    $\psi\subst{x}{z}$, whose constructor count equals that of $\psi$. The resulting body has no bound names in
    $S$, and the outer name $z$ also lies outside $S$. The same construction works for both quantifiers.
    \end{proof}
-/
theorem exists_fresh_boundNames (φ : Formula L) (S : Finset ℕ) :
    ∃ ψ, Alpha φ ψ ∧ Disjoint ψ.boundNames S := by
  have bounded : ∀ k (φ : Formula L), φ.nodes ≤ k → ∃ ψ, Alpha φ ψ ∧ Disjoint ψ.boundNames S := by
    intro k
    induction k with
    | zero => intro φ hφ; have := φ.nodes_pos; omega
    | succ k ih =>
      intro φ hφ
      cases φ with
      | falsum => exact ⟨.falsum, .refl _, by simp [boundNames]⟩
      | equal t r => exact ⟨.equal t r, .refl _, by simp [boundNames]⟩
      | rel R ts => exact ⟨.rel R ts, .refl _, by simp [boundNames]⟩
      | binary c φ ψ =>
        obtain ⟨φ', hφ', hfφ⟩ := ih φ (by simp only [nodes] at hφ; omega)
        obtain ⟨ψ', hψ', hfψ⟩ := ih ψ (by simp only [nodes] at hφ; omega)
        exact ⟨.binary c φ' ψ', .binary c hφ' hψ', by simpa [boundNames] using And.intro hfφ hfψ⟩
      | quant q x φ =>
        let z := NamedLambda.Term.fresh (φ.fv ∪ S)
        have hz : z ∉ φ.fv ∧ z ∉ S := by
          simpa only [z, Finset.mem_union, not_or] using NamedLambda.Term.fresh_not_mem (φ.fv ∪ S)
        obtain ⟨ψ, hψ, hfψ⟩ := ih (φ.subst x (.var z))
          (by simpa only [nodes_subst] using (Nat.le_of_succ_le_succ hφ))
        refine ⟨.quant q z ψ, (Alpha.rename q φ x z hz.1).trans (.quant q z hψ), ?_⟩
        simpa [boundNames] using And.intro hz.2 hfψ
  exact bounded φ.nodes φ le_rfl

/-- With fresh binders, substitution introduces no new bound names. -/
theorem boundNames_subst_of_disjoint (φ : Formula L) (x : ℕ) (t : L.Term ℕ)
    (ht : Disjoint φ.boundNames t.varFinset) : (φ.subst x t).boundNames = φ.boundNames := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | binary c φ ψ ihφ ihψ =>
    have h : Disjoint φ.boundNames t.varFinset ∧ Disjoint ψ.boundNames t.varFinset := by
      simpa [boundNames] using ht
    simp [subst_binary, boundNames, ihφ h.1, ihψ h.2]
  | quant q y φ ih =>
    have h : y ∉ t.varFinset ∧ Disjoint φ.boundNames t.varFinset := by simpa [boundNames] using ht
    rw [subst_quant]
    by_cases hy : y = x
    · simp [hy]
    · simp [hy, h.1, boundNames, ih h.2]

end Formula
end PolishSpaceBook.NamedFirstOrder
