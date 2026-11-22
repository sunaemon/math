module

public import PolishSpaceBook.FirstOrderRelationClasses

@[expose] public section

/-!
# Substitution into an instantiated definition

A common representative with fresh binders reduces both sides to composition
of literal term substitutions. This is equality of alpha-classes.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v
variable {L : Language.{u,v}}
namespace AlphaFormula

/-- Substitution into an instance acts on all its argument terms. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    First consider an instance of a defining formula $\varphi$ with input variables $\vec{x}$.
    For a further substitution of $t$ for $y$, put $u_i:=r_i\subst{y}{t}$. Then
    $$\bigl(\varphi\subst{\vec{x}}{\vec{r}}\bigr)\subst{y}{t}
    \equiv_\alpha\varphi\subst{\vec{x}}{\vec{u}}.$$
    To prove this, choose one representative of $\varphi$ whose binders avoid the inputs, both argument lists,
    both lists of temporary names, $y$, and all variables of $t$. The preceding literal-replacement argument applies
    to both instances and to the further substitution. Composition replaces each input by $u_i$ and fixes every
    other name occurring in the representative. This proves the displayed identity even if $y$ is an input variable.
-/
theorem simultaneous_subst {n : ℕ} (φ : AlphaFormula L) (ts : Fin n → L.Term ℕ)
    (x : ℕ) (t : L.Term ℕ) (hf : φ.fv ⊆ Finset.range n) :
    (φ.simultaneous ts).subst x t =
      φ.simultaneous (fun i => (ts i).subst (fun y => if y = x then t else .var y)) := by
  let σ : ℕ → L.Term ℕ := fun y => if y = x then t else .var y
  let us : Fin n → L.Term ℕ := fun i => (ts i).subst σ
  let B := φ.substitutionBound ts
  let C := φ.substitutionBound us
  have hb := φ.substitutionBound_spec ts
  have hc := φ.substitutionBound_spec us
  obtain ⟨ψ, he, hψ⟩ := φ.exists_fresh_rep
    ((Finset.range n ∪ temporaryNames n B ∪ argumentVars ts) ∪
      (Finset.range n ∪ temporaryNames n C ∪ argumentVars us) ∪ insert x t.varFinset)
  have hp := Finset.disjoint_union_right.mp hψ
  have hp' := Finset.disjoint_union_right.mp hp.1
  have hb' : ∀ z ∈ ψ.fv, z < B := by
    intro z hz; apply hb.2.1 z; rw [← he]; exact hz
  have hc' : ∀ z ∈ ψ.fv, z < C := by
    intro z hz; apply hc.2.1 z; rw [← he]; exact hz
  change (φ.simultaneousAt ts B).subst x t = φ.simultaneousAt us C
  rw [← he, simultaneousAt_mk_literal ψ ts B hb.1 hb' hb.2.2 hp'.1,
    simultaneousAt_mk_literal ψ us C hc.1 hc' hc.2.2 hp'.2, subst_mk,
    Formula.subst_eq_literal _ x t (by simpa only [Formula.boundNames_literalSubst] using hp.2),
    Formula.literalSubst_comp]
  apply congrArg mk
  apply ψ.literalSubst_congr
  intro z hz
  by_cases hn : z < n
  · simp only [dite_eq_left hn]; rfl
  · have hzbound : z ∈ ψ.boundNames := by
      rcases Finset.mem_union.mp hz with hz | hz
      · have hz' : z ∈ φ.fv := by rw [← he]; exact hz
        exact False.elim (hn (Finset.mem_range.mp (hf hz')))
      · exact hz
    have hzx : z ≠ x := fun h => Finset.disjoint_left.mp hp.2 hzbound
      (h ▸ Finset.mem_insert_self _ _)
    simp only [dite_eq_right hn, Term.subst, ite_eq_right hzx]

/-- Instantiating the input variables by themselves leaves the alpha-class unchanged. -/
theorem simultaneous_vars (φ : AlphaFormula L) (n : ℕ) :
    φ.simultaneous (fun i : Fin n => (Term.var i.val : L.Term ℕ)) = φ := by
  let ts : Fin n → L.Term ℕ := fun i => .var i.val
  let B := φ.substitutionBound ts
  have hb := φ.substitutionBound_spec ts
  obtain ⟨ψ, he, hψ⟩ := φ.exists_fresh_rep
    (Finset.range n ∪ temporaryNames n B ∪ argumentVars ts)
  have hb' : ∀ z ∈ ψ.fv, z < B := by
    intro z hz; apply hb.2.1 z; rw [← he]; exact hz
  change φ.simultaneousAt ts B = φ
  rw [← he, simultaneousAt_mk_literal ψ ts B hb.1 hb' hb.2.2 hψ]
  have hh : (fun z => if h : z < n then ts ⟨z,h⟩ else Term.var z) = Term.var := by
    funext z; split_ifs <;> rfl
  rw [hh, Formula.literalSubst_var]

end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
