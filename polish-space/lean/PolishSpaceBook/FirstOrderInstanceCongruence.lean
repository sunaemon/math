module

public import PolishSpaceBook.FirstOrderTermGraphTotality

@[expose] public section

/-!
# Equality replacement in simultaneous instances

A fresh hole isolates one input of a defining formula. Equality elimination
changes that input, and finite induction changes every input in turn.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace AlphaFormula

/-- Substituting into a fresh argument hole changes exactly that argument. -/
theorem simultaneous_hole {n : ℕ} (φ : AlphaFormula L) (hf : φ.fv ⊆ Finset.range n)
    (ts : Fin n → L.Term ℕ) (i : Fin n) (x : ℕ) (t : L.Term ℕ)
    (hx : ∀ j, x ∉ (ts j).varFinset) :
    (φ.simultaneous (Function.update ts i (.var x))).subst x t =
      φ.simultaneous (Function.update ts i t) := by
  rw [simultaneous_subst _ _ _ _ hf]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self, Term.subst, ite_true]
  · simp only [Function.update_of_ne hj]
    exact termSubst_not_free (ts j) x t (hx j)

end AlphaFormula
namespace Derives

/-- Change one input of an instance by equality elimination in a fresh hole. -/
theorem simultaneous_update {Γ : Context L} {n : ℕ} (φ : AlphaFormula L)
    (hf : φ.fv ⊆ Finset.range n) (ts : Fin n → L.Term ℕ) (i : Fin n) (t : L.Term ℕ)
    (hφ : Derives Γ (φ.simultaneous ts)) (heq : Derives Γ (equal (ts i) t)) :
    Derives Γ (φ.simultaneous (Function.update ts i t)) := by
  let x := NamedLambda.Term.fresh (argumentVars ts)
  have hx (j : Fin n) : x ∉ (ts j).varFinset := fun hm =>
    NamedLambda.Term.fresh_not_mem (argumentVars ts) (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hm⟩)
  have h := Derives.eqElim (φ.simultaneous (Function.update ts i (.var x))) x (ts i) t
    (by simpa only [simultaneous_hole φ hf ts i x (ts i) hx, Function.update_eq_self] using hφ) heq
  simpa only [simultaneous_hole φ hf ts i x t hx] using h

/-- Pointwise provable equality transports any simultaneous instance. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Change one position at a time. For the current position, replace its argument by a variable absent from all
    current arguments. Substituting the old or new argument into this hole yields precisely the corresponding
    simultaneous instance: the substitution composition lemma shows that every other argument stays unchanged.
    Equality elimination therefore transports the current instance to the one with this argument changed.
    Induction on the finite set of positions yet to be changed gives the conclusion. No assumption on the free
    variables of the context is needed. For an old operation, use the formula equating the output slot to its
    function term; for a defined operation, use its defining graph. Both have free variables only in their input
    and output slots, so the same argument applies.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Equality in simultaneous instances
-/
theorem simultaneous_congr {Γ : Context L} {n : ℕ} (φ : AlphaFormula L)
    (hf : φ.fv ⊆ Finset.range n) (ts us : Fin n → L.Term ℕ)
    (heq : ∀ i, Derives Γ (equal (ts i) (us i))) (hφ : Derives Γ (φ.simultaneous ts)) :
    Derives Γ (φ.simultaneous us) := by
  have step : ∀ (S : Finset (Fin n)) (ts : Fin n → L.Term ℕ),
      (∀ i ∉ S, ts i = us i) → (∀ i, Derives Γ (equal (ts i) (us i))) →
      Derives Γ (φ.simultaneous ts) → Derives Γ (φ.simultaneous us) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro ts h _ hh
      have he : ts = us := funext (fun i => h i (by simp))
      simpa only [he] using hh
    | @insert i S hi ih =>
      intro ts hout heq hh
      apply ih (Function.update ts i (us i))
      · intro j hj
        by_cases he : j = i
        · subst j; exact Function.update_self _ _ _
        · rw [Function.update_of_ne he]
          exact hout j (by simp [he,hj])
      · intro j
        by_cases he : j = i
        · subst j; simpa only [Function.update_self] using Derives.eqIntro Γ (us i)
        · simpa only [Function.update_of_ne he] using heq j
      · exact simultaneous_update φ hf ts i (us i) hh (heq i)
  exact step Finset.univ ts (by simp) heq hφ

/-- Symmetry of equality for arbitrary terms uses a fresh variable as a hole. -/
theorem eq_symm {Γ : Context L} {t r : L.Term ℕ} (h : Derives Γ (equal t r)) :
    Derives Γ (equal r t) := by
  let x := NamedLambda.Term.fresh t.varFinset
  have hx : x ∉ t.varFinset := NamedLambda.Term.fresh_not_mem _
  have hd := Derives.eqElim (equal (.var x) t) x t r
    (by simpa only [subst_equal, termSubst_var_self, termSubst_not_free t x t hx]
      using Derives.eqIntro Γ t) h
  simpa only [subst_equal, termSubst_var_self, termSubst_not_free t x r hx] using hd

/-- Transitivity uses equality elimination in a fresh right-hand hole. -/
theorem eq_trans {Γ : Context L} {t r s : L.Term ℕ}
    (htr : Derives Γ (equal t r)) (hrs : Derives Γ (equal r s)) : Derives Γ (equal t s) := by
  let x := NamedLambda.Term.fresh t.varFinset
  have hx : x ∉ t.varFinset := NamedLambda.Term.fresh_not_mem _
  have hd := Derives.eqElim (equal t (.var x)) x r s
    (by simpa only [subst_equal, termSubst_var_self, termSubst_not_free t x r hx] using htr) hrs
  simpa only [subst_equal, termSubst_var_self, termSubst_not_free t x s hx] using hd

end Derives
end PolishSpaceBook.NamedFirstOrder
