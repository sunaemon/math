module

public import PolishSpaceBook.FirstOrderNamedSubstitution

@[expose] public section

/-!
# Free variables of capture-avoiding first-order substitution

The replacement contributes free variables exactly when the replaced variable
occurs freely. The proof follows both recursive calls in the fresh-binder case.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v
variable {L : Language.{u,v}}

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Free variables of substitution
-/
theorem mem_varFinset_termSubst (t : L.Term ℕ) (x : ℕ) (r : L.Term ℕ) (v : ℕ) :
    v ∈ (termSubst t x r).varFinset ↔
      (v ∈ t.varFinset ∧ v ≠ x) ∨ (x ∈ t.varFinset ∧ v ∈ r.varFinset) := by
  induction t with
  | var y =>
    by_cases hy : y = x
    · subst y; simp [termSubst, Term.subst, Term.varFinset]
    · simp [termSubst, Term.subst, Term.varFinset, hy, Ne.symm hy]
      aesop
  | func f ts ih =>
    simp only [termSubst, Term.subst, Term.varFinset, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    change (∃ i, v ∈ (termSubst (ts i) x r).varFinset) ↔ _
    simp_rw [ih]
    aesop

theorem termSubst_not_free (t : L.Term ℕ) (x : ℕ) (r : L.Term ℕ)
    (hx : x ∉ t.varFinset) : termSubst t x r = t := by
  induction t with
  | var y =>
    have hy : y ≠ x := by simpa [Term.varFinset, eq_comm] using hx
    simp [termSubst, Term.subst, hy]
  | func f ts ih =>
    simp only [termSubst, Term.subst]
    congr 1
    funext i
    apply ih i
    intro h
    exact hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, h⟩)

namespace Formula

theorem subst_falsum (x : ℕ) (t : L.Term ℕ) : (falsum : Formula L).subst x t = falsum := rfl

theorem subst_equal (a b : L.Term ℕ) (x : ℕ) (t : L.Term ℕ) :
    (equal a b).subst x t = equal (termSubst a x t) (termSubst b x t) := rfl

theorem subst_rel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term ℕ)
    (x : ℕ) (t : L.Term ℕ) :
    (rel R ts).subst x t = rel R (fun i => termSubst (ts i) x t) := rfl

theorem subst_binary (c : Connective) (φ ψ : Formula L) (x : ℕ) (t : L.Term ℕ) :
    (binary c φ ψ).subst x t = binary c (φ.subst x t) (ψ.subst x t) := by
  simp only [subst, nodes, substFuel]
  congr 1
  · exact substFuel_stable _ φ x t _ (by omega) le_rfl
  · exact substFuel_stable _ ψ x t _ (by omega) le_rfl

theorem nodes_subst (φ : Formula L) (x : ℕ) (t : L.Term ℕ) :
    (φ.subst x t).nodes = φ.nodes := nodes_substFuel _ _ _ _

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    For terms, use structural induction: substituting for a variable gives the stated alternatives, and a function
    application takes the union of the free-variable sets of its arguments. For formulas, use strong induction on the
    number of formula constructors. The atomic and Boolean cases take unions of the corresponding free-variable sets.
    At a quantifier binding $x$, substitution stops and $x$ is absent from the quantified formula's free variables.
    At a different binder $y\notin\FreeVars{t}$, apply the induction hypothesis to the body and remove $y$.
    In the remaining case, first rename $y$ to the prescribed fresh $z$. The induction hypothesis replaces free occurrences
    of $y$ in the body by occurrences of $z$. Apply it again to substitution of $t$ for $x$ in that renamed body.
    Since $z\notin\FreeVars{\varphi}\cup\FreeVars{t}\cup\{x\}$ for the original body $\varphi$, removing $z$ at the new
    quantifier removes precisely the renamed occurrences. This gives the displayed formula in both quantifier cases.
    \end{proof}
-/
private theorem mem_fv_subst_bounded (k : ℕ) (φ : Formula L) (x : ℕ) (t : L.Term ℕ)
    (v : ℕ) (hk : φ.nodes ≤ k) :
    v ∈ (φ.subst x t).fv ↔ (v ∈ φ.fv ∧ v ≠ x) ∨ (x ∈ φ.fv ∧ v ∈ t.varFinset) := by
  induction k generalizing φ x t v with
  | zero => have := nodes_pos φ; omega
  | succ k ih =>
    cases φ with
    | falsum => simp [subst_falsum, fv]
    | equal a b =>
      simp only [subst_equal, fv, Finset.mem_union, mem_varFinset_termSubst]
      tauto
    | rel R ts =>
      simp only [subst_rel, fv, Finset.mem_biUnion, Finset.mem_univ, true_and,
        mem_varFinset_termSubst]
      aesop
    | binary c φ ψ =>
      have hφ : φ.nodes ≤ k := by simp only [nodes] at hk; omega
      have hψ : ψ.nodes ≤ k := by simp only [nodes] at hk; omega
      simp only [subst_binary, fv, Finset.mem_union, ih φ x t v hφ, ih ψ x t v hψ]
      tauto
    | quant q y φ =>
      have hφ : φ.nodes ≤ k := by simpa only [nodes, Nat.add_le_add_iff_right] using hk
      rw [subst_quant]
      by_cases hy : y = x
      · simp only [ite_eq_left hy]
        subst y
        simp only [fv, Finset.mem_erase]
        tauto
      · simp only [ite_eq_right hy]
        by_cases hfree : y ∉ t.varFinset
        · simp only [ite_eq_left hfree, fv, Finset.mem_erase, ih φ x t v hφ]
          have hv : v ∈ t.varFinset → v ≠ y := fun hv he => hfree (he ▸ hv)
          have hxy : x ≠ y := Ne.symm hy
          tauto
        · simp only [ite_eq_right hfree]
          let z := NamedLambda.Term.fresh (φ.fv ∪ t.varFinset ∪ {x})
          have hz : z ∉ φ.fv ∧ z ∉ t.varFinset ∧ z ≠ x := by
            simpa only [z, Finset.mem_union, Finset.mem_singleton, not_or, and_assoc]
              using NamedLambda.Term.fresh_not_mem (φ.fv ∪ t.varFinset ∪ {x})
          have hv := ih φ y (.var z) v hφ
          have hx := ih φ y (.var z) x hφ
          simp only [Term.varFinset, Finset.mem_singleton] at hv hx
          have ho := ih (φ.subst y (.var z)) x t v (by simpa only [nodes_subst] using hφ)
          change v ∈ ((φ.subst y (.var z)).subst x t).fv.erase z ↔ _
          simp only [fv, Finset.mem_erase]
          rw [ho, hv, hx]
          have hvφ : v ∈ φ.fv → v ≠ z := fun hv he => hz.1 (he ▸ hv)
          have hvt : v ∈ t.varFinset → v ≠ z := fun hv he => hz.2.1 (he ▸ hv)
          have hxy : x ≠ y := Ne.symm hy
          have hxz : x ≠ z := Ne.symm hz.2.2
          clear ih hv hx ho hk hφ hfree hz
          tauto

/-- Exact free variables, including substitution for a variable that is absent. -/
theorem mem_fv_subst (φ : Formula L) (x : ℕ) (t : L.Term ℕ) (v : ℕ) :
    v ∈ (φ.subst x t).fv ↔ (v ∈ φ.fv ∧ v ≠ x) ∨ (x ∈ φ.fv ∧ v ∈ t.varFinset) :=
  mem_fv_subst_bounded φ.nodes φ x t v le_rfl

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Free variables of substitution
-/
theorem fv_subst (φ : Formula L) (x : ℕ) (t : L.Term ℕ) :
    (φ.subst x t).fv = φ.fv.erase x ∪ if x ∈ φ.fv then t.varFinset else ∅ := by
  ext v
  simp only [mem_fv_subst, Finset.mem_union, Finset.mem_erase]
  split_ifs <;> simp_all <;> tauto

/-- Literal named substitution can rename a binder even when the variable is absent. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The second assertion need not be literal equality of named formulas: the substitution rule may rename a binder
    even when $x$ is absent.
-/
theorem absent_substitution_can_rename (L : Language.{u,v}) :
    ∃ φ : Formula L, 1 ∉ φ.fv ∧ φ.subst 1 (.var 0) ≠ φ := by
  refine ⟨.quant .all 0 .falsum, by simp [fv], ?_⟩
  rw [subst_quant]
  simp only [show (0 : ℕ) ≠ 1 by decide, ite_false, Term.varFinset,
    Finset.mem_singleton, not_true_eq_false, subst_falsum]
  intro h
  have he : NamedLambda.Term.fresh ((falsum : Formula L).fv ∪ ({0} : Finset ℕ) ∪ {1}) = 0 := by
    injection h
  have hn := NamedLambda.Term.fresh_not_mem ((falsum : Formula L).fv ∪ ({0} : Finset ℕ) ∪ {1})
  rw [he] at hn
  exact hn (by simp)

end Formula
end PolishSpaceBook.NamedFirstOrder
