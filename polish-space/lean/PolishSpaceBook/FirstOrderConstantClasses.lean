module

public import PolishSpaceBook.FirstOrderConstantFormulas

@[expose] public section

/-!
# Capture-avoiding elimination of added constants on alpha-classes

Choose bound names away from the replacement variable, then use literal
replacement. Alpha comparison proves that the result does not depend on this
choice. A larger finite avoidance set proves compatibility with substitution.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v w
variable {L : Language.{u,v}} {A : Type w}
namespace Formula

def freshRepresentative (φ : Formula L) (S : Finset ℕ) : Formula L :=
  Classical.choose (φ.exists_fresh_boundNames S)

theorem freshRepresentative_spec (φ : Formula L) (S : Finset ℕ) :
    Alpha φ (φ.freshRepresentative S) ∧ Disjoint (φ.freshRepresentative S).boundNames S :=
  Classical.choose_spec (φ.exists_fresh_boundNames S)

theorem freshRepresentative_avoids (φ : Formula L) (y : ℕ) :
    y ∉ (φ.freshRepresentative {y}).boundNames := by
  simpa using (φ.freshRepresentative_spec {y}).2

end Formula
namespace AlphaFormula

theorem exists_fresh_rep (φ : AlphaFormula L) (S : Finset ℕ) :
    ∃ ψ : Formula L, mk ψ = φ ∧ Disjoint ψ.boundNames S := by
  induction φ using Quotient.inductionOn with
  | _ φ =>
    obtain ⟨ψ, hψ, hf⟩ := φ.exists_fresh_boundNames S
    exact ⟨ψ, Quotient.sound hψ.symm, hf⟩

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Fix a variable $y$. To replace every added constant in a formula by $y$, first use the
    \termuse{fresh bound names lemma} to choose a representative with no binder named $y$, then perform the
    literal replacement. This operation is well-defined on $\alpha$-classes. Indeed, compare two such representatives
    using \termuse{comparison of named first-order formulas}. At a new constant, both replacements are the same
    variable; at each quantifier, that variable is different from either bound name, so it remains paired with itself.
    The operation adds no free variable other than $y$, and on old-language formulas it is the identity.
-/
def dropConstants (y : ℕ) : AlphaFormula L[[A]] → AlphaFormula L :=
  Quotient.lift (fun φ => mk ((φ.freshRepresentative {y}).dropConstants y)) (by
    intro φ ψ h
    apply Quotient.sound
    have hα := (φ.freshRepresentative_spec {y}).1.symm.trans
      (Formula.Alpha.trans h (ψ.freshRepresentative_spec {y}).1)
    exact hα.dropConstants y (φ.freshRepresentative_avoids y) (ψ.freshRepresentative_avoids y))

theorem dropConstants_mk (y : ℕ) (φ : Formula L[[A]]) (hy : y ∉ φ.boundNames) :
    (mk φ).dropConstants y = mk (φ.dropConstants y) := by
  apply Quotient.sound
  exact (φ.freshRepresentative_spec {y}).1.symm.dropConstants y (φ.freshRepresentative_avoids y) hy

@[simp] theorem dropConstants_falsum (y : ℕ) :
    (falsum : AlphaFormula L[[A]]).dropConstants y = falsum :=
  dropConstants_mk y .falsum (by simp [Formula.boundNames])

@[simp] theorem dropConstants_equal (y : ℕ) (t r : L[[A]].Term ℕ) :
    (equal t r).dropConstants y = equal (dropConstantTerm y t) (dropConstantTerm y r) :=
  dropConstants_mk y (.equal t r) (by simp [Formula.boundNames])

@[simp] theorem dropConstants_binary (y : ℕ) (c : Connective) (φ ψ : AlphaFormula L[[A]]) :
    (binary c φ ψ).dropConstants y = binary c (φ.dropConstants y) (ψ.dropConstants y) := by
  obtain ⟨φ, rfl, hφ⟩ := φ.exists_fresh_rep {y}
  obtain ⟨ψ, rfl, hψ⟩ := ψ.exists_fresh_rep {y}
  have hfφ : y ∉ φ.boundNames := by simpa using hφ
  have hfψ : y ∉ ψ.boundNames := by simpa using hψ
  change (mk (.binary c φ ψ)).dropConstants y = _
  rw [dropConstants_mk y _ (by simp [Formula.boundNames, hfφ, hfψ]),
    dropConstants_mk y φ hfφ, dropConstants_mk y ψ hfψ]
  rfl

theorem dropConstants_quant (y : ℕ) (q : Quantifier) (x : ℕ) (φ : AlphaFormula L[[A]]) (hyx : y ≠ x) :
    (quant q x φ).dropConstants y = quant q x (φ.dropConstants y) := by
  obtain ⟨φ, rfl, hφ⟩ := φ.exists_fresh_rep {y}
  have hfφ : y ∉ φ.boundNames := by simpa using hφ
  change (mk (.quant q x φ)).dropConstants y = _
  rw [dropConstants_mk y _ (by simp [Formula.boundNames, hyx, hfφ]), dropConstants_mk y φ hfφ]
  rfl

theorem fv_dropConstants (y : ℕ) (φ : AlphaFormula L[[A]]) :
    (φ.dropConstants y).fv ⊆ φ.fv ∪ {y} := by
  obtain ⟨φ, rfl, hφ⟩ := φ.exists_fresh_rep {y}
  rw [dropConstants_mk y φ (by simpa using hφ)]
  exact Formula.fv_dropConstants y φ

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Replacement commutes with substitution for a variable $x\ne y$. To see this for substitution of a term $t$,
    choose a representative whose bound names avoid $\FreeVars{t}\cup\{y\}$.
    The replacement term has no free variables outside this set, so neither substitution needs to rename a binder
    to avoid capture. Induction on terms and formulas now proves commutation, including the case where substitution
    stops at a binder for the substituted variable. Independence of the representative gives the identity on
    $\alpha$-classes.
-/
theorem dropConstants_subst (y x : ℕ) (hyx : y ≠ x) (φ : AlphaFormula L[[A]]) (t : L[[A]].Term ℕ) :
    (φ.subst x t).dropConstants y = (φ.dropConstants y).subst x (dropConstantTerm y t) := by
  obtain ⟨φ, rfl, hf⟩ := φ.exists_fresh_rep (t.varFinset ∪ {y})
  have ht : Disjoint φ.boundNames t.varFinset ∧ y ∉ φ.boundNames := by simpa [and_comm] using hf
  have hs : y ∉ (φ.subst x t).boundNames := by
    rw [Formula.boundNames_subst_of_disjoint φ x t ht.1]
    exact ht.2
  rw [subst_mk, dropConstants_mk y _ hs, dropConstants_mk y φ ht.2]
  exact congrArg mk (Formula.dropConstants_subst_of_fresh y x hyx φ t hf)

@[simp] theorem dropConstants_inclusion (y : ℕ) (φ : AlphaFormula L) :
    (φ.mapLanguage (L.lhomWithConstants A)).dropConstants y = φ := by
  obtain ⟨φ, rfl, hf⟩ := φ.exists_fresh_rep {y}
  rw [mapLanguage_mk, dropConstants_mk y _ (by simpa using hf)]
  exact congrArg mk (Formula.dropConstants_inclusion y φ)

end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
