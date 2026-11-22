module

public import PolishSpaceBook.FirstOrderRelationDefinitions

@[expose] public section

/-!
# Unique existence in named syntax

The uniqueness clause uses a fresh comparison variable. Its interpretation is
proved from capture-avoiding substitution and assignment locality.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v w
variable {L : Language.{u,v}}

namespace AlphaFormula

/-- The usual expansion of `∃! x, φ`, with a fresh comparison variable `z`. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\exists!\, x\, \varphi(x) \;:\equiv\; \exists x\,[\varphi(x) \land \forall y\,(\varphi(y) \to y = x)]$ — pure
        first-order logic.
-/
def uniqueAt (x z : ℕ) (φ : AlphaFormula L) : AlphaFormula L :=
  quant .ex x (binary .conj φ
    (quant .all z (binary .imp (φ.subst x (.var z)) (equal (.var z) (.var x)))))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Function symbols.**
    Function notation requires uniqueness. Suppose $\theta(\vec{x},y)$ is an $L$-formula whose free variables are
    among the pairwise distinct variables in $\vec{x}$ and $y$, and suppose
    $$
    T \vdash \forall \vec{x}\,\exists! y\,\theta(\vec{x},y).
    $$
    Here unique existence abbreviates
    $$\exists!y\,\theta(\vec{x},y)
    \quad:\equiv\quad
    \exists y\,\bigl(\theta(\vec{x},y)\land
    \forall z\,(\theta(\vec{x},z)\to z=y)\bigr),$$
    where $z$ is fresh, and $\theta(\vec{x},z)$ is obtained by capture-avoiding substitution for $y$.
    The substitution lemma and assignment locality show that this formula says exactly that there is one and only one
    possible value of $y$. The comparison variable introduces no additional free parameter.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\exists!\, x\, \varphi(x) \;:\equiv\; \exists x\,[\varphi(x) \land \forall y\,(\varphi(y) \to y = x)]$ — pure
        first-order logic.
-/
theorem realize_uniqueAt {M : Type w} [L.Structure M] (x z : ℕ) (φ : AlphaFormula L)
    (hxz : x ≠ z) (hz : z ∉ φ.fv) (s : ℕ → M) :
    (uniqueAt x z φ).Realize s ↔ ∃! a, φ.Realize (Function.update s x a) := by
  have he (a b : M) :
      φ.Realize (Function.update (Function.update (Function.update s x a) z b) x b) ↔
        φ.Realize (Function.update s x b) := by
    apply φ.realize_congr
    intro y hy
    by_cases hxy : y = x
    · subst y; simp
    · have hzy : y ≠ z := fun h => hz (h ▸ hy)
      simp [Function.update_of_ne, hxy, hzy]
  simp only [uniqueAt, realize_ex, realize_conj, realize_all, realize_imp, realize_subst,
    realize_equal, Term.realize_var, Function.update_self, Function.update_of_ne hxz]
  simp_rw [he]
  rfl

/-- Binding the witness and the fresh comparison variable leaves no other free names. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Function symbols.**
    Function notation requires uniqueness. Suppose $\theta(\vec{x},y)$ is an $L$-formula whose free variables are
    among the pairwise distinct variables in $\vec{x}$ and $y$, and suppose
    $$
    T \vdash \forall \vec{x}\,\exists! y\,\theta(\vec{x},y).
    $$
    Here unique existence abbreviates
    $$\exists!y\,\theta(\vec{x},y)
    \quad:\equiv\quad
    \exists y\,\bigl(\theta(\vec{x},y)\land
    \forall z\,(\theta(\vec{x},z)\to z=y)\bigr),$$
    where $z$ is fresh, and $\theta(\vec{x},z)$ is obtained by capture-avoiding substitution for $y$.
    The substitution lemma and assignment locality show that this formula says exactly that there is one and only one
    possible value of $y$. The comparison variable introduces no additional free parameter.
-/
theorem fv_uniqueAt_subset (x z : ℕ) (φ : AlphaFormula L) :
    (uniqueAt x z φ).fv ⊆ φ.fv.erase x := by
  have heq : (equal (.var z) (.var x) : AlphaFormula L).fv = {z} ∪ {x} := rfl
  intro y hy
  simp only [uniqueAt, fv_quant, fv_binary, fv_subst, Term.varFinset, heq,
    Finset.mem_erase, Finset.mem_union, Finset.mem_singleton] at hy ⊢
  rcases hy with ⟨hyx, hy | ⟨hyz, hy | hy⟩⟩
  · exact ⟨hyx, hy⟩
  · rcases hy with hy | hy
    · exact hy
    · split_ifs at hy with hx
      · exact (hyz (Finset.mem_singleton.mp hy)).elim
      · exact (Finset.notMem_empty _ hy).elim
  · exact (hy.elim hyz hyx).elim

end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
