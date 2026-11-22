module

public import PolishSpaceBook.FirstOrderFunctionDefinitions

@[expose] public section

/-!
# Eliminating a function value by its defining graph

This is the single-witness step of the formula translation. Capture-avoiding
substitution connects the original occurrence with the existential witness.
FirstOrderTermGraphs and FirstOrderFunctionElimination give the recursive syntax
translation. Its action on derivations is separate.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

/-- An expression with a specified unique graph value can be replaced by an existential witness. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    By the substitution lemma, the left side holds exactly when $\psi$ holds under $s[y\mapsto b]$.
    The right side requires some graph witness for which the same formula holds; that witness must be $b$.
    This proves both implications, with all other parameters fixed.
-/
theorem realize_graph_elimination (φ ψ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) (s : ℕ → M)
    (hgraph : ∀ a, φ.Realize (Function.update s x a) ↔ a = t.realize s) :
    (ψ.subst x t).Realize s ↔ (quant .ex x (binary .conj φ ψ)).Realize s := by
  simp only [realize_subst, realize_ex, realize_conj]
  constructor
  · intro hψ
    exact ⟨t.realize s, (hgraph _).mpr rfl, hψ⟩
  · rintro ⟨a, ha, hψ⟩
    simpa only [(hgraph a).mp ha] using hψ

namespace FunctionDefinitions
variable {ι : ℕ → Type*} (D : FunctionDefinitions L ι)

/-- The defining axiom and uniqueness identify all graph witnesses with the function value. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Fix an assignment $s$, and let $b$ be the value of $f(\vec{x})$ at that assignment.
    The defining axiom and uniqueness say that $\theta(\vec{x},y)$ holds under $s[y\mapsto a]$ exactly when $a=b$.
-/
theorem graph_iff_function_value [(L.sum (functionSymbols ι)).Structure M]
    [(inclusion (L := L) (ι := ι)).IsExpansionOn M] {n : ℕ} (f : ι n) (s : ℕ → M)
    (hunique : ∃! b, (D.graph f).Realize (Function.update s n b))
    (haxiom : ∀ t : ℕ → M, (D.definingAxiom f).Realize t) (a : M) :
    (D.graph f).Realize (Function.update s n a) ↔
      a = (application (L := L) f).realize s := by
  have ht := (D.realize_axiom_iff f).mp haxiom s
  change (D.graph f).Realize (Function.update s n ((application (L := L) f).realize s)) at ht
  exact ⟨fun ha => hunique.unique ha ht, fun ha => ha ▸ ht⟩

/-- Single occurrence elimination in an arbitrary surrounding expanded-language formula. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Graph-witness elimination
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Constants are the $0$-ary function case. If $T \vdash \exists! y\,\theta(y)$, a new constant $c$ may be added with axiom
    $\theta(c)$, and each occurrence of $c$ can be eliminated by replacing it with a fresh witness satisfying $\theta$.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    To eliminate a chosen occurrence of $f(\vec{t})$, replace it by a variable fresh for the original formula,
    rename bound variables to avoid capture, and apply this equivalence with the graph at $\vec{t}$. For example,
    one truth-preserving elimination of
    $$
    P(f(x),z)
    $$
    is
    $$
    \exists u\,\bigl(\theta(x,u) \land P(u,z)\bigr),
    $$
    and
    $$
    f(x)=g(z)
    $$
    translates to
    $$
    \exists u\,\exists v\,\bigl(\theta_f(x,u) \land \theta_g(z,v) \land u=v\bigr).
    $$
    Unique existence makes this translation independent of the chosen fresh witnesses, so the expanded notation has the same
    truth conditions as its old-language expansion.
-/
theorem eliminate_application [(L.sum (functionSymbols ι)).Structure M]
    [(inclusion (L := L) (ι := ι)).IsExpansionOn M] {n : ℕ} (f : ι n)
    (ψ : AlphaFormula (L.sum (functionSymbols ι))) (s : ℕ → M)
    (hunique : ∃! b, (D.graph f).Realize (Function.update s n b))
    (haxiom : ∀ t : ℕ → M, (D.definingAxiom f).Realize t) :
    (ψ.subst n (application f)).Realize s ↔
      (quant .ex n (binary .conj ((D.graph f).mapLanguage inclusion) ψ)).Realize s := by
  apply realize_graph_elimination
  intro a
  rw [mapLanguage_realize_expansion]
  exact D.graph_iff_function_value f s hunique haxiom a

end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
