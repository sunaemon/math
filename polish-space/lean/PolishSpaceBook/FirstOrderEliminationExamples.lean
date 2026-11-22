module

public import PolishSpaceBook.FirstOrderFunctionGraphInstances

@[expose] public section

/-! # The two displayed function-elimination examples -/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v z w
variable {L : Language.{u,v}} {ι : ℕ → Type z}
namespace FunctionDefinitions
variable (D : FunctionDefinitions L ι)

/-- A unary new function applied to one named variable. -/
def unaryTerm (f : ι 1) (x : ℕ) : (L.sum (functionSymbols ι)).Term ℕ :=
  .func (Sum.inr f) (fun _ => .var x)

/-- Instantiate the defining graph at the input and output names. -/
def unaryGraph (f : ι 1) (x y : ℕ) : AlphaFormula L :=
  D.operationGraph (Sum.inr f) (fun _ => .var x) y

section Semantics
variable {M : Type w} [L.Structure M] [(L.sum (functionSymbols ι)).Structure M]
    [(inclusion (L := L) (ι := ι)).IsExpansionOn M]
variable (hu : ∀ n (f : ι n) (s : ℕ → M), ∃! b, (D.graph f).Realize (Function.update s n b))
    (ha : ∀ n (f : ι n) (s : ℕ → M), (D.definingAxiom f).Realize s)

include hu ha in
theorem realize_unaryGraph (f : ι 1) (x y : ℕ) (s : ℕ → M) :
    (D.unaryGraph f x y).Realize s ↔ s y = (unaryTerm (L := L) f x).realize s :=
  D.realize_operationGraph (Sum.inr f) (fun _ => .var x) y s hu ha

include hu ha in
/-- `P(f(x),z)` is equivalent to the graph witness `∃u, θ(x,u) ∧ P(u,z)`. -/
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
theorem eliminate_unary_relation (f : ι 1) (R : L.Relations 2) (s : ℕ → M) :
    (rel (L := L.sum (functionSymbols ι)) (Sum.inl R) ![unaryTerm (L := L) f 0, .var 2]).Realize s ↔
      (quant .ex 1 (binary .conj ((D.unaryGraph f 0 1).mapLanguage (inclusion (L := L) (ι := ι)))
        (rel (L := L.sum (functionSymbols ι)) (Sum.inl R) ![.var 1, .var 2]))).Realize s := by
  simp only [realize_ex, realize_conj, mapLanguage_realize_expansion]
  simp_rw [D.realize_unaryGraph hu ha]
  simp [unaryTerm, Term.realize]
  apply iff_of_eq
  change Structure.RelMap (L := L.sum (functionSymbols ι)) (Sum.inl R) _ =
    Structure.RelMap (L := L.sum (functionSymbols ι)) (Sum.inl R) _
  congr 1
  funext i
  fin_cases i <;> rfl

include hu ha in
/-- `f(x)=g(z)` is equivalent to two graph witnesses with equal values. -/
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
theorem eliminate_unary_equality (f g : ι 1) (s : ℕ → M) :
    (equal (unaryTerm (L := L) f 0) (unaryTerm (L := L) g 2)).Realize s ↔
      (quant .ex 1 (binary .conj ((D.unaryGraph f 0 1).mapLanguage (inclusion (L := L) (ι := ι)))
        (quant .ex 3 (binary .conj ((D.unaryGraph g 2 3).mapLanguage (inclusion (L := L) (ι := ι)))
          (equal (.var 1) (.var 3)))))).Realize s := by
  simp only [realize_ex, realize_conj, realize_equal, mapLanguage_realize_expansion]
  simp_rw [D.realize_unaryGraph hu ha]
  simp [unaryTerm, Term.realize]

end Semantics
end FunctionDefinitions
end PolishSpaceBook.NamedFirstOrder
