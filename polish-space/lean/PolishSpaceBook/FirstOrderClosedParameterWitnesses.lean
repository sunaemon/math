module

public import PolishSpaceBook.FirstOrderSimultaneousSubstitution

@[expose] public section

/-! # Henkin witnesses after substituting closed parameters -/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}

/-- A closed-parameter instance is among the one-variable formulas witnessed by the limit theory. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This covers closed parameters as well. If $\theta(x,\vec y)$ is an $L_H$-formula and $\vec r$ is a tuple of closed
    $L_H$-terms, then $\theta(x,\vec r)$ has free variables only among $x$ and belongs to a finite stage.
    Its Henkin axiom supplies a constant witnessing $\exists x\,\theta(x,\vec r)$.
-/
theorem henkin_closed_parameter_witness (T : Set (AlphaFormula L)) {n : ℕ}
    (φ : AlphaFormula (henkinLanguage L)) (hφ : φ.fv ⊆ Finset.range (n + 1))
    (x : ℕ) (rs : Fin n → (henkinLanguage L).Term Empty) :
    let ψ := φ.simultaneous (Fin.cons (.var x) (fun i => namedClosedTerm (rs i)))
    ∃ c : (henkinLanguage L).Constants,
      binary .imp (quant .ex x ψ) (ψ.subst x c.term) ∈ henkinLimitTheory T :=
  henkinLimitTheory_witnesses T x _ (fv_closed_parameter_instance φ hφ x rs)

end PolishSpaceBook.NamedFirstOrder
