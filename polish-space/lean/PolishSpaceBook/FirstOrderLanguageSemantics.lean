module

public import PolishSpaceBook.FirstOrderTermModelTruth

@[expose] public section

/-!
# Formula interpretation under reducts

Language maps change symbols without changing arities, variables, or binders.
Induction on terms and formulas identifies interpretation of a translated
formula with interpretation in the reduct, including the named quantifiers.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v u' v' w
variable {L : Language.{u,v}} {K : Language.{u',v'}} {M : Type w} [K.Structure M]

theorem onTerm_realize_reduct (f : L →ᴸ K) (t : L.Term ℕ) (s : ℕ → M) :
    (f.onTerm t).realize s = @Term.realize L M (f.reduct M) ℕ s t := by
  induction t with
  | var x => rfl
  | func F ts ih => simp only [LHom.onTerm, Term.realize, ih]; rfl

theorem Formula.mapLanguage_realize_reduct (f : L →ᴸ K) (φ : Formula L) (s : ℕ → M) :
    (φ.mapLanguage f).Realize s ↔ @Formula.Realize L M (f.reduct M) φ s := by
  induction φ generalizing s with
  | falsum => rfl
  | equal t r => simp only [Formula.mapLanguage, Formula.Realize, onTerm_realize_reduct]
  | rel R ts => simp only [Formula.mapLanguage, Formula.Realize, onTerm_realize_reduct]; rfl
  | binary c φ ψ ihφ ihψ => exact c.eval_congr (ihφ s) (ihψ s)
  | quant q x φ ih => exact q.eval_congr (fun a => ih (Function.update s x a))

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Finally forget the additional constants and retain only the interpretations of the symbols of $L$.
    Induction on terms and formulas shows that this reduct preserves the interpretation of every $L$-formula:
    term evaluation is unchanged, and the logical clauses use the same domain and assignments.
    It is therefore an $L$-model of $T$ falsifying $\varphi$, which proves the contrapositive.
-/
theorem AlphaFormula.mapLanguage_realize_reduct (f : L →ᴸ K) (φ : AlphaFormula L) (s : ℕ → M) :
    (φ.mapLanguage f).Realize s ↔ @AlphaFormula.Realize L M (f.reduct M) φ s := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact Formula.mapLanguage_realize_reduct f φ s

end PolishSpaceBook.NamedFirstOrder
