module

public import PolishSpaceBook.FirstOrderLindenbaum

@[expose] public section

/-!
# Transporting the named calculus along a language map

The language and term maps are mathlib's canonical maps. Variable names and
binders are unchanged, so free-variable sets and the prescribed fresh-name
choices are unchanged as well. This is the transport used when new Henkin
constant symbols are adjoined.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language
universe u v u' v' u'' v''
variable {L : Language.{u,v}} {K : Language.{u',v'}} {J : Language.{u'',v''}}

theorem varFinset_onTerm (f : L →ᴸ K) (t : L.Term ℕ) : (f.onTerm t).varFinset = t.varFinset := by
  induction t with
  | var => rfl
  | func g ts ih => simp only [LHom.onTerm, Term.varFinset, ih]

theorem onTerm_termSubst (f : L →ᴸ K) (t : L.Term ℕ) (x : ℕ) (r : L.Term ℕ) :
    f.onTerm (termSubst t x r) = termSubst (f.onTerm t) x (f.onTerm r) := by
  induction t with
  | var y => by_cases h : y = x <;> simp [termSubst, Term.subst, h]
  | func g ts ih =>
    simp only [termSubst, Term.subst, LHom.onTerm]
    congr 1
    funext i
    exact ih i

namespace Formula

def mapLanguage (f : L →ᴸ K) : Formula L → Formula K
  | .falsum => .falsum
  | .equal t r => .equal (f.onTerm t) (f.onTerm r)
  | .rel R ts => .rel (f.onRelation R) (fun i => f.onTerm (ts i))
  | .binary c φ ψ => .binary c (mapLanguage f φ) (mapLanguage f ψ)
  | .quant q x φ => .quant q x (mapLanguage f φ)

@[simp] theorem fv_mapLanguage (f : L →ᴸ K) (φ : Formula L) : (φ.mapLanguage f).fv = φ.fv := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapLanguage, fv, varFinset_onTerm]
  | rel => simp [mapLanguage, fv, varFinset_onTerm]
  | binary c φ ψ ihφ ihψ => simp [mapLanguage, fv, ihφ, ihψ]
  | quant q x φ ih => simp [mapLanguage, fv, ih]

@[simp] theorem nodes_mapLanguage (f : L →ᴸ K) (φ : Formula L) :
    (φ.mapLanguage f).nodes = φ.nodes := by
  induction φ <;> simp_all [mapLanguage, nodes]

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    The inclusion changes only the ambient language of function and relation symbols, leaving their arities and
    all variable names unchanged. Induction on terms proves preservation of free variables and commutation with
    term substitution. Induction on formulas preserves their free-variable sets and constructor counts.
    To check formula substitution, induct on the recursion budget in its definition. At a quantifier, the test for
    capture is unchanged, and a renaming clause chooses the same least fresh variable in both languages.
    Apply induction to both recursive calls in that clause. Since the constructor count is unchanged, this proves
    the substitution identity for the total operation. The generators of $\alpha$-equivalence are therefore preserved.
-/
theorem mapLanguage_substFuel (f : L →ᴸ K) (k : ℕ) (φ : Formula L) (x : ℕ) (t : L.Term ℕ) :
    (substFuel k φ x t).mapLanguage f = substFuel k (φ.mapLanguage f) x (f.onTerm t) := by
  induction k generalizing φ x t with
  | zero => rfl
  | succ k ih =>
    cases φ with
    | falsum => rfl
    | equal a b => simp [substFuel, mapLanguage, onTerm_termSubst]
    | rel R ts => simp [substFuel, mapLanguage, onTerm_termSubst]
    | binary c φ ψ => simp [substFuel, mapLanguage, ih]
    | quant q y φ =>
      simp only [substFuel, mapLanguage, varFinset_onTerm, fv_mapLanguage]
      split_ifs <;> simp only [mapLanguage, ih, LHom.onTerm]

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Language inclusion
-/
@[simp] theorem mapLanguage_subst (f : L →ᴸ K) (φ : Formula L) (x : ℕ) (t : L.Term ℕ) :
    (φ.subst x t).mapLanguage f = (φ.mapLanguage f).subst x (f.onTerm t) := by
  simp only [subst, nodes_mapLanguage, mapLanguage_substFuel]

theorem Alpha.mapLanguage {φ ψ : Formula L} (h : Alpha φ ψ) (f : L →ᴸ K) :
    Alpha (φ.mapLanguage f) (ψ.mapLanguage f) := by
  induction h with
  | refl => exact .refl _
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | binary c h₁ h₂ ih₁ ih₂ => exact .binary c ih₁ ih₂
  | quant q x h ih => exact .quant q x ih
  | rename q φ x z hz =>
    simpa only [Formula.mapLanguage, mapLanguage_subst, LHom.onTerm] using
      Alpha.rename q (φ.mapLanguage f) x z (by simpa using hz)

@[simp] theorem mapLanguage_id (φ : Formula L) : φ.mapLanguage (LHom.id L) = φ := by
  induction φ <;> simp_all [mapLanguage]

@[simp] theorem mapLanguage_comp (φ : Formula L) (f : L →ᴸ K) (g : K →ᴸ J) :
    (φ.mapLanguage f).mapLanguage g = φ.mapLanguage (g.comp f) := by
  induction φ <;> simp_all [mapLanguage, LHom.comp_onTerm]

end Formula
namespace AlphaFormula

def mapLanguage (f : L →ᴸ K) : AlphaFormula L → AlphaFormula K :=
  Quotient.map (Formula.mapLanguage f) (by intro a b h; exact h.mapLanguage f)

@[simp] theorem mapLanguage_mk (f : L →ᴸ K) (φ : Formula L) :
    (mk φ).mapLanguage f = mk (φ.mapLanguage f) := rfl

@[simp] theorem mapLanguage_id (φ : AlphaFormula L) : φ.mapLanguage (LHom.id L) = φ := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact congrArg mk (Formula.mapLanguage_id φ)

@[simp] theorem mapLanguage_comp (φ : AlphaFormula L) (f : L →ᴸ K) (g : K →ᴸ J) :
    (φ.mapLanguage f).mapLanguage g = φ.mapLanguage (g.comp f) := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact congrArg mk (Formula.mapLanguage_comp φ f g)

@[simp] theorem mapLanguage_falsum (f : L →ᴸ K) :
    (falsum : AlphaFormula L).mapLanguage f = falsum := rfl

@[simp] theorem mapLanguage_equal (f : L →ᴸ K) (t r : L.Term ℕ) :
    (equal t r).mapLanguage f = equal (f.onTerm t) (f.onTerm r) := rfl

@[simp] theorem mapLanguage_binary (f : L →ᴸ K) (c : Connective) (φ ψ : AlphaFormula L) :
    (binary c φ ψ).mapLanguage f = binary c (φ.mapLanguage f) (ψ.mapLanguage f) := by
  induction φ, ψ using Quotient.inductionOn₂ with
  | _ φ ψ => rfl

@[simp] theorem mapLanguage_quant (f : L →ᴸ K) (q : Quantifier) (x : ℕ) (φ : AlphaFormula L) :
    (quant q x φ).mapLanguage f = quant q x (φ.mapLanguage f) := by
  induction φ using Quotient.inductionOn with
  | _ φ => rfl

@[simp] theorem mapLanguage_subst (f : L →ᴸ K) (φ : AlphaFormula L) (x : ℕ) (t : L.Term ℕ) :
    (φ.subst x t).mapLanguage f = (φ.mapLanguage f).subst x (f.onTerm t) := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact congrArg mk (Formula.mapLanguage_subst f φ x t)

@[simp] theorem fv_mapLanguage (f : L →ᴸ K) (φ : AlphaFormula L) : (φ.mapLanguage f).fv = φ.fv := by
  induction φ using Quotient.inductionOn with
  | _ φ => exact Formula.fv_mapLanguage f φ

end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
