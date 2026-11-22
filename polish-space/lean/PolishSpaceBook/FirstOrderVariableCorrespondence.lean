module

public import PolishSpaceBook.FirstOrderTermGraphUniqueness

@[expose] public section

/-!
# Variable substitutions as functional name correspondences

The correspondence need not be injective: substitution may merge two free
names. Its right-hand name still determines the left-hand name uniquely, and
that property makes two corresponding formulas equal as alpha-classes.
-/

namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
namespace AlphaFormula.Corresponds

/-- A relation functional from right to left determines the left formula up to alpha-equivalence. -/
theorem left_unique {R : ℕ → ℕ → Prop} {φ ψ χ : AlphaFormula L}
    (h : Corresponds R φ ψ) (h' : Corresponds R χ ψ)
    (hR : ∀ a b c, R a b → R c b → a = c) : φ = χ := by
  rcases h with ⟨a,b,rfl,rfl,h⟩
  rcases h' with ⟨c,d,rfl,hd,h'⟩
  have hh := h'.transport (.refl c) (Quotient.exact hd)
  exact Quotient.sound ((h.trans hh.symm (fun a b c hab hcb => hR a b c hab hcb)).eq_alpha)

end AlphaFormula.Corresponds

/-- Replacing one term variable compares with the original under the replacement map. -/
theorem termSubst_var_corresponds (t : L.Term ℕ) (x y : ℕ) :
    TermRel (fun a b => a = if b = x then y else b) (termSubst t x (.var y)) t := by
  have h := (TermRel.refl t).subst x x (S := fun a b => a = if b = x then y else b)
    (a := .var y) (b := .var x) (.var (by simp))
    (fun a b hab => by subst b; rfl)
    (fun a b hab ha => by subst b; simp [ha])
  simpa only [termSubst_self] using h

namespace AlphaFormula

/-- Capture-avoiding variable substitution follows the replacement relation even when names merge. -/
theorem subst_var_corresponds (φ : AlphaFormula L) (x y : ℕ) :
    Corresponds (fun a b => a = if b = x then y else b) (φ.subst x (.var y)) φ := by
  induction φ using Quotient.inductionOn with
  | _ φ =>
    have h := (Formula.NameRel.refl φ).subst x x (S := fun a b => a = if b = x then y else b)
      (T := .var y) (U := .var x) (.var (by simp))
      (fun a b hab => by subst b; rfl)
      (fun a b hab ha => by subst b; simp [ha])
    apply (corresponds_mk _ _ _).mpr
    simpa only [Formula.subst_self] using h

/-- A simultaneous variable instance compares with its template by the finite replacement map. -/
theorem simultaneous_vars_corresponds {n : ℕ} (φ : AlphaFormula L)
    (a : Fin n → ℕ) (hf : φ.fv ⊆ Finset.range n) :
    Corresponds (fun u v => u = if h : v < n then a ⟨v,h⟩ else v)
      (φ.simultaneous (fun i => .var (a i))) φ := by
  have h := simultaneous_corresponds φ (fun i => .var (a i)) (fun i : Fin n => .var i.val)
    (fun u v => u = if h : v < n then a ⟨v,h⟩ else v) hf
    (fun i => .var (by simp only [dite_eq_left i.isLt]))
  simpa only [simultaneous_vars] using h

end AlphaFormula
end PolishSpaceBook.NamedFirstOrder
