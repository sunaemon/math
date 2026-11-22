module

public import PolishSpaceBook.FirstOrderNaturalDeduction
public import PolishSpaceBook.FirstOrderPermutation

@[expose] public section

/-!
# Admissible renaming and weakening

The strengthened induction permits both a permutation and an enlarged context.
At an eigenvariable rule, a transposition moves its eigenvariable outside the
new context while fixing the rule's external formulas up to alpha-equivalence.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance : DecidableEq (AlphaFormula L) := Classical.decEq _

namespace Derives

/-- A fresh transposition fixes the old context inside the larger context. -/
private theorem fresh_context {Γ Δ : Context L} (e : Equiv.Perm ℕ) (x z : ℕ)
    (h : ∀ φ ∈ Γ, φ.permute e ∈ Δ) (hx : x ∉ Γ.fv) (hz : z ∉ Δ.fv) :
    ∀ φ ∈ Γ, φ.permute (e.trans (Equiv.swap (e x) z)) ∈ Δ := by
  intro φ hφ
  rw [← permute_comp, permute_swap_fixed]
  · exact h φ hφ
  · simpa using fun hxφ => hx (Context.mem_fv_of_mem hφ hxφ)
  · exact fun hzφ => hz (Context.mem_fv_of_mem (h φ hφ) hzφ)

/-- Simultaneously rename all variables and enlarge the finite hypothesis set. -/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: statement
  kind: lemma
  title: Renaming and weakening
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    \begin{proof}
    Prove the first assertion by induction on the derivation, allowing both the permutation and the enlarged context
    to vary. For the assumption rule, the renamed assumption belongs to the new context. The propositional rules
    follow by applying induction to their premises; for a discharged assumption, add its renamed formula to the new
    context. Equality and quantifier instantiation use the substitution identity above. The two eigenvariable rules
    require a fresh choice.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For $(\forall\text{I})$, the premise is $\Gamma\vdash\varphi$ and $x\notin\FreeVars{\Gamma}$.
    Choose $z$ outside $\FreeVars{\Delta}\cup\FreeVars{e(\varphi)}$, let $\tau$ interchange $e(x)$ and $z$, and
    put $f:=\tau\circ e$. The transposition fixes every formula of $e(\Gamma)$ and fixes
    $e(\forallbind{x}{\varphi})$: the first name is absent from their free-variable sets, and the second was chosen
    fresh. Apply induction to the premise with permutation $f$ and context $\Delta$.
    It gives $\Delta\vdash f(\varphi)$. Since $f(x)=z\notin\FreeVars{\Delta}$, universal introduction gives
    $\Delta\vdash\forallbind{z}{f(\varphi)}$, whose conclusion is $e(\forallbind{x}{\varphi})$.
-/
/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    For $(\exists\text{E})$, the premises are $\Gamma\vdash\existsbind{x}{\varphi}$ and
    $\Gamma,\varphi\subst{x}{y}\vdash\chi$, with the displayed side condition on $y$.
    Choose $z$ outside the free-variable sets of $\Delta$, $e(\chi)$, and $e(\existsbind{x}{\varphi})$.
    Let $\tau$ interchange $e(y)$ and $z$, and put $f:=\tau\circ e$.
    The side condition and freshness imply that $\tau$ fixes $e(\Gamma)$, $e(\chi)$, and
    $e(\existsbind{x}{\varphi})$. Apply induction to both premises with permutation $f$, adding
    $f(\varphi)\subst{f(x)}{z}$ to $\Delta$ in the second premise.
    The substitution identity identifies this added assumption with the renamed original assumption.
    Existential elimination with eigenvariable $z$ now gives $\Delta\vdash f(\chi)$, which is the required conclusion.
    This argument also allows $y=x$.
-/
theorem permute_weaken {Γ : Context L} {φ : AlphaFormula L} (h : Derives Γ φ)
    (e : Equiv.Perm ℕ) (Δ : Context L) (hΓ : ∀ ψ ∈ Γ, ψ.permute e ∈ Δ) :
    Derives Δ (φ.permute e) := by
  induction h generalizing e Δ with
  | hyp Γ φ => exact assumption (hΓ φ (Finset.mem_insert_self _ _))
  | andIntro hφ hψ ihφ ihψ => simpa using andIntro (ihφ e Δ hΓ) (ihψ e Δ hΓ)
  | andLeft h ih => exact andLeft (by simpa using ih e Δ hΓ)
  | andRight h ih => exact andRight (by simpa using ih e Δ hΓ)
  | orLeft ψ h ih => simpa using orLeft (ψ.permute e) (ih e Δ hΓ)
  | orRight φ h ih => simpa using orRight (φ.permute e) (ih e Δ hΓ)
  | @orElim Γ φ ψ χ hd hl hr ihd ihl ihr =>
    apply orElim (by simpa using ihd e Δ hΓ)
    · apply ihl e (insert (φ.permute e) Δ)
      intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hΓ A hA)
    · apply ihr e (insert (ψ.permute e) Δ)
      intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hΓ A hA)
  | @impIntro Γ φ ψ h ih =>
    rw [permute_binary]
    apply impIntro
    apply ih e (insert (φ.permute e) Δ)
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hΓ A hA)
  | impElim hf ha ihf iha => exact impElim (by simpa using ihf e Δ hΓ) (iha e Δ hΓ)
  | falseElim φ h ih => exact falseElim _ (by simpa using ih e Δ hΓ)
  | @allIntro Γ φ x h hx ih =>
    let z := NamedLambda.Term.fresh (Δ.fv ∪ (φ.permute e).fv)
    have hz : z ∉ Δ.fv ∧ z ∉ (φ.permute e).fv := by
      simpa only [z, Finset.mem_union, not_or] using
        NamedLambda.Term.fresh_not_mem (Δ.fv ∪ (φ.permute e).fv)
    let f := e.trans (Equiv.swap (e x) z)
    have hf : f x = z := by simp [f]
    have hp := ih f Δ (fresh_context e x z hΓ hx hz.1)
    have hd := allIntro z hp hz.1
    have hfix : (quant .all x φ).permute f = (quant .all x φ).permute e := by
      rw [← permute_comp]
      apply permute_swap_fixed
      · simp
      · exact fun hmem => hz.2 (Finset.mem_of_mem_erase (by simpa using hmem))
    rw [← hfix, permute_quant, hf]
    exact hd
  | allElim x φ t h ih =>
    rw [permute_subst]
    exact allElim (e x) (φ.permute e) (t.relabel e) (by simpa using ih e Δ hΓ)
  | exIntro x φ t h ih =>
    rw [permute_quant]
    exact exIntro (e x) (φ.permute e) (t.relabel e) (by simpa using ih e Δ hΓ)
  | @exElim Γ x y φ χ hex hc hy ihex ihc =>
    have hy' : y ∉ Γ.fv ∧ y ∉ χ.fv ∧ y ∉ (quant .ex x φ).fv := by
      simpa only [Finset.mem_union, not_or, and_assoc] using hy
    let z := NamedLambda.Term.fresh (Δ.fv ∪ (χ.permute e).fv ∪ ((quant .ex x φ).permute e).fv)
    have hz : z ∉ Δ.fv ∧ z ∉ (χ.permute e).fv ∧ z ∉ ((quant .ex x φ).permute e).fv := by
      simpa only [z, Finset.mem_union, not_or, and_assoc] using
        NamedLambda.Term.fresh_not_mem (Δ.fv ∪ (χ.permute e).fv ∪ ((quant .ex x φ).permute e).fv)
    let f := e.trans (Equiv.swap (e y) z)
    have hf : f y = z := by simp [f]
    have hχ : χ.permute f = χ.permute e := by
      rw [← permute_comp]
      exact permute_swap_fixed _ _ _ (by simpa using hy'.2.1) hz.2.1
    have hφ : (quant .ex x φ).permute f = (quant .ex x φ).permute e := by
      rw [← permute_comp]
      exact permute_swap_fixed _ _ _ (by simpa using hy'.2.2) hz.2.2
    have hΓ' := fresh_context e y z hΓ hy'.1 hz.1
    have he : Derives Δ (quant .ex (f x) (φ.permute f)) := by simpa using ihex f Δ hΓ'
    have hc' : Derives (insert ((φ.permute f).subst (f x) (.var (f y))) Δ) (χ.permute f) := by
      apply ihc f
      intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · simp
      · exact Finset.mem_insert_of_mem (hΓ' A hA)
    have hyf : f y ∉ Δ.fv ∪ (χ.permute f).fv ∪ (quant .ex (f x) (φ.permute f)).fv := by
      rw [hf, hχ, ← permute_quant, hφ]
      simpa only [Finset.mem_union, not_or, and_assoc] using hz
    rw [← hχ]
    exact exElim (f x) (f y) (φ.permute f) (χ.permute f) he hc' hyf
  | eqIntro Γ t => simpa using eqIntro Δ (t.relabel e)
  | eqElim φ x t r ht he iht ihe =>
    rw [permute_subst]
    exact eqElim (φ.permute e) (e x) (t.relabel e) (r.relabel e)
      (by simpa using iht e Δ hΓ) (by simpa using ihe e Δ hΓ)
  | excludedMiddle Γ φ => simpa [neg] using excludedMiddle Δ (φ.permute e)

/-@ booklink:
  source: polish-space-book/appendix-logic.md
  target: proof
  excerpt: |
    Taking $\Delta=e(\Gamma)$ proves invariance under variable permutations. Taking $e$ to be the identity proves
    weakening.
    \end{proof}
-/
theorem weaken {Γ Δ : Context L} {φ : AlphaFormula L} (h : Derives Γ φ) (hΓ : Γ ⊆ Δ) :
    Derives Δ φ := by
  simpa using h.permute_weaken (Equiv.refl ℕ) Δ (by intro ψ hψ; simpa using hΓ hψ)

theorem permute {Γ : Context L} {φ : AlphaFormula L} (h : Derives Γ φ) (e : Equiv.Perm ℕ) :
    Derives (Γ.permute e) (φ.permute e) :=
  h.permute_weaken e _ (by intro ψ hψ; exact Finset.mem_image.mpr ⟨ψ, hψ, rfl⟩)

end Derives
end PolishSpaceBook.NamedFirstOrder
