module

public import PolishSpaceBook.FirstOrderProofCongruence

@[expose] public section

/-!
# Natural-deduction rules for theory consequences

Merge finite proof supports and discharge added assumptions. Quantifier rules
retain the explicit freshness condition for every formula in the theory.
-/

noncomputable section
namespace PolishSpaceBook.NamedFirstOrder
open FirstOrder Language AlphaFormula
universe u v
variable {L : Language.{u,v}}
local instance theoryRulesDecidableEq : DecidableEq (AlphaFormula L) := Classical.decEq _
namespace ProvesFrom

/-- Disjunction elimination with possibly different finite supports in the two branches. -/
theorem orElim {T : Set (AlphaFormula L)} {φ ψ χ : AlphaFormula L}
    (hd : ProvesFrom T (binary .disj φ ψ))
    (hl : ProvesFrom (insert φ T) χ) (hr : ProvesFrom (insert ψ T) χ) : ProvesFrom T χ := by
  have hp := (deduction.mp hl).map₂ (deduction.mp hr) (fun {Γ} hl hr => by
    apply Derives.impIntro
    apply Derives.orElim (.hyp Γ (binary .disj φ ψ))
    · exact .impElim (hl.weaken (by intro θ hθ; simp [hθ])) (.hyp _ φ)
    · exact .impElim (hr.weaken (by intro θ hθ; simp [hθ])) (.hyp _ ψ))
  exact hp.impElim hd

/-- A name absent from every theory assumption may be universally quantified. -/
theorem allIntro {T : Set (AlphaFormula L)} {φ : AlphaFormula L} (x : ℕ)
    (hx : ∀ θ ∈ T, x ∉ θ.fv) (h : ProvesFrom T φ) : ProvesFrom T (quant .all x φ) := by
  obtain ⟨Γ,hΓ,h⟩ := h
  refine ⟨Γ,hΓ,Derives.allIntro x h ?_⟩
  intro hm
  obtain ⟨θ,hθ,hxθ⟩ := Finset.mem_biUnion.mp hm
  exact hx θ (hΓ θ hθ) hxθ

/-- Existential elimination combines finite supports before discharging the witness assumption. -/
theorem exElim {T : Set (AlphaFormula L)} (x y : ℕ) (φ χ : AlphaFormula L)
    (he : ProvesFrom T (quant .ex x φ)) (hb : ProvesFrom (insert (φ.subst x (.var y)) T) χ)
    (hyT : ∀ θ ∈ T, y ∉ θ.fv) (hyχ : y ∉ χ.fv) (hyφ : y ∉ (quant .ex x φ).fv) : ProvesFrom T χ := by
  obtain ⟨Γ,hΓ,he⟩ := he
  obtain ⟨Δ,hΔ,hb⟩ := deduction.mp hb
  have hctx (θ) (hθ : θ ∈ Γ ∪ Δ) : θ ∈ T :=
    (Finset.mem_union.mp hθ).elim (hΓ θ) (hΔ θ)
  refine ⟨Γ ∪ Δ,hctx,Derives.exElim x y φ χ (he.weaken Finset.subset_union_left) ?_ ?_⟩
  · exact .impElim (hb.weaken (Finset.Subset.trans Finset.subset_union_right (Finset.subset_insert _ _)))
      (.hyp _ _)
  · simp only [Finset.mem_union,not_or]
    refine ⟨⟨?_,hyχ⟩,hyφ⟩
    intro hm
    obtain ⟨θ,hθ,hyθ⟩ := Finset.mem_biUnion.mp hm
    exact hyT θ (hctx θ hθ) hyθ

end ProvesFrom
end PolishSpaceBook.NamedFirstOrder
