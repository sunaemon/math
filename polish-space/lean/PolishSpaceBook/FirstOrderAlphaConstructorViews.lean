module

public import PolishSpaceBook.FirstOrderAlphaSubstitution

@[expose] public section

/-! # Constructor inversion on alpha-classes

The representative of a quantified class may have a different bound name.
The view records equality of every capture-avoiding instance instead of
identifying those names.
-/
namespace PolishSpaceBook.NamedFirstOrder.AlphaFormula
open FirstOrder Language
universe u v
variable {L : Language.{u,v}}

theorem mk_binary_view {φ : Formula L} {c : Connective} {A B : AlphaFormula L}
    (h : mk φ = binary c A B) :
    ∃ ψ χ, φ = .binary c ψ χ ∧ mk ψ = A ∧ mk χ = B := by
  induction A using Quotient.inductionOn with
  | _ A =>
    induction B using Quotient.inductionOn with
    | _ B =>
      have hr := ((mk_eq_iff φ (.binary c A B)).mp h).nameRel
      cases hr with
      | binary c hA hB =>
        exact ⟨_, _, rfl, (mk_eq_iff _ _).mpr hA.eq_alpha,
          (mk_eq_iff _ _).mpr hB.eq_alpha⟩

theorem mk_quant_view {φ : Formula L} {q : Quantifier} {x : ℕ} {A : AlphaFormula L}
    (h : mk φ = quant q x A) :
    ∃ y ψ, φ = .quant q y ψ ∧
      ∀ t : L.Term ℕ, mk (ψ.subst y t) = A.subst x t := by
  induction A using Quotient.inductionOn with
  | _ A =>
    have ha := (mk_eq_iff φ (.quant q x A)).mp h
    have hr := ha.nameRel
    cases hr with
    | quant q hb =>
      refine ⟨_, _, rfl, ?_⟩
      intro t
      exact (mk_eq_iff _ _).mpr (ha.instantiate t)

theorem mk_equal_view {φ : Formula L} {t r : L.Term ℕ}
    (h : mk φ = mk (.equal t r)) : φ = .equal t r := by
  have hr := ((mk_eq_iff _ _).mp h).nameRel
  cases hr with
  | equal ht hr => rw [ht.eq_eq, hr.eq_eq]

theorem mk_falsum_view {φ : Formula L}
    (h : mk φ = mk .falsum) : φ = .falsum := by
  have hr := ((mk_eq_iff _ _).mp h).nameRel
  cases hr
  rfl

end PolishSpaceBook.NamedFirstOrder.AlphaFormula
