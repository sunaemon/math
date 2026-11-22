module

public import PolishSpaceBook.ForcingInternalRegularCodes
public import Mathlib.Order.Hom.BoundedLattice

@[expose] public section

/-! # The faithful Boolean representation of internal regular sets -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic
universe u

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (P R : M) [Preorder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)

local notation "Alg" => internalRegularBooleanAlgebra hM hinf hpair hunion hsep P R hR
local notation "eqv" => internalRegularEquiv hM hinf hpair hunion hsep P R hR

lemma decodeInternalRegular_inf (a b : BooleanElement (internalRegularCarrier M P.val R.val)) :
    letI := Alg
    decodeInternalRegular hR M (a ⊓ b) = decodeInternalRegular hR M a ⊓ decodeInternalRegular hR M b := by
  let _ := Alg
  change ((eqv) ((eqv).symm ((eqv) a ⊓ (eqv) b))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma decodeInternalRegular_sup (a b : BooleanElement (internalRegularCarrier M P.val R.val)) :
    letI := Alg
    decodeInternalRegular hR M (a ⊔ b) = decodeInternalRegular hR M a ⊔ decodeInternalRegular hR M b := by
  let _ := Alg
  change ((eqv) ((eqv).symm ((eqv) a ⊔ (eqv) b))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma decodeInternalRegular_compl (a : BooleanElement (internalRegularCarrier M P.val R.val)) :
    letI := Alg
    decodeInternalRegular hR M aᶜ = (decodeInternalRegular hR M a)ᶜ := by
  let _ := Alg
  change ((eqv) ((eqv).symm ((eqv) a)ᶜ)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma decodeInternalRegular_bot :
    letI := Alg
    decodeInternalRegular hR M ⊥ = ⊥ := by
  let _ := Alg
  change ((eqv) ((eqv).symm ⊥)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma decodeInternalRegular_top :
    letI := Alg
    decodeInternalRegular hR M ⊤ = ⊤ := by
  let _ := Alg
  change ((eqv) ((eqv).symm ⊤)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The internal algebra is a Boolean subalgebra of the external regular-set
algebra. This certifies finite operations, without an external completeness claim. -/
def internalRegularBoundedLatticeHom :
    letI := Alg
    BoundedLatticeHom (BooleanElement (internalRegularCarrier M P.val R.val)) (RegularForcingSet (Condition P.val)) := by
  letI := Alg
  exact {
    toFun := decodeInternalRegular hR M
    map_inf' := decodeInternalRegular_inf hM hinf hpair hunion hsep P R hR
    map_sup' := decodeInternalRegular_sup hM hinf hpair hunion hsep P R hR
    map_bot' := decodeInternalRegular_bot hM hinf hpair hunion hsep P R hR
    map_top' := decodeInternalRegular_top hM hinf hpair hunion hsep P R hR }

end PolishSpaceBook.SetTheoryModels
