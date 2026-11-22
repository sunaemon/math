module

public import PolishSpaceBook.ForcingInternalRegularSets

@[expose] public section

/-! # The Boolean algebra on the model's regular-set carrier -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic BoundedSetPredicate
universe u

lemma conditionSet_inter (P : ZFSet.{u}) (U V : Set (Condition P)) :
    conditionSet P (U ∩ V) = conditionSet P U ∩ conditionSet P V := by
  ext x
  simp only [conditionSet, mem_sep, ZFSet.mem_inter, Set.mem_inter_iff]
  aesop

lemma conditionSet_union (P : ZFSet.{u}) (U V : Set (Condition P)) :
    conditionSet P (U ∪ V) = conditionSet P U ∪ conditionSet P V := by
  ext x
  simp only [conditionSet, mem_sep, ZFSet.mem_union, Set.mem_union]
  aesop

lemma conditionSet_forcingNeg {P R : ZFSet.{u}} [Preorder (Condition P)]
    (hR : ∀ p q : Condition P, pair p.val q.val ∈ R ↔ p ≤ q) (U : Set (Condition P)) :
    conditionSet P (forcingNeg U) = regularNegCode P R (conditionSet P U) := by
  have he := regularNegCode_correct hR (conditionSet P U)
  rw [conditionsOfCode_conditionSet] at he
  rw [← he, conditionSet_conditionsOfCode]
  exact fun _ h => (mem_sep.mp h).1

lemma conditionSet_forcingDense {P R : ZFSet.{u}} [Preorder (Condition P)]
    (hR : ∀ p q : Condition P, pair p.val q.val ∈ R ↔ p ≤ q) (U : Set (Condition P)) :
    conditionSet P (forcingDense U) = regularDenseCode P R (conditionSet P U) := by
  have he := regularDenseCode_correct hR (conditionSet P U) (conditionSet_subset P U)
  rw [conditionsOfCode_conditionSet] at he
  rw [← he, conditionSet_conditionsOfCode]
  exact fun _ h => (mem_sep.mp h).1

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (P R : M) [Preorder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)

def internalRegularSubalgebra : BooleanSubalgebra (RegularForcingSet (Condition P.val)) where
  carrier U := conditionSet P.val (U.val : Set (Condition P.val)) ∈ M
  infClosed' := by
    intro U hU V hV
    change conditionSet P.val ((U.val : Set (Condition P.val)) ∩ V.val) ∈ M
    apply conditionSet_mem hM P _ (BoundedSetPredicate.conj (.member 2 0) (.member 2 1)).compile (hsep _)
      ![⟨conditionSet P.val U.val, hU⟩, ⟨conditionSet P.val V.val, hV⟩]
    intro p
    rw [BoundedSetPredicate.realize_compile hM]
    change (p.val ∈ conditionSet P.val U.val ∧ p.val ∈ conditionSet P.val V.val) ↔ _
    rw [mem_conditionSet, mem_conditionSet]
    rfl
  supClosed' := by
    intro U hU V hV
    change conditionSet P.val ((U ⊔ V).val : Set (Condition P.val)) ∈ M
    rw [regularForcingSet_sup_carrier, conditionSet_forcingDense hR, conditionSet_union]
    exact regularDenseCode_mem hM hsep P R
      ⟨_, binaryUnion_mem hM hpair hunion hU hV⟩
  compl_mem' := by
    intro U hU
    change conditionSet P.val ((Uᶜ).val : Set (Condition P.val)) ∈ M
    rw [regularForcingSet_compl_carrier, conditionSet_forcingNeg hR]
    exact regularNegCode_mem hM hsep P R ⟨_, hU⟩
  bot_mem' := by
    change conditionSet P.val ∅ ∈ M
    have he : conditionSet P.val ∅ = ∅ := by ext x; simp [conditionSet]
    rw [he]
    exact empty_mem_of_infinity hM hinf

/-- The actual coded carrier is equivalent to the subalgebra of ambient
regular sets whose codes belong to M. Only finite algebraic operations are
transported along this equivalence. -/
def internalRegularEquiv : BooleanElement (internalRegularCarrier M P.val R.val) ≃
    internalRegularSubalgebra hM hinf hpair hunion hsep P R hR where
  toFun U := ⟨decodeInternalRegular hR M U, by
    change conditionSet P.val (conditionsOfCode P.val U.val) ∈ M
    rw [conditionSet_conditionsOfCode P.val U.val
      ((mem_internalRegularCarrier hR M U.val).mp U.property).2.1]
    exact ((mem_internalRegularCarrier hR M U.val).mp U.property).1⟩
  invFun U := ⟨conditionSet P.val U.val.val, by
    apply (mem_internalRegularCarrier hR M _).mpr
    refine ⟨U.property, conditionSet_subset _ _, ?_, ?_⟩ <;> rw [conditionsOfCode_conditionSet]
    · exact U.val.val.lower
    · exact regularForcingSet_saturated U.val⟩
  left_inv U := by
    apply BooleanElement.ext
    exact conditionSet_conditionsOfCode P.val U.val
      ((mem_internalRegularCarrier hR M U.val).mp U.property).2.1
  right_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    apply LowerSet.ext
    exact conditionsOfCode_conditionSet P.val U.val.val

abbrev internalRegularBooleanAlgebra : BooleanAlgebra (BooleanElement (internalRegularCarrier M P.val R.val)) :=
  (internalRegularEquiv hM hinf hpair hunion hsep P R hR).booleanAlgebra

end PolishSpaceBook.SetTheoryModels
