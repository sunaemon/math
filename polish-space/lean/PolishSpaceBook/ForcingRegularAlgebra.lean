module

public import PolishSpaceBook.ForcingLogicalOperations
public import Mathlib.Order.UpperLower.Principal
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra

@[expose] public section

/-! # Regular lower sets of a forcing order -/

noncomputable section
namespace PolishSpaceBook
open Set
variable {P : Type*} [Preorder P]

lemma lowerSet_compl_carrier (U : LowerSet P) :
    ((Uᶜ : LowerSet P) : Set P) = forcingNeg (U : Set P) := by
  ext p
  constructor
  · intro hp q hqp hq
    have hqc := (Uᶜ).lower hqp hp
    have hz : q ∈ (U ⊓ Uᶜ : LowerSet P) := ⟨hq, hqc⟩
    rw [inf_compl_eq_bot] at hz
    exact hz
  · intro h
    have hd : Disjoint (LowerSet.Iic p) U := by
      apply disjoint_iff.mpr
      apply LowerSet.ext
      ext q
      constructor
      · rintro ⟨hqp, hq⟩
        exact (h q hqp hq).elim
      · intro hq; exact hq.elim
    exact (le_compl_iff_disjoint_right.mpr hd) le_rfl

lemma forcingNeg_neg_eq_dense (U : Set P) : forcingNeg (forcingNeg U) = forcingDense U := by
  ext p
  simp only [forcingNeg, forcingDense, Set.mem_ofPred_eq]
  constructor
  · intro h q hqp
    by_contra hn
    apply h q hqp
    intro r hrq hr
    exact hn ⟨r, hrq, hr⟩
  · intro h q hqp hn
    obtain ⟨r, hrq, hr⟩ := h q hqp
    exact hn r hrq hr

lemma lowerSet_double_compl_carrier (U : LowerSet P) :
    ((Uᶜᶜ : LowerSet P) : Set P) = forcingDense (U : Set P) := by
  rw [lowerSet_compl_carrier, lowerSet_compl_carrier, forcingNeg_neg_eq_dense]

abbrev RegularForcingSet (P : Type*) [Preorder P] := Heyting.Regular (LowerSet P)

instance regularForcingSetCompleteBooleanAlgebra : CompleteBooleanAlgebra (RegularForcingSet P) := by
  let C : CompleteLattice (Heyting.Regular (LowerSet P)) := Heyting.Regular.gi.liftCompleteLattice
  exact { (inferInstance : BooleanAlgebra (Heyting.Regular (LowerSet P))) with
    sSup := C.sSup
    isLUB_sSup := C.isLUB_sSup
    sInf := C.sInf
    isGLB_sInf := C.isGLB_sInf }

def regularForcingSet (U : Set P) (hl : IsLowerSet U) (hs : forcingDense U ⊆ U) : RegularForcingSet P :=
  ⟨⟨U, hl⟩, by
    apply LowerSet.ext
    rw [lowerSet_double_compl_carrier]
    apply Set.Subset.antisymm hs
    intro p hp q hqp
    exact ⟨q, le_rfl, hl hqp hp⟩⟩

lemma regularForcingSet_saturated (U : RegularForcingSet P) :
    forcingDense (U.val : Set P) ⊆ (U.val : Set P) := by
  rw [← lowerSet_double_compl_carrier]
  exact Eq.subset (congrArg (fun V : LowerSet P => (V : Set P)) U.property)

lemma regularForcingSet_compl_carrier (U : RegularForcingSet P) :
    ((Uᶜ).val : Set P) = forcingNeg (U.val : Set P) := lowerSet_compl_carrier U.val

lemma regularForcingSet_sup_carrier (U V : RegularForcingSet P) :
    ((U ⊔ V).val : Set P) = forcingDense ((U.val : Set P) ∪ (V.val : Set P)) := by
  change (((U.val ⊔ V.val)ᶜᶜ : LowerSet P) : Set P) = _
  rw [lowerSet_double_compl_carrier]
  rfl

lemma regularForcingSet_sSup_carrier (S : Set (RegularForcingSet P)) :
    ((sSup S).val : Set P) = forcingDense (⋃ U ∈ S, (U.val : Set P)) := by
  change (((sSup ((fun U : RegularForcingSet P => U.val) '' S))ᶜᶜ : LowerSet P) : Set P) = _
  rw [lowerSet_double_compl_carrier, LowerSet.coe_sSup]
  simp only [Set.biUnion_image]

end PolishSpaceBook
