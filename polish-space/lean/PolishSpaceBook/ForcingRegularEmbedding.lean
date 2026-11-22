module

public import PolishSpaceBook.ForcingInternalRegularCodes

@[expose] public section

/-! # The represented dense embedding into the internal regular-set algebra -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic InternalBooleanAlgebra
universe u

lemma condition_eq_of_val_eq {S : ZFSet.{u}} {p q : Condition S} (h : p.val = q.val) : p = q := by
  cases p; cases q; cases h; rfl

def principalConditionCode (P R p : ZFSet.{u}) : ZFSet.{u} := P.sep (fun q => pair q p ∈ R)

lemma principalConditionCode_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (P R p : M) : principalConditionCode P.val R.val p.val ∈ M := by
  exact (BoundedSetPredicate.pairMember 0 2 1).separation_mem hM (hsep _) ![R, p] P.property

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
  (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (P R : M) [PartialOrder (Condition P.val)]
  (hR : ∀ p q : Condition P.val, pair p.val q.val ∈ R.val ↔ p ≤ q)
  (hseparative : ∀ p q : Condition P.val, ¬p ≤ q → ∃ r ≤ p, incompatible P.val r q)

local notation "Alg" => internalRegularBooleanAlgebra hM hinf hpair hunion hsep P R hR
local notation "B" => regularCarrierInModel hM hpower hsep P R

include hR in
lemma principalConditionCode_correct (p : Condition P.val) :
    conditionsOfCode P.val (principalConditionCode P.val R.val p.val) = Set.Iic p := by
  ext q
  exact (mem_sep.trans (and_iff_right q.property)).trans (hR q p)

include hseparative in
lemma principal_condition_saturated (p : Condition P.val) : forcingDense (Set.Iic p) ⊆ Set.Iic p := by
  intro q hq
  by_contra hqp
  obtain ⟨r, hrq, hrp⟩ := hseparative q p hqp
  obtain ⟨s, hsr, hsp⟩ := hq r hrq
  exact hrp ⟨s, hsr, hsp⟩

def regularPrincipal (p : Condition P.val) : BooleanElement (B).val :=
  ⟨principalConditionCode P.val R.val p.val, by
    apply (mem_internalRegularCarrier hR M _).mpr
    refine ⟨principalConditionCode_mem hM hsep P R ⟨p.val, hM.mem_trans p.property P.property⟩,
      (fun _ h => (mem_sep.mp h).1), ?_, ?_⟩ <;> rw [principalConditionCode_correct P R hR]
    · exact isLowerSet_Iic p
    · exact principal_condition_saturated P hseparative p⟩

lemma regularPrincipal_ne_bot (p : Condition P.val) :
    letI := Alg
    regularPrincipal hM hpower hsep P R hR hseparative p ≠ ⊥ := by
  let _ := Alg
  intro he
  have hp : p.val ∈ (regularPrincipal hM hpower hsep P R hR hseparative p).val := by
    change p.val ∈ P.val.sep (fun q => pair q p.val ∈ R.val)
    exact mem_sep.mpr ⟨p.property, (hR p p).mpr le_rfl⟩
  rw [he, internalRegular_bot_val hM hinf hpair hunion hsep P R hR] at hp
  exact ZFSet.notMem_empty _ hp

lemma regularPrincipal_le_iff (p q : Condition P.val) :
    letI := Alg
    regularPrincipal hM hpower hsep P R hR hseparative p ≤
      regularPrincipal hM hpower hsep P R hR hseparative q ↔ p ≤ q := by
  let _ := Alg
  rw [internalRegular_le_iff hM hinf hpair hunion hsep P R hR]
  change P.val.sep (fun x => pair x p.val ∈ R.val) ⊆
    P.val.sep (fun x => pair x q.val ∈ R.val) ↔ _
  constructor
  · intro h
    exact (hR p q).mp (mem_sep.mp (h (mem_sep.mpr ⟨p.property, (hR p p).mpr le_rfl⟩))).2
  · intro h x hx
    obtain ⟨hxP, hxp⟩ := mem_sep.mp hx
    exact mem_sep.mpr ⟨hxP, (hR ⟨x, hxP⟩ q).mpr (((hR ⟨x, hxP⟩ p).mp hxp).trans h)⟩

def regularCompletionEmbedding :
    letI := Alg
    Condition P.val ↪o Condition (positiveSet B) := by
  letI := Alg
  refine {
    toFun := fun p => positive B (regularPrincipal hM hpower hsep P R hR hseparative p)
      (regularPrincipal_ne_bot hM hinf hpair hunion hpower hsep P R hR hseparative p)
    inj' := ?_
    map_rel_iff' := ?_ }
  · intro p q he
    have hv := congrArg (element B) he
    apply le_antisymm
    · exact (regularPrincipal_le_iff hM hinf hpair hunion hpower hsep P R hR hseparative p q).mp (le_of_eq hv)
    · exact (regularPrincipal_le_iff hM hinf hpair hunion hpower hsep P R hR hseparative q p).mp (le_of_eq hv.symm)
  · intro p q
    exact regularPrincipal_le_iff hM hinf hpair hunion hpower hsep P R hR hseparative p q

theorem regularCompletionEmbedding_dense :
    letI := Alg
    ∀ b : Condition (positiveSet B), ∃ p : Condition P.val,
      regularCompletionEmbedding hM hinf hpair hunion hpower hsep P R hR hseparative p ≤ b := by
  let _ := Alg
  intro b
  have hne : (element B b).val ≠ ∅ := by
    intro he
    apply element_ne_bot B b
    apply BooleanElement.ext
    rw [he, internalRegular_bot_val hM hinf hpair hunion hsep P R hR]
  have hex : ∃ x, x ∈ (element B b).val := by
    by_contra hn
    apply hne
    ext x
    simp only [ZFSet.notMem_empty, iff_false]
    exact fun hx => hn ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hex
  have hb := (mem_internalRegularCarrier hR M (element B b).val).mp (element B b).property
  let p : Condition P.val := ⟨x, hb.2.1 hx⟩
  refine ⟨p, ?_⟩
  change regularPrincipal hM hpower hsep P R hR hseparative p ≤ element B b
  apply (internalRegular_le_iff hM hinf hpair hunion hsep P R hR _ _).mpr
  intro y hy
  change y ∈ P.val.sep (fun x => pair x p.val ∈ R.val) at hy
  obtain ⟨hyP, hyp⟩ := mem_sep.mp hy
  exact hb.2.2.1 ((hR ⟨y, hyP⟩ p).mp hyp) hx

/-- The graph is defined by the bounded equation for a principal ideal. -/
def regularEmbeddingGraphPredicate : BoundedSetPredicate 4 :=
  .ex 0 (.ex 2 (.conj (.orderedPair 3 4 5)
    (.conj (.subset 5 0) (.all 0 (.iff (.member 6 5) (.pairMember 1 6 4))))))

def regularEmbeddingGraph (S T C : ZFSet.{u}) : ZFSet.{u} :=
  (prod S C).sep (fun z => regularEmbeddingGraphPredicate.eval ![S, T, C, z])

include hM hpair hunion hpower hsep in
omit [PartialOrder (Condition P.val)] in
lemma regularEmbeddingGraph_mem (C : M) : regularEmbeddingGraph P.val R.val C.val ∈ M := by
  have he (z : ZFSet.{u}) : Fin.snoc (Subtype.val ∘ ![P, R, C]) z = ![P.val, R.val, C.val, z] := by
    funext i; fin_cases i <;> rfl
  simpa only [regularEmbeddingGraph, he] using regularEmbeddingGraphPredicate.separation_mem hM (hsep _)
    ![P, R, C] (prod_mem_of_separation hM hpair hunion hpower (hsep _) P.property C.property)

lemma pair_mem_regularEmbeddingGraph (S T : ZFSet.{u}) {C p b : ZFSet.{u}} (hp : p ∈ S) (hb : b ∈ C) :
    pair p b ∈ regularEmbeddingGraph S T C ↔ b = principalConditionCode S T p := by
  simp only [regularEmbeddingGraph, mem_sep, pair_mem_prod, hp, hb, true_and,
    regularEmbeddingGraphPredicate, BoundedSetPredicate.eval, Fin.snoc, Fin.castLT]
  change (∃ x ∈ S, ∃ y ∈ C, pair p b = pair x y ∧
    y ⊆ S ∧ ∀ q ∈ S, q ∈ y ↔ pair q x ∈ T) ↔ _
  constructor
  · rintro ⟨x, _, y, _, he, hyP, h⟩
    obtain ⟨rfl, rfl⟩ := pair_inj.mp he
    ext q
    rw [principalConditionCode, mem_sep]
    exact ⟨fun hq => ⟨hyP hq, (h q (hyP hq)).mp hq⟩, fun hq => (h q hq.1).mpr hq.2⟩
  · intro he
    refine ⟨p, hp, b, hb, rfl, ?_, ?_⟩
    · rw [he]; exact fun _ h => (mem_sep.mp h).1
    · intro q hq; rw [he, principalConditionCode, mem_sep]; exact and_iff_right hq

lemma regularCompletionEmbedding_graph (p : Condition P.val) :
    letI := Alg
    ∀ b : Condition (positiveSet B),
      pair p.val b.val ∈ regularEmbeddingGraph P.val R.val (B).val ↔
        regularCompletionEmbedding hM hinf hpair hunion hpower hsep P R hR hseparative p = b := by
  let _ := Alg
  intro b
  have hb : b.val ∈ (B).val := (element B b).property
  rw [pair_mem_regularEmbeddingGraph P.val R.val p.property hb]
  change b.val = principalConditionCode P.val R.val p.val ↔ _
  exact ⟨fun h => condition_eq_of_val_eq h.symm, fun h => (congrArg (fun c : Condition (positiveSet B) => c.val) h).symm⟩

end PolishSpaceBook.SetTheoryModels
