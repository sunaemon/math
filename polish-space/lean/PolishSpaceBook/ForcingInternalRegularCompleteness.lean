module

public import PolishSpaceBook.ForcingInternalRegularAlgebra

@[expose] public section

/-! # Internal completeness of the regular-set algebra -/

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

lemma internalRegular_le_iff (U V : BooleanElement (internalRegularCarrier M P.val R.val)) :
    letI := Alg
    U ≤ V ↔ U.val ⊆ V.val := by
  let _ := Alg
  change (conditionsOfCode P.val U.val ⊆ conditionsOfCode P.val V.val) ↔ _
  constructor
  · intro h x hx
    exact h (a := ⟨x, ((mem_internalRegularCarrier hR M U.val).mp U.property).2.1 hx⟩) hx
  · intro h p hp
    exact h hp

lemma internalRegular_inf_val (U V : BooleanElement (internalRegularCarrier M P.val R.val)) :
    letI := Alg
    (U ⊓ V).val = U.val ∩ V.val := by
  let _ := Alg
  change conditionSet P.val ((conditionsOfCode P.val U.val) ∩ (conditionsOfCode P.val V.val)) = _
  rw [conditionSet_inter, conditionSet_conditionsOfCode P.val U.val
    ((mem_internalRegularCarrier hR M U.val).mp U.property).2.1,
    conditionSet_conditionsOfCode P.val V.val ((mem_internalRegularCarrier hR M V.val).mp V.property).2.1]

lemma internalRegular_compl_val (U : BooleanElement (internalRegularCarrier M P.val R.val)) :
    letI := Alg
    Uᶜ.val = regularNegCode P.val R.val U.val := by
  let _ := Alg
  change conditionSet P.val (((decodeInternalRegular hR M U)ᶜ).val : Set (Condition P.val)) = _
  rw [regularForcingSet_compl_carrier, conditionSet_forcingNeg hR]
  change regularNegCode P.val R.val (conditionSet P.val (conditionsOfCode P.val U.val)) = _
  rw [conditionSet_conditionsOfCode P.val U.val ((mem_internalRegularCarrier hR M U.val).mp U.property).2.1]

lemma internalRegular_bot_val :
    letI := Alg
    (⊥ : BooleanElement (internalRegularCarrier M P.val R.val)).val = ∅ := by
  let _ := Alg
  change conditionSet P.val ∅ = ∅
  ext x
  simp [conditionSet]

/-- The union of an internal family is internal; regularizing that union gives
its supremum. This theorem does not quantify over arbitrary external families. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{proof}[Internal construction of the completion]
    Let $P\in M$ be a forcing order whose order relation belongs to $M$ as well. Use the negative operation
    from §{sec:random-forcing-detail} with conditions in $P$:
    $$\ForcingNeg{U}=\{p\in P:\forall q\le p\ (q\notin U)\}.$$
    The regular lower sets are the downward-closed subsets $U$ of $P$ satisfying
    $U=\ForcingNeg{\ForcingNeg{U}}$. Take only those subsets that belong to $M$.
    Their carrier is a set in $M$: apply Separation to the power set of $P$ computed inside $M$.
    All quantifiers in the defining conditions are bounded by $P$, so transitivity makes these conditions
    agree with their external meanings.

    Order this carrier by inclusion. Intersection is meet, $\ForcingNeg{U}$ is complement, and the bottom
    and top are $\varnothing$ and $P$. The double negative is precisely the set of conditions below which
    $U$ is dense. It is an idempotent closure operation on lower sets, and its fixed points form a Boolean
    algebra with these operations. Separation also puts the order, complement, and meet graphs in $M$.

    For a family $\mathcal A\in M$ of regular lower sets, Union and Separation give
    $$\bigvee\mathcal A=\ForcingNeg{\ForcingNeg{\bigcup\mathcal A}}\in M.$$
    Each member of the family is contained in this regularization. Every regular upper bound contains
    the union and therefore also its regularization. This proves the supremum property and hence
    completeness for all families in $M$.
    \end{proof}
-/
theorem internalRegular_complete (S : M) (hS : S.val ⊆ internalRegularCarrier M P.val R.val) :
    letI := Alg
    ∃ b : BooleanElement (internalRegularCarrier M P.val R.val),
      IsLUB {a : BooleanElement (internalRegularCarrier M P.val R.val) | a.val ∈ S.val} b := by
  let _ := Alg
  have hUP : ZFSet.sUnion S.val ⊆ P.val := by
    intro x hx
    obtain ⟨U, hUS, hxU⟩ := mem_sUnion.mp hx
    exact ((mem_internalRegularCarrier hR M U).mp (hS hUS)).2.1 hxU
  let U : M := ⟨ZFSet.sUnion S.val, union_mem hM hunion S.property⟩
  let bCode := regularDenseCode P.val R.val U.val
  have hbM : bCode ∈ M := regularDenseCode_mem hM hsep P R U
  have hbP : bCode ⊆ P.val := fun _ h => (mem_sep.mp h).1
  have hbc : conditionsOfCode P.val bCode = forcingDense (conditionsOfCode P.val U.val) :=
    regularDenseCode_correct hR U.val hUP
  have hbreg : bCode ∈ internalRegularCarrier M P.val R.val := by
    apply (mem_internalRegularCarrier hR M bCode).mpr
    refine ⟨hbM, hbP, ?_, ?_⟩ <;> rw [hbc]
    · exact forcingDense_lower _
    · exact fun _ h => ForcingAtomic.dense_dense _ h
  let b : BooleanElement (internalRegularCarrier M P.val R.val) := ⟨bCode, hbreg⟩
  refine ⟨b, ?_, ?_⟩
  · intro a ha
    apply (internalRegular_le_iff hM hinf hpair hunion hsep P R hR a b).mpr
    intro x hx
    have hxP := ((mem_internalRegularCarrier hR M a.val).mp a.property).2.1 hx
    change x ∈ bCode
    have hh : (⟨x, hxP⟩ : Condition P.val) ∈ conditionsOfCode P.val bCode := by
      rw [hbc]
      intro q hqx
      refine ⟨q, le_rfl, mem_sUnion.mpr ⟨a.val, ha, ?_⟩⟩
      exact ((mem_internalRegularCarrier hR M a.val).mp a.property).2.2.1 hqx hx
    exact hh
  · intro a ha
    apply (internalRegular_le_iff hM hinf hpair hunion hsep P R hR b a).mpr
    intro x hx
    have hxP := hbP hx
    have hd : (⟨x, hxP⟩ : Condition P.val) ∈ forcingDense (conditionsOfCode P.val U.val) := by
      rw [← hbc]; exact hx
    have hsat : forcingDense (conditionsOfCode P.val a.val) ⊆ conditionsOfCode P.val a.val :=
      ((mem_internalRegularCarrier hR M a.val).mp a.property).2.2.2
    apply hsat (a := (⟨x, hxP⟩ : Condition P.val))
    intro q hqx
    obtain ⟨r, hrq, hrU⟩ := hd q hqx
    obtain ⟨V, hVS, hrV⟩ := mem_sUnion.mp hrU
    have hVa := (internalRegular_le_iff hM hinf hpair hunion hsep P R hR ⟨V, hS hVS⟩ a).mp (ha hVS)
    exact ⟨r, hrq, hVa hrV⟩

end PolishSpaceBook.SetTheoryModels
