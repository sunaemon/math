module

public import PolishSpaceBook.SetTheoryGrothendieckUniverse
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.FundamentalSequence

@[expose] public section

/-! # The height of a Grothendieck universe is inaccessible

Power-set closure gives the strong-limit property. An allegedly shorter
cofinal sequence would have its supremum in the universe, which is impossible.
-/
noncomputable section
namespace PolishSpaceBook.SetTheoryModels.IsGrothendieckUniverse
open Order
universe u
variable {U : ZFSet.{u}} (hU : IsGrothendieckUniverse U)
include hU

lemma iSup_lt_height {I : ZFSet.{u}} (hI : I ∈ U) (f : I → Ordinal.{u})
    (hf : ∀ i, f i < height U) : (⨆ i, f i) < height U := by
  have hm := hU.indexedUnion_mem hI (fun i => (f i).toZFSet)
    (fun i => hU.ordinal_mem_iff.mpr (hf i))
  rw [hU.eq_vonNeumann_height] at hm
  simpa only [ZFSet.mem_vonNeumann, ZFSet.rank_iUnion, Ordinal.rank_toZFSet] using hm

lemma cof_height_ord : (height U).cof.ord = height U := by
  apply le_antisymm (Ordinal.ord_cof_le _)
  by_contra! hlt
  let μ := (height U).cof.ord
  have hμ : μ.toZFSet ∈ U := hU.ordinal_mem_iff.mpr hlt
  obtain ⟨f, hf⟩ := Ordinal.exists_isFundamentalSeq (o := height U) rfl
  let g : μ.toZFSet → Ordinal.{u} := fun i =>
    (f ⟨i.val.rank, by
      change i.val.rank < μ
      simpa only [Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem i.property⟩).val + 1
  have hg : ∀ i, g i < height U := fun i => hU.height_isSuccLimit.succ_lt (f _).property
  have hsup := hU.iSup_lt_height hμ g hg
  have hle : height U ≤ ⨆ i, g i := by
    rw [← hf.iSup_add_one_eq]
    apply Ordinal.iSup_le
    intro i
    have hi := Ordinal.le_iSup g ⟨i.val.toZFSet, Ordinal.toZFSet_mem_toZFSet_iff.mpr i.property⟩
    simpa only [g, Ordinal.rank_toZFSet] using hi
  exact (hle.trans_lt hsup).false

/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: proof
  excerpt: |
    If $\lambda<\kappa$ is a cardinal, then $\lambda\in U$ and $\PowerSet{\lambda}\in U$, so the size bound gives
    $2^\lambda=|\PowerSet{\lambda}|<\kappa$. Thus $\kappa$ is a strong limit.
    It is also regular. A cofinal sequence $\langle\alpha_i:i<\mu\rangle$ of length $\mu<\kappa$ would have
    $\mu\in U$, so indexed-union closure would put its supremum $\kappa$ in $U$, again a contradiction.
    Together with $\omega<\kappa$, this proves that $\kappa$ is inaccessible.
    \end{proof}
-/
lemma height_isInaccessible : Cardinal.IsInaccessible (height U).card := by
  have hω : Cardinal.aleph0 < (height U).card := by
    apply Cardinal.ord_lt_ord.mp
    simpa only [Cardinal.ord_aleph0, hU.height_card_ord] using hU.omega_lt_height
  refine ⟨hω, ?_, ?_⟩
  · rw [hU.height_card_ord]
    have hc := congrArg Ordinal.card hU.cof_height_ord
    simpa only [Cardinal.card_ord] using hc.ge
  · intro c hc
    have ho : c.ord < height U := by
      rw [← hU.height_card_ord]
      exact Cardinal.ord_lt_ord.mpr hc
    have hp := hU.card_lt_height_card (hU.powerset_mem (hU.ordinal_mem_iff.mpr ho))
    simpa only [ZFSet.card_powerset, Ordinal.card_toZFSet, Cardinal.card_ord] using hp

theorem exists_inaccessible_stage :
    ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ U = ZFSet.vonNeumann κ.ord := by
  refine ⟨(height U).card, hU.height_isInaccessible, ?_⟩
  rw [hU.height_card_ord]
  exact hU.eq_vonNeumann_height

end PolishSpaceBook.SetTheoryModels.IsGrothendieckUniverse
