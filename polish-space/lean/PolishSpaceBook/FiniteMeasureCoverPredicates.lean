module

public import PolishSpaceBook.FiniteMeasureApproximation
public import PolishSpaceBook.SetTheorySequenceOperations

@[expose] public section

/-! # Bounded descriptions of finite approximate measure covers -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open ZFSet SetTheoryModels SetTheoryModels.BoundedSetPredicate
universe u

namespace FiniteMeasureCover

/-- A finite list of arbitrary sets, represented by its function graph. -/
def listGraph (l : List ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun i : Fin l.length => pair (natOrdinal i.val) (l.get i))

lemma listGraph_isFunc {E : ZFSet.{u}} (l : List ZFSet.{u}) (hl : ∀ B ∈ l, B ∈ E) :
    IsFunc (natOrdinal l.length) E (listGraph l) := by
  constructor
  · intro p hp
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hp
    exact ZFSet.pair_mem_prod.mpr
      ⟨mem_natOrdinal.mpr ⟨i.val, i.isLt, rfl⟩, hl _ (List.get_mem ..)⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_natOrdinal.mp ha
    refine ⟨l.get ⟨i, hi⟩, ZFSet.mem_range.mpr ⟨⟨i, hi⟩, rfl⟩, ?_⟩
    intro b hb
    obtain ⟨j, hj⟩ := ZFSet.mem_range.mp hb
    obtain ⟨he, hv⟩ := ZFSet.pair_inj.mp hj
    have he' := natOrdinal_injective he
    simpa only [List.get_eq_getElem, he'] using hv.symm

lemma listGraph_union (l : List ZFSet.{u}) :
    sUnion (graphRange (listGraph l)) = FiniteAdditiveCutGraph.listUnion l := by
  ext x
  rw [ZFSet.mem_sUnion, FiniteAdditiveCutGraph.mem_listUnion]
  constructor
  · rintro ⟨B, hB, hx⟩
    obtain ⟨a, ha⟩ := mem_graphRange.mp hB
    obtain ⟨i, hi⟩ := ZFSet.mem_range.mp ha
    have he := (ZFSet.pair_inj.mp hi).2
    exact ⟨B, he ▸ List.get_mem l i, hx⟩
  · rintro ⟨B, hB, hx⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hB
    exact ⟨l.get i, mem_graphRange.mpr ⟨natOrdinal i.val, ZFSet.mem_range.mpr ⟨i, rfl⟩⟩, hx⟩

/-- Parameters omega, family, ambient set, function graph, union. -/
def unionPredicate : BoundedSetPredicate 5 :=
  .conj (.subset 4 2) (.all 2 (.iff (.member 5 4)
    (.ex 1 (.ex 0 (.conj (.pairMember 3 7 6) (.member 5 6))))))

lemma eval_unionPredicate {E Y f : ZFSet.{u}} {k : ℕ}
    (hf : IsFunc (natOrdinal k) E f) (hEY : ∀ B ∈ E, B ⊆ Y) (U : ZFSet.{u}) :
    unionPredicate.eval ![Ordinal.omega0.toZFSet, E, Y, f, U] ↔ U = sUnion (graphRange f) := by
  change (U ⊆ Y ∧ ∀ x ∈ Y, x ∈ U ↔ ∃ B ∈ E, ∃ i ∈ Ordinal.omega0.toZFSet,
    pair i B ∈ f ∧ x ∈ B) ↔ _
  have hm (x : ZFSet.{u}) : x ∈ sUnion (graphRange f) ↔
      ∃ B ∈ E, ∃ i ∈ Ordinal.omega0.toZFSet, pair i B ∈ f ∧ x ∈ B := by
    constructor
    · rintro hx
      obtain ⟨B, hB, hxB⟩ := ZFSet.mem_sUnion.mp hx
      obtain ⟨i, hi⟩ := mem_graphRange.mp hB
      obtain ⟨hiK, hBE⟩ := ZFSet.pair_mem_prod.mp (hf.1 hi)
      obtain ⟨j, _, rfl⟩ := mem_natOrdinal.mp hiK
      exact ⟨B, hBE, natOrdinal j, mem_omegaOrdinal.mpr ⟨j, rfl⟩, hi, hxB⟩
    · rintro ⟨B, _, i, _, hi, hx⟩
      exact ZFSet.mem_sUnion.mpr ⟨B, mem_graphRange.mpr ⟨i, hi⟩, hx⟩
  have hsub : sUnion (graphRange f) ⊆ Y := by
    intro x hx
    obtain ⟨B, hB, _, _, _, hxB⟩ := (hm x).mp hx
    exact hEY B hB hxB
  constructor
  · rintro ⟨hu, ht⟩
    ext x
    exact ⟨fun hx => (hm x).mpr ((ht x (hu hx)).mp hx),
      fun hx => (ht x (hsub hx)).mpr ((hm x).mp hx)⟩
  · rintro rfl
    exact ⟨hsub, fun x _ => hm x⟩

/-- Parameters domain, cut range, measure graph, family, numerator one, denominator, union. -/
def residualPredicate : BoundedSetPredicate 7 :=
  .all 3 (.ex 0 (.ex 1 (.conj (relativeComplementPredicate.rename ![7, 6, 8])
    (.conj (.pairMember 2 8 9) (.neg (.pairMember 9 4 5))))))

lemma eval_residualPredicate {D R F E U : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
    (hED : ∀ B ∈ E, B ∈ D) (hU : U ∈ D) (n : ℕ) :
    residualPredicate.eval ![D, R, F, E, natOrdinal 1, natOrdinal (n + 1), U] ↔
      ∀ B ∈ E, h.value (B \ U) ≤ 1 / (n + 1 : ℝ) := by
  simp only [residualPredicate, eval, eval_rename, Fin.snoc]
  change (∀ B ∈ E, ∃ W ∈ D, ∃ C ∈ R,
    relativeComplementPredicate.eval ![B, U, W] ∧ pair W C ∈ F ∧
      ¬pair (natOrdinal 1) (natOrdinal (n + 1)) ∈ C) ↔ _
  simp only [eval_relativeComplementPredicate]
  have hdiff (B : ZFSet.{u}) : B.sep (fun x => x ∉ U) = B \ U := by
    ext x
    simp
  simp only [hdiff]
  have hcut (B : ZFSet.{u}) (hB : B ∈ E) :
      (¬pair (natOrdinal 1) (natOrdinal (n + 1)) ∈ h.code (B \ U)) ↔
        h.value (B \ U) ≤ 1 / (n + 1 : ℝ) := by
    have he := (h.code_valid (h.diff_mem B (hED B hB) U hU)).encode_decode
    rw [he, pair_mem_nonnegativeRealCutCode]
    simp [FiniteAdditiveCutGraph.value]
  constructor
  · intro ht B hB
    obtain ⟨W, _, C, _, rfl, hp, hc⟩ := ht B hB
    rw [← h.code_eq (h.diff_mem B (hED B hB) U hU) hp] at hc
    exact (hcut B hB).mp hc
  · intro ht B hB
    have hd := h.diff_mem B (hED B hB) U hU
    exact ⟨B \ U, hd, h.code (B \ U), h.code_mem hd, rfl, h.pair_code hd,
      (hcut B hB).mpr (ht B hB)⟩

/-- Output is a pair of a finite graph and its approximate union; all quantifiers are bounded. -/
def coverPredicate : BoundedSetPredicate 10 :=
  .ex 6 (.ex 3 (.conj (.orderedPair 9 10 11)
    (.conj (.ex 0 (.function 12 1 10))
      (.conj (unionPredicate.rename ![0, 1, 2, 10, 11])
        (.ex 0 (.conj (.successor 12 8) (residualPredicate.rename ![3, 4, 5, 1, 7, 12, 11])))))))

set_option maxHeartbeats 800000 in
lemma eval_coverPredicate {D R F E Y K : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
    (hED : ∀ B ∈ E, B ∈ D) (hEY : ∀ B ∈ E, B ⊆ Y) (n : ℕ) (y : ZFSet.{u}) :
    coverPredicate.eval ![Ordinal.omega0.toZFSet, E, Y, D, R, F, K, natOrdinal 1, natOrdinal n, y] ↔
      ∃ f ∈ K, ∃ U ∈ D, y = pair f U ∧ (∃ k : ℕ, IsFunc (natOrdinal k) E f) ∧
        U = sUnion (graphRange f) ∧ ∀ B ∈ E, h.value (B \ U) ≤ 1 / (n + 1 : ℝ) := by
  simp only [coverPredicate, eval, eval_rename, Fin.snoc]
  change (∃ f ∈ K, ∃ U ∈ D, y = pair f U ∧
    (∃ k ∈ Ordinal.omega0.toZFSet, IsFunc k E f) ∧
    unionPredicate.eval ![Ordinal.omega0.toZFSet, E, Y, f, U] ∧
    ∃ m ∈ Ordinal.omega0.toZFSet, m = insert (natOrdinal n) (natOrdinal n) ∧
      residualPredicate.eval ![D, R, F, E, natOrdinal 1, m, U]) ↔ _
  simp only [exists_mem_omegaOrdinal, ← natOrdinal_succ, natOrdinal_injective.eq_iff]
  constructor
  · rintro ⟨f, hf, U, hU, hy, ⟨k, hk⟩, hu, m, rfl, hr⟩
    exact ⟨f, hf, U, hU, hy, ⟨k, hk⟩, (eval_unionPredicate hk hEY U).mp hu,
      (eval_residualPredicate h hED hU n).mp hr⟩
  · rintro ⟨f, hf, U, hU, hy, ⟨k, hk⟩, hu, hr⟩
    exact ⟨f, hf, U, hU, hy, ⟨k, hk⟩, (eval_unionPredicate hk hEY U).mpr hu,
      n + 1, rfl, (eval_residualPredicate h hED hU n).mpr hr⟩

end FiniteMeasureCover
end PolishSpaceBook.CantorTreeMeasure
