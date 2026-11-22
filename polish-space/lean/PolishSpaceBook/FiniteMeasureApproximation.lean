module

public import PolishSpaceBook.FiniteAdditiveCutGraphs

@[expose] public section

/-! # Finite approximate covers in a finite measure ring -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure.FiniteAdditiveCutGraph
open ZFSet SetTheoryModels
universe u

variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)

lemma value_union_gain {A B : ZFSet.{u}} (hA : A ∈ D) (hB : B ∈ D) :
    h.value (A ∪ B) = h.value A + h.value (B \ A) := by
  have he : (A ∪ B) \ A = B \ A := by
    ext x
    simp only [ZFSet.mem_sdiff, ZFSet.mem_union]
    tauto
  have hadd := h.value_sdiff_add hA (h.union_mem A hA B hB)
    (fun _ hx => ZFSet.mem_union.mpr (Or.inl hx))
  rw [he] at hadd
  exact hadd.symm

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Finite approximate covers
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    If no such list exists, every finite union $U$ of members of $E$ admits a further $B\in E$ with
    $\nu(\SetDifference{B}{U})>\varepsilon$. Finite additivity gives
    $$\nu(U\cup B)=\nu(U)+\nu(\SetDifference{B}{U}).$$
    Starting with $U_0=\emptyset$, finite induction therefore gives a union $U_n$ of $n$ members of $E$ with
    $\nu(U_n)\ge n\varepsilon$. But $U_n\IncludedIn Y$, so monotonicity gives $\nu(U_n)\le\nu(Y)$.
    Choose $n>\nu(Y)/\varepsilon$ to obtain a contradiction.
-/
theorem exists_finite_approximate_cover {Y E : ZFSet.{u}} (hY : Y ∈ D)
    (hED : ∀ B ∈ E, B ∈ D) (hEY : ∀ B ∈ E, B ⊆ Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List ZFSet.{u}, (∀ B ∈ l, B ∈ E) ∧
      ∀ B ∈ E, h.value (B \ listUnion l) ≤ ε := by
  classical
  by_contra hn
  have hstep (l : List ZFSet.{u}) (hl : ∀ B ∈ l, B ∈ E) :
      ∃ B ∈ E, ε < h.value (B \ listUnion l) := by
    by_contra hb
    apply hn
    refine ⟨l, hl, ?_⟩
    intro B hB
    exact le_of_not_gt (fun hx => hb ⟨B, hB, hx⟩)
  have hgrow (n : ℕ) : ∃ l : List ZFSet.{u}, (∀ B ∈ l, B ∈ E) ∧
      (n : ℝ) * ε ≤ h.value (listUnion l) := by
    induction n with
    | zero => exact ⟨[], by simp, by simp [listUnion, h.value_zero]⟩
    | succ n ih =>
      obtain ⟨l, hl, hv⟩ := ih
      obtain ⟨B, hB, hgain⟩ := hstep l hl
      refine ⟨B :: l, by simpa using And.intro hB hl, ?_⟩
      have hadd := h.value_union_gain (h.listUnion_mem l (fun C hC => hED C (hl C hC))) (hED B hB)
      have hcomm : listUnion (B :: l) = listUnion l ∪ B := by
        ext x
        simp only [listUnion, ZFSet.mem_union, or_comm]
      rw [hcomm, hadd, Nat.cast_add, Nat.cast_one]
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (h.value Y / ε)
  obtain ⟨l, hl, hv⟩ := hgrow n
  have hsub : listUnion l ⊆ Y := by
    intro x hx
    obtain ⟨B, hB, hxB⟩ := (mem_listUnion l x).mp hx
    exact hEY B (hl B hB) hxB
  have hbound := h.value_mono (h.listUnion_mem l (fun B hB => hED B (hl B hB))) hY hsub
  have hn' := (div_lt_iff₀ hε).mp hn
  linarith

end PolishSpaceBook.CantorTreeMeasure.FiniteAdditiveCutGraph
