module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Recovering spectral multiplicities from positive threshold counts -/

noncomputable section

open Set

namespace PolishSpaceBook.SpectralCountRecovery

variable {ι κ : Type*}

/-- Local finiteness away from zero gives a gap immediately below any
positive spectral parameter, whether or not that parameter occurs. -/
theorem exists_positive_gap (f : ι → ℝ)
    (hf : ∀ r > 0, {i | r ≤ f i}.Finite) {μ : ℝ} (hμ : 0 < μ) :
    ∃ r : ℝ, 0 < r ∧ r < μ ∧ {i | r < f i} = {i | μ ≤ f i} := by
  classical
  let s := {i | μ / 2 ≤ f i ∧ f i < μ}
  have hs : s.Finite := (hf (μ / 2) (half_pos hμ)).subset (fun _ h => h.1)
  let t := insert (μ / 2) (f '' s)
  have ht : t.Finite := (hs.image f).insert _
  have htn : t.Nonempty := ⟨μ / 2, mem_insert _ _⟩
  let r := sSup t
  have hhalf : μ / 2 ≤ r := le_csSup ht.bddAbove (mem_insert _ _)
  have hrμ : r < μ := by
    change sSup t < μ
    have hm := htn.csSup_mem ht
    rcases hm with hm | ⟨i, hi, heq⟩
    · rw [hm]
      exact half_lt_self hμ
    · rw [← heq]
      exact hi.2
  refine ⟨r, (half_pos hμ).trans_le hhalf, hrμ, ?_⟩
  ext i
  constructor
  · intro hi
    by_contra h
    have his : i ∈ s := ⟨hhalf.trans hi.le, lt_of_not_ge h⟩
    have hir : f i ≤ r := le_csSup ht.bddAbove (mem_insert_of_mem _ ⟨i, his, rfl⟩)
    exact (not_le_of_gt hi) hir
  · intro hi
    exact hrμ.trans_le hi

/-- Counts above every positive threshold recover each positive fiber's
multiplicity. Both sides may have infinitely many entries accumulating at zero. -/
theorem positive_fiber_ncard_eq (f : ι → ℝ) (g : κ → ℝ)
    (hf : ∀ r > 0, {i | r ≤ f i}.Finite)
    (hg : ∀ r > 0, {j | r ≤ g j}.Finite)
    (hc : ∀ r > 0, {i | r < f i}.ncard = {j | r < g j}.ncard)
    {μ : ℝ} (hμ : 0 < μ) : {i | f i = μ}.ncard = {j | g j = μ}.ncard := by
  obtain ⟨rf, hrf0, hrfμ, hrf⟩ := exists_positive_gap f hf hμ
  obtain ⟨rg, hrg0, hrgμ, hrg⟩ := exists_positive_gap g hg hμ
  let r := max rf rg
  have hr0 : 0 < r := hrf0.trans_le (le_max_left _ _)
  have hrμ : r < μ := max_lt hrfμ hrgμ
  have hfr : {i | r < f i} = {i | μ ≤ f i} := by
    ext i
    constructor
    · intro hi
      have h : i ∈ {i | rf < f i} := (le_max_left rf rg).trans_lt hi
      rwa [hrf] at h
    · intro hi
      exact hrμ.trans_le hi
  have hgr : {j | r < g j} = {j | μ ≤ g j} := by
    ext j
    constructor
    · intro hj
      have h : j ∈ {j | rg < g j} := (le_max_right rf rg).trans_lt hj
      rwa [hrg] at h
    · intro hj
      exact hrμ.trans_le hj
  have hge : {i | μ ≤ f i}.ncard = {j | μ ≤ g j}.ncard := by
    simpa only [hfr, hgr] using hc r hr0
  have hfe : {i | f i = μ} = {i | μ ≤ f i} \ {i | μ < f i} := by
    ext i
    simp only [mem_ofPred_eq, mem_sdiff]
    constructor <;> intro h
    · simp [h]
    · exact le_antisymm (le_of_not_gt h.2) h.1
  have hge' : {j | g j = μ} = {j | μ ≤ g j} \ {j | μ < g j} := by
    ext j
    simp only [mem_ofPred_eq, mem_sdiff]
    constructor <;> intro h
    · simp [h]
    · exact le_antisymm (le_of_not_gt h.2) h.1
  rw [hfe, hge', ncard_sdiff' (s := {i | μ < f i}) (t := {i | μ ≤ f i})
      (fun i h => show μ ≤ f i from le_of_lt h) (hf μ hμ),
    ncard_sdiff' (s := {j | μ < g j}) (t := {j | μ ≤ g j})
      (fun j h => show μ ≤ g j from le_of_lt h) (hg μ hμ), hge, hc μ hμ]

end PolishSpaceBook.SpectralCountRecovery
