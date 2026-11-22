module

public import PolishSpaceBook.DomainTheoryQuasiPolishSpaces
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # A Smyth complete quasi-metric for the Scott powerset

A lost positive digit i costs 2⁻ⁱ. Forward Cauchy sequences eventually preserve
each digit, so every digit eventually stabilizes. The limit retains precisely
the eventually persistent digits. No effective choice of the stabilization
stages is asserted.
-/
noncomputable section
namespace PolishSpaceBook
open Set Topology TopologicalSpace

def lossValues (A B : Set ℕ) : Set ℝ :=
  {0} ∪ {r | ∃ i, i ∈ A ∧ i ∉ B ∧ r = (1/2 : ℝ)^i}

private theorem lossValues_bounded (A B : Set ℕ) : BddAbove (lossValues A B) := by
  refine ⟨1, ?_⟩
  rintro r (h | ⟨i,hi,hni,rfl⟩)
  · rcases h with rfl
    norm_num
  · exact pow_le_one₀ (by norm_num) (by norm_num)

/-- Supremum of the costs of positive digits lost on passing from A to B. -/
def powersetLoss (A B : Set ℕ) : ℝ := sSup (lossValues A B)

theorem powersetLoss_nonneg (A B : Set ℕ) : 0 ≤ powersetLoss A B :=
  le_csSup (lossValues_bounded A B) (Or.inl rfl)

private theorem weight_le_powersetLoss {A B : Set ℕ} {i : ℕ}
    (hi : i ∈ A) (hni : i ∉ B) : (1/2 : ℝ)^i ≤ powersetLoss A B :=
  le_csSup (lossValues_bounded A B) (Or.inr ⟨i,hi,hni,rfl⟩)

theorem powersetLoss_eq_zero_iff (A B : Set ℕ) : powersetLoss A B = 0 ↔ A ⊆ B := by
  constructor
  · intro h i hi
    by_contra hni
    have hw := weight_le_powersetLoss hi hni
    rw [h] at hw
    exact (not_le_of_gt (pow_pos (by norm_num : (0:ℝ)<1/2) i)) hw
  · intro h
    apply le_antisymm ?_ (powersetLoss_nonneg A B)
    apply csSup_le (s := lossValues A B) ⟨0,Or.inl rfl⟩
    rintro r (hr | ⟨i,hi,hni,rfl⟩)
    · rcases hr with rfl
      exact le_rfl
    · exact False.elim (hni (h hi))

/-- The one-sided finite-information distance. -/
def powersetQuasiMetric : QuasiMetricData (Set ℕ) where
  dist := powersetLoss
  nonneg := powersetLoss_nonneg
  refl A := (powersetLoss_eq_zero_iff A A).mpr subset_rfl
  triangle A B C := by
    apply csSup_le (s := lossValues A C) ⟨0,Or.inl rfl⟩
    rintro r (hr | ⟨i,hi,hni,rfl⟩)
    · rcases hr with rfl
      exact add_nonneg (powersetLoss_nonneg A B) (powersetLoss_nonneg B C)
    · by_cases hib : i ∈ B
      · exact (weight_le_powersetLoss hib hni).trans (le_add_of_nonneg_left (powersetLoss_nonneg A B))
      · exact (weight_le_powersetLoss hi hib).trans (le_add_of_nonneg_right (powersetLoss_nonneg B C))
  eq_of_both_zero hAB hBA :=
    Set.Subset.antisymm ((powersetLoss_eq_zero_iff _ _).mp hAB)
      ((powersetLoss_eq_zero_iff _ _).mp hBA)

/-- Agreeing on positive information below N bounds the forward distance. -/
theorem powersetLoss_le_of_prefix {A B : Set ℕ} {N : ℕ}
    (h : ∀ i < N, i ∈ A → i ∈ B) : powersetLoss A B ≤ (1/2 : ℝ)^N := by
  apply csSup_le (s := lossValues A B) ⟨0,Or.inl rfl⟩
  rintro r (hr | ⟨i,hi,hni,rfl⟩)
  · rcases hr with rfl
    exact pow_nonneg (by norm_num : (0:ℝ)≤1/2) N
  · have hNi : N ≤ i := by
      by_contra hn
      exact hni (h i (by omega) hi)
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hNi

/-- A distance smaller than the cost of digit i prevents that digit from being lost. -/
theorem powersetLoss_preserves {A B : Set ℕ} {i : ℕ}
    (h : powersetLoss A B < (1/2 : ℝ)^i) (hi : i ∈ A) : i ∈ B := by
  by_contra hni
  exact (not_le_of_gt h) (weight_le_powersetLoss hi hni)

/-- Membership in the limit means eventual persistence, not membership at an arbitrary stage. -/
def powersetLimit (x : ℕ → Set ℕ) : Set ℕ := {i | ∃ N, ∀ n ≥ N, i ∈ x n}

/-- The oriented Cauchy condition implies eventual stability of each individual digit. -/
theorem powerset_eventually_stable {x : ℕ → Set ℕ}
    (hx : LeftKCauchy powersetQuasiMetric x) (i : ℕ) :
    ∃ N, ∀ n ≥ N, (i ∈ x n ↔ i ∈ powersetLimit x) := by
  obtain ⟨N,hN⟩ := hx ((1/2 : ℝ)^i) (pow_pos (by norm_num) _)
  by_cases hhit : ∃ n ≥ N, i ∈ x n
  · obtain ⟨n,hn,hi⟩ := hhit
    have hp : ∀ m ≥ n, i ∈ x m := fun m hm => powersetLoss_preserves (hN n m hn hm) hi
    exact ⟨n,fun m hm => iff_of_true (hp m hm) ⟨n,hp⟩⟩
  · refine ⟨N,fun n hn => ?_⟩
    have hnot : i ∉ x n := fun hi => hhit ⟨n,hn,hi⟩
    have hlimit : i ∉ powersetLimit x := by
      rintro ⟨M,hM⟩
      exact hhit ⟨max N M, le_max_left _ _, hM _ (le_max_right _ _)⟩
    exact iff_of_false hnot hlimit

/-- Finitely many stabilization stages suffice for a prescribed symmetric error. -/
theorem powersetQuasiMetric_smythComplete : SmythComplete powersetQuasiMetric := by
  intro x hx
  refine ⟨powersetLimit x,fun ε hε => ?_⟩
  obtain ⟨K,hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2 : ℝ)<1)
  choose N hN using powerset_eventually_stable hx
  refine ⟨(Finset.range K).sup N,fun n hn => ?_⟩
  have hbits (i : ℕ) (hi : i < K) : i ∈ x n ↔ i ∈ powersetLimit x :=
    hN i n ((Finset.le_sup (f := N) (Finset.mem_range.mpr hi)).trans hn)
  exact (max_le (powersetLoss_le_of_prefix (fun i hi => (hbits i hi).mp))
    (powersetLoss_le_of_prefix (fun i hi => (hbits i hi).mpr))).trans_lt hK

section ScottTopology
local instance powersetMetricScottTopology : TopologicalSpace (Set ℕ) := Topology.scott (Set ℕ) univ
local instance powersetMetricIsScott : Topology.IsScott (Set ℕ) univ := ⟨rfl⟩

/-- A forward ball specifies finitely many positive digits, and every finite
positive requirement contains a sufficiently small forward ball. -/
theorem powersetQuasiMetric_topology : powersetQuasiMetric.topology = Topology.scott (Set ℕ) univ := by
  apply TopologicalSpace.ext
  funext U
  apply propext
  rw [powersetQuasiMetric.isOpen_iff, powerset_scott_open_iff]
  constructor
  · intro h A hA
    obtain ⟨r,hr,hsub⟩ := h A hA
    obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1/2 : ℝ)<1)
    let F : Set ℕ := {i | i ∈ A ∧ i < N}
    have hF : F.Finite := (Finset.range N).finite_toSet.subset (by
      intro i hi
      exact Finset.mem_range.mpr hi.2)
    refine ⟨F,hF,fun i hi => hi.1,fun B hFB => hsub ?_⟩
    exact (powersetLoss_le_of_prefix (fun i hi hia => hFB ⟨hia,hi⟩)).trans_lt hN
  · intro h A hA
    obtain ⟨F,hF,hFA,hFU⟩ := h A hA
    obtain ⟨N,hN⟩ := hF.bddAbove
    refine ⟨(1/2 : ℝ)^N, pow_pos (by norm_num) _, fun B hB => hFU ?_⟩
    intro i hi
    have hweight : (1/2 : ℝ)^N ≤ (1/2 : ℝ)^i :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hN hi)
    exact powersetLoss_preserves (hB.trans_le hweight) (hFA hi)

/-- The finite principal upper sets give a countable Scott basis. -/
theorem powerset_scott_secondCountable : SecondCountableTopology (Set ℕ) := by
  have hb : IsTopologicalBasis (range (fun F : Finset ℕ => Ici (F : Set ℕ))) := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro U ⟨F,rfl⟩
      exact powerset_principal_finite_isOpen F.finite_toSet
    · intro A U hA hU
      obtain ⟨F,hF,hFA,hFU⟩ := (powerset_scott_open_iff U).mp hU A hA
      refine ⟨Ici F, ⟨hF.toFinset, by simp⟩, hFA, hFU⟩
  exact hb.secondCountableTopology (Set.countable_range _)

/-- Scott powerset space is quasi-Polish by its explicit compatible complete
quasi-metric, without assuming the external domain characterization. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: example
  title: Scott topology on Pomega{Scott topology on $omega$}
-/
theorem powerset_scott_quasiPolish : IsQuasiPolish (Set ℕ) := by
  refine ⟨powerset_scott_secondCountable, ?_, powersetQuasiMetric,
    powersetQuasiMetric_smythComplete, powersetQuasiMetric_topology⟩
  change @T0Space (Set ℕ) (Topology.scott (Set ℕ) univ)
  rw [← powersetQuasiMetric_topology]
  exact powersetQuasiMetric.t0Space

/-- Strict inclusion prevents T₁ separation and hence prevents Polishness. -/
/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: statement
  kind: example
  title: Scott topology on Pomega{Scott topology on $omega$}
-/
theorem powerset_scott_not_polish : ¬ PolishSpace (Set ℕ) := by
  intro h
  let := h
  exact powerset_scott_not_t1 (α := ℕ) inferInstance

end ScottTopology
end PolishSpaceBook
