module

public import PolishSpaceBook.AnalyticConditionCatalog
public import Mathlib.Topology.MetricSpace.PiNat

@[expose] public section

/-!
# Numerical diameter bounds for witnessed Baire fusion

Use mathlib's standard Baire ultrametric: the first differing coordinate k
has distance 2^{-k}. Its topology and uniformity are the product ones.
Prefix smallness therefore gives the book's numerical diameter bounds.
The decreasing dense schedule below imposes the bound 2^{-n} at stage n
inside the restricted catalog, preserving all previously listed tests.
-/

namespace PolishSpaceBook
open Set Function MeasureTheory

attribute [local instance] PiNat.metricSpaceNatNat

/-- Finite-prefix agreement is exactly a pairwise ultrametric bound. -/
theorem smallPrefixRequirement_iff_dist_bound (P : AnalyticCondition FusionReal) (n : ℕ) :
    P ∈ smallPrefixRequirement n ↔ ∀ x ∈ P.val, ∀ y ∈ P.val, dist x y ≤ (1 / 2 : ℝ) ^ n := by
  constructor
  · intro h x hx y hy
    apply PiNat.mem_cylinder_iff_dist_le.mp
    exact h x hx y hy
  · intro h x hx y hy
    exact PiNat.mem_cylinder_iff_dist_le.mpr (h x hx y hy)

/-- The metric diameter of a prefix-small condition is at most 2^{-n}. -/
theorem smallPrefixRequirement_diameter (P : AnalyticCondition FusionReal) (n : ℕ)
    (hP : P ∈ smallPrefixRequirement n) : Metric.diam P.val ≤ (1 / 2 : ℝ) ^ n :=
  Metric.diam_le_of_forall_dist_le (by positivity) ((smallPrefixRequirement_iff_dist_bound P n).mp hP)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Include also the small-diameter
    requirements, which are dense by intersecting with cylinders.
-/
/-- Every catalog condition has a catalogued refinement with the requested
numerical bound. The metric is never substituted for actual point witnesses. -/
theorem catalog_diameter_refinement (C : AnalyticConditionCatalog) (P : C.Condition) (n : ℕ) :
    ∃ Q ≤ P, Metric.diam Q.val.val ≤ (1 / 2 : ℝ) ^ n := by
  obtain ⟨Q, hQ, hQP⟩ := C.small_coinitial n P
  exact ⟨Q, hQP, smallPrefixRequirement_diameter Q.val n hQ⟩

/-- Finite intersections of dense tests together with the stage's shrinking
diameter test form a decreasing schedule. Every listed test is eventually
included in every stage, and every stage enforces its own numerical bound. -/
theorem catalog_diameter_schedule (C : AnalyticConditionCatalog)
    (F : Set (Set C.Condition)) (hFc : F.Countable)
    (hFd : ∀ D ∈ F, IsCoinitial D) (hFl : ∀ D ∈ F, IsLowerSet D) :
    ∃ D : ℕ → Set C.Condition,
      Antitone D ∧ (∀ n, IsCoinitial (D n)) ∧ (∀ n, IsLowerSet (D n)) ∧
      (∀ n, ∀ P ∈ D n, Metric.diam P.val.val ≤ (1 / 2 : ℝ) ^ n) ∧
      ∀ A ∈ F, ∃ N, ∀ n, N ≤ n → D n ⊆ A := by
  obtain ⟨d, hda, hdd, hdl, hdF⟩ := countable_dense_schedule F hFc hFd hFl
  let D (n : ℕ) := d n ∩ {P : C.Condition | P.val ∈ smallPrefixRequirement n}
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · intro n m hnm P hP
    refine ⟨hda hnm hP.1, ?_⟩
    intro x hx y hy k hk
    exact hP.2 x hx y hy k (hk.trans_le hnm)
  · intro n P
    obtain ⟨Q, hQ, hQP⟩ := hdd n P
    obtain ⟨R, hR, hRQ⟩ := C.small_coinitial n Q
    exact ⟨R, ⟨hdl n hRQ hQ, hR⟩, hRQ.trans hQP⟩
  · intro n P Q hQP hP
    exact ⟨hdl n hQP hP.1, smallPrefixRequirement_lower n hQP hP.2⟩
  · intro n P hP
    exact smallPrefixRequirement_diameter P.val n hP.2
  · intro A hA
    obtain ⟨N, hN⟩ := hdF A hA
    exact ⟨N, fun n hn P hP => hN n hn hP.1⟩

/-- Silver's binary construction with the book's numerical diameter bound
at every node, while meeting the prescribed catalog and product families. -/
theorem catalog_silver_levels_diameter (C : AnalyticConditionCatalog) (B : C.Condition)
    (F : Set (Set C.Condition)) (hFc : F.Countable)
    (hFd : ∀ D ∈ F, IsCoinitial D) (hFl : ∀ D ∈ F, IsLowerSet D)
    (J : Set (Set (C.Condition × C.Condition))) (hJc : J.Countable)
    (hJd : ∀ D ∈ J, IsCoinitial D) (hJl : ∀ D ∈ J, IsLowerSet D) :
    ∃ A : ∀ n, binaryWord n → C.Condition,
      (∀ s, A 0 s ≤ B) ∧
      (∀ n s b, A (n + 1) (Fin.snoc s b) ≤ A n s) ∧
      (∀ n s, Metric.diam (A n s).val.val ≤ (1 / 2 : ℝ) ^ n) ∧
      (∀ D ∈ F, ∃ N, ∀ n, N ≤ n → ∀ s, A n s ∈ D) ∧
      ∀ D ∈ J, ∃ N, ∀ n, N ≤ n → ∀ s t, s ≠ t → (A n s, A n t) ∈ D := by
  obtain ⟨d, _, hdd, hdl, hdiam, hdF⟩ := catalog_diameter_schedule C F hFc hFd hFl
  obtain ⟨j, _, hjd, hjl, hjJ⟩ := countable_dense_schedule J hJc hJd hJl
  obtain ⟨A, hA0, hparent, hAd, hAj⟩ := silver_binary_levels B d hdd hdl j hjd hjl
  refine ⟨A, hA0, hparent, fun n s => hdiam n _ (hAd n s), ?_, ?_⟩
  · intro D hD
    obtain ⟨N, hN⟩ := hdF D hD
    exact ⟨N, fun n hn s => hN n hn (hAd n s)⟩
  · intro D hD
    obtain ⟨N, hN⟩ := hjJ D hD
    exact ⟨N, fun n hn s t hst => hN n hn (hAj n s t hst)⟩

end PolishSpaceBook
