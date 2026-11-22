module

public import PolishSpaceBook.DomainCoverage
public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Analysis.Real.Cardinality

@[expose] public section

namespace PolishSpaceBook
open Set

/-- In a chain, a strict lower approximation is way below. -/
theorem domainWayBelow_of_lt {L : Type*} [LinearOrder L] {a b : L} (hab : a < b) :
    DomainWayBelow a b := by
  intro S s _ _ hs hbs
  by_contra! h
  have hsa : s ≤ a := hs.2 (fun x hx => (h x hx).le)
  exact (not_lt_of_ge (hbs.trans hsa)) hab

/-- Rational points of the actual closed real unit interval. -/
def unitIntervalRationalPoint (q : Set.Icc (0 : ℚ) 1) : unitInterval :=
  ⟨(q.val : ℝ), by
    change (0 : ℝ) ≤ (q.val : ℝ) ∧ (q.val : ℝ) ≤ 1
    constructor
    · exact_mod_cast q.property.1
    · exact_mod_cast q.property.2⟩

def unitIntervalRationalBasis : Set unitInterval := range unitIntervalRationalPoint

theorem unitIntervalRationalBasis_countable : unitIntervalRationalBasis.Countable :=
  countable_range _

theorem unitIntervalRationalBasis_isBasis : IsDomainBasis unitIntervalRationalBasis := by
  intro x
  have hbot : (⊥ : unitInterval) ∈ unitIntervalRationalBasis := by
    refine ⟨⟨0, by norm_num⟩, ?_⟩
    apply Subtype.ext
    norm_num [unitIntervalRationalPoint]
  refine ⟨⟨⊥, hbot, domainWayBelow_bot x⟩, ?_, ?_, ?_⟩
  · intro a ha b hb
    rcases le_total a b with h | h
    · exact ⟨b, hb, h, le_rfl⟩
    · exact ⟨a, ha, le_rfl, h⟩
  · intro a ha
    exact domainWayBelow_le ha.2
  · intro y hy
    by_contra hxy
    have hyx : y.val < x.val := lt_of_not_ge hxy
    obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hyx
    have hq : q ∈ Set.Icc (0 : ℚ) 1 := by
      constructor
      · exact_mod_cast (y.property.1.trans hyq.le)
      · exact_mod_cast (hqx.le.trans x.property.2)
    let z := unitIntervalRationalPoint ⟨q, hq⟩
    have hzx : z < x := hqx
    have hzy : z ≤ y := hy ⟨⟨⟨q, hq⟩, rfl⟩, domainWayBelow_of_lt hzx⟩
    exact not_le_of_gt hyq hzy

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    For example, the chain $[0,1]$ with its Scott topology is an uncountable $\omega$-continuous dcpo, but it has no
-/
theorem unitInterval_omegaContinuousDomain : IsOmegaContinuousDomain unitInterval :=
  ⟨isDomainDcpo_of_completePartialOrder _, unitIntervalRationalBasis,
    unitIntervalRationalBasis_countable, unitIntervalRationalBasis_isBasis⟩

/-@ booklink:
  source: polish-space-book/domain-theory-quasi-polish-spaces.md
  target: prose
  excerpt: |
    For example, the chain $[0,1]$ with its Scott topology is an uncountable $\omega$-continuous dcpo, but it has no
-/
theorem unitInterval_uncountable : ¬ (unitInterval : Set ℝ).Countable := by
  rw [unitInterval, Cardinal.Real.Icc_countable_iff]
  norm_num

end PolishSpaceBook
