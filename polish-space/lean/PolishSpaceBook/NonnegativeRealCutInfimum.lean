module

public import PolishSpaceBook.NonnegativeRealCutReflection
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Rounded intersections encode countable infima of nonnegative reals -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open ZFSet SetTheoryModels
universe u

/-- A common strictly larger rational margin removes a possible endpoint of the intersection. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a sequence $\mathcal D= \Sequence{D_n}{n \in \omega}$ of sets, define $\RealCutInfimum{ \mathcal D}
    \IncludedIn \omega \times \omega$ by
    $$\begin{aligned}
    \Pair{a}{b}\in\RealCutInfimum{\mathcal D}
    &\longleftrightarrow 0<b\ \land\ \exists m,d\in\omega\;[\\
    &\qquad 0<d\ \land\ ad<mb\\
    &\qquad{}\land\forall n\in\omega\;(\Pair{m}{d}\in D_n)].
    \end{aligned}$$
    The witness fraction $m/d$ lies strictly above $a/b$ and belongs to every cut. This common margin is what
    removes a possible endpoint. The formula is meaningful for arbitrary sets $D_n$; validity is used in the
    numerical identification below.
-/
def roundedInfCutCode (C : ℕ → ZFSet.{u}) : ZFSet.{u} :=
  naturalPairSet (fun a b => 0 < b ∧ ∃ m d : ℕ,
    0 < d ∧ a * d < m * b ∧ ∀ n, pair (natOrdinal m) (natOrdinal d) ∈ C n)

lemma nonnegative_range_bddBelow (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) : BddBelow (Set.range r) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact hr n⟩

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The sequence is bounded below by zero, so its infimum $r$ is a nonnegative real.
    For $q=a/b$ with $b>0$, suppose $q<r$. Choose a nonnegative rational $m/d$ with
    $$q<m/d<r,\qquad d>0.$$
    It belongs to every cut, because $r\le r_n$ for all $n$. Conversely, a common witness $m/d$ is below every
    $r_n$, hence at most their infimum; therefore $q<m/d\le r$.
    These two implications prove equality of the codes, including their exclusion of zero denominators.
    For an arbitrary sequence of valid codes, apply §{sec:internal-borel-measure-cut} to each term and use the
    identity just proved. The same decoding theorem gives validity and the displayed value of the result.
-/
lemma fraction_lt_ciInf_iff (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / b < ⨅ n, r n ↔
      ∃ m d : ℕ, 0 < d ∧ a * d < m * b ∧ ∀ n, (m : ℝ) / d < r n := by
  have hbound := nonnegative_range_bddBelow r hr
  constructor
  · intro hq
    have hq0 : 0 ≤ (a : ℝ) / b := by positivity
    obtain ⟨m, d, hd, hqm, hmr⟩ :=
      (lt_iff_nat_fraction_margin ((a : ℝ) / b) (((a : ℝ) / b + ⨅ n, r n) / 2) hq0).mp (by linarith)
    refine ⟨m, d, hd, (rationalLess_iff a b m d hb hd).mpr hqm, ?_⟩
    intro n
    exact (show (m : ℝ) / d < ⨅ n, r n by linarith).trans_le (ciInf_le hbound n)
  · rintro ⟨m, d, hd, hqm, hmr⟩
    exact ((rationalLess_iff a b m d hb hd).mp hqm).trans_le (le_ciInf (fun n => (hmr n).le))

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Rounded intersection of real cut codes
-/
theorem roundedInfCutCode_eq (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) :
    roundedInfCutCode (fun n => nonnegativeRealCutCode.{u} (r n)) =
      nonnegativeRealCutCode (⨅ n, r n) := by
  apply naturalPairSet_ext
  intro a b
  apply and_congr_right
  intro hb
  rw [fraction_lt_ciInf_iff r hr a b hb]
  simp only [pair_mem_nonnegativeRealCutCode]
  constructor
  · rintro ⟨m, d, hd, hq, h⟩
    exact ⟨m, d, hd, hq, fun n => (h n).2⟩
  · rintro ⟨m, d, hd, hq, h⟩
    exact ⟨m, d, hd, hq, fun n => ⟨hd, h n⟩⟩

theorem decode_roundedInfCutCode (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) :
    decodeNonnegativeRealCut (roundedInfCutCode (fun n => nonnegativeRealCutCode.{u} (r n))) =
      ⨅ n, r n := by
  rw [roundedInfCutCode_eq r hr, decode_nonnegativeRealCutCode (le_ciInf hr)]

/-- This form starts with recognized codes rather than already specified external values. -/
theorem roundedInfCutCode_eq_decoded (C : ℕ → ZFSet.{u}) (hC : ∀ n, ValidNonnegativeRealCutCode (C n)) :
    roundedInfCutCode C = nonnegativeRealCutCode (⨅ n, decodeNonnegativeRealCut (C n)) := by
  have he : C = fun n => nonnegativeRealCutCode (decodeNonnegativeRealCut (C n)) :=
    funext fun n => (hC n).encode_decode
  exact (congrArg roundedInfCutCode he).trans
    (roundedInfCutCode_eq _ (fun n => decodeNonnegativeRealCut_nonneg (hC n)))

theorem roundedInfCutCode_valid (C : ℕ → ZFSet.{u}) (hC : ∀ n, ValidNonnegativeRealCutCode (C n)) :
    ValidNonnegativeRealCutCode (roundedInfCutCode C) := by
  rw [roundedInfCutCode_eq_decoded C hC]
  exact nonnegativeRealCutCode_valid _

theorem decode_roundedInfCutCode_of_valid (C : ℕ → ZFSet.{u})
    (hC : ∀ n, ValidNonnegativeRealCutCode (C n)) :
    decodeNonnegativeRealCut (roundedInfCutCode C) = ⨅ n, decodeNonnegativeRealCut (C n) := by
  rw [roundedInfCutCode_eq_decoded C hC,
    decode_nonnegativeRealCutCode (le_ciInf (fun n => decodeNonnegativeRealCut_nonneg (hC n)))]

lemma reciprocal_successor_infimum : (⨅ n : ℕ, 1 / ((n : ℝ) + 1)) = 0 := by
  have hnonneg (n : ℕ) : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  apply le_antisymm
  · exact ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n => ciInf_le (nonnegative_range_bddBelow (fun n => 1 / ((n : ℝ) + 1)) hnonneg) n)
  · exact le_ciInf hnonneg

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: example
  title: Why the intersection needs rounding
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Every $r_n$ is positive, and the sequence converges to zero. Hence $0<r_n$ for every index, whereas $0<0$
    is false. The membership conditions give the stated discrepancy.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For continuity from above, the numerical operation we need is a countable infimum. It cannot be represented
    by the plain intersection of strict lower cuts: that intersection can retain the limiting endpoint.
-/
theorem intersection_endpoint :
    (∀ n : ℕ, pair (natOrdinal 0) (natOrdinal 1) ∈ nonnegativeRealCutCode.{u} (1 / ((n : ℝ) + 1))) ∧
    pair (natOrdinal 0) (natOrdinal 1) ∉
      roundedInfCutCode (fun n => nonnegativeRealCutCode.{u} (1 / ((n : ℝ) + 1))) := by
  constructor
  · intro n
    rw [pair_mem_nonnegativeRealCutCode]
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_div, Nat.zero_lt_one, true_and]
    positivity
  · rw [roundedInfCutCode_eq _ (fun n => by positivity), reciprocal_successor_infimum,
      nonnegativeRealCutCode_zero]
    exact ZFSet.notMem_empty _

end PolishSpaceBook.CantorTreeMeasure
