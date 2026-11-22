module

public import PolishSpaceBook.DiagonalMinMax
public import PolishSpaceBook.CompactMinMax
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! # Compact min–max coordinates count eigenvalues above positive thresholds -/

noncomputable section

open Set Filter
open scoped Topology

namespace PolishSpaceBook.CompactMinMaxCounting

open HilbertMinMax DiagonalMinMax CompactMinMax

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable {ι : Type*}

/-- There are only finitely many eigenbasis vectors with eigenvalue at least
any fixed positive threshold. This counts multiplicities. -/
theorem finite_eigenvalue_ge (A : H →L[𝕜] H) (hc : IsCompactOperator A)
    (hs : IsSelfAdjoint A) (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i) {r : ℝ} (hr : 0 < r) :
    {i | r ≤ ev i}.Finite := by
  classical
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_minMax_zero A hc) r hr
  have hsmall : minMax A N < r := by
    simpa only [dist_zero_right, Real.norm_of_nonneg (minMax_nonneg A N)] using hN N le_rfl
  by_contra hinf
  obtain ⟨s, hs', hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (N + 1)
  have hlow := minMax_lower_of_finite_basisSpan A hs b ev he (s : Set ι)
    (n := N) (r := r) (by simp [hcard]) (fun i hi => hs' hi)
  exact (not_le_of_gt hsmall) hlow

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    This count is finite. Otherwise, for every $n$ choose $n+1$ such vectors. Their span meets the orthogonal
    complement of every subspace of dimension at most $n$ in a unit vector, whose quadratic value is greater
    than $r$. The minimum of the finitely many chosen eigenvalues gives a bound independent of the discarded
    subspace. Thus $\MinMaxValue{A}{n}>r$ for every $n$, contradicting convergence to zero.
-/
theorem finite_eigenvalue_gt (A : H →L[𝕜] H) (hc : IsCompactOperator A)
    (hs : IsSelfAdjoint A) (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i) {r : ℝ} (hr : 0 < r) :
    {i | r < ev i}.Finite :=
  (finite_eigenvalue_ge A hc hs b ev he hr).subset (fun i h => show r ≤ ev i from le_of_lt h)

/-- The exact min–max counting rule: the `n`th coordinate exceeds a positive
threshold iff more than `n` eigenvectors, counted with multiplicity, exceed it. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    The same dimension argument, now using all the $\PositiveSpectralCount{A}{r}$ basis vectors above $r$,
    gives $\MinMaxValue{A}{n}>r$ when $n<\PositiveSpectralCount{A}{r}$. If
    $\PositiveSpectralCount{A}{r}\le n$, discard their span. Parseval's identity bounds the quadratic form
    by $r$ on the remaining unit ball, so $\MinMaxValue{A}{n}\le r$. Consequently,
    $$r<\MinMaxValue{A}{n}\quad\Longleftrightarrow\quad n<\PositiveSpectralCount{A}{r}
    \qquad(r>0).$$
-/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For $r>0$, let
    $\PositiveSpectralCount{A}{r}$ count its vectors whose eigenvalues exceed $r$.
-/
theorem minMax_gt_iff_count (A : H →L[𝕜] H) (hc : IsCompactOperator A)
    (hs : IsSelfAdjoint A) (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i) {r : ℝ} (hr : 0 < r) (n : ℕ) :
    r < minMax A n ↔ n < {i | r < ev i}.ncard := by
  classical
  let s := {i | r < ev i}
  have hsfin : s.Finite := finite_eigenvalue_gt A hc hs b ev he hr
  let : Fintype s := hsfin.fintype
  have hcard : s.ncard = Fintype.card s := by simp [Set.ncard]
  constructor
  · intro h
    by_contra hn
    have hle : Fintype.card s ≤ n := by simpa [← hcard] using Nat.le_of_not_gt hn
    have hu := minMax_upper_of_finite_cutoff A hs b ev he s hle hr.le
      (fun i hi => le_of_not_gt hi)
    exact (not_le_of_gt h) hu
  · intro hn
    have hnon : Nonempty s := by
      rw [hcard] at hn
      exact Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hn)
    let : Nonempty s := hnon
    let q := Finset.univ.inf' Finset.univ_nonempty (fun i : s => ev i)
    have hrq : r < q := by
      exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => i.2)
    have hq : ∀ i ∈ s, q ≤ ev i := by
      intro i hi
      exact Finset.inf'_le _ (Finset.mem_univ (⟨i, hi⟩ : s))
    have hlow := minMax_lower_of_finite_basisSpan A hs b ev he s
      (by simpa [← hcard] using hn) hq
    exact hrq.trans_le hlow

/-- Positive threshold cuts of the min–max sequence have precisely the
spectral multiplicity prescribed by the compact eigenbasis. -/
theorem minMax_threshold_set (A : H →L[𝕜] H) (hc : IsCompactOperator A)
    (hs : IsSelfAdjoint A) (b : HilbertBasis ι 𝕜 H) (ev : ι → ℝ)
    (he : ∀ i, A (b i) = (ev i : 𝕜) • b i) {r : ℝ} (hr : 0 < r) :
    {n | r < minMax A n} = Set.Iio {i | r < ev i}.ncard := by
  ext n
  exact minMax_gt_iff_count A hc hs b ev he hr n

end PolishSpaceBook.CompactMinMaxCounting
