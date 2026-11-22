module

public import PolishSpaceBook.CantorTreeMeasure
public import PolishSpaceBook.BorelMeasureRegularity

@[expose] public section

/-! # Closed-tree bounds for the measure of a Borel set

Two closed subsets, one of a Borel set and one of its complement, squeeze its
measure. These are the witnesses whose codes and inclusion relations must be
transferred in a model-theoretic measure-absoluteness proof.
-/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open Set MeasureTheory

/-- Regularity produces tree-coded lower bounds for a Borel set and its complement. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Closed-tree bounds for Borel measure
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Closed-set regularity from §{sec:borel-measures-radon} gives a closed set $F$ and an open set $U$ with
    $$F\IncludedIn A\IncludedIn U,\qquad\mu(\SetDifference{U}{F})<\varepsilon.$$
    Take $T=\ClosedTreeCode{F}$ and $S=\ClosedTreeCode{U^c}$. Their bodies are $F$ and $U^c$, respectively, by the
    closed-set coding theorem. Since $F\IncludedIn U$, finite additivity gives
    $$\begin{aligned}
    1-\mu(U^c)-\mu(F)&=\mu(U)-\mu(F)\\
    &=\mu(\SetDifference{U}{F})<\varepsilon.
    \end{aligned}$$
-/
theorem exists_closed_bounds {A : Set (ℕ → Bool)} (hA : MeasurableSet A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T S : Set (List Bool), IsSubtree T ∧ IsSubtree S ∧
      treeBody T ⊆ A ∧ treeBody S ⊆ Aᶜ ∧
      1 - fairCoinProduct.real (treeBody S) - fairCoinProduct.real (treeBody T) < ε := by
  obtain ⟨F, U, hF, hU, hFA, hAU, hgap⟩ :=
    BorelMeasureRegularity.closed_open_approximation fairCoinProduct hA
      (ENNReal.ofReal_pos.mpr hε)
  refine ⟨closedTreeCode F, closedTreeCode Uᶜ,
    closedTreeCode_isSubtree F, closedTreeCode_isSubtree Uᶜ, ?_⟩
  rw [treeBody_closedTreeCode_eq_of_closed hF,
    treeBody_closedTreeCode_eq_of_closed hU.isClosed_compl]
  refine ⟨hFA, compl_subset_compl.mpr hAU, ?_⟩
  have hg : fairCoinProduct.real U - fairCoinProduct.real F < ε := by
    rw [← measureReal_sdiff (hFA.trans hAU) hF.measurableSet]
    exact ENNReal.toReal_lt_of_lt_ofReal hgap
  have hc := measureReal_add_measureReal_compl (μ := fairCoinProduct) hU.measurableSet
  rw [probReal_univ] at hc
  linarith

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The two inclusions give the stated lower and upper bounds by monotonicity and complementation.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: theorem
  title: Closed-tree bounds for Borel measure
-/
lemma measure_bounds {A : Set (ℕ → Bool)} (hA : MeasurableSet A)
    {T S : Set (List Bool)} (hT : treeBody T ⊆ A) (hS : treeBody S ⊆ Aᶜ) :
    fairCoinProduct.real (treeBody T) ≤ fairCoinProduct.real A ∧
      fairCoinProduct.real A ≤ 1 - fairCoinProduct.real (treeBody S) := by
  refine ⟨measureReal_mono hT, ?_⟩
  have h := measureReal_mono (μ := fairCoinProduct) hS
  have hc := measureReal_add_measureReal_compl (μ := fairCoinProduct) hA
  rw [probReal_univ] at hc
  linarith

/-- Any candidate number in the same closed-tree interval is close to the actual measure. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Restricting them back to the internal points, monotonicity and
    complementation place the decoded internal measure between
    $\mu(\TreeBody{T})$ and $1-\mu(\TreeBody{S})$.
    The external value $\mu(A)$ lies between the same endpoints, so the values are equal.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Both $a$ and $\mu(A)$ lie in the same interval of length less than $\varepsilon$, so
    $|a-\mu(A)|<\varepsilon$.
-/
lemma abs_sub_measure_lt {A : Set (ℕ → Bool)} (hA : MeasurableSet A)
    {T S : Set (List Bool)} (hT : treeBody T ⊆ A) (hS : treeBody S ⊆ Aᶜ)
    {r ε : ℝ} (hrT : fairCoinProduct.real (treeBody T) ≤ r)
    (hrS : r ≤ 1 - fairCoinProduct.real (treeBody S))
    (hgap : 1 - fairCoinProduct.real (treeBody S) - fairCoinProduct.real (treeBody T) < ε) :
    |r - fairCoinProduct.real A| < ε := by
  obtain ⟨ha, hb⟩ := measure_bounds hA hT hS
  rw [abs_lt]
  constructor <;> linarith

/-- This comparison does not assume a second external measure on the old points. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Comparison by closed-tree bounds
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    If the two numbers differed, taking $\varepsilon=|a-\mu(A)|$ would be a contradiction.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Once both obligations are met, the comparison proposition identifies
    the internal numerical value with the measure of the external interpretation, without treating the old points
    as an external probability space.
-/
theorem measure_eq_of_closed_bounds {A : Set (ℕ → Bool)} (hA : MeasurableSet A) {r : ℝ}
    (hr : ∀ ε : ℝ, 0 < ε → ∃ T S : Set (List Bool),
      treeBody T ⊆ A ∧ treeBody S ⊆ Aᶜ ∧
      fairCoinProduct.real (treeBody T) ≤ r ∧
      r ≤ 1 - fairCoinProduct.real (treeBody S) ∧
      1 - fairCoinProduct.real (treeBody S) - fairCoinProduct.real (treeBody T) < ε) :
    r = fairCoinProduct.real A := by
  by_contra h
  have hpos : 0 < |r - fairCoinProduct.real A| := abs_pos.mpr (sub_ne_zero.mpr h)
  obtain ⟨T, S, hT, hS, hrT, hrS, hgap⟩ := hr _ hpos
  exact (lt_irrefl _) (abs_sub_measure_lt hA hT hS hrT hrS hgap)

/-- A strict rational bound on Borel measure is certified by a closed tree and
uniform rational bounds on all its finite levels. The inclusion is the only
clause that still quantifies over points. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Tree certificate for a rational measure bound
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    If $q<\mu(A)$, apply the theorem with $\varepsilon=\mu(A)-q$. Its bounds give
    $q<\mu(\TreeBody{T})$. Choose a rational $r$ strictly between these two numbers; then
    $r\le d_n(T)$ for every $n$. Conversely, the finite-level lower bounds give
    $r\le\mu(\TreeBody{T})\le\mu(A)$, and $q<r$ finishes the proof.
-/
theorem borel_lower_cut {A : Set (ℕ → Bool)} (hA : MeasurableSet A) (q : ℚ) :
    (q : ℝ) < fairCoinProduct.real A ↔
      ∃ T : Set (List Bool), IsSubtree T ∧ treeBody T ⊆ A ∧
        ∃ r : ℚ, q < r ∧ ∀ n, r ≤ levelWeight T n := by
  constructor
  · intro hq
    obtain ⟨T, S, hT, _, hTA, hSA, hgap⟩ := exists_closed_bounds hA (sub_pos.mpr hq)
    have hb := (measure_bounds hA hTA hSA).2
    have hlower : (q : ℝ) < fairCoinProduct.real (treeBody T) := by linarith
    obtain ⟨r, hqr, hr⟩ := exists_rat_btwn hlower
    exact ⟨T, hT, hTA, r, by exact_mod_cast hqr, (closed_lower_bound hT r).mp hr.le⟩
  · rintro ⟨T, hT, hTA, r, hqr, hr⟩
    have hqr' : (q : ℝ) < (r : ℝ) := by exact_mod_cast hqr
    exact hqr'.trans_le (((closed_lower_bound hT r).mpr hr).trans (measureReal_mono hTA))

end PolishSpaceBook.CantorTreeMeasure
