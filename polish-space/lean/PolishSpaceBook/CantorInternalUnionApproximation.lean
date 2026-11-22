module

public import PolishSpaceBook.CantorInternalFamilyOperations
public import PolishSpaceBook.BorelMeasureRegularity

@[expose] public section

/-! # Combining internal approximation families using a finite measure tail -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory
universe u

/-- The same finite-tail estimate as in ordinary Borel regularity, with dyadic child errors. -/
lemma exists_dyadic_union_gap (A F U : ℕ → Set (ℕ → Bool))
    (hA : ∀ n, MeasurableSet (A n))
    (hFA : ∀ n, F n ⊆ A n) (hAU : ∀ n, A n ⊆ U n) (k : ℕ)
    (hgap : ∀ n, fairCoinProduct.real (U n \ F n) < unionApproximationError k n) :
    ∃ N : ℕ, fairCoinProduct.real ((⋃ n, U n) \ ⋃ n ≤ N, F n) < 1 / (2 : ℝ) ^ k := by
  have hhalf : 0 < 1 / (2 : ℝ) ^ (k + 1) := by positivity
  have hsum : (∑' n, ENNReal.ofReal (unionApproximationError k n)) =
      ENNReal.ofReal (1 / (2 : ℝ) ^ (k + 1)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (unionApproximationError_pos k n).le)
      (unionApproximationError_hasSum k).summable, (unionApproximationError_hasSum k).tsum_eq]
  have hg (n : ℕ) : fairCoinProduct (U n \ F n) < ENNReal.ofReal (unionApproximationError k n) :=
    (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).mpr (hgap n)
  obtain ⟨N, hN⟩ := BorelMeasureRegularity.exists_finite_union_remainder fairCoinProduct A hA
    (ENNReal.ofReal_pos.mpr hhalf)
  refine ⟨N, (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top _ _)).mp ?_⟩
  calc
    fairCoinProduct ((⋃ n, U n) \ ⋃ n ≤ N, F n) ≤
        (∑' n, fairCoinProduct (U n \ F n)) + fairCoinProduct ((⋃ n, A n) \ ⋃ n ≤ N, A n) :=
      BorelMeasureRegularity.measure_union_gap_le _ A F U hFA hAU N
    _ ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ (k + 1)) + fairCoinProduct ((⋃ n, A n) \ ⋃ n ≤ N, A n) := by
      gcongr
      rw [← hsum]
      exact ENNReal.tsum_le_tsum (fun n => (hg n).le)
    _ < ENNReal.ofReal (1 / (2 : ℝ) ^ (k + 1)) + ENNReal.ofReal (1 / (2 : ℝ) ^ (k + 1)) :=
      ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hN
    _ = ENNReal.ofReal (1 / (2 : ℝ) ^ k) := by
      rw [← ENNReal.ofReal_add hhalf.le hhalf.le]
      congr 1
      rw [pow_succ, div_mul_eq_div_div]
      ring

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Retain the transitive-model hypotheses of §{sec:internal-approximation-errors}.
    For a valid Borel expression $c$ whose label graph belongs to $M$, write $A_s$ for its external binary
    interpretation at $s$. Every $A_s$ is Borel: well-founded evaluation preserves Borel measurability,
    and the inclusion of Cantor space into Baire space is continuous.
-/
lemma measurableSet_cantorNodeSet (c : BorelExpression) (hc : c.Valid) (s : List ℕ) :
    MeasurableSet (cantorNodeSet c hc.2.2.2.2.2 s) := by
  rw [← cantorSet_nodeCode c hc s]
  exact measurableSet_cantorSet _ _

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal approximation at a countable union
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Let $\varepsilon>0$. Choose $k\in\omega$ with $2^{-k}<\varepsilon$. The internal selection theorem of
    §{sec:internal-approximation-errors} supplies downward-closed trees $T_n,S_n$ with a single internal
    paired graph. Put
    $$\begin{gathered}
    \mathcal F_n=\TreeBody{T_n},\qquad O_n=\SetDifference{\finseq{2}}{S_n},\qquad \mathcal U_n=U(O_n)=\TreeBody{S_n}^c,\\
    \mathcal F_n\IncludedIn A_n\IncludedIn \mathcal U_n,\qquad
    \mu(\SetDifference{\mathcal U_n}{\mathcal F_n})<\delta_n:=\frac{1}{2^{k+2+n}}.
    \end{gathered}$$
    Absent children are included with empty interpretation, as in that theorem. The sum of the errors is
    at most $\sum_n\delta_n=2^{-(k+1)}$.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Write $A=\bigcup_n A_n$ and $A_N^*=\bigcup_{n\le N}A_n$. Since $\mu$ is finite and all the sets $A_n$
    are measurable, the finite-tail estimate of §{sec:borel-measures-radon} gives $N\in\omega$ with
    $$\mu(\SetDifference{A}{A_N^*})<2^{-(k+1)}.$$
    Use the combined codes
    $$T=\bigcup_{n\le N}T_n,\qquad O=\bigcup_n O_n.$$
    The family-operation proposition gives $W_T,W_O\in M$. The tree $T$ is downward closed, and its body is
    $\mathcal F:=\bigcup_{n\le N}\mathcal F_n$; the open set coded by $O$ is $\mathcal U:=\bigcup_n \mathcal U_n$.
    Consequently $\mathcal F\IncludedIn A\IncludedIn \mathcal U$.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Apply the union-gap estimate proved in §{sec:borel-measures-radon}:
    $$\begin{aligned}
    \mu(\SetDifference{\mathcal U}{\mathcal F})
    &\le\sum_{n=0}^{\infty}\mu(\SetDifference{\mathcal U_n}{\mathcal F_n})
      +\mu(\SetDifference{A}{A_N^*})\\
    &<2^{-(k+1)}+2^{-(k+1)}=2^{-k}<\varepsilon.
    \end{aligned}$$
    This proves the required approximation property. The choice of the finite cutoff $N$ is external;
    every actual natural number belongs to $M$, and the finite-union construction gives an internal code
    for this particular cutoff. No internal sequence of cutoff choices is needed.
-/
theorem internallyApproximable_childUnion {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (s : List ℕ)
    (hA : ∀ n, c (s ++ [n]) ≠ 0 → InternallyApproximable M (cantorNodeSet c hc.2.2.2.2.2 (s ++ [n]))) :
    InternallyApproximable M (⋃ n, cantorNodeSet c hc.2.2.2.2.2 (s ++ [n])) := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  rw [one_div_pow] at hk
  obtain ⟨T, S, hH, hTS⟩ := internally_selected_child_approximations hM hinf hpair hunion hpower
    hsep hrep hchoice c hc hcM s k hA
  let A (n : ℕ) := cantorNodeSet c hc.2.2.2.2.2 (s ++ [n])
  have hgap (n : ℕ) : fairCoinProduct.real ((treeBody (S n))ᶜ \ treeBody (T n)) <
      unionApproximationError k n := by
    have he : (treeBody (S n))ᶜ \ treeBody (T n) = (treeBody (T n) ∪ treeBody (S n))ᶜ := by
      ext x; simp only [Set.mem_sdiff, Set.mem_compl_iff, Set.mem_union]; tauto
    rw [he]
    exact (hTS n).2.2.2.2.2
  obtain ⟨N, hN⟩ := exists_dyadic_union_gap A (fun n => treeBody (T n)) (fun n => (treeBody (S n))ᶜ)
    (fun n => measurableSet_cantorNodeSet c hc _) (fun n => (hTS n).2.2.2.2.1.1)
    (fun n => (hTS n).2.2.2.2.1.2) k hgap
  have hcodes := approximation_union_codes_mem hM hinf hpair hunion hpower hsep hrep T S
    (fun n => (hTS n).1) (fun n => (hTS n).2.1) hH N
  have hbody : treeBody (⋃ n ∈ Finset.range (N + 1), T n) = ⋃ n ≤ N, treeBody (T n) := by
    rw [treeBody_finiteUnion _ T (fun n => (hTS n).2.2.1)]
    simp only [Finset.mem_range, Nat.lt_succ_iff]
  have hopen : openFromWords (⋃ n, (S n)ᶜ) = ⋃ n, (treeBody (S n))ᶜ := by
    rw [openFromWords_iUnion]
    simp only [openFromWords_compl]
  refine ⟨⋃ n ∈ Finset.range (N + 1), T n, ⋃ n, (S n)ᶜ, ?_, hcodes.2, hcodes.1, ?_, ?_, ?_⟩
  · intro v w hv hw
    obtain ⟨n, hn, hv⟩ := Set.mem_iUnion₂.mp hv
    exact Set.mem_iUnion₂.mpr ⟨n, hn, (hTS n).2.2.1 hv hw⟩
  · rw [hbody]
    exact Set.iUnion₂_subset fun n _ => (hTS n).2.2.2.2.1.1.trans (Set.subset_iUnion A n)
  · rw [hopen]
    exact Set.iUnion_mono (fun n => (hTS n).2.2.2.2.1.2)
  · rw [hopen, hbody]
    exact hN.trans hk

end PolishSpaceBook.CantorTreeMeasure
