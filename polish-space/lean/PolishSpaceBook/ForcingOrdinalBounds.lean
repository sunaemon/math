module

public import PolishSpaceBook.ForcingNames

@[expose] public section

/-! # Rank bounds for valuations and the ordinal-preservation reduction

The calculation is external and needs no genericity. The closure hypotheses in
its ground-model corollaries are explicit: this file does not infer internal
rank or check-name recursion from transitivity alone.
ForcingOrdinalPreservation derives these hypotheses from ground-model axioms.
-/

noncomputable section
namespace PolishSpaceBook.ForcingNames
open ZFSet
universe u

/-- Evaluating a name cannot increase its ambient set-theoretic rank. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: statement
  kind: lemma
  title: Rank bound for name valuations
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: proof
  excerpt: |
    Induct on $\mathrm{rank}(\tau)$. If $x\in\tau^G$, choose $\langle\sigma,p\rangle\in\tau$ with $p\in G$
    and $x=\sigma^G$. The induction hypothesis and the rank decrease for first coordinates give
    $$\begin{aligned}
    \mathrm{rank}(x)&=\mathrm{rank}(\sigma^G)\\
    &\le\mathrm{rank}(\sigma)<\mathrm{rank}(\tau).
    \end{aligned}$$
    A set has rank at most an ordinal $\beta$ exactly when each of its elements has rank less than $\beta$.
    Apply this characterization to $\tau^G$ and $\beta=\mathrm{rank}(\tau)$.
-/
theorem rank_valuation_le (G : Set ZFSet.{u}) (τ : ZFSet.{u}) :
    (valuation G τ).rank ≤ τ.rank := by
  apply ZFSet.rank_le_iff.mpr
  intro x hx
  obtain ⟨σ, p, _, hστ, rfl⟩ := (mem_valuation G τ x).mp hx
  exact (rank_valuation_le G σ).trans_lt (child_rank_lt hστ)
termination_by τ.rank
 decreasing_by exact child_rank_lt hστ

/-- A ground ordinal bounding the rank of a name also bounds any ordinal it evaluates to. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    Write an ordinal $\alpha\in M[G]$ as $\alpha=\tau^G$ with $\tau\in M^P$.
    Since an ordinal is its own rank, the valuation bound gives
    $$\alpha\le\mathrm{rank}(\tau).$$
    The rank-closure lemma supplies $\beta:=\mathrm{rank}(\tau)\in M$.
    Either $\alpha=\beta$ or $\alpha\in\beta$, so $\alpha\in M$ by transitivity.
-/
theorem ordinal_valuation_mem_ground {M τ α β : ZFSet.{u}}
    (hM : M.IsTransitive) (G : Set ZFSet.{u}) (hα : α.IsOrdinal) (hβ : β.IsOrdinal)
    (hβM : β ∈ M) (hτβ : τ.rank ≤ β.rank) (he : valuation G τ = α) : α ∈ M := by
  have hr : α.rank ≤ β.rank := he ▸ (rank_valuation_le G τ).trans hτβ
  have hs : α ⊆ β := (ZFSet.IsOrdinal.rank_le_iff_subset hα hβ).mp hr
  rcases (hα.subset_iff_eq_or_mem hβ).mp hs with heq | hmem
  · exact heq ▸ hβM
  · exact hM.mem_trans hmem hβM

/-- Rank-ordinal closure suffices for the no-new-ordinals direction. -/
theorem extension_ordinal_mem_ground {P M α : ZFSet.{u}} (hM : M.IsTransitive)
    (hrank : ∀ τ ∈ M, τ.rank.toZFSet ∈ M) (G : Set ZFSet.{u})
    (hα : α.IsOrdinal) (hαE : α ∈ extension P M G) : α ∈ M := by
  obtain ⟨τ, hτ, _, he⟩ := (mem_extension P M G α).mp hαE
  exact ordinal_valuation_mem_ground hM G hα (ZFSet.isOrdinal_toZFSet τ.rank)
    (hrank τ hτ) (by rw [Ordinal.rank_toZFSet]) he

/-- Together with check-name closure, the extension has exactly the ground ordinals. -/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  target: prose
  excerpt: |
    In the other direction, the check-name lemma and $\check{\alpha}^G=\alpha$ put every ground-model ordinal in $M[G]$.
    The bounded ordinal predicate in §{sec:zfc-absoluteness} identifies the ordinals of each transitive domain
    with its actual ordinal elements, so these two inclusions give the displayed equality.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-forcing.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The proof separates the external rank estimate from the internal closure constructions.
    The latter have now been derived from the stated axioms. For a weaker ground theory, it is enough to supply
    rank and check-name closure separately and then use the same ordinal comparison.
-/
theorem ordinal_mem_extension_iff {P M α : ZFSet.{u}} (hM : M.IsTransitive)
    (hrank : ∀ τ ∈ M, τ.rank.toZFSet ∈ M)
    (hcheck : ∀ x ∈ M, check P x ∈ M) (G : Set ZFSet.{u})
    (hG : ∃ p ∈ G, p ∈ P) (hα : α.IsOrdinal) :
    α ∈ extension P M G ↔ α ∈ M := by
  constructor
  · exact extension_ordinal_mem_ground hM hrank G hα
  · intro hαM
    exact (mem_extension P M G α).mpr
      ⟨check P α, hcheck α hαM, check_isName P α, valuation_check P G hG α⟩

end PolishSpaceBook.ForcingNames
