module

public import PolishSpaceBook.CantorInternalRegularity
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section

/-! # Finite Boolean operations on sets with internal two-sided approximations -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory
universe u

lemma openFromWords_union (O V : Set (List Bool)) :
    openFromWords (O ∪ V) = openFromWords O ∪ openFromWords V := by
  ext x
  simp only [openFromWords, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨s, hs | hs, hx⟩
    · exact Or.inl ⟨s, hs, hx⟩
    · exact Or.inr ⟨s, hs, hx⟩
  · rintro (⟨s, hs, hx⟩ | ⟨s, hs, hx⟩)
    · exact ⟨s, Or.inl hs, hx⟩
    · exact ⟨s, Or.inr hs, hx⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal approximations under finite Boolean operations
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Given $\varepsilon>0$, choose closed inner and open outer approximants for each set with error less
    than $\varepsilon/2$. For the union, take the union of the two closed approximants and the union of
    the two open approximants. §{sec:internal-finite-measure-bounds} constructs their entire codes
    in the model: finite unions of downward-closed trees represent unions of their bodies, and unions
    of open word codes represent unions of their open sets. If the inner approximants are $F,K$ and the
    outer approximants are $U,V$, then
    $$\begin{aligned}
    \mu(\SetDifference{(U\cup V)}{(F\cup K)})
    &\le\mu(\SetDifference{U}{F})+\mu(\SetDifference{V}{K})\\
    &<\varepsilon.
    \end{aligned}$$
    Thus the union has the required approximants. Complementation was proved in
    §{sec:internal-finite-measure-bounds}; apply it twice to
    $\SetDifference{A}{B}=(A^c\cup B)^c$.
-/
theorem internallyApproximable_union {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    {A B : Set (ℕ → Bool)} (hA : InternallyApproximable M A) (hB : InternallyApproximable M B) :
    InternallyApproximable M (A ∪ B) := by
  intro ε hε
  obtain ⟨T, O, hT, hTM, hOM, hTA, hAO, hgA⟩ := hA (ε / 2) (by linarith)
  obtain ⟨S, V, hS, hSM, hVM, hSB, hBV, hgB⟩ := hB (ε / 2) (by linarith)
  refine ⟨T ∪ S, O ∪ V, subtree_union hT hS,
    treeUnion_mem hM hpair hunion T S hTM hSM,
    treeUnion_mem hM hpair hunion O V hOM hVM, ?_, ?_, ?_⟩
  · rw [treeBody_union hT hS]
    exact Set.union_subset_union hTA hSB
  · rw [openFromWords_union]
    exact Set.union_subset_union hAO hBV
  · rw [openFromWords_union, treeBody_union hT hS]
    have hs : (openFromWords O ∪ openFromWords V) \ (treeBody T ∪ treeBody S) ⊆
        (openFromWords O \ treeBody T) ∪ (openFromWords V \ treeBody S) := by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_union] at *
      tauto
    have hm := (measureReal_mono (μ := fairCoinProduct) hs).trans
      (measureReal_union_le (openFromWords O \ treeBody T) (openFromWords V \ treeBody S))
    linarith

lemma internallyApproximable_finset_union {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    {ι : Type*} (s : Finset ι) (A : ι → Set (ℕ → Bool))
    (hA : ∀ i ∈ s, InternallyApproximable M (A i)) : InternallyApproximable M (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using internallyApproximable_empty hM hinf hpair hunion hpower hsep
  | @insert i s hi ih =>
    have hAi := hA i (Finset.mem_insert_self i s)
    have hAs := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left] using
      internallyApproximable_union hM hpair hunion hAi hAs

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal approximations under finite Boolean operations
-/
theorem internallyApproximable_diff {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    {A B : Set (ℕ → Bool)} (hA : InternallyApproximable M A) (hB : InternallyApproximable M B) :
    InternallyApproximable M (A \ B) := by
  have hcA := internallyApproximable_compl hM hinf hpair hunion hpower hsep hA
  have hu := internallyApproximable_union hM hpair hunion hcA hB
  simpa only [Set.compl_union, compl_compl, Set.sdiff_eq] using
    internallyApproximable_compl hM hinf hpair hunion hpower hsep hu

end PolishSpaceBook.CantorTreeMeasure
