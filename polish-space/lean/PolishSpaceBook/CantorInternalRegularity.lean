module

public import PolishSpaceBook.CantorInternalCodeOperations

@[expose] public section

/-! # Open cases and complements for two-sided approximations with internal codes

This is an external mathematical property of a set and a transitive model.
It is not yet claimed to be the interpretation of an internal formula.
-/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression
universe u

/-- Inner closed and outer open approximants with both complete node sets in the model. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $\mathcal R_M$ be the class of sets $A\IncludedIn\CantorSpace$ such that, for every real
    $\varepsilon>0$, there are a downward-closed binary tree $T$ and a word family $O$ satisfying
    $$\begin{gathered}
    W_T,W_O\in M,\qquad \TreeBody{T}\IncludedIn A\IncludedIn U(O),\\
    \mu(\SetDifference{U(O)}{\TreeBody{T}})<\varepsilon.
    \end{gathered}$$
    This is an external approximation property; it is not yet a definition of an internal predicate.
-/
def InternallyApproximable (M : ZFSet.{u}) (A : Set (ℕ → Bool)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T O : Set (List Bool),
    IsSubtree T ∧ wordTreeSet (binaryLift T) ∈ M ∧ wordTreeSet (binaryLift O) ∈ M ∧
    treeBody T ⊆ A ∧ A ⊆ openFromWords O ∧
    fairCoinProduct.real (openFromWords O \ treeBody T) < ε

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal approximations under complementation
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The open case follows from §{sec:internal-finite-measure-bounds}, retaining the original open code as the
    outer approximant. For complementation, replace the inner tree $T$ and outer word family $O$ by
    $$T':=D(O),\qquad O':=\SetDifference{\finseq{2}}{T}.$$
    Both codes are internal by the preceding constructions, and
    $$\TreeBody{T'}=U(O)^c\IncludedIn A^c\IncludedIn\TreeBody{T}^c=U(O').$$
    The error set is unchanged:
    $$\SetDifference{U(O')}{\TreeBody{T'}}
    =\SetDifference{\TreeBody{T}^c}{U(O)^c}
    =\SetDifference{U(O)}{\TreeBody{T}}.$$
-/
theorem internallyApproximable_openCode {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (O : Set (List Bool)) (hO : wordTreeSet (binaryLift O) ∈ M) :
    InternallyApproximable M (openFromWords O) := by
  intro ε hε
  obtain ⟨T, hT, hTM, hTA, _, hgap⟩ :=
    exists_internal_openCode_approximation hM hinf hpair hunion hpower hsep O hO hε
  exact ⟨T, O, hT, hTM, hO, hTA, Set.Subset.rfl, hgap⟩

/-- The absent-node case of the Borel induction. -/
lemma internallyApproximable_empty {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    InternallyApproximable M ∅ := by
  have he : wordTreeSet (binaryLift (∅ : Set (List Bool))) = (∅ : ZFSet.{u}) := by
    ext x; simp [mem_wordTreeSet, binaryLift]
  have hO : wordTreeSet (binaryLift (∅ : Set (List Bool))) ∈ M := by
    rw [he]
    exact empty_mem_of_infinity hM hinf
  simpa [openFromWords] using
    internallyApproximable_openCode hM hinf hpair hunion hpower hsep ∅ hO

/-- Complementation exchanges the two approximants and preserves the exact error set. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal approximations under complementation
-/
theorem internallyApproximable_compl {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    {A : Set (ℕ → Bool)} (hA : InternallyApproximable M A) : InternallyApproximable M Aᶜ := by
  intro ε hε
  obtain ⟨T, O, _, hTM, hOM, hTA, hAO, hgap⟩ := hA ε hε
  refine ⟨avoidWords O, Tᶜ, avoidWords_isSubtree O,
    avoidWords_mem hM hinf hpair hunion hpower hsep O hOM,
    missingWords_mem hM hinf hpair hunion hpower hsep T hTM, ?_, ?_, ?_⟩
  · rw [treeBody_avoidWords]
    exact Set.compl_subset_compl.mpr hAO
  · rw [openFromWords_compl]
    exact Set.compl_subset_compl.mpr hTA
  · rw [treeBody_avoidWords, openFromWords_compl]
    have he : (treeBody T)ᶜ \ (openFromWords O)ᶜ = openFromWords O \ treeBody T := by
      ext x; simp only [Set.mem_sdiff, Set.mem_compl_iff]; tauto
    rwa [he]

end PolishSpaceBook.CantorTreeMeasure
