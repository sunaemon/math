module

public import PolishSpaceBook.SetTheoryTernaryRelations
public import PolishSpaceBook.SetTheoryWordMap

@[expose] public section

/-! # Internal graphs needed for finite Borel-certificate rows -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

def wordLookupGraph : ZFSet.{u} :=
  ternaryRelationGraph finiteSequences Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet
    (SetWordLookup Ordinal.omega0.toZFSet (natOrdinal 0))

def wordTakeGraph : ZFSet.{u} :=
  ternaryRelationGraph finiteSequences Ordinal.omega0.toZFSet finiteSequences
    (SetWordTake Ordinal.omega0.toZFSet)

def wordSnocGraph : ZFSet.{u} :=
  ternaryRelationGraph finiteSequences Ordinal.omega0.toZFSet finiteSequences
    (SetWordSnoc Ordinal.omega0.toZFSet)

lemma pair_mem_wordLookupGraph (s : List ℕ) (i v : ℕ) :
    pair (pair (wordGraph s) (natOrdinal i)) (natOrdinal v) ∈ (wordLookupGraph : ZFSet.{u}) ↔
      v = s.getD i 0 := by
  rw [wordLookupGraph, pair_mem_ternaryRelationGraph]
  simp only [mem_finiteSequences.mpr ⟨s, rfl⟩, mem_omegaOrdinal.mpr ⟨i, rfl⟩,
    mem_omegaOrdinal.mpr ⟨v, rfl⟩, true_and]
  exact setWordLookup_iff s i v

lemma pair_mem_wordTakeGraph (s t : List ℕ) (n : ℕ) :
    pair (pair (wordGraph s) (natOrdinal n)) (wordGraph t) ∈ (wordTakeGraph : ZFSet.{u}) ↔
      t = s.take n := by
  rw [wordTakeGraph, pair_mem_ternaryRelationGraph]
  simp only [mem_finiteSequences.mpr ⟨s, rfl⟩, mem_omegaOrdinal.mpr ⟨n, rfl⟩,
    mem_finiteSequences.mpr ⟨t, rfl⟩, true_and]
  exact setWordTake_iff s t n

lemma pair_mem_wordSnocGraph (s t : List ℕ) (a : ℕ) :
    pair (pair (wordGraph s) (natOrdinal a)) (wordGraph t) ∈ (wordSnocGraph : ZFSet.{u}) ↔
      t = s ++ [a] := by
  rw [wordSnocGraph, pair_mem_ternaryRelationGraph]
  simp only [mem_finiteSequences.mpr ⟨s, rfl⟩, mem_omegaOrdinal.mpr ⟨a, rfl⟩,
    mem_finiteSequences.mpr ⟨t, rfl⟩, true_and]
  exact setWordSnoc_iff s t a

/-- The graphs of default-zero lookup, restriction, and one-entry extension belong to the model. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: proposition
  title: Internal finite-word operation graphs
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The bounding products are internal by the product construction. The preceding proposition identifies the
    internally interpreted predicates with the actual operations. Separation collects each whole graph. To encode
    an input-output triple, form the intermediate ordered pair by Pairing; its two coordinates and the output are
    bounded by the displayed factors. This is one graph-collection argument applied to the three predicates.
-/
theorem finiteWordOperationGraphs_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    (wordLookupGraph : ZFSet.{u}) ∈ M ∧ (wordTakeGraph : ZFSet.{u}) ∈ M ∧ (wordSnocGraph : ZFSet.{u}) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let F : M := ⟨finiteSequences, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  let z : M := ⟨natOrdinal 0, hM.mem_trans (mem_omegaOrdinal.mpr ⟨0, rfl⟩) Ω.property⟩
  refine ⟨?_, ?_, ?_⟩
  · apply ternaryRelationGraph_mem hM hpair hunion hpower hsep
      (reindex wordLookupFormula ![0, 1, 3, 4, 5]) Ω z F F Ω Ω
    intro s i v
    rw [realize_reindex]
    have he : ![Ω, z, F, s, i, v] ∘ ![(0 : Fin 6), 1, 3, 4, 5] = ![Ω, z, s, i, v] := by
      funext j; fin_cases j <;> rfl
    rw [he]
    exact realize_wordLookupFormula hM Ω z s i v
  · apply ternaryRelationGraph_mem hM hpair hunion hpower hsep
      (reindex wordTakeFormula ![0, 3, 4, 5]) Ω z F F Ω F
    intro s n t
    rw [realize_reindex]
    have he : ![Ω, z, F, s, n, t] ∘ ![(0 : Fin 6), 3, 4, 5] = ![Ω, s, n, t] := by
      funext j; fin_cases j <;> rfl
    rw [he]
    exact realize_wordTakeFormula hM Ω s n t
  · apply ternaryRelationGraph_mem hM hpair hunion hpower hsep
      (reindex wordSnocFormula ![0, 3, 4, 5]) Ω z F F Ω F
    intro s a t
    rw [realize_reindex]
    have he : ![Ω, z, F, s, a, t] ∘ ![(0 : Fin 6), 3, 4, 5] = ![Ω, s, a, t] := by
      funext j; fin_cases j <;> rfl
    rw [he]
    exact realize_wordSnocFormula hM Ω s a t

end PolishSpaceBook.SetTheoryModels
