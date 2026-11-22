module

public import PolishSpaceBook.SetTheoryDefinableChoice
public import PolishSpaceBook.SetTheoryInternalIteration

@[expose] public section

/-! # Countable internal choice with the entire sequence graph preserved -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Reindex an internal function on omega without replacing its graph by an external choice graph. -/
lemma exists_internal_sequence_of_isFunc {M : ZFSet.{u}} (hM : M.IsTransitive)
    (B F : M) (hf : IsFunc Ordinal.omega0.toZFSet B.val F.val) :
    ∃ s : ℕ → M, sequenceGraph (fun n => (s n).val) = F.val := by
  have hex (n : ℕ) : ∃ y : M, pair (natOrdinal n) y.val ∈ F.val := by
    obtain ⟨y, hy, _⟩ := hf.2 _ (mem_omegaOrdinal.mpr ⟨n, rfl⟩)
    exact ⟨⟨y, hM.mem_trans (ZFSet.pair_mem_prod.mp (hf.1 hy)).2 B.property⟩, hy⟩
  choose s hs using hex
  refine ⟨s, ZFSet.ext fun p => ?_⟩
  constructor
  · intro hp
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hp
    exact hs n
  · intro hp
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.mp (hf.1 hp)
    obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp hx
    have he : y = (s n).val := (hf.2 _ (mem_omegaOrdinal.mpr ⟨n, rfl⟩)).unique hp (hs n)
    exact (pair_mem_sequenceGraph _ n y).mpr he

/-- Pointwise internal totality yields a sequence whose entire graph is internal. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Taking $\mathcal D=\omega$ gives a whole internal sequence of witnesses.
-/
theorem internal_countable_choice {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (ψ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence ψ)
    (hrep : ∀ {k : ℕ} (ψ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence ψ)
    (hchoice : M ⊨ choiceSentence) {n : ℕ} (φ : ForcingFormulas.Formula (n + 2))
    (ps : Fin n → M) (Ω : M) (hΩ : Ω.val = Ordinal.omega0.toZFSet)
    (htotal : ∀ k : M, k.val ∈ Ω.val → ∃ y : M,
      φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps k) y)) :
    ∃ s : ℕ → M, sequenceGraph (fun k => (s k).val) ∈ M ∧
      ∀ k : M, ∀ i : ℕ, k.val = natOrdinal i →
        φ.Realize Empty.elim (Fin.snoc (Fin.snoc ps k) (s i)) := by
  obtain ⟨B, F, hf, hφ⟩ := internal_definable_choice hM hinf hpair hunion hpower hsep hrep hchoice
    φ ps Ω htotal
  rw [hΩ] at hf
  obtain ⟨s, hs⟩ := exists_internal_sequence_of_isFunc hM B F hf
  refine ⟨s, hs.symm ▸ F.property, ?_⟩
  intro k i hk
  apply hφ
  rw [hk, ← hs]
  exact (pair_mem_sequenceGraph _ i _).mpr rfl

end PolishSpaceBook.SetTheoryModels
