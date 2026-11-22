module

public import PolishSpaceBook.SetTheoryPredicateComposition
public import PolishSpaceBook.SetTheoryWordCons

@[expose] public section

/-! # Internal powers of two from iteration of doubling -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BoundedSetPredicate
universe u

def doublingPairPredicate : BoundedSetPredicate 3 :=
  .ex 0 (.ex 0 (.conj (.orderedPair 2 3 4) (binaryMemberAt 1 3 3 4)))

lemma eval_doublingPairPredicate (p : ZFSet.{u}) :
    doublingPairPredicate.eval ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun a b => a + b), p] ↔
      p ∈ sequenceGraph (fun n => natOrdinal (n + n)) := by
  simp [doublingPairPredicate, eval, eval_binaryMemberAt, Fin.snoc, Fin.castPred, Fin.castLT, exists_mem_omegaOrdinal,
    pair_mem_naturalBinaryGraph, natOrdinal_injective.eq_iff, sequenceGraph, ZFSet.mem_range, eq_comm]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    Use the internal addition graph to separate the graph of $j\mapsto j+j$ from $\omega\times\omega$.
-/
theorem naturalDoublingGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    sequenceGraph (fun n => natOrdinal (n + n)) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let A : M := ⟨naturalBinaryGraph (fun a b => a + b), naturalAdditionGraph_mem hM hinf hpair hunion hpower hsep⟩
  let ps : Fin 2 → M := ![Ω, A]
  apply doublingPairPredicate.subset_mem hM (hsep _) ps
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property Ω.property)
    (sequenceGraph_isFunc _ (fun n => mem_omegaOrdinal.mpr ⟨n + n, rfl⟩)).1
  intro p _
  have he : Fin.snoc (Subtype.val ∘ ps) p =
      ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun a b => a + b), p] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_doublingPairPredicate]

/-- The entire exponentiation sequence is obtained by the existing internal-iteration theorem. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: lemma
  title: Internal powers of two
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    Apply internal numerical iteration from §{sec:internal-natural-arithmetic}, starting at $1$.
    Induction identifies the $n$th value with $2^n$, including $2^0=1$.
-/
theorem naturalTwoPowerGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    sequenceGraph (fun n => natOrdinal (2 ^ n)) ∈ M := by
  let d : M := ⟨sequenceGraph (fun n => natOrdinal (n + n)),
    naturalDoublingGraph_mem hM hinf hpair hunion hpower hsep⟩
  have hg := numericIterationGraph_mem hM hinf hpair hunion hpower hsep d (fun n => n + n)
    (sequenceGraph_isFunc _ (fun n => mem_omegaOrdinal.mpr ⟨n + n, rfl⟩))
    (fun n => (pair_mem_sequenceGraph _ n _).mpr rfl) 1
  have hi (n : ℕ) : (fun k : ℕ => k + k)^[n] 1 = 2 ^ n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, pow_succ, Nat.mul_two]
  simpa only [hi] using hg

end PolishSpaceBook.SetTheoryModels
