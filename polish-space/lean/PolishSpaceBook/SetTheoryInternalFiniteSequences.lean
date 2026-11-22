module

public import PolishSpaceBook.SetTheoryPredicateReflection

@[expose] public section

/-! # The full finite-word set belongs to a transitive model -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

def finiteSequencePredicate {n : ℕ} (Ω f : Fin n) : BoundedSetPredicate n :=
  .ex Ω (.function (Fin.last n) Ω.castSucc f.castSucc)

def finiteSequenceFormula {n : ℕ} (Ω f : Fin n) : ForcingFormulas.Formula n :=
  (finiteSequencePredicate Ω f).compile

lemma finiteSequenceFormula_deltaZero {n : ℕ} (Ω f : Fin n) :
    IsDeltaZero (finiteSequenceFormula Ω f) :=
  (finiteSequencePredicate Ω f).compile_deltaZero

lemma realize_finiteSequenceFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (Ω f : Fin n) (xs : Fin n → M) :
    (finiteSequenceFormula Ω f).Realize Empty.elim xs ↔
      ∃ k ∈ (xs Ω).val, IsFunc k (xs Ω).val (xs f).val := by
  rw [finiteSequenceFormula, BoundedSetPredicate.realize_compile hM]
  simp only [finiteSequencePredicate, BoundedSetPredicate.eval, Fin.snoc_last,
    Fin.snoc_castSucc, Function.comp_apply]

/-- Separate finite function graphs from the internal power set of ω × ω. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: lemma
  title: Internal finite-word set
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The product and internal power-set constructions give
    $$P:=\PowerSet{\omega\times\omega}\cap M\in M.$$
    Apply Separation to the bounded function-graph predicate to obtain
    $$T':=\{f\in P:\exists n\in\omega\;(f:n\to\omega)\}\in M.$$
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Each word graph belongs to $P$ by the preceding lemma and satisfies the displayed predicate.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Thus $T'=T$. In particular, this construction retains every external finite word; it does not require
    $M$ to contain every external subset of $\omega\times\omega$.
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Keep the axioms of §{sec:internal-natural-arithmetic}, and let $F\in M$ be the set of all finite natural-number
    function graphs constructed in §{sec:internal-borel-inputs}. For a finite word $s$, write $e(s)\in F$ for its graph.
-/
theorem finiteSequences_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    finiteSequences ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let B := internalPowerSet M (ZFSet.prod Ω.val Ω.val)
  have hB : B ∈ M := internalPowerSet_mem hM hpower
    (prod_mem_of_separation hM hpair hunion hpower (hsep _) Ω.property Ω.property)
  have hS := separation_mem_of_absolute hM (finiteSequenceFormula (0 : Fin 2) 1) (hsep _)
    ![Ω] hB (fun f => ∃ n ∈ Ω.val, IsFunc n Ω.val f) (by
      intro f _
      exact realize_finiteSequenceFormula hM 0 1 (Fin.snoc ![Ω] f))
  have he : B.sep (fun f => ∃ n ∈ Ω.val, IsFunc n Ω.val f) = finiteSequences := by
    apply ZFSet.ext
    intro f
    rw [ZFSet.mem_sep, finiteSequences, ZFSet.mem_sep, ZFSet.mem_powerset]
    constructor
    · rintro ⟨hfB, hf⟩
      exact ⟨(ZFSet.mem_sep.mp hfB).2, hf⟩
    · rintro ⟨hfsub, n, hn, hf⟩
      refine ⟨ZFSet.mem_sep.mpr ⟨?_, hfsub⟩, n, hn, hf⟩
      obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp hn
      exact finite_function_mem hM hinf hpair hunion Ω.property hf
  exact he ▸ hS

end PolishSpaceBook.SetTheoryModels
