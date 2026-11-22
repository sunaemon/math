module

public import PolishSpaceBook.CantorInternalLevels

@[expose] public section

/-! # The full binary word set inside a transitive model -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
universe u

lemma bool_toNat_injective : Function.Injective Bool.toNat := by
  intro a b h; cases a <;> cases b <;> simp_all

lemma exists_binary_word_iff (s : List ℕ) :
    (∃ t : List Bool, t.map Bool.toNat = s) ↔ ∀ a ∈ s, a < 2 := by
  induction s with
  | nil => simp
  | cons a s ih =>
    constructor
    · rintro ⟨t, ht⟩
      cases t with
      | nil => simp at ht
      | cons b t =>
        have htail := (List.cons.inj ht).2
        have hhead := (List.cons.inj ht).1
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨by rw [← hhead]; cases b <;> decide, ih.mp ⟨t, htail⟩⟩
    · intro h
      have ha := h a (by simp)
      obtain ⟨t, ht⟩ := ih.mpr (fun b hb => h b (by simp [hb]))
      have hcases : a = 0 ∨ a = 1 := by omega
      rcases hcases with rfl | rfl
      · exact ⟨false :: t, by simp [ht]⟩
      · exact ⟨true :: t, by simp [ht]⟩

lemma wordGraph_binary_iff (s : List ℕ) :
    IsFunc (natOrdinal s.length) (natOrdinal 2) (wordGraph.{u} s) ↔
      ∃ t : List Bool, t.map Bool.toNat = s := by
  rw [exists_binary_word_iff]
  constructor
  · intro h a ha
    obtain ⟨i, hi⟩ := List.get_of_mem ha
    have hp := mem_wordGraph.mpr ⟨i, rfl⟩
    have hv := (ZFSet.pair_mem_prod.mp (h.1 hp)).2
    rw [hi] at hv
    exact (natOrdinal_mem_natOrdinal a 2).mp hv
  · intro h
    refine ⟨?_, (wordGraph_isFunc s).2⟩
    intro p hp
    obtain ⟨i, rfl⟩ := mem_wordGraph.mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨mem_natOrdinal.mpr ⟨i.val, i.isLt, rfl⟩,
      (natOrdinal_mem_natOrdinal _ 2).mpr (h _ (List.get_mem _ _))⟩

/-- Parameters omega, two, candidate graph; length is a bounded natural witness. -/
def binaryWordPredicate : BoundedSetPredicate 3 := .ex 0 (.function 3 1 2)

lemma eval_binaryWordPredicate (s : List ℕ) :
    binaryWordPredicate.eval ![Ordinal.omega0.toZFSet, natOrdinal 2, wordGraph.{u} s] ↔
      s ∈ binaryLift Set.univ := by
  simp only [binaryWordPredicate, eval]
  change (∃ n ∈ Ordinal.omega0.toZFSet, IsFunc n (natOrdinal 2) (wordGraph s)) ↔ _
  rw [exists_mem_omegaOrdinal]
  constructor
  · rintro ⟨n, hn⟩
    have he := natOrdinal_injective (isFunc_domain_unique hn (wordGraph_isFunc s))
    subst n
    obtain ⟨t, ht⟩ := (wordGraph_binary_iff s).mp hn
    exact ⟨t, Set.mem_univ _, ht⟩
  · rintro ⟨t, _, ht⟩
    exact ⟨s.length, (wordGraph_binary_iff s).mpr ⟨t, ht⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: lemma
  title: Internal binary words
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    From the internal set $F$ of finite natural-number word graphs, separate the graphs satisfying
    $$\exists n\in\omega\;(\sigma:n\to2).$$
    This bounded predicate recognizes exactly the binary words: each value is $0$ or $1$, and conversely every
    binary word has such a graph. Apply the bounded-recognition lemma of §{sec:internal-finite-tests}.
-/
theorem binaryWords_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ) :
    wordTreeSet (binaryLift Set.univ) ∈ M := by
  let Ω : M := ⟨Ordinal.omega0.toZFSet, omegaOrdinal_mem hM hinf (hsep _)⟩
  let two : M := ⟨natOrdinal 2, hM.mem_trans (mem_omegaOrdinal.mpr ⟨2, rfl⟩) Ω.property⟩
  apply binaryWordPredicate.subset_mem hM (hsep _) ![Ω, two]
    (finiteSequences_mem hM hinf hpair hunion hpower hsep)
  · intro x hx
    obtain ⟨s, _, rfl⟩ := mem_wordTreeSet.mp hx
    exact mem_finiteSequences.mpr ⟨s, rfl⟩
  · intro x hx
    obtain ⟨s, rfl⟩ := mem_finiteSequences.mp hx
    have he : Fin.snoc (Subtype.val ∘ ![Ω, two]) (wordGraph s) =
        ![Ordinal.omega0.toZFSet, natOrdinal 2, wordGraph s] := by funext i; fin_cases i <;> rfl
    rw [he, eval_binaryWordPredicate, wordGraph_mem_wordTreeSet]

end PolishSpaceBook.CantorTreeMeasure
