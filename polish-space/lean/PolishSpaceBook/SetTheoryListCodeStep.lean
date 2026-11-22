module

public import PolishSpaceBook.SetTheoryWordCons
public import PolishSpaceBook.LambdaFiniteLists

@[expose] public section

/-! # An internal monotone step for the book's finite-list numbering -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas NamedLambda
universe u

lemma wordGraph_nil : (wordGraph [] : ZFSet.{u}) = natOrdinal 0 := by
  rw [natOrdinal_zero]
  ext p
  simp [wordGraph]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    $$\begin{aligned}
    \Phi(C):={}&\{\Pair{e([])}{0}\}\\
     &{}\cup\{\Pair{h}{k}\in F\times\omega:\exists a,n,l\in\omega\;\exists g\in F\;[\\
     &\qquad K(a,g,h)\land\Pair{g}{n}\in C\\
     &\qquad{}\land\Pair{\Pair{a}{n}}{l}\in P\land k=l\cup\{l\}]\}.
    \end{aligned}$$
-/
def listCodeStep (Ω F P z C p : ZFSet.{u}) : Prop :=
  p = pair z z ∨ ∃ a ∈ Ω, ∃ s ∈ F, ∃ t ∈ F, ∃ n ∈ Ω, ∃ l ∈ Ω, ∃ k ∈ Ω,
    p = pair t k ∧ SetWordCons Ω z a s t ∧ pair s n ∈ C ∧
      pair (pair a n) l ∈ P ∧ k = insert l l

/-- Parameters omega, finite-word set, pairing graph, zero, candidate, output. -/
def listCodeStepPredicate : BoundedSetPredicate 6 :=
  .disj (.orderedPair 5 3 3)
    (.ex 0 (.ex 1 (.ex 1 (.ex 0 (.ex 0 (.ex 0
      (.conj (.orderedPair 5 8 11)
        (.conj (wordConsPredicate.rename ![0, 3, 6, 7, 8])
          (.conj (.pairMember 4 7 9)
            (.conj (binaryMemberAt 2 6 9 10) (.successor 11 10)))))))))))

def listCodeStepFormula : ForcingFormulas.Formula 6 := listCodeStepPredicate.compile

lemma listCodeStepFormula_deltaZero : IsDeltaZero listCodeStepFormula :=
  listCodeStepPredicate.compile_deltaZero

lemma realize_listCodeStepFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    (Ω F P z C p : M) :
    listCodeStepFormula.Realize Empty.elim ![Ω, F, P, z, C, p] ↔
      listCodeStep Ω.val F.val P.val z.val C.val p.val := by
  simpa [listCodeStepFormula, listCodeStepPredicate, BoundedSetPredicate.eval,
    eval_binaryMemberAt, wordConsPredicate, SetWordCons, listCodeStep,
    Function.comp_def, Fin.snoc, Fin.castPred, Fin.castLT] using
    listCodeStepPredicate.realize_compile hM ![Ω, F, P, z, C, p]

/-- The internal step uses exactly zero and paired-successor list coding. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Here $e([])=0$ as sets. The graph $P$ and the preceding lemma identify the step with adjoining
    $\langle e(a::s),p(a,n)+1\rangle$ whenever $\langle e(s),n\rangle\in C$.
-/
lemma listCodeStep_natural (C p : ZFSet.{u}) :
    listCodeStep Ordinal.omega0.toZFSet finiteSequences (naturalBinaryGraph Nat.pair) (natOrdinal 0) C p ↔
      p = pair (wordGraph []) (natOrdinal 0) ∨
        ∃ a : ℕ, ∃ s : List ℕ, ∃ n : ℕ,
          pair (wordGraph s) (natOrdinal n) ∈ C ∧
            p = pair (wordGraph (a :: s)) (natOrdinal (Nat.pair a n + 1)) := by
  constructor
  · rintro (hp | ⟨a, ha, s, hs, t, ht, n, hn, l, hl, k, hk, hp, hc, hnC, hpair, hsucc⟩)
    · exact Or.inl (by simpa only [wordGraph_nil] using hp)
    · obtain ⟨a, rfl⟩ := mem_omegaOrdinal.mp ha
      obtain ⟨s, rfl⟩ := mem_finiteSequences.mp hs
      obtain ⟨t, rfl⟩ := mem_finiteSequences.mp ht
      obtain ⟨n, rfl⟩ := mem_omegaOrdinal.mp hn
      obtain ⟨l, rfl⟩ := mem_omegaOrdinal.mp hl
      obtain ⟨k, rfl⟩ := mem_omegaOrdinal.mp hk
      have ht' := (setWordCons_wordGraph_iff a s t).mp hc
      subst t
      have hl' := natOrdinal_injective ((pair_mem_naturalBinaryGraph Nat.pair a n _).mp hpair)
      subst l
      rw [← natOrdinal_succ] at hsucc
      have hk' := natOrdinal_injective hsucc
      subst k
      exact Or.inr ⟨a, s, n, hnC, hp⟩
  · rintro (hp | ⟨a, s, n, hnC, hp⟩)
    · exact Or.inl (by simpa only [wordGraph_nil] using hp)
    · have hn (j : ℕ) : natOrdinal j ∈ Ordinal.omega0.toZFSet := mem_omegaOrdinal.mpr ⟨j, rfl⟩
      exact Or.inr ⟨natOrdinal a, hn a, wordGraph s, mem_finiteSequences.mpr ⟨s, rfl⟩,
        wordGraph (a :: s), mem_finiteSequences.mpr ⟨a :: s, rfl⟩, natOrdinal n, hn n,
        natOrdinal (Nat.pair a n), hn _, natOrdinal (Nat.pair a n + 1), hn _, hp,
        (setWordCons_wordGraph_iff a s (a :: s)).mpr rfl, hnC,
        (pair_mem_naturalBinaryGraph Nat.pair a n _).mpr rfl, natOrdinal_succ _⟩

end PolishSpaceBook.SetTheoryModels
