module

public import PolishSpaceBook.SetTheoryInternalFiniteSequences
public import PolishSpaceBook.SetTheoryInternalOrderMinima

@[expose] public section

/-! # Immediate extension of finite words is an internal bounded relation -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- t extends s by one coordinate. -/
def ImmediateWordExtension (t s : ZFSet.{u}) : Prop :=
  ∃ n ∈ Ordinal.omega0.toZFSet, ∃ m ∈ Ordinal.omega0.toZFSet,
    IsFunc n Ordinal.omega0.toZFSet s ∧ IsFunc m Ordinal.omega0.toZFSet t ∧
      m = insert n n ∧ s ⊆ t

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    For word graphs,
    $$J(e(t),e(s))\quad\Longleftrightarrow\quad\exists k\in\omega\;(t=s\concat\langle k\rangle).$$
    To see this, the function-graph clauses determine the two lengths, and inclusion gives a prefix.
    Their lengths differ by exactly one, so the remaining suffix has one entry. The converse follows by
    appending that entry to the graph.
-/
lemma immediateWordExtension_iff {s t : List ℕ} :
    ImmediateWordExtension (wordGraph t) (wordGraph s) ↔ ∃ k, t = s ++ [k] := by
  constructor
  · rintro ⟨n, hn, m, hm, hs, ht, hsucc, hsub⟩
    have hn' := isFunc_domain_unique hs (wordGraph_isFunc s)
    have hm' := isFunc_domain_unique ht (wordGraph_isFunc t)
    rw [hn', hm', ← natOrdinal_succ] at hsucc
    have hlen := natOrdinal_injective hsucc
    obtain ⟨r, hr⟩ := wordGraph_subset_iff.mp hsub
    have hrlen : r.length = 1 := by rw [← hr, List.length_append] at hlen; omega
    obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hrlen
    exact ⟨k, hr.symm⟩
  · rintro ⟨k, rfl⟩
    refine ⟨natOrdinal s.length, mem_omegaOrdinal.mpr ⟨s.length, rfl⟩,
      natOrdinal (s ++ [k]).length, mem_omegaOrdinal.mpr ⟨(s ++ [k]).length, rfl⟩,
      wordGraph_isFunc s, wordGraph_isFunc _, ?_, wordGraph_subset_iff.mpr ⟨[k], rfl⟩⟩
    simpa only [List.length_append, List.length_singleton] using natOrdinal_succ s.length

def immediateWordPredicate {n : ℕ} (Ω t s : Fin n) : BoundedSetPredicate n :=
  .ex Ω (.ex Ω.castSucc
    (.conj (.function (Fin.last n).castSucc Ω.castSucc.castSucc s.castSucc.castSucc)
      (.conj (.function (Fin.last (n + 1)) Ω.castSucc.castSucc t.castSucc.castSucc)
        (.conj (.successor (Fin.last (n + 1)) (Fin.last n).castSucc)
          (.subset s.castSucc.castSucc t.castSucc.castSucc)))))

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: prose
  excerpt: |
    Immediate extension is recognized by the bounded formula
    $$\begin{aligned}
    J(t,s)\;:\equiv\;\exists n,m\in\omega\;[&s:n\to\omega\land t:m\to\omega\\
    &{}\land m=n\cup\{n\}\land s\IncludedIn t].
    \end{aligned}$$
-/
def immediateWordFormula {n : ℕ} (Ω t s : Fin n) : ForcingFormulas.Formula n :=
  (immediateWordPredicate Ω t s).compile

lemma immediateWordFormula_deltaZero {n : ℕ} (Ω t s : Fin n) :
    IsDeltaZero (immediateWordFormula Ω t s) :=
  (immediateWordPredicate Ω t s).compile_deltaZero

lemma eval_immediateWordPredicate {n : ℕ} (Ω t s : Fin n) (xs : Fin n → ZFSet.{u})
    (hΩ : xs Ω = Ordinal.omega0.toZFSet) :
    (immediateWordPredicate Ω t s).eval xs ↔ ImmediateWordExtension (xs t) (xs s) := by
  simp only [immediateWordPredicate, BoundedSetPredicate.eval, Fin.snoc_last,
    Fin.snoc_castSucc, hΩ, ImmediateWordExtension]

/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    Immediate extension is recognized by the bounded formula
    $$\begin{aligned}
    J(t,s)\;:\equiv\;\exists n,m\in\omega\;[&s:n\to\omega\land t:m\to\omega\\
    &{}\land m=n\cup\{n\}\land s\IncludedIn t].
    \end{aligned}$$
-/
lemma realize_immediateWordFormula {M : ZFSet.{u}} (hM : M.IsTransitive)
    {n : ℕ} (Ω t s : Fin n) (xs : Fin n → M) (hΩ : (xs Ω).val = Ordinal.omega0.toZFSet) :
    (immediateWordFormula Ω t s).Realize Empty.elim xs ↔
      ImmediateWordExtension (xs t).val (xs s).val :=
  ((immediateWordPredicate Ω t s).realize_compile hM xs).trans
    (eval_immediateWordPredicate Ω t s (Subtype.val ∘ xs) hΩ)

end PolishSpaceBook.SetTheoryModels
