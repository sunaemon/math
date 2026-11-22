module

public import PolishSpaceBook.CountablyAdditiveCutGraphs

@[expose] public section

/-! # The internal nonnegative-series clause of countable additivity -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate Filter Topology
universe u

/-- Parameters omega, domain, value range, measure graph, family graph, its range, its union,
natural-pair ambient set, proposed sum code. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $A_n\in D$ be pairwise disjoint and suppose $G_A\in M$. The countable-additivity clause consists
    of $U:=\bigcup_n A_n\in D$ and the assertion that the value at $U$ is the sum of the values at $A_n$.
    For a proposed sum code $V$, write this assertion as $V\IncludedIn\omega\times\omega$ and, for every
    $p\in\omega\times\omega$,
    $$\begin{aligned}
    p\in V\quad\longleftrightarrow\quad
    &\exists n\in\omega\;\exists B\in D\;\exists C\in R\\
    &\bigl(B=P_n(A)\land\langle B,C\rangle\in F\land p\in C\bigr).
    \end{aligned}$$
    Here $B=P_n(A)$ abbreviates the bounded membership description in the first proof, together with
    $B\IncludedIn\bigcup_n A_n$. The fixed parameters include $G_A$, its range, and its union.
-/
def countableSumValuePredicate : BoundedSetPredicate 9 :=
  setComprehension 7 8 (.ex 0 (.ex 1 (.ex 2
    (.conj (partialUnionValuePredicate.rename ![4, 5, 6, 10, 11])
      (.conj (.pairMember 3 11 12) (.member 9 12))))))

def countableSumParameters (D R F : ZFSet.{u}) (A : ℕ → ZFSet.{u}) (V : ZFSet.{u}) : Fin 9 → ZFSet.{u} :=
  ![Ordinal.omega0.toZFSet, D, R, F, sequenceGraph A, graphRange (sequenceGraph A), sequenceUnion A,
    prod Ordinal.omega0.toZFSet Ordinal.omega0.toZFSet, V]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let $A_n\in D$ be pairwise disjoint and suppose $G_A\in M$. The countable-additivity clause consists
    of $U:=\bigcup_n A_n\in D$ and the assertion that the value at $U$ is the sum of the values at $A_n$.
    For a proposed sum code $V$, write this assertion as $V\IncludedIn\omega\times\omega$ and, for every
    $p\in\omega\times\omega$,
    $$\begin{aligned}
    p\in V\quad\longleftrightarrow\quad
    &\exists n\in\omega\;\exists B\in D\;\exists C\in R\\
    &\bigl(B=P_n(A)\land\langle B,C\rangle\in F\land p\in C\bigr).
    \end{aligned}$$
    Here $B=P_n(A)$ abbreviates the bounded membership description in the first proof, together with
    $B\IncludedIn\bigcup_n A_n$. The fixed parameters include $G_A$, its range, and its union.
-/
lemma eval_countableSumValuePredicate {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
    (A : ℕ → ZFSet.{u}) (hA : ∀ n, A n ∈ D) (V : ZFSet.{u}) :
    countableSumValuePredicate.eval (countableSumParameters D R F A V) ↔
      V = sequenceUnion (fun n => h.code (partialUnion A n)) := by
  let ps := countableSumParameters D R F A V
  apply eval_setComprehension_iff_eq (7 : Fin 9) 8 _ ps
  · intro x hx
    obtain ⟨n, hn⟩ := (mem_sequenceUnion _ x).mp hx
    obtain ⟨a, b, rfl, _⟩ := (h.code_valid (h.partialUnion_domain A hA n)).typed x hn
    exact ZFSet.pair_mem_prod.mpr ⟨mem_omegaOrdinal.mpr ⟨a, rfl⟩, mem_omegaOrdinal.mpr ⟨b, rfl⟩⟩
  · intro x _
    have he (N B C : ZFSet.{u}) : Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc ps x) N) B) C ∘
        ![(4 : Fin 13), 5, 6, 10, 11] =
        ![sequenceGraph A, graphRange (sequenceGraph A), sequenceUnion A, N, B] := by
      funext i; fin_cases i <;> rfl
    simp only [eval, eval_rename, he]
    change (∃ N ∈ Ordinal.omega0.toZFSet, ∃ B ∈ D, ∃ C ∈ R,
      partialUnionValuePredicate.eval ![sequenceGraph A, graphRange (sequenceGraph A), sequenceUnion A, N, B] ∧
        pair B C ∈ F ∧ x ∈ C) ↔ _
    simp only [exists_mem_omegaOrdinal, eval_partialUnionValuePredicate, mem_sequenceUnion]
    constructor
    · rintro ⟨n, B, hB, C, _, rfl, hp, hx⟩
      exact ⟨n, (h.code_eq hB hp).symm ▸ hx⟩
    · rintro ⟨n, hx⟩
      have hn := h.partialUnion_domain A hA n
      exact ⟨n, partialUnion A n, hn, h.code (partialUnion A n), h.code_mem hn,
        rfl, h.pair_code hn, hx⟩

lemma countableSumParameters_mem {M D R F : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hD : D ∈ M) (hR : R ∈ M) (hF : F ∈ M) (A : ℕ → ZFSet.{u}) (hG : sequenceGraph A ∈ M)
    (V : ZFSet.{u}) (hV : V ∈ M) : ∀ i, countableSumParameters D R F A V i ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  intro i
  fin_cases i
  · exact hΩ
  · exact hD
  · exact hR
  · exact hF
  · exact hG
  · exact graphRange_mem hM hunion (hsep _) hG
  · exact sequenceUnion_mem hM hunion hsep A hG
  · exact prod_mem_of_separation hM hpair hunion hpower (hsep _) hΩ hΩ
  · exact hV

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal interpretation of a nonnegative series
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Apply the shared bounded interpretation theorem to the displayed formula. Extensionality and
    uniqueness of graph values identify $V$ with the union of the partial-union value codes.
    Finite additivity gives $\nu(P_n(A))=\sum_{i<n}\nu(A_i)$. These values increase and are bounded by
    $\nu(U)$ by monotonicity, so the preceding lemma gives the convergence equivalence.
    This interprets each whole internal family; it does not quantify over new external families.
-/
theorem realize_countableSumValuePredicate {M D R F : ZFSet.{u}} (hM : M.IsTransitive)
    (h : FiniteAdditiveCutGraph D R F) (A : ℕ → ZFSet.{u}) (hA : ∀ n, A n ∈ D)
    (V : ZFSet.{u}) (ps : Fin 9 → M) (hp : Subtype.val ∘ ps = countableSumParameters D R F A V) :
    countableSumValuePredicate.compile.Realize Empty.elim ps ↔
      V = sequenceUnion (fun n => h.code (partialUnion A n)) := by
  rw [countableSumValuePredicate.realize_compile hM, hp, eval_countableSumValuePredicate h A hA V]

namespace FiniteAdditiveCutGraph
variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)

/-- The countable-union domain clause and the model's series clause, applied to each entire internal
pairwise disjoint family. The arithmetic inputs, family and measure graph stay fixed in each instance. -/
def ModelsCountableAdditivity (M : ZFSet.{u}) : Prop :=
  ∀ A : ℕ → ZFSet.{u}, sequenceGraph A ∈ M → (∀ n, A n ∈ D) →
    Pairwise (fun i j => Disjoint (A i : Set ZFSet) (A j : Set ZFSet)) →
      sequenceUnion A ∈ D ∧ ∃ ps : Fin 9 → M,
        Subtype.val ∘ ps = countableSumParameters D R F A (h.code (sequenceUnion A)) ∧
        countableSumValuePredicate.compile.Realize Empty.elim ps

theorem countablyAdditiveOn_of_model {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hc : h.ModelsCountableAdditivity M) : h.CountablyAdditiveOn M := by
  intro A hG hA hd
  obtain ⟨hU, ps, hp, hc⟩ := hc A hG hA hd
  exact ⟨hU, (realize_countableSumValuePredicate hM h A hA _ ps hp).mp hc⟩

theorem modelsCountableAdditivity_iff {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hD : D ∈ M) (hR : R ∈ M) (hF : F ∈ M) :
    h.ModelsCountableAdditivity M ↔ h.CountablyAdditiveOn M := by
  refine ⟨h.countablyAdditiveOn_of_model hM, ?_⟩
  intro hc A hG hA hd
  obtain ⟨hU, he⟩ := hc A hG hA hd
  have hV := hM.mem_trans (h.code_mem hU) hR
  let ps (i : Fin 9) : M := ⟨countableSumParameters D R F A (h.code (sequenceUnion A)) i,
    countableSumParameters_mem hM hinf hpair hunion hpower hsep hD hR hF A hG _ hV i⟩
  exact ⟨hU, ps, rfl, (realize_countableSumValuePredicate hM h A hA _ ps rfl).mpr he⟩

/-- On a disjoint family, the code equation is exactly the usual convergence of partial sums. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal interpretation of a nonnegative series
-/
theorem code_union_iff_partial_sums (A : ℕ → ZFSet.{u}) (hA : ∀ n, A n ∈ D)
    (hd : Pairwise (fun i j => Disjoint (A i : Set ZFSet) (A j : Set ZFSet))) (hU : sequenceUnion A ∈ D) :
    h.code (sequenceUnion A) = sequenceUnion (fun n => h.code (partialUnion A n)) ↔
      Tendsto (fun n => ∑ i ∈ Finset.range n, h.value (A i)) atTop (𝓝 (h.value (sequenceUnion A))) := by
  have hm : Monotone (fun n => h.value (partialUnion A n)) := fun m n hmn =>
    h.value_mono (h.partialUnion_domain A hA m) (h.partialUnion_domain A hA n) (partialUnion_mono A hmn)
  have hb : BddAbove (Set.range (fun n => h.value (partialUnion A n))) := by
    refine ⟨h.value (sequenceUnion A), ?_⟩
    rintro _ ⟨n, rfl⟩
    apply h.value_mono (h.partialUnion_domain A hA n) hU
    intro x hx
    obtain ⟨i, _, hi⟩ := (mem_partialUnion A n x).mp hx
    exact (mem_sequenceUnion A x).mpr ⟨i, hi⟩
  constructor
  · intro he
    have ht := tendsto_decode_of_code_union _ _
      (fun n => h.code_valid (h.partialUnion_domain A hA n)) (h.code_valid hU) hm he
    change Tendsto (fun n => h.value (partialUnion A n)) atTop (𝓝 (h.value (sequenceUnion A))) at ht
    simpa only [h.value_partialUnion_sum A hA hd] using ht
  · intro ht
    apply code_union_of_tendsto _ _ (fun n => h.code_valid (h.partialUnion_domain A hA n)) (h.code_valid hU) hm hb
    change Tendsto (fun n => h.value (partialUnion A n)) atTop (𝓝 (h.value (sequenceUnion A)))
    simpa only [h.value_partialUnion_sum A hA hd] using ht

end FiniteAdditiveCutGraph
end PolishSpaceBook.CantorTreeMeasure
