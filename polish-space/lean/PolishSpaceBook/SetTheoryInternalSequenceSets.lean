module

public import PolishSpaceBook.SetTheoryDefinableSequences

@[expose] public section

/-! # Internal unions, finite initial unions, and adjacent differences of whole sequences -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BoundedSetPredicate
universe u

lemma mem_sequenceRange (A : ℕ → ZFSet.{u}) (B : ZFSet.{u}) :
    B ∈ graphRange (sequenceGraph A) ↔ ∃ n, A n = B := by
  rw [mem_graphRange]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨n, hn⟩ := ZFSet.mem_range.mp ha
    exact ⟨n, (ZFSet.pair_inj.mp hn).2⟩
  · rintro ⟨n, rfl⟩
    exact ⟨natOrdinal n, (pair_mem_sequenceGraph A n _).mpr rfl⟩

def sequenceUnion (A : ℕ → ZFSet.{u}) : ZFSet.{u} := sUnion (graphRange (sequenceGraph A))

lemma mem_sequenceUnion (A : ℕ → ZFSet.{u}) (x : ZFSet.{u}) : x ∈ sequenceUnion A ↔ ∃ n, x ∈ A n := by
  simp only [sequenceUnion, ZFSet.mem_sUnion, mem_sequenceRange]
  constructor
  · rintro ⟨B, ⟨n, rfl⟩, hx⟩
    exact ⟨n, hx⟩
  · rintro ⟨n, hx⟩
    exact ⟨A n, ⟨n, rfl⟩, hx⟩

lemma sequence_term_mem {M : ZFSet.{u}} (hM : M.IsTransitive) (hunion : M ⊨ unionSentence)
    (A : ℕ → ZFSet.{u}) (hG : sequenceGraph A ∈ M) (n : ℕ) : A n ∈ M :=
  hM.mem_trans (second_mem_doubleUnion ((pair_mem_sequenceGraph A n _).mpr rfl))
    (union_mem hM hunion (union_mem hM hunion hG))

lemma sequenceUnion_mem {M : ZFSet.{u}} (hM : M.IsTransitive) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (A : ℕ → ZFSet.{u}) (hG : sequenceGraph A ∈ M) : sequenceUnion A ∈ M :=
  union_mem hM hunion (graphRange_mem hM hunion (hsep _) hG)

/-- The union of the first n terms; the empty initial segment gives the empty set. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a sequence $A=\Sequence{A_n}{n\in\omega}$, put
    $$\begin{gathered}
    G_A=\{\langle n,A_n\rangle:n\in\omega\},\qquad
    P_n(A)=\bigcup_{i<n}A_i,\\
    B_n=\SetDifference{A_n}{A_{n+1}},\qquad I=\bigcap_n A_n.
    \end{gathered}$$
-/
def partialUnion (A : ℕ → ZFSet.{u}) (n : ℕ) : ZFSet.{u} :=
  (sequenceUnion A).sep (fun x => ∃ i < n, x ∈ A i)

lemma mem_partialUnion (A : ℕ → ZFSet.{u}) (n : ℕ) (x : ZFSet.{u}) :
    x ∈ partialUnion A n ↔ ∃ i < n, x ∈ A i := by
  rw [partialUnion, ZFSet.mem_sep]
  exact ⟨And.right, fun h => ⟨(mem_sequenceUnion A x).mpr (by obtain ⟨i, _, hi⟩ := h; exact ⟨i, hi⟩), h⟩⟩

/-- Parameters sequence graph, range, index, candidate point. -/
def partialUnionMemberPredicate : BoundedSetPredicate 4 :=
  .ex 2 (.ex 1 (.conj (.pairMember 0 4 5) (.member 3 5)))

lemma eval_partialUnionMemberPredicate (A : ℕ → ZFSet.{u}) (n : ℕ) (x : ZFSet.{u}) :
    partialUnionMemberPredicate.eval ![sequenceGraph A, graphRange (sequenceGraph A), natOrdinal n, x] ↔
      x ∈ partialUnion A n := by
  change (∃ i ∈ natOrdinal n, ∃ B ∈ graphRange (sequenceGraph A), pair i B ∈ sequenceGraph A ∧ x ∈ B) ↔ _
  rw [mem_partialUnion]
  constructor
  · rintro ⟨i, hi, B, _, hp, hx⟩
    obtain ⟨k, hk, rfl⟩ := mem_natOrdinal.mp hi
    have he := (pair_mem_sequenceGraph A k B).mp hp
    exact ⟨k, hk, he ▸ hx⟩
  · rintro ⟨k, hk, hx⟩
    exact ⟨natOrdinal k, mem_natOrdinal.mpr ⟨k, hk, rfl⟩, A k,
      (mem_sequenceRange A _).mpr ⟨k, rfl⟩, (pair_mem_sequenceGraph A k _).mpr rfl, hx⟩

lemma partialUnion_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (A : ℕ → ZFSet.{u}) (hG : sequenceGraph A ∈ M) (n : ℕ) : partialUnion A n ∈ M := by
  let G : M := ⟨_, hG⟩
  let R : M := ⟨_, graphRange_mem hM hunion (hsep _) hG⟩
  let N : M := ⟨natOrdinal n, hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) (omegaOrdinal_mem hM hinf (hsep _))⟩
  apply partialUnionMemberPredicate.subset_mem hM (hsep _) ![G, R, N]
    (B := partialUnion A n) (sequenceUnion_mem hM hunion hsep A hG)
    (by intro x hx; exact (ZFSet.mem_sep.mp hx).1)
  intro x _
  have he : Fin.snoc (Subtype.val ∘ ![G, R, N]) x =
      ![sequenceGraph A, graphRange (sequenceGraph A), natOrdinal n, x] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_partialUnionMemberPredicate]

/-- Parameters sequence graph, range, ambient union, index, candidate output. -/
def partialUnionValuePredicate : BoundedSetPredicate 5 :=
  setComprehension 2 4 (partialUnionMemberPredicate.rename ![0, 1, 3, 5])

lemma eval_partialUnionValuePredicate (A : ℕ → ZFSet.{u}) (n : ℕ) (U : ZFSet.{u}) :
    partialUnionValuePredicate.eval ![sequenceGraph A, graphRange (sequenceGraph A), sequenceUnion A, natOrdinal n, U] ↔
      U = partialUnion A n := by
  let ps : Fin 5 → ZFSet.{u} := ![sequenceGraph A, graphRange (sequenceGraph A), sequenceUnion A, natOrdinal n, U]
  apply eval_setComprehension_iff_eq (2 : Fin 5) 4 _ ps
  · intro x hx
    exact (ZFSet.mem_sep.mp hx).1
  · intro x _
    rw [eval_rename]
    have he : Fin.snoc ps x ∘ ![(0 : Fin 6), 1, 3, 5] =
        ![sequenceGraph A, graphRange (sequenceGraph A), natOrdinal n, x] := by
      funext i; fin_cases i <;> rfl
    rw [he, eval_partialUnionMemberPredicate]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal initial unions and differences
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The range $\GraphRange{G_A}$ and its union belong to $M$ by the graph-range construction and Union.
    Membership in $P_n(A)$ is expressed by
    $$\exists i\in n\;\exists C\in\GraphRange{G_A}\;
      (\langle i,C\rangle\in G_A\land x\in C).$$
    Use the union as the ambient set for Separation. For $B_n$, retrieve $A_n$ and $A_{n+1}$ from $G_A$
    and separate the points of the former that do not belong to the latter. The successor relation and
    these graph lookups have the bounded descriptions already established above. The common interpretation
    and graph-collection lemmas therefore give both entire sequence graphs by Replacement.
    Finally, separate from $A_0$ the points belonging to every member of $\GraphRange{G_A}$ to obtain $I$.
-/
theorem partialUnion_sequence_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (A : ℕ → ZFSet.{u}) (hG : sequenceGraph A ∈ M) : sequenceGraph (partialUnion A) ∈ M := by
  let G : M := ⟨_, hG⟩
  let R : M := ⟨_, graphRange_mem hM hunion (hsep _) hG⟩
  let Y : M := ⟨_, sequenceUnion_mem hM hunion hsep A hG⟩
  let values (n : ℕ) : M := ⟨_, partialUnion_mem hM hinf hunion hsep A hG n⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep partialUnionValuePredicate ![G, R, Y] values
  intro n y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ![G, R, Y]) (natOrdinal n)) y.val =
      ![sequenceGraph A, graphRange (sequenceGraph A), sequenceUnion A, natOrdinal n, y.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_partialUnionValuePredicate]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- Parameters A,B,C; C is the difference A minus B. -/
def setDifferencePredicate : BoundedSetPredicate 3 := setComprehension 0 2 (.neg (.member 3 1))

lemma eval_setDifferencePredicate (A B C : ZFSet.{u}) :
    setDifferencePredicate.eval ![A, B, C] ↔ C = A \ B := by
  apply eval_setComprehension_iff_eq (0 : Fin 3) 2 _ ![A, B, C]
  · exact fun _ hx => (ZFSet.mem_sdiff.mp hx).1
  · intro x hx
    change x ∈ A at hx
    change (x ∉ B) ↔ x ∈ A \ B
    simp only [ZFSet.mem_sdiff, hx, true_and]

lemma difference_mem_of_separation {M A B : ZFSet.{u}} (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hA : A ∈ M) (hB : B ∈ M) : A \ B ∈ M :=
  (BoundedSetPredicate.neg (.member (1 : Fin 2) 0)).separation_mem hM (hsep _) ![⟨B, hB⟩] hA

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a sequence $A=\Sequence{A_n}{n\in\omega}$, put
    $$\begin{gathered}
    G_A=\{\langle n,A_n\rangle:n\in\omega\},\qquad
    P_n(A)=\bigcup_{i<n}A_i,\\
    B_n=\SetDifference{A_n}{A_{n+1}},\qquad I=\bigcap_n A_n.
    \end{gathered}$$
-/
def adjacentDifference (A : ℕ → ZFSet.{u}) (n : ℕ) : ZFSet.{u} := A n \ A (n + 1)

/-- Parameters omega, sequence graph, range, index, output. -/
def adjacentDifferencePredicate : BoundedSetPredicate 5 :=
  .ex 0 (.ex 2 (.ex 2 (.conj (.successor 5 3) (.conj (.pairMember 1 3 6)
    (.conj (.pairMember 1 5 7) (setDifferencePredicate.rename ![6, 7, 4]))))))

lemma eval_adjacentDifferencePredicate (A : ℕ → ZFSet.{u}) (n : ℕ) (C : ZFSet.{u}) :
    adjacentDifferencePredicate.eval ![Ordinal.omega0.toZFSet, sequenceGraph A,
      graphRange (sequenceGraph A), natOrdinal n, C] ↔ C = adjacentDifference A n := by
  let ps : Fin 5 → ZFSet.{u} := ![Ordinal.omega0.toZFSet, sequenceGraph A, graphRange (sequenceGraph A), natOrdinal n, C]
  have he (s B E : ZFSet.{u}) : Fin.snoc (Fin.snoc (Fin.snoc ps s) B) E ∘ ![(6 : Fin 8), 7, 4] = ![B, E, C] := by
    funext i; fin_cases i <;> rfl
  change adjacentDifferencePredicate.eval ps ↔ _
  simp only [adjacentDifferencePredicate, eval, eval_rename, he, eval_setDifferencePredicate]
  change (∃ s ∈ Ordinal.omega0.toZFSet, ∃ B ∈ graphRange (sequenceGraph A),
    ∃ E ∈ graphRange (sequenceGraph A), s = insert (natOrdinal n) (natOrdinal n) ∧
      pair (natOrdinal n) B ∈ sequenceGraph A ∧ pair s E ∈ sequenceGraph A ∧ C = B \ E) ↔ _
  rw [← natOrdinal_succ]
  simp only [pair_mem_sequenceGraph]
  constructor
  · rintro ⟨s, _, B, _, E, _, rfl, rfl, hp, hc⟩
    have he := (pair_mem_sequenceGraph A (n + 1) E).mp hp
    simpa only [adjacentDifference, he] using hc
  · intro hc
    exact ⟨natOrdinal (n + 1), mem_omegaOrdinal.mpr ⟨n + 1, rfl⟩,
      A n, (mem_sequenceRange A _).mpr ⟨n, rfl⟩,
      A (n + 1), (mem_sequenceRange A _).mpr ⟨n + 1, rfl⟩,
      rfl, rfl, (pair_mem_sequenceGraph A (n + 1) _).mpr rfl, hc⟩

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal initial unions and differences
-/
theorem adjacentDifference_sequence_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (A : ℕ → ZFSet.{u}) (hG : sequenceGraph A ∈ M) : sequenceGraph (adjacentDifference A) ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  let G : M := ⟨_, hG⟩
  let R : M := ⟨_, graphRange_mem hM hunion (hsep _) hG⟩
  let values (n : ℕ) : M := ⟨_, difference_mem_of_separation hM hsep
    (sequence_term_mem hM hunion A hG n) (sequence_term_mem hM hunion A hG (n + 1))⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep adjacentDifferencePredicate ![Ω, G, R] values
  intro n y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ![Ω, G, R]) (natOrdinal n)) y.val =
      ![Ordinal.omega0.toZFSet, sequenceGraph A, graphRange (sequenceGraph A), natOrdinal n, y.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_adjacentDifferencePredicate]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end PolishSpaceBook.SetTheoryModels
