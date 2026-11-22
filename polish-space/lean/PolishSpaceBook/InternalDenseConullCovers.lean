module

public import PolishSpaceBook.InternalDenseRepresentatives
public import PolishSpaceBook.SetTheoryFiniteRowFlattening

@[expose] public section

/-! # Entire internal conull representative sequences for ground-model dense sets -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet SetTheoryModels ForcingFormulas MeasureTheory
universe u

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal conull sequences for dense sets
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    To verify genericity, let $\Delta\in M$ be dense in the internal positive part. Apply the conull-sequence theorem
    of §{sec:internal-random-point-filters} to obtain a whole internal sequence of sets $V_j$, each either empty
    or a representative of a condition in $\Delta$, whose union is internally conull.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Form $E=\{B\in D:q(B)\in\Delta\}$ by the dense representative lemma. It belongs to $M$ and satisfies the
    actual-subset density hypothesis of the finite-cover theorem. That theorem supplies the entire sequence of
    finite graphs $f_n:k_n\to E$ in $M$, with $U_n=\bigcup\GraphRange{f_n}$ and internally conull union.
    Flatten these rows with default value $\emptyset$. The flattening lemma gives the entire graph of $V$ in $M$,
    identifies its nonempty entries as members of $E$, and preserves the union. All the assertions follow.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For an internal forcing argument, §{sec:internal-random-point-filters} constructs finite approximate covers and their
    entire sequence inside the ground model. Their union is conull when the family of representatives is dense.
-/
theorem internal_dense_conull_sequence {M D R F Y Δ : ZFSet.{u}}
    (hM : M.IsTransitive) (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (h : FiniteAdditiveCutGraph D R F) (hca : h.CountablyAdditiveOn M)
    (hD : D ∈ M) (hR : R ∈ M) (hF : F ∈ M) (hYM : Y ∈ M) (hY : Y ∈ D)
    (hdom : ∀ A ∈ D, A ⊆ Y) (hΔ : Δ ∈ M)
    (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)
    (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔
      h.value (A.val \ B.val) = 0)
    (hdense : IsCoinitial {p : InternalRandomCondition D F η | p.val ∈ Δ}) :
    ∃ V : ℕ → ZFSet.{u}, sequenceGraph V ∈ M ∧
      (∀ j, V j ∈ D ∧ (V j = ∅ ∨ relationClass D (nullRelation D F) (V j) ∈ Δ)) ∧
      sequenceUnion V ∈ D ∧ h.value (Y \ sequenceUnion V) = 0 := by
  let E := denseRepresentatives D F Δ
  have hEM : E ∈ M := denseRepresentatives_mem hM hpair hunion hpower hsep hrep h hD hF hΔ
  have hED : ∀ B ∈ E, B ∈ D := fun _ hb => (ZFSet.mem_sep.mp hb).1
  obtain ⟨f, U, _, hfG, _, hu, hUD, hz⟩ := internal_conull_finite_covers
    hM hinf hpair hunion hpower hsep hrep hchoice h hca hD hR hF hEM hYM hY
    hED (fun B hb => hdom B (hED B hb)) (denseRepresentatives_dense h η hle hdense)
  have hf (n : ℕ) : ∃ k : ℕ, IsFunc (natOrdinal k) E (f n) := (hu n).1
  let V := flattenRows E f ∅
  have hVG : sequenceGraph V ∈ M := flattenRows_sequence_mem hM hinf hpair hunion hpower hsep hrep
    hEM f hfG hf ⟨∅, empty_mem_of_infinity hM hinf⟩
  have hVU : sequenceUnion V = sequenceUnion U := by
    rw [show V = flattenRows E f ∅ from rfl, flattenRows_empty_union E f hf]
    congr 1
    funext n
    exact (hu n).2.2.1.symm
  refine ⟨V, hVG, ?_, hVU.symm ▸ hUD, ?_⟩
  · intro j
    rcases (flattenRows_range E f ∅ hf (V j)).mp ⟨j, rfl⟩ with he | ⟨n, hn⟩
    · exact ⟨he.symm ▸ h.empty_mem, Or.inl he⟩
    · obtain ⟨i, hi⟩ := mem_graphRange.mp hn
      obtain ⟨k, hk⟩ := hf n
      have hVE := (ZFSet.pair_mem_prod.mp (hk.1 hi)).2
      exact ⟨hED _ hVE, Or.inr (ZFSet.mem_sep.mp hVE).2⟩
  · rwa [hVU]

end PolishSpaceBook.CantorTreeMeasure
