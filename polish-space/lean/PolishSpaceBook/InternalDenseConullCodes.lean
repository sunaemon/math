module

public import PolishSpaceBook.InternalDenseConullCovers
public import PolishSpaceBook.BorelInternalCodeSelection
public import PolishSpaceBook.BorelInternalDefects

@[expose] public section

/-! # Whole internal code tables and their conull union for a dense set -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet SetTheoryModels ForcingFormulas BorelExpression MeasureTheory
universe u

lemma internalBorelCantorSet_iUnion (M : ZFSet.{u}) (c : ℕ → Code) :
    internalBorelCantorSet M (Code.iUnion c).val (Code.iUnion c).property.2.2.2.2.2 =
      sequenceUnion (fun n => internalBorelCantorSet M (c n).val (c n).property.2.2.2.2.2) := by
  ext g
  by_cases hg : g ∈ internalCantor M
  · obtain ⟨x, rfl, hxM⟩ := mem_internalCantor.mp hg
    simp only [mem_sequenceUnion, cantorPointGraph_mem_internalBorelCantorSet]
    change (cantorPointGraph x ∈ M ∧ x ∈ (Code.iUnion c).cantor) ↔
      ∃ n, cantorPointGraph x ∈ M ∧ x ∈ (c n).cantor
    simp only [hxM, true_and, Code.cantor_iUnion, Set.mem_iUnion]
  · constructor
    · intro h
      exact False.elim (hg (ZFSet.mem_inter.mp h).2)
    · intro h
      rw [mem_sequenceUnion] at h
      obtain ⟨n, hn⟩ := h
      exact False.elim (hg (ZFSet.mem_inter.mp hn).2)

lemma internalBorelCantorSet_compl (M : ZFSet.{u}) (c : Code) :
    internalBorelCantorSet M c.compl.val c.compl.property.2.2.2.2.2 =
      internalCantor M \ internalBorelCantorSet M c.val c.property.2.2.2.2.2 := by
  ext g
  by_cases hg : g ∈ internalCantor M
  · obtain ⟨x, rfl, hxM⟩ := mem_internalCantor.mp hg
    simp only [ZFSet.mem_sdiff, cantorPointGraph_mem_internalBorelCantorSet,
      cantorPointGraph_mem_internalCantor, hxM, true_and]
    change x ∈ c.compl.cantor ↔ x ∉ c.cantor
    rw [Code.cantor_compl, Set.mem_compl_iff]
  · exact iff_of_false (fun h => hg (ZFSet.mem_inter.mp h).2)
      (fun h => hg (ZFSet.mem_sdiff.mp h).1)

/-- The union constructor receives an entire internal label table, not just separate internal codes. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: corollary
  title: Internally coded conull covers
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Apply the selection theorem to the entire sequence supplied by the conull-sequence theorem.
    Its conclusion is exactly the whole-table hypothesis of the union constructor in
    §{sec:internal-random-point-filters}. Membership in the union interpretation is membership in some component
    interpretation, so the displayed identities follow. The complement code also belongs to $M$ and is internally null.
-/
theorem internal_dense_conull_codes {M D R F Δ : ZFSet.{u}}
    (hM : M.IsTransitive) (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (h : FiniteAdditiveCutGraph D R F) (hca : h.CountablyAdditiveOn M)
    (hD : D ∈ M) (hR : R ∈ M) (hF : F ∈ M) (hY : internalCantor M ∈ D)
    (hdom : ∀ A ∈ D, A ⊆ internalCantor M) (hΔ : Δ ∈ M)
    (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)
    (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔
      h.value (A.val \ B.val) = 0)
    (hdense : IsCoinitial {p : InternalRandomCondition D F η | p.val ∈ Δ})
    (hcodes : HasInternalBorelRepresentatives M D) :
    ∃ c : ℕ → Code, sequenceGraph (fun n => (c n).val.labelGraph) ∈ M ∧
      (∀ n, let A := internalBorelCantorSet M (c n).val (c n).property.2.2.2.2.2
            A ∈ D ∧ (A = ∅ ∨ relationClass D (nullRelation D F) A ∈ Δ)) ∧
      (Code.iUnion c).val.labelGraph ∈ M ∧
      internalBorelCantorSet M (Code.iUnion c).val (Code.iUnion c).property.2.2.2.2.2 ∈ D ∧
      h.value (internalCantor M \
        internalBorelCantorSet M (Code.iUnion c).val (Code.iUnion c).property.2.2.2.2.2) = 0 := by
  obtain ⟨V,hV,hVD,hUD,hz⟩ := internal_dense_conull_sequence hM hinf hpair hunion hpower hsep hrep
    hchoice h hca hD hR hF (internalCantor_mem hM hinf hpair hunion hpower hsep) hY hdom hΔ η hle hdense
  obtain ⟨c,hc,hcV⟩ := internal_borel_code_sequence hM hinf hpair hunion hpower hsep hrep hchoice V hV
    (fun n => hcodes ⟨V n, (hVD n).1⟩)
  have hU : internalBorelCantorSet M (Code.iUnion c).val (Code.iUnion c).property.2.2.2.2.2 =
      sequenceUnion V := by
    rw [internalBorelCantorSet_iUnion]
    congr 1
    funext n
    exact hcV n
  refine ⟨c,hc,?_,Code.iUnion_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c hc,
    hU.symm ▸ hUD,?_⟩
  · intro n
    dsimp only
    rw [hcV n]
    exact hVD n
  · rwa [hU]

end PolishSpaceBook.CantorTreeMeasure
