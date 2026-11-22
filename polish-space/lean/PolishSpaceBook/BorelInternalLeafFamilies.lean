module

public import PolishSpaceBook.BorelInternalCylinderCodes
public import PolishSpaceBook.BorelGraphValidity

@[expose] public section

/-! # Entire internal families of leaf codes

Internality of each leaf separately does not collect a sequence of leaves. A
single bounded description of a leaf's label graph supplies that missing step.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

/-- Parameters omega, finite words, empty word, zero, addition graph, three,
leaf index, and candidate label graph. -/
def leafGraphPredicate : BoundedSetPredicate 8 :=
  .ex 0 (.conj (binaryMemberAt 4 6 5 8)
    (.conj (.function 1 0 7)
      (.all 1 (.all 0 (.iff (.pairMember 7 9 10)
        (.disj (.conj (.equal 9 2) (.equal 10 8))
          (.conj (.neg (.equal 9 2)) (.equal 10 3))))))))

lemma eval_leafGraphPredicate (n : ℕ) (L : ZFSet.{u}) :
    leafGraphPredicate.eval ![Ordinal.omega0.toZFSet, finiteSequences, wordGraph [], natOrdinal 0,
      naturalBinaryGraph (fun a b => a + b), natOrdinal 3, natOrdinal n, L] ↔
      L = (basic n).labelGraph := by
  simp only [leafGraphPredicate, eval, eval_binaryMemberAt, Fin.snoc]
  change (∃ a ∈ Ordinal.omega0.toZFSet,
    pair (pair (natOrdinal n) (natOrdinal 3)) a ∈ naturalBinaryGraph (fun a b => a + b) ∧
    IsFunc finiteSequences Ordinal.omega0.toZFSet L ∧
    ∀ s ∈ finiteSequences, ∀ y ∈ Ordinal.omega0.toZFSet,
      (pair s y ∈ L ↔ (s = wordGraph [] ∧ y = a) ∨
        (s ≠ wordGraph [] ∧ y = natOrdinal 0))) ↔ _
  simp only [pair_mem_naturalBinaryGraph]
  constructor
  · rintro ⟨_, _, rfl, hf, hv⟩
    obtain ⟨c, rfl⟩ := exists_labelGraph_of_isFunc hf
    apply congrArg labelGraph
    funext s
    have h := (hv (wordGraph s) (mem_finiteSequences.mpr ⟨s, rfl⟩)
      (natOrdinal (c s)) (mem_omegaOrdinal.mpr ⟨c s, rfl⟩)).mp
        ((pair_mem_labelGraph c s _).mpr rfl)
    cases s <;> simpa [basic, wordGraph_injective.eq_iff, natOrdinal_injective.eq_iff] using h
  · rintro rfl
    refine ⟨natOrdinal (n + 3), mem_omegaOrdinal.mpr ⟨n + 3, rfl⟩, rfl, labelGraph_isFunc _, ?_⟩
    intro s hs y _
    obtain ⟨s, rfl⟩ := mem_finiteSequences.mp hs
    rw [pair_mem_labelGraph]
    cases s <;> simp [basic, wordGraph_injective.eq_iff]

/-- The input sequence supplies the leaf index before applying the shared graph description. -/
def leafSequencePredicate : BoundedSetPredicate 9 :=
  .ex 0 (.conj (.pairMember 6 7 9)
    (leafGraphPredicate.rename ![0, 1, 2, 3, 4, 5, 9, 8]))

lemma eval_leafSequencePredicate (f : ℕ → ℕ) (n : ℕ) (L : ZFSet.{u}) :
    leafSequencePredicate.eval ![Ordinal.omega0.toZFSet, finiteSequences, wordGraph [], natOrdinal 0,
      naturalBinaryGraph (fun a b => a + b), natOrdinal 3, pointGraph f, natOrdinal n, L] ↔
      L = (basic (f n)).labelGraph := by
  change (∃ a ∈ Ordinal.omega0.toZFSet, pair (natOrdinal n) a ∈ pointGraph f ∧
    leafGraphPredicate.eval ![Ordinal.omega0.toZFSet, finiteSequences, wordGraph [], natOrdinal 0,
      naturalBinaryGraph (fun a b => a + b), natOrdinal 3, a, L]) ↔ _
  rw [exists_mem_omegaOrdinal]
  simp only [pair_mem_pointGraph, eval_leafGraphPredicate]
  constructor
  · rintro ⟨m, hm, hL⟩
    rwa [← hm] at hL
  · intro h
    exact ⟨f n, rfl, h⟩

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hinf hpair hunion hpower hsep hrep

/-- Replacement collects the whole table from the internal index sequence. -/
theorem leafFamily_labelGraphs_mem (f : ℕ → ℕ) (hf : pointGraph f ∈ M) :
    sequenceGraph (fun n => (Code.leaf (f n)).val.labelGraph) ∈ M := by
  let Ω : M := ⟨_, omegaOrdinal_mem hM hinf (hsep _)⟩
  have hn (n : ℕ) : natOrdinal n ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) Ω.property
  let W : M := ⟨_, finiteSequences_mem hM hinf hpair hunion hpower hsep⟩
  let e : M := ⟨_, hM.mem_trans (mem_finiteSequences.mpr ⟨[], rfl⟩) W.property⟩
  let ps : Fin 7 → M := ![Ω, W, e, ⟨_, hn 0⟩,
    ⟨_, naturalAdditionGraph_mem hM hinf hpair hunion hpower hsep⟩, ⟨_, hn 3⟩, ⟨_, hf⟩]
  let values (n : ℕ) : M :=
    ⟨_, basic_labelGraph_mem hM hinf hpair hunion hpower hsep hrep (f n)⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep leafSequencePredicate ps values
  intro n y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ps) (natOrdinal n)) y.val =
      ![Ordinal.omega0.toZFSet, finiteSequences, wordGraph [], natOrdinal 0,
        naturalBinaryGraph (fun a b => a + b), natOrdinal 3, pointGraph f, natOrdinal n, y.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_leafSequencePredicate]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end PolishSpaceBook.BorelExpression
