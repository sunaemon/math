module

public import PolishSpaceBook.BorelInternalDefects

@[expose] public section

/-! # Internal one-leaf codes for binary cylinders -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
universe u

lemma basic_labelGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ) (n : ℕ) :
    ((basic n).labelGraph : ZFSet.{u}) ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hn (k : ℕ) := hM.mem_trans (mem_omegaOrdinal.mpr ⟨k,rfl⟩) hΩ
  have hW := finiteSequences_mem hM hinf hpair hunion hpower hsep
  let e : M := ⟨_, hM.mem_trans (mem_finiteSequences.mpr ⟨[],rfl⟩) hW⟩
  let z : M := ⟨_, hn 0⟩
  let a : M := ⟨_, hn (n+3)⟩
  let p : BoundedSetPredicate 5 := .disj (.conj (.equal 3 0) (.equal 4 2))
    (.conj (.neg (.equal 3 0)) (.equal 4 1))
  apply bounded_labelGraph_mem hM hinf hpair hunion hpower hsep hrep p ![e,z,a] (basic n)
  intro s y
  change ((wordGraph s = wordGraph [] ∧ y.val = natOrdinal (n+3)) ∨
    (wordGraph s ≠ wordGraph [] ∧ y.val = natOrdinal 0)) ↔ y.val = natOrdinal (basic n s)
  cases s <;> simp [basic, wordGraph_injective.eq_iff]

/-- Use the existing standard list numbering, retaining the original cylinder as the interpretation. -/
def Code.binaryCylinder (s : List Bool) : Code := Code.leaf (NamedLambda.NatListCode.encode (s.map Bool.toNat))

lemma Code.cantor_binaryCylinder (s : List Bool) : (Code.binaryCylinder s).cantor = cyl s := by
  change cantorInclusion ⁻¹' (Code.leaf _).value cylinderBasis = cyl s
  rw [Code.value_leaf]
  simp only [cylinderBasis, NamedLambda.NatListCode.decode_encode, cantorInclusion_preimage_cyl]

lemma Code.binaryCylinder_labelGraph_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (s : List Bool) : ((Code.binaryCylinder s).val.labelGraph : ZFSet.{u}) ∈ M :=
  basic_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _

end PolishSpaceBook.BorelExpression
