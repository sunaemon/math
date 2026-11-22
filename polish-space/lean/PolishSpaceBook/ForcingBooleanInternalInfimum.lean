module

public import PolishSpaceBook.ForcingBooleanRecursion

@[expose] public section

/-! # Internal infima and the universal Boolean-value clause -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.InternalBooleanAlgebra
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic
universe u

variable {M : ZFSet.{u}} (B : M) [BooleanAlgebra (BooleanElement B.val)]
  (A : InternalBooleanAlgebra B)

def complementImage (S : M) : ZFSet.{u} :=
  B.val.sep (fun b => ∃ a ∈ S.val, pair a b ∈ A.complementCode.val)

lemma complementImage_subset (S : M) : complementImage B A S ⊆ B.val :=
  fun _ h => (mem_sep.mp h).1

lemma complementImage_mem (hM : M.IsTransitive)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (S : M) : complementImage B A S ∈ M := by
  simpa [complementImage, BoundedSetPredicate.eval, Fin.snoc] using
    (BoundedSetPredicate.ex 0 (.pairMember 1 3 2)).separation_mem hM (hsep _)
      ![S, A.complementCode] B.property

lemma mem_complementImage (S : M) (hS : S.val ⊆ B.val) (b : BooleanElement B.val) :
    b.val ∈ complementImage B A S ↔ ∃ a : BooleanElement B.val, a.val ∈ S.val ∧ b = aᶜ := by
  rw [complementImage, mem_sep]
  constructor
  · rintro ⟨_, a, ha, hab⟩
    exact ⟨⟨a, hS ha⟩, ha, (A.complement_iff ⟨a, hS ha⟩ b).mp hab⟩
  · rintro ⟨a, ha, hab⟩
    exact ⟨b.property, a.val, ha, (A.complement_iff a b).mpr hab⟩

variable (hM : M.IsTransitive)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)

def internalInf (S : M) : BooleanElement B.val :=
  (A.internalSup B ⟨complementImage B A S, complementImage_mem B A hM hsep S⟩
    (complementImage_subset B A S))ᶜ

theorem internalInf_isGLB (S : M) (hS : S.val ⊆ B.val) :
    IsGLB {a : BooleanElement B.val | a.val ∈ S.val} (internalInf B A hM hsep S) := by
  have hs := A.internalSup_isLUB B
    ⟨complementImage B A S, complementImage_mem B A hM hsep S⟩ (complementImage_subset B A S)
  constructor
  · intro b hb
    apply compl_le_iff_compl_le.mpr
    exact hs.1 ((mem_complementImage B A S hS bᶜ).mpr ⟨b, hb, rfl⟩)
  · intro b hb
    apply le_compl_comm.mpr
    apply hs.2
    intro a ha
    obtain ⟨c, hc, rfl⟩ := (mem_complementImage B A S hS a).mp ha
    exact compl_le_compl (hb hc)

variable (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

local notation "V" => booleanValue B A hM hinf hpair hunion hpower hsep hrep

/-- The universal value is the internally computed infimum of the actual
witness-value set furnished by Separation. -/
theorem booleanValue_all_internalInf {n : ℕ} (φ : ForcingFormulas.Formula (n + 1))
    (xs : Fin n → Name (positiveSet B) M) :
    V φ.all xs = internalInf B A hM hsep
      ⟨witnessValues B A hM hinf hpair hunion hpower hsep hrep φ xs,
        witnessValues_mem B A hM hinf hpair hunion hpower hsep hrep φ xs⟩ := by
  apply (booleanValue_all_isGLB B A hM hinf hpair hunion hpower hsep hrep φ xs).unique
  have he : {a : BooleanElement B.val | a.val ∈ witnessValues B A hM hinf hpair hunion hpower hsep hrep φ xs} =
      Set.range (fun τ => V φ (Fin.snoc xs τ)) := by
    ext a
    simp only [Set.mem_ofPred_eq, witnessValues, mem_sep, Set.mem_range]
    constructor
    · rintro ⟨_, τ, hτ⟩
      exact ⟨τ, BooleanElement.ext hτ⟩
    · rintro ⟨τ, rfl⟩
      exact ⟨(V φ (Fin.snoc xs τ)).property, τ, rfl⟩
  have hh := internalInf_isGLB B A hM hsep
    ⟨witnessValues B A hM hinf hpair hunion hpower hsep hrep φ xs,
      witnessValues_mem B A hM hinf hpair hunion hpower hsep hrep φ xs⟩
    (witnessValues_subset B A hM hinf hpair hunion hpower hsep hrep φ xs)
  rw [he] at hh
  exact hh

end PolishSpaceBook.SetTheoryModels.InternalBooleanAlgebra
