module

public import PolishSpaceBook.ForcingBooleanAtomic
public import PolishSpaceBook.ForcingBooleanInternalInfimum

@[expose] public section

/-! # Internal sets of atomic coefficients

Separation on the Boolean carrier collects the actual label/value meets. Its
defining formula uses positive principal ideals, so no external collection of
names or values is passed to the internal completeness axiom.
-/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.InternalBooleanAlgebra
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames
universe u

/-- Parameters are base name, containing name, P, order code, candidate value.
The two bound witnesses are an actual child and its positive label. -/
def coefficientFormula (φ : ForcingFormulas.Formula 2) : ForcingFormulas.Formula 5 :=
  (boundedExists (2 : Fin 6)
    (pairMemberFormula (1 : Fin 7) 5 6 ⊓ boundedAll 2
      ((pairMemberFormula (3 : Fin 8) 7 4).iff
        (pairMemberFormula 3 7 6 ⊓ reindex (forcingTranslation φ) ![0, 5, 2, 3, 7])))).ex

variable {M : ZFSet.{u}} (B : M) [BooleanAlgebra (BooleanElement B.val)]
  (A : InternalBooleanAlgebra B)
  (hM : M.IsTransitive) (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

local notation "V" => booleanValue B A hM hinf hpair hunion hpower hsep hrep
local notation "force_le" => force_iff_le_booleanValue B A hM hinf hpair hunion hpower hsep hrep

def coefficients (φ : ForcingFormulas.Formula 2) (σ τ : Name (positiveSet B) M) : ZFSet.{u} :=
  B.val.sep (fun b => ∃ c : LabelledChild B τ, (element B c.val.2 ⊓ V φ ![σ, c.val.1]).val = b)

lemma coefficients_subset (φ : ForcingFormulas.Formula 2) (σ τ : Name (positiveSet B) M) :
    coefficients B A hM hinf hpair hunion hpower hsep hrep φ σ τ ⊆ B.val :=
  fun _ h => (mem_sep.mp h).1

theorem coefficients_definable (φ : ForcingFormulas.Formula 2)
    (σ τ : Name (positiveSet B) M) (b : BooleanElement B.val) :
    (coefficientFormula φ).Realize Empty.elim
      ![nameInModel σ, nameInModel τ, positiveInModel B hM hsep, A.orderCode, elementInModel B hM b] ↔
      ∃ c : LabelledChild B τ, (element B c.val.2 ⊓ V φ ![σ, c.val.1]).val = b.val := by
  simp only [coefficientFormula, BoundedFormula.realize_ex, realize_boundedExists_model,
    BoundedFormula.realize_inf, realize_boundedAll_model, BoundedFormula.realize_iff,
    realize_pairMemberFormula_model hM, realize_reindex]
  have he (π r q : M) :
      (Fin.snoc (Fin.snoc (Fin.snoc
        ![nameInModel σ, nameInModel τ, positiveInModel B hM hsep, A.orderCode, elementInModel B hM b]
        π) r) q ∘ ![(0 : Fin 8), 5, 2, 3, 7]) =
      forcingAssignment ![nameInModel σ, π] (positiveInModel B hM hsep) A.orderCode q := by
    funext i
    fin_cases i <;> rfl
  simp only [he]
  change (∃ π : M, ∃ r : M, r.val ∈ positiveSet B ∧ pair π.val r.val ∈ τ.val ∧
    ∀ q : M, q.val ∈ positiveSet B →
      (pair q.val b.val ∈ A.orderCode.val ↔ pair q.val r.val ∈ A.orderCode.val ∧
        (forcingTranslation φ).Realize Empty.elim
          (forcingAssignment ![nameInModel σ, π] (positiveInModel B hM hsep) A.orderCode q))) ↔ _
  constructor
  · rintro ⟨π, r, hr, hπ, hv⟩
    let rP : Condition (positiveSet B) := ⟨r.val, hr⟩
    let c := child B hM τ π.val rP hπ
    refine ⟨c, congrArg BooleanElement.val ?_⟩
    apply eq_of_positive_le_iff B
    intro p
    have hpM := hM.mem_trans p.property (positiveSet_mem B hM hsep)
    have hh := hv ⟨p.val, hpM⟩ p.property
    have hf := forcing_definable hM hinf hpair hunion hpower hsep hrep
      (positiveInModel B hM hsep) A.orderCode (A.positive_order_iff B) φ ![σ, c.val.1] p
    have hn : (fun i => nameInModel (![σ, c.val.1] i)) = ![nameInModel σ, π] := by
      funext i; fin_cases i <;> rfl
    rw [hn] at hf
    rw [le_inf_iff]
    exact ((and_congr (A.order_iff (element B p) (element B rP)).symm
      (hf.trans (force_le φ ![σ, c.val.1] p)).symm).trans hh.symm).trans
      (A.order_iff (element B p) b)
  · rintro ⟨c, hc⟩
    have hbc : b = element B c.val.2 ⊓ V φ ![σ, c.val.1] := BooleanElement.ext hc.symm
    refine ⟨nameInModel c.val.1,
      ⟨c.val.2.val, hM.mem_trans c.val.2.property (positiveSet_mem B hM hsep)⟩,
      c.val.2.property, c.property, ?_⟩
    intro q hq
    let qP : Condition (positiveSet B) := ⟨q.val, hq⟩
    have hf := forcing_definable hM hinf hpair hunion hpower hsep hrep
      (positiveInModel B hM hsep) A.orderCode (A.positive_order_iff B) φ ![σ, c.val.1] qP
    have hn : (fun i => nameInModel (![σ, c.val.1] i)) = ![nameInModel σ, nameInModel c.val.1] := by
      funext i; fin_cases i <;> rfl
    rw [hn] at hf
    have hi : element B qP ≤ b ↔ element B qP ≤ element B c.val.2 ∧ element B qP ≤ V φ ![σ, c.val.1] := by
      rw [hbc, le_inf_iff]
    exact (A.order_iff (element B qP) b).trans (hi.trans
      (and_congr (A.order_iff (element B qP) (element B c.val.2)).symm
        (hf.trans (force_le φ ![σ, c.val.1] qP)).symm))

theorem coefficients_mem (φ : ForcingFormulas.Formula 2) (σ τ : Name (positiveSet B) M) :
    coefficients B A hM hinf hpair hunion hpower hsep hrep φ σ τ ∈ M := by
  apply separation_mem_of_absolute hM (coefficientFormula φ) (hsep _)
    ![nameInModel σ, nameInModel τ, positiveInModel B hM hsep, A.orderCode] B.property
  intro b hb
  have he : Fin.snoc ![nameInModel σ, nameInModel τ, positiveInModel B hM hsep, A.orderCode] b =
      ![nameInModel σ, nameInModel τ, positiveInModel B hM hsep, A.orderCode, elementInModel B hM ⟨b.val, hb⟩] := by
    funext i; fin_cases i <;> rfl
  rw [he]
  exact coefficients_definable B A hM hinf hpair hunion hpower hsep hrep φ σ τ ⟨b.val, hb⟩

lemma coefficients_carrier (φ : ForcingFormulas.Formula 2) (σ τ : Name (positiveSet B) M) :
    {b : BooleanElement B.val | b.val ∈ coefficients B A hM hinf hpair hunion hpower hsep hrep φ σ τ} =
      Set.range (fun c : LabelledChild B τ => element B c.val.2 ⊓ V φ ![σ, c.val.1]) := by
  ext b
  simp only [Set.mem_ofPred_eq, coefficients, mem_sep, Set.mem_range]
  constructor
  · rintro ⟨_, c, hc⟩
    exact ⟨c, BooleanElement.ext hc⟩
  · rintro ⟨c, rfl⟩
    exact ⟨(element B c.val.2 ⊓ V φ ![σ, c.val.1]).property, c, rfl⟩

theorem membershipValue_internalSup (σ τ : Name (positiveSet B) M) :
    membershipValue B A hM hinf hpair hunion hpower hsep hrep σ τ = A.internalSup B
      ⟨coefficients B A hM hinf hpair hunion hpower hsep hrep (equalAt 0 1) σ τ,
        coefficients_mem B A hM hinf hpair hunion hpower hsep hrep (equalAt 0 1) σ τ⟩
      (coefficients_subset B A hM hinf hpair hunion hpower hsep hrep (equalAt 0 1) σ τ) := by
  apply (membershipValue_isLUB B A hM hinf hpair hunion hpower hsep hrep σ τ).unique
  have hh := A.internalSup_isLUB B
    ⟨coefficients B A hM hinf hpair hunion hpower hsep hrep (equalAt 0 1) σ τ,
      coefficients_mem B A hM hinf hpair hunion hpower hsep hrep (equalAt 0 1) σ τ⟩
    (coefficients_subset B A hM hinf hpair hunion hpower hsep hrep (equalAt 0 1) σ τ)
  rw [coefficients_carrier] at hh
  exact hh

local notation "MV" => membershipValue B A hM hinf hpair hunion hpower hsep hrep

lemma swapped_membershipValue (σ τ : Name (positiveSet B) M) :
    V (memberAt 1 0) ![σ, τ] = MV τ σ := by
  apply eq_of_positive_le_iff B
  intro p
  rw [← force_le, ← atomic_membership_iff_le]
  simp [memberAt, force, termName, variableAt]

/-- The implication coefficients are complements of the corresponding
label meets negated membership values, so their image is also internal. -/
def equalityHalfCoefficients (σ τ : Name (positiveSet B) M) : ZFSet.{u} :=
  complementImage B A
    ⟨coefficients B A hM hinf hpair hunion hpower hsep hrep (memberAt 1 0).not τ σ,
      coefficients_mem B A hM hinf hpair hunion hpower hsep hrep (memberAt 1 0).not τ σ⟩

theorem equalityHalfCoefficients_mem (σ τ : Name (positiveSet B) M) :
    equalityHalfCoefficients B A hM hinf hpair hunion hpower hsep hrep σ τ ∈ M :=
  complementImage_mem B A hM hsep _

lemma equalityHalfCoefficients_carrier (σ τ : Name (positiveSet B) M) :
    {b : BooleanElement B.val | b.val ∈ equalityHalfCoefficients B A hM hinf hpair hunion hpower hsep hrep σ τ} =
      Set.range (fun c : LabelledChild B σ => element B c.val.2 ⇨ MV c.val.1 τ) := by
  ext b
  change b.val ∈ complementImage B A _ ↔ _
  rw [mem_complementImage B A _
    (coefficients_subset B A hM hinf hpair hunion hpower hsep hrep (memberAt 1 0).not τ σ)]
  have hv (c : LabelledChild B σ) :
      (element B c.val.2 ⊓ V (memberAt 1 0).not ![τ, c.val.1])ᶜ = element B c.val.2 ⇨ MV c.val.1 τ := by
    rw [booleanValue_not, swapped_membershipValue, compl_inf, compl_compl, himp_eq, sup_comm]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hr := coefficients_carrier B A hM hinf hpair hunion hpower hsep hrep (memberAt 1 0).not τ σ
    have ha' : a ∈ Set.range (fun c : LabelledChild B σ => element B c.val.2 ⊓ V (memberAt 1 0).not ![τ, c.val.1]) := by
      rw [← hr]; exact ha
    obtain ⟨c, rfl⟩ := ha'
    exact ⟨c, (hv c).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨element B c.val.2 ⊓ V (memberAt 1 0).not ![τ, c.val.1], ?_, (hv c).symm⟩
    change (element B c.val.2 ⊓ V (memberAt 1 0).not ![τ, c.val.1]).val ∈
      coefficients B A hM hinf hpair hunion hpower hsep hrep (memberAt 1 0).not τ σ
    rw [coefficients, mem_sep]
    exact ⟨(element B c.val.2 ⊓ V (memberAt 1 0).not ![τ, c.val.1]).property, c, rfl⟩

def equalityCoefficients (σ τ : Name (positiveSet B) M) : ZFSet.{u} :=
  ZFSet.sUnion {equalityHalfCoefficients B A hM hinf hpair hunion hpower hsep hrep σ τ,
    equalityHalfCoefficients B A hM hinf hpair hunion hpower hsep hrep τ σ}

theorem equalityCoefficients_mem (σ τ : Name (positiveSet B) M) :
    equalityCoefficients B A hM hinf hpair hunion hpower hsep hrep σ τ ∈ M :=
  union_mem hM hunion (unorderedPair_mem hM hpair
    (equalityHalfCoefficients_mem B A hM hinf hpair hunion hpower hsep hrep σ τ)
    (equalityHalfCoefficients_mem B A hM hinf hpair hunion hpower hsep hrep τ σ))

lemma equalityCoefficients_subset (σ τ : Name (positiveSet B) M) :
    equalityCoefficients B A hM hinf hpair hunion hpower hsep hrep σ τ ⊆ B.val := by
  intro x hx
  obtain ⟨S, hS, hxS⟩ := mem_sUnion.mp hx
  simp only [mem_insert_iff, mem_singleton] at hS
  rcases hS with rfl | rfl <;>
    simp only [equalityHalfCoefficients, complementImage, mem_sep] at hxS <;> exact hxS.1

theorem equalityValue_internalInf (σ τ : Name (positiveSet B) M) :
    equalityValue B A hM hinf hpair hunion hpower hsep hrep σ τ = internalInf B A hM hsep
      ⟨equalityCoefficients B A hM hinf hpair hunion hpower hsep hrep σ τ,
        equalityCoefficients_mem B A hM hinf hpair hunion hpower hsep hrep σ τ⟩ := by
  apply (equalityValue_isGLB B A hM hinf hpair hunion hpower hsep hrep σ τ).unique
  have he : {b : BooleanElement B.val | b.val ∈ equalityCoefficients B A hM hinf hpair hunion hpower hsep hrep σ τ} =
      Set.range (fun c : LabelledChild B σ => element B c.val.2 ⇨ MV c.val.1 τ) ∪
        Set.range (fun c : LabelledChild B τ => element B c.val.2 ⇨ MV c.val.1 σ) := by
    rw [← equalityHalfCoefficients_carrier, ← equalityHalfCoefficients_carrier]
    ext b
    simp [equalityCoefficients]
  have hh := internalInf_isGLB B A hM hsep
    ⟨equalityCoefficients B A hM hinf hpair hunion hpower hsep hrep σ τ,
      equalityCoefficients_mem B A hM hinf hpair hunion hpower hsep hrep σ τ⟩
    (equalityCoefficients_subset B A hM hinf hpair hunion hpower hsep hrep σ τ)
  rw [he] at hh
  exact hh

end PolishSpaceBook.SetTheoryModels.InternalBooleanAlgebra
