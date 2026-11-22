module

public import PolishSpaceBook.ForcingBooleanRecursion

@[expose] public section

/-! # The simultaneous atomic clauses for constructed Boolean values -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels.InternalBooleanAlgebra
open FirstOrder Language ZFSet ForcingFormulas ForcingAtomic ForcingNames
universe u

variable {M : ZFSet.{u}} (B : M) [BooleanAlgebra (BooleanElement B.val)]

lemma dense_principal_iff (b : BooleanElement B.val) (p : Condition (positiveSet B)) :
    p ∈ forcingDense {q | element B q ≤ b} ↔ element B p ≤ b := by
  constructor
  · intro h
    have hd : element B p ⊓ bᶜ = ⊥ := by
      by_contra hn
      let q := positive B (element B p ⊓ bᶜ) hn
      obtain ⟨r, hrq, hrb⟩ := h q inf_le_left
      have hrc : element B r ≤ bᶜ := (show element B r ≤ element B q from hrq).trans inf_le_right
      exact element_ne_bot B r (le_antisymm ((le_inf hrb hrc).trans (by simp)) bot_le)
    exact disjoint_compl_right_iff.mp (disjoint_iff.mpr hd)
  · intro h q hqp
    exact ⟨q, le_rfl, (show element B q ≤ element B p from hqp).trans h⟩

lemma incompatible_iff_le_compl (p r : Condition (positiveSet B)) :
    incompatible (positiveSet B) p r ↔ element B p ≤ (element B r)ᶜ := by
  rw [le_compl_iff_disjoint_right, disjoint_iff]
  constructor
  · intro h
    by_contra hn
    exact h ⟨positive B (element B p ⊓ element B r) hn, inf_le_left, inf_le_right⟩
  · intro h ⟨q, hqp, hqr⟩
    exact element_ne_bot B q (le_antisymm ((le_inf hqp hqr).trans_eq h) bot_le)

lemma dense_union_principal_iff (a b : BooleanElement B.val) (p : Condition (positiveSet B)) :
    p ∈ forcingDense {q | element B q ≤ a ∨ element B q ≤ b} ↔ element B p ≤ a ⊔ b := by
  constructor
  · intro h
    apply (dense_principal_iff B (a ⊔ b) p).mp
    intro q hqp
    obtain ⟨r, hrq, hr⟩ := h q hqp
    exact ⟨r, hrq, hr.elim (fun h => h.trans le_sup_left) (fun h => h.trans le_sup_right)⟩
  · intro h q hqp
    by_cases hz : element B q ⊓ a = ⊥
    · have hqa : element B q ≤ aᶜ := le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr hz)
      have hqb : element B q ≤ b := by
        calc
          element B q ≤ (a ⊔ b) ⊓ aᶜ := le_inf ((show element B q ≤ element B p from hqp).trans h) hqa
          _ = (a ⊓ aᶜ) ⊔ (b ⊓ aᶜ) := inf_sup_right _ _ _
          _ ≤ b := by simp
      exact ⟨q, le_rfl, Or.inr hqb⟩
    · exact ⟨positive B (element B q ⊓ a) hz, inf_le_left, Or.inl inf_le_right⟩

variable (A : InternalBooleanAlgebra B)
  (hM : M.IsTransitive) (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

local notation "V" => booleanValue B A hM hinf hpair hunion hpower hsep hrep
local notation "force_le" => force_iff_le_booleanValue B A hM hinf hpair hunion hpower hsep hrep

def membershipValue (σ τ : Name (positiveSet B) M) : BooleanElement B.val := V (memberAt 0 1) ![σ, τ]
def equalityValue (σ τ : Name (positiveSet B) M) : BooleanElement B.val := V (equalAt 0 1) ![σ, τ]

local notation "MV" => membershipValue B A hM hinf hpair hunion hpower hsep hrep
local notation "EV" => equalityValue B A hM hinf hpair hunion hpower hsep hrep

lemma atomic_membership_iff_le (σ τ : Name (positiveSet B) M) (p : Condition (positiveSet B)) :
    p ∈ atomic (positiveSet B) false σ.val τ.val ↔ element B p ≤ MV σ τ := by
  simpa [membershipValue, memberAt, force, termName, variableAt] using force_le (memberAt 0 1) ![σ, τ] p

lemma atomic_equality_iff_le (σ τ : Name (positiveSet B) M) (p : Condition (positiveSet B)) :
    p ∈ atomic (positiveSet B) true σ.val τ.val ↔ element B p ≤ EV σ τ := by
  simpa [equalityValue, equalAt, force, termName, variableAt] using force_le (equalAt 0 1) ![σ, τ] p

/-- The actual labelled children, with ground-model membership and namehood
retained in the first coordinate. -/
abbrev LabelledChild (τ : Name (positiveSet B) M) :=
  {x : Name (positiveSet B) M × Condition (positiveSet B) // pair x.1.val x.2.val ∈ τ.val}

def child (τ : Name (positiveSet B) M) (π : ZFSet.{u}) (r : Condition (positiveSet B))
    (h : pair π r.val ∈ τ.val) : LabelledChild B τ :=
  ⟨(⟨π, child_mem_ground hM τ.property.1 h, τ.property.2.child h⟩, r), h⟩

/-- Membership is the join of label meets equality values, including the empty
family case. This uses the established well-founded atomic recursion. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  exclude-books: polish-space-ch1
  target: proof
  excerpt: |
    The condition-forcing recursion now gives the Boolean recursive clauses, since positive principal
    ideals determine their Boolean elements.
-/
theorem membershipValue_isLUB (σ τ : Name (positiveSet B) M) :
    IsLUB (Set.range (fun c : LabelledChild B τ => element B c.val.2 ⊓ EV σ c.val.1)) (MV σ τ) := by
  constructor
  · rintro b ⟨c, rfl⟩
    change element B c.val.2 ⊓ EV σ c.val.1 ≤ MV σ τ
    by_cases hz : element B c.val.2 ⊓ EV σ c.val.1 = ⊥
    · rw [hz]; exact bot_le
    · let p := positive B (element B c.val.2 ⊓ EV σ c.val.1) hz
      apply (atomic_membership_iff_le B A hM hinf hpair hunion hpower hsep hrep σ τ p).mp
      exact membership_of_witness _ ⟨c.val.1.val, c.val.2, c.property, inf_le_left,
        (atomic_equality_iff_le B A hM hinf hpair hunion hpower hsep hrep σ c.val.1 p).mpr inf_le_right⟩
  · intro b hb
    rw [membershipValue, booleanValue_le_iff]
    intro p hp
    apply (dense_principal_iff B b p).mp
    have hp' : p ∈ atomic (positiveSet B) false σ.val τ.val := by
      simpa [memberAt, force, termName, variableAt] using hp
    rw [membership_eq] at hp'
    intro q hqp
    obtain ⟨r, hrq, π, s, hπ, hrs, he⟩ := hp' q hqp
    let c := child B hM τ π s hπ
    have hrE : element B r ≤ EV σ c.val.1 :=
      (atomic_equality_iff_le B A hM hinf hpair hunion hpower hsep hrep σ c.val.1 r).mp he
    exact ⟨r, hrq, (le_inf hrs hrE).trans (hb ⟨c, rfl⟩)⟩

lemma equality_half_iff (σ τ : Name (positiveSet B) M) (p : Condition (positiveSet B)) :
    (∀ π (r : Condition (positiveSet B)), pair π r.val ∈ σ.val → p ∈ forcingDense
      {q | incompatible (positiveSet B) q r ∨ q ∈ atomic (positiveSet B) false π τ.val}) ↔
    ∀ c : LabelledChild B σ, element B p ≤ element B c.val.2 ⇨ MV c.val.1 τ := by
  constructor
  · intro h c
    rw [himp_eq]
    apply (dense_union_principal_iff B (MV c.val.1 τ) (element B c.val.2)ᶜ p).mp
    intro q hqp
    obtain ⟨r, hrq, hr⟩ := h c.val.1.val c.val.2 c.property q hqp
    refine ⟨r, hrq, ?_⟩
    exact hr.elim (fun hi => Or.inr ((incompatible_iff_le_compl B _ _).mp hi))
      (fun hm => Or.inl ((atomic_membership_iff_le B A hM hinf hpair hunion hpower hsep hrep _ _ _).mp hm))
  · intro h π r hπ
    let c := child B hM σ π r hπ
    have hh := h c
    rw [himp_eq] at hh
    have hd := (dense_union_principal_iff B (MV c.val.1 τ) (element B r)ᶜ p).mpr hh
    intro q hqp
    obtain ⟨s, hsq, hs⟩ := hd q hqp
    refine ⟨s, hsq, ?_⟩
    exact hs.elim
      (fun hm => Or.inr ((atomic_membership_iff_le B A hM hinf hpair hunion hpower hsep hrep _ _ _).mpr hm))
      (fun hi => Or.inl ((incompatible_iff_le_compl B _ _).mpr hi))

/-- Equality is the meet of the two families of labelled membership
implications from the simultaneous atomic recursion. -/
theorem equalityValue_isGLB (σ τ : Name (positiveSet B) M) :
    IsGLB (Set.range (fun c : LabelledChild B σ => element B c.val.2 ⇨ MV c.val.1 τ) ∪
      Set.range (fun c : LabelledChild B τ => element B c.val.2 ⇨ MV c.val.1 σ)) (EV σ τ) := by
  have hiff : ∀ p : Condition (positiveSet B), element B p ≤ EV σ τ ↔
      (∀ c : LabelledChild B σ, element B p ≤ element B c.val.2 ⇨ MV c.val.1 τ) ∧
      (∀ c : LabelledChild B τ, element B p ≤ element B c.val.2 ⇨ MV c.val.1 σ) := by
    intro p
    rw [← atomic_equality_iff_le, equality_iff,
      equality_half_iff B A hM hinf hpair hunion hpower hsep hrep,
      equality_half_iff B A hM hinf hpair hunion hpower hsep hrep]
  constructor
  · intro b hb
    by_cases hz : EV σ τ = ⊥
    · rw [hz]; exact bot_le
    · have hp := (hiff (positive B (EV σ τ) hz)).mp le_rfl
      rcases hb with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact hp.1 c
      · exact hp.2 c
  · intro b hb
    by_cases hz : b = ⊥
    · rw [hz]; exact bot_le
    · exact (hiff (positive B b hz)).mpr
        ⟨fun c => hb (Or.inl ⟨c, rfl⟩), fun c => hb (Or.inr ⟨c, rfl⟩)⟩

end PolishSpaceBook.SetTheoryModels.InternalBooleanAlgebra
