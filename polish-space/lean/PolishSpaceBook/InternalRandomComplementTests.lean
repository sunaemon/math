module

public import PolishSpaceBook.InternalRandomUnionTests

@[expose] public section

/-! # Complement decisions for the internal random filter -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels ForcingAtomic MeasureTheory
universe u

variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
  (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)
  (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔ h.value (A.val \ B.val) = 0)

include h hle in
lemma internalCondition_not_below_disjoint (B C : D) (hd : Disjoint (B.val : Set ZFSet) (C.val : Set ZFSet))
    (p : InternalRandomCondition D F η)
    (hpB : η (internalConditionClass η p) ≤ η (nullClassOf (F := F) B))
    (hpC : η (internalConditionClass η p) ≤ η (nullClassOf (F := F) C)) : False := by
  let A := nullClassRepresentative (internalConditionClass η p)
  have he : nullClassOf (F := F) A = internalConditionClass η p := Subtype.ext (nullClassRepresentative_spec _)
  have hb := (hle A B).mp (he.symm ▸ hpB)
  have hc := (hle A C).mp (he.symm ▸ hpC)
  have ha : 0 < h.value A.val := (class_mem_positiveNullQuotient_iff h A).mp
    ((nullClassRepresentative_spec _).symm ▸ p.property)
  have hu : (A.val \ B.val) ∪ (A.val \ C.val) = A.val := by
    ext x
    simp only [ZFSet.mem_union, ZFSet.mem_sdiff]
    have hn : ¬ (x ∈ B.val ∧ x ∈ C.val) := fun hx => Set.disjoint_left.mp hd hx.1 hx.2
    tauto
  have hv := h.value_union_le (h.diff_mem _ A.property _ B.property) (h.diff_mem _ A.property _ C.property)
  rw [hu, hb, hc, zero_add] at hv
  exact (not_lt_of_ge hv) ha

include h hle in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal complement decisions
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    A positive condition cannot lie below two disjoint internal sets $B,C$.
    Indeed, if $q(A)$ did so, both $\SetDifference{A}{B}$ and $\SetDifference{A}{C}$ would have measure zero.
    Their union is $A$, because $B\cap C=\emptyset$, so finite subadditivity would contradict $\nu(A)>0$.
    It follows that every condition below $q(\SetDifference{Y_M}{B})$ has no strengthening below $q(B)$.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Conversely, let $p=q(A)$ have no strengthening below $q(B)$.
    If $\nu(A\cap B)>0$, the condition $q(A\cap B)$ would be such a strengthening.
    Thus $\nu(A\cap B)=0$. Since $A\IncludedIn Y_M$,
    $$\SetDifference{A}{(\SetDifference{Y_M}{B})}=A\cap B,$$
    and the order criterion gives $p\le q(\SetDifference{Y_M}{B})$.
    This proves the set equality. By §{sec:internal-random-union-tests}, the filter meets
    $\ForcingDecision{\InternalMeasureCone{B}}$.
    The positive and negative alternatives cannot both occur in a filter, by directedness.
    If no positive witness occurs, the decision test therefore supplies a negative one, proving the equivalence.
-/
lemma internalNullCone_neg_iff (Y B : D) (hdom : ∀ A ∈ D, A ⊆ Y.val)
    (p : InternalRandomCondition D F η) :
    p ∈ forcingNeg {r : InternalRandomCondition D F η | r.val ∈ internalNullCone D F B.val} ↔
      η (internalConditionClass η p) ≤ η (nullClassOf (F := F) ⟨Y.val \ B.val, h.diff_mem _ Y.property _ B.property⟩) := by
  constructor
  · intro hn
    let A := nullClassRepresentative (internalConditionClass η p)
    have heA : nullClassOf (F := F) A = internalConditionClass η p := Subtype.ext (nullClassRepresentative_spec _)
    rw [← heA, hle]
    have he : A.val \ (Y.val \ B.val) = A.val ∩ B.val := by
      ext x
      simp only [ZFSet.mem_sdiff, ZFSet.mem_inter]
      have hy : x ∈ A.val → x ∈ Y.val := fun hx => hdom A.val A.property hx
      tauto
    rw [he]
    by_contra hz
    have hp : 0 < h.value (A.val ∩ B.val) := lt_of_le_of_ne
      (h.value_nonneg (h.inter_mem A.property B.property)) (Ne.symm hz)
    let C : D := ⟨A.val ∩ B.val, h.inter_mem A.property B.property⟩
    let r : InternalRandomCondition D F η := ⟨(nullClassOf (F := F) C).val,
      (class_mem_positiveNullQuotient_iff h C).mpr hp⟩
    have hrp : r ≤ p := by
      change η (nullClassOf (F := F) C) ≤ η (internalConditionClass η p)
      rw [← heA]
      exact internalCondition_le_class_of_subset h η hle C A (fun _ hx => (ZFSet.mem_inter.mp hx).1)
    apply hn r hrp
    apply (mem_internalNullCone_iff h η hle B r).mpr
    exact internalCondition_le_class_of_subset h η hle C B (fun _ hx => (ZFSet.mem_inter.mp hx).2)
  · intro hp r hr hrB
    have hrC : η (internalConditionClass η r) ≤
        η (nullClassOf (F := F) ⟨Y.val \ B.val, h.diff_mem _ Y.property _ B.property⟩) :=
      (show η (internalConditionClass η r) ≤ η (internalConditionClass η p) from hr).trans hp
    exact internalCondition_not_below_disjoint h η hle B ⟨_, h.diff_mem _ Y.property _ B.property⟩
      (Set.disjoint_left.mpr (fun _ hb hc => (ZFSet.mem_sdiff.mp hc).2 hb)) r
      ((mem_internalNullCone_iff h η hle B r).mp hrB) hrC

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hpair hunion hpower hsep hrep h hle in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal complement decisions
-/
theorem modelGeneric_complement_witness (hD : D ∈ M) (hF : F ∈ M)
    (Y B : D) (hdom : ∀ A ∈ D, A ⊆ Y.val) (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G)) :
    (∃ p ∈ G, η (internalConditionClass η p) ≤
      η (nullClassOf (F := F) ⟨Y.val \ B.val, h.diff_mem _ Y.property _ B.property⟩)) ↔
      ¬ ∃ p ∈ G, η (internalConditionClass η p) ≤ η (nullClassOf (F := F) B) := by
  have hlow : IsLowerSet {p : InternalRandomCondition D F η | p.val ∈ internalNullCone D F B.val} := by
    intro p q hqp hp
    apply (mem_internalNullCone_iff h η hle B q).mpr
    exact (show η (internalConditionClass η q) ≤ η (internalConditionClass η p) from hqp).trans
      ((mem_internalNullCone_iff h η hle B p).mp hp)
  constructor
  · rintro ⟨p, hp, hpC⟩ ⟨q, hq, hqB⟩
    exact pfilter_not_pos_neg G hlow hq hp ((mem_internalNullCone_iff h η hle B q).mpr hqB)
      ((internalNullCone_neg_iff h η hle Y B hdom p).mpr hpC)
  · intro hn
    obtain ⟨p, hp, hs⟩ := modelGeneric_meets_internalDecision hM hpair hunion hpower hsep hrep h η hle hD hF
      (internalNullCone D F B.val)
      (internalNullCone_mem hM hpair hunion hpower hsep hrep ⟨D, hD⟩ ⟨F, hF⟩ h B.val B.property) G hG
    rcases hs with hs | hs
    · exact False.elim (hn ⟨p, hp, (mem_internalNullCone_iff h η hle B p).mp hs⟩)
    · exact ⟨p, hp, (internalNullCone_neg_iff h η hle Y B hdom p).mp hs⟩

end PolishSpaceBook.CantorTreeMeasure
