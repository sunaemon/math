module

public import PolishSpaceBook.InternalConullFamilyCovers
public import PolishSpaceBook.InternalRandomLengthTests

@[expose] public section

/-! # Internal families of all representatives of a dense set of conditions -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet SetTheoryModels ForcingFormulas BoundedSetPredicate MeasureTheory
universe u

def denseRepresentatives (D F Δ : ZFSet.{u}) : ZFSet.{u} :=
  D.sep (fun B => relationClass D (nullRelation D F) B ∈ Δ)

lemma mem_denseRepresentatives (D F Δ B : ZFSet.{u}) :
    B ∈ denseRepresentatives D F Δ ↔ B ∈ D ∧ relationClass D (nullRelation D F) B ∈ Δ :=
  ZFSet.mem_sep

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal dense representative families
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The entire quotient map $q$ belongs to $M$ by §{sec:internal-null-quotients}. For $B\in D$, the condition
    $\exists p\in\Delta\;(\langle B,p\rangle\in q)$ is bounded, so Separation gives $E\in M$.
    For positive $A$, choose $p\in\Delta$ with $p\le q(A)$, and choose $B\in D$ with $q(B)=p$.
    Put $C:=B\cap A$. Finite ring closure gives $C\in D$, and
    $$\SetDifference{C}{B}=\emptyset,\qquad
    \SetDifference{B}{C}=\SetDifference{B}{A},\qquad\nu(\SetDifference{B}{A})=0.$$
    Thus $q(C)=q(B)=p$, so $C\in E$ and $\nu(C)>0$, while $C\IncludedIn A$ as an actual subset.
-/
theorem denseRepresentatives_mem {M D R F Δ : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (h : FiniteAdditiveCutGraph D R F) (hD : D ∈ M) (hF : F ∈ M) (hΔ : Δ ∈ M) :
    denseRepresentatives D F Δ ∈ M := by
  let q : M := ⟨_, (nullQuotient_mem hM hpair hunion hpower hsep hrep ⟨D, hD⟩ ⟨F, hF⟩ h).1⟩
  let p : BoundedSetPredicate 3 := .ex 1 (.pairMember 0 2 3)
  apply p.subset_mem hM (hsep _) ![q, ⟨Δ, hΔ⟩] hD (fun _ hx => (ZFSet.mem_sep.mp hx).1)
  intro B hB
  change (∃ C ∈ Δ, pair B C ∈ relationClassMap D (nullRelation D F)) ↔
    B ∈ denseRepresentatives D F Δ
  rw [mem_denseRepresentatives, and_iff_right hB]
  simp only [pair_mem_relationClassMap D (nullRelation D F) ⟨B, hB⟩]
  exact ⟨fun ⟨C, hC, he⟩ => he.symm ▸ hC,
    fun hb => ⟨relationClass D (nullRelation D F) B, hb, rfl⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal dense representative families
-/
theorem denseRepresentatives_dense {D R F Y Δ : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
    (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)
    (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔
      h.value (A.val \ B.val) = 0)
    (hdense : IsCoinitial {p : InternalRandomCondition D F η | p.val ∈ Δ}) :
    h.DenseRepresentativeFamily (denseRepresentatives D F Δ) Y := by
  intro A hA _ hpos
  let p : InternalRandomCondition D F η := ⟨relationClass D (nullRelation D F) A,
    (class_mem_positiveNullQuotient_iff h ⟨A, hA⟩).mpr hpos⟩
  obtain ⟨q, hqΔ, hqp⟩ := hdense p
  let B := nullClassRepresentative (internalConditionClass η q)
  have hBq : nullClassOf (F := F) B = internalConditionClass η q :=
    Subtype.ext (nullClassRepresentative_spec _)
  have hBA : h.value (B.val \ A) = 0 := by
    apply (hle B ⟨A, hA⟩).mp
    rw [hBq]
    exact hqp
  let C : D := ⟨B.val ∩ A, h.inter_mem B.property hA⟩
  have hCB : relationClass D (nullRelation D F) C.val = relationClass D (nullRelation D F) B.val := by
    apply (nullClass_eq_iff h C B).mpr
    have hleft : C.val \ B.val = ∅ := by
      ext x
      simp only [C, ZFSet.mem_sdiff, ZFSet.mem_inter, ZFSet.notMem_empty]
      tauto
    have hright : B.val \ C.val = B.val \ A := by
      ext x
      simp only [C, ZFSet.mem_sdiff, ZFSet.mem_inter]
      tauto
    rw [hleft, hright, h.value_zero]
    exact ⟨rfl, hBA⟩
  have hCq : relationClass D (nullRelation D F) C.val = q.val :=
    hCB.trans (nullClassRepresentative_spec _)
  refine ⟨C.val, (mem_denseRepresentatives D F Δ C.val).mpr ⟨C.property, hCq.symm ▸ hqΔ⟩,
    fun _ hx => (ZFSet.mem_inter.mp hx).2, ?_⟩
  exact (class_mem_positiveNullQuotient_iff h C).mp (hCq.symm ▸ q.property)

end PolishSpaceBook.CantorTreeMeasure
