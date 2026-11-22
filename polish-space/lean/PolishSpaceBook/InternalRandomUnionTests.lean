module

public import PolishSpaceBook.InternalRandomLengthTests
public import PolishSpaceBook.ForcingSetDecisions

@[expose] public section

/-! # Internal decision tests and witnesses for countable unions in random forcing -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BoundedSetPredicate
universe u

/-- Parameters: sequence graph, its range, fixed set, index, output. -/
def fixedDifferencePredicate : BoundedSetPredicate 5 :=
  .ex 1 (.conj (.pairMember 0 3 5) (setDifferencePredicate.rename ![2, 5, 4]))

lemma eval_fixedDifferencePredicate (A : ℕ → ZFSet.{u}) (B : ZFSet.{u}) (n : ℕ) (C : ZFSet.{u}) :
    fixedDifferencePredicate.eval ![sequenceGraph A, graphRange (sequenceGraph A), B, natOrdinal n, C] ↔
      C = B \ A n := by
  simp only [fixedDifferencePredicate, eval, eval_rename, Fin.snoc]
  change (∃ X ∈ graphRange (sequenceGraph A), pair (natOrdinal n) X ∈ sequenceGraph A ∧
    setDifferencePredicate.eval ![B, X, C]) ↔ _
  simp only [pair_mem_sequenceGraph, eval_setDifferencePredicate]
  exact ⟨fun ⟨_, _, he, hc⟩ => he ▸ hc,
    fun hc => ⟨A n, (mem_sequenceRange A _).mpr ⟨n, rfl⟩, rfl, hc⟩⟩

lemma fixedDifference_sequence_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (A : ℕ → ZFSet.{u}) (hA : sequenceGraph A ∈ M) (B : M) :
    sequenceGraph (fun n => B.val \ A n) ∈ M := by
  let G : M := ⟨_, hA⟩
  let R : M := ⟨_, graphRange_mem hM hunion (hsep _) hA⟩
  let values (n : ℕ) : M := ⟨_, difference_mem_of_separation hM hsep B.property
    (sequence_term_mem hM hunion A hA n)⟩
  apply bounded_sequenceGraph_mem hM hinf hpair hsep hrep fixedDifferencePredicate ![G, R, B] values
  intro n y
  have he : Fin.snoc (Fin.snoc (Subtype.val ∘ ![G, R, B]) (natOrdinal n)) y.val =
      ![sequenceGraph A, graphRange (sequenceGraph A), B.val, natOrdinal n, y.val] := by
    funext i; fin_cases i <;> rfl
  rw [he, eval_fixedDifferencePredicate]
  exact ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩

lemma intersect_sequence_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (A : ℕ → ZFSet.{u}) (hA : sequenceGraph A ∈ M) (B : M) :
    sequenceGraph (fun n => A n ∩ B.val) ∈ M := by
  have hfirst := fixedDifference_sequence_mem hM hinf hpair hunion hsep hrep A hA B
  have hsecond := fixedDifference_sequence_mem hM hinf hpair hunion hsep hrep _ hfirst B
  have he (n) : B.val \ (B.val \ A n) = A n ∩ B.val := by
    ext x; simp only [ZFSet.mem_sdiff, ZFSet.mem_inter]; tauto
  simpa only [he] using hsecond

end PolishSpaceBook.SetTheoryModels

namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
open ForcingAtomic MeasureTheory Filter Topology
universe u

namespace FiniteAdditiveCutGraph
variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)

lemma value_diff_eq_of_inter_null {A B : ZFSet.{u}} (hA : A ∈ D) (hB : B ∈ D)
    (hz : h.value (A ∩ B) = 0) : h.value (A \ B) = h.value A := by
  have ha := h.value_sdiff_add (h.inter_mem hA hB) hA (fun _ hx => (ZFSet.mem_inter.mp hx).1)
  have he : A \ (A ∩ B) = A \ B := by ext x; simp only [ZFSet.mem_sdiff, ZFSet.mem_inter]; tauto
  rw [he, hz, zero_add] at ha
  exact ha

/-- Countable additivity applies to the entire coded family; individual internal terms do not suffice. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Positive intersections with an internal union
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Suppose every intersection has measure zero. Put
    $$H_n:=\bigcup_{i<n}B_i,\qquad C_n:=\SetDifference{A}{H_n}.$$
    The finite-union construction in §{sec:internal-finite-measure-laws} puts the entire sequence
    $H_n$ in $M$. The bounded difference predicate and graph collection then put the entire sequence
    $C_n$ in $M$. Explicitly, its output $C$ at index $n$ is characterized by
    $\exists B\in\GraphRange{H}\ (\langle n,B\rangle\in H\land C=\SetDifference{A}{B})$,
    where $H$ is the sequence graph. Each output is internal by Separation, so Replacement collects the graph.
    Finite subadditivity gives $\nu(A\cap H_n)=0$, and finite additivity gives $\nu(C_n)=\nu(A)$.
    But $C_n$ decreases to $\SetDifference{A}{U}$. Continuity from above in
    §{sec:internal-finite-measure-laws} forces this constant positive sequence of values to tend to $0$,
    a contradiction.
-/
lemma exists_positive_intersection_sequence {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hca : h.CountablyAdditiveOn M) (B : ℕ → ZFSet.{u}) (hBM : sequenceGraph B ∈ M)
    (hB : ∀ n, B n ∈ D) (A : ZFSet.{u}) (hAM : A ∈ M) (hA : A ∈ D)
    (hp : 0 < h.value A) (hbelow : h.value (A \ sequenceUnion B) = 0) :
    ∃ n, 0 < h.value (A ∩ B n) := by
  by_contra! hn
  have hz (n) : h.value (A ∩ B n) = 0 := le_antisymm (hn n) (h.value_nonneg (h.inter_mem hA (hB n)))
  have hf (n) : h.value (A ∩ partialUnion B n) = 0 := by
    induction n with
    | zero =>
      have he : A ∩ (∅ : ZFSet) = ∅ := by ext x; simp
      rw [partialUnion_zero, he, h.value_zero]
    | succ n ih =>
      have he : A ∩ partialUnion B (n + 1) = (A ∩ partialUnion B n) ∪ (A ∩ B n) := by
        ext x; simp only [partialUnion_succ, ZFSet.mem_inter, ZFSet.mem_union]; tauto
      rw [he]
      apply le_antisymm
      · have hu := h.value_union_le (h.inter_mem hA (h.partialUnion_domain B hB n)) (h.inter_mem hA (hB n))
        simpa only [ih, hz n, add_zero] using hu
      · exact h.value_nonneg (h.union_mem _ (h.inter_mem hA (h.partialUnion_domain B hB n))
          _ (h.inter_mem hA (hB n)))
  let C := fun n => A \ partialUnion B n
  have hCM : sequenceGraph C ∈ M := fixedDifference_sequence_mem hM hinf hpair hunion hsep hrep
    (partialUnion B) (partialUnion_sequence_mem hM hinf hpair hunion hsep hrep B hBM) ⟨A, hAM⟩
  have hC (n) : C n ∈ D := h.diff_mem _ hA _ (h.partialUnion_domain B hB n)
  have hanti : Antitone (fun n => (C n : Set ZFSet)) := by
    intro m n hmn x hx
    exact ZFSet.mem_sdiff.mpr ⟨(ZFSet.mem_sdiff.mp hx).1,
      fun hx' => (ZFSet.mem_sdiff.mp hx).2 (partialUnion_mono B hmn hx')⟩
  have he : sequenceIntersection C = A \ sequenceUnion B := by
    ext x
    simp only [mem_sequenceIntersection, C, ZFSet.mem_sdiff, mem_sequenceUnion_iff_partial]
    exact ⟨fun h => ⟨(h 0).1, fun ⟨n, hn⟩ => (h n).2 hn⟩,
      fun ⟨hx, hn⟩ n => ⟨hx, fun hxn => hn ⟨n, hxn⟩⟩⟩
  have ht := (h.continuity_from_above hM hinf hpair hunion hsep hrep hca C hCM hC hanti).2
  have hv (n) : h.value (C n) = h.value A := h.value_diff_eq_of_inter_null hA (h.partialUnion_domain B hB n) (hf n)
  simp only [hv, he, hbelow] at ht
  exact (ne_of_gt hp) (tendsto_nhds_unique tendsto_const_nhds ht)

end FiniteAdditiveCutGraph

/-- A union of lower cones, indexed by an internal set of measurable sets. -/
def internalFamilyCone (D F E : ZFSet.{u}) : ZFSet.{u} :=
  (positiveNullQuotient D F).sep (fun p => ∃ B ∈ E, p ∈ internalNullCone D F B)

/-- Parameters: domain, measure graph, quotient map, zero code, family, condition. -/
def internalFamilyConePredicate : BoundedSetPredicate 6 :=
  .ex 4 (internalNullConePredicate.rename ![0, 1, 2, 3, 6, 5])

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Internal decision tests
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Replace $r\le p$ by $\langle r,p\rangle\in\mathcal O$. The displayed condition is bounded,
    so Separation constructs the decision test. Its density is the general decision lemma of
    §{sec:random-forcing-detail}: either a condition has a strengthening in $S$, or it already
    belongs to the negative alternative. For the family of lower cones, membership says
    $\exists B\in E\ (p\in\InternalMeasureCone{B})$. Substitute the bounded lower-cone test from
    §{sec:internal-random-filter-valuation} and apply Separation on $P$.
    This constructs the whole union without choosing an enumeration of $E$.
-/
lemma internalFamilyCone_mem (D F E : M) {R : ZFSet.{u}} (h : FiniteAdditiveCutGraph D.val R F.val)
    (hE : E.val ⊆ D.val) : internalFamilyCone D.val F.val E.val ∈ M := by
  let q : M := ⟨_, (nullQuotient_mem hM hpair hunion hpower hsep hrep D F h).1⟩
  let Z : M := ⟨∅, hM.mem_trans h.empty_mem D.property⟩
  apply internalFamilyConePredicate.subset_mem hM (hsep _) ![D, F, q, Z, E]
    (B := internalFamilyCone D.val F.val E.val)
    (positiveNullQuotient_mem hM hpair hunion hpower hsep hrep D F h)
    (fun _ hp => (ZFSet.mem_sep.mp hp).1)
  intro p hp
  change (∃ B ∈ E.val, internalNullConePredicate.eval
    ![D.val, F.val, relationClassMap D.val (nullRelation D.val F.val), ∅, B, p]) ↔ _
  rw [internalFamilyCone, ZFSet.mem_sep, and_iff_right hp]
  apply exists_congr; intro B
  apply and_congr_right; intro hB
  rw [eval_internalNullConePredicate h B p (hE hB), internalNullCone, ZFSet.mem_sep, and_iff_right hp]

variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
  (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)
  (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔ h.value (A.val \ B.val) = 0)

include h hle in
lemma mem_internalFamilyCone_iff (E : ZFSet.{u}) (hE : E ⊆ D) (p : InternalRandomCondition D F η) :
    p.val ∈ internalFamilyCone D F E ↔
      ∃ B : D, B.val ∈ E ∧ η (internalConditionClass η p) ≤ η (nullClassOf (F := F) B) := by
  rw [internalFamilyCone, ZFSet.mem_sep, and_iff_right p.property]
  constructor
  · rintro ⟨B, hB, hp⟩
    exact ⟨⟨B, hE hB⟩, hB, (mem_internalNullCone_iff h η hle ⟨B, hE hB⟩ p).mp hp⟩
  · rintro ⟨B, hB, hp⟩
    exact ⟨B.val, hB, (mem_internalNullCone_iff h η hle B p).mpr hp⟩

include h hle in
lemma internalCondition_le_class_of_subset (A B : D) (hab : A.val ⊆ B.val) :
    η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) := by
  apply (hle A B).mpr
  have he : A.val \ B.val = ∅ := by
    ext x; simp only [ZFSet.mem_sdiff, ZFSet.notMem_empty, iff_false, not_and]; exact fun hx hn => hn (hab hx)
  rw [he, h.value_zero]

include hM hinf hpair hunion hsep hrep h hle in
lemma internalFamilyCone_dense_below (hD : D ∈ M) (hca : h.CountablyAdditiveOn M)
    (B : ℕ → ZFSet.{u}) (hBM : sequenceGraph B ∈ M) (hB : ∀ n, B n ∈ D)
    (hU : sequenceUnion B ∈ D) (p : InternalRandomCondition D F η)
    (hp : η (internalConditionClass η p) ≤ η (nullClassOf (F := F) ⟨sequenceUnion B, hU⟩)) :
    p ∈ forcingDense {q : InternalRandomCondition D F η |
      q.val ∈ internalFamilyCone D F (graphRange (sequenceGraph B))} := by
  intro q hqp
  let A := nullClassRepresentative (internalConditionClass η q)
  have heA : nullClassOf (F := F) A = internalConditionClass η q :=
    Subtype.ext (nullClassRepresentative_spec _)
  have hposA : 0 < h.value A.val := (class_mem_positiveNullQuotient_iff h A).mp
    ((nullClassRepresentative_spec _).symm ▸ q.property)
  change η (internalConditionClass η q) ≤ η (internalConditionClass η p) at hqp
  have hbelow : h.value (A.val \ sequenceUnion B) = 0 :=
    (hle A ⟨_, hU⟩).mp (heA.symm ▸ (hqp.trans hp))
  obtain ⟨n, hn⟩ := h.exists_positive_intersection_sequence hM hinf hpair hunion hsep hrep hca
    B hBM hB A.val (hM.mem_trans A.property hD) A.property hposA hbelow
  let C : D := ⟨A.val ∩ B n, h.inter_mem A.property (hB n)⟩
  let r : InternalRandomCondition D F η := ⟨(nullClassOf (F := F) C).val,
    (class_mem_positiveNullQuotient_iff h C).mpr hn⟩
  have hrq : r ≤ q := by
    change η (nullClassOf (F := F) C) ≤ η (internalConditionClass η q)
    rw [← heA]
    exact internalCondition_le_class_of_subset h η hle C A (fun _ hx => (ZFSet.mem_inter.mp hx).1)
  refine ⟨r, hrq, ZFSet.mem_sep.mpr ⟨r.property, B n, (mem_sequenceRange B _).mpr ⟨n, rfl⟩, ?_⟩⟩
  apply (mem_internalNullCone_iff h η hle ⟨B n, hB n⟩ r).mpr
  exact internalCondition_le_class_of_subset h η hle C ⟨_, hB n⟩ (fun _ hx => (ZFSet.mem_inter.mp hx).2)

include hM hpair hunion hpower hsep hrep h hle in
lemma modelGeneric_meets_internalDecision (hD : D ∈ M) (hF : F ∈ M)
    (S : ZFSet.{u}) (hS : S ∈ M) (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G)) :
    ∃ p ∈ G, p ∈ forcingDecision {q : InternalRandomCondition D F η | q.val ∈ S} := by
  let := internalConditionCodedOrder η
  let P : M := ⟨_, positiveNullQuotient_mem hM hpair hunion hpower hsep hrep ⟨D, hD⟩ ⟨F, hF⟩ h⟩
  let O : M := ⟨_, internalNullOrder_mem hM hpair hunion hpower hsep hrep ⟨D, hD⟩ ⟨F, hF⟩ h⟩
  have ho (p q : Condition P.val) : pair p.val q.val ∈ O.val ↔ p ≤ q :=
    pair_mem_internalNullOrder h η hle ((internalConditionCoding η).symm p) ((internalConditionCoding η).symm q)
  obtain ⟨p, hp, hs⟩ := modelGeneric_meets_setDecision hM hsep P O ⟨S, hS⟩ ho (codedRandomFilter η G) hG
  let q := (internalConditionCoding η).symm p
  have hq : q ∈ G := (image_mem_transportPFilter (internalConditionCoding η).toOrderEmbedding G q).mp hp
  refine ⟨q, hq, ?_⟩
  rcases hs with hs | hs
  · exact Or.inl hs
  · exact Or.inr (fun r hr => hs (internalConditionCoding η r) ((internalConditionCoding η).monotone hr))

include hM hinf hpair hunion hpower hsep hrep h hle in
/-- An internal countable union selected by a generic filter has a selected term. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Generic witnesses for internal unions
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The range $E:=\{B_n:n\in\omega\}$ belongs to $M$, so the first lemma puts
    $S:=\bigcup_{B\in E}\InternalMeasureCone{B}$ and $\ForcingDecision{S}$ in $M$.
    Suppose $p\in G$ and $p\le q(U)$. We claim that $S$ is dense below $p$.
    Given any $q(A)\le p$, the order definition gives $\nu(\SetDifference{A}{U})=0$.
    The preceding lemma supplies $n$ with $\nu(A\cap B_n)>0$.
    The condition $q(A\cap B_n)$ lies below $q(A)$ and belongs to $\InternalMeasureCone{B_n}$,
    proving the claim.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Choose a member of $G\cap\ForcingDecision{S}$. Its negative alternative is impossible:
    a common strengthening with $p$ could be strengthened into $S$, contradicting that alternative.
    Thus some $r\in G$ belongs to $S$, and its witnessing $B_n$ proves the forward implication.
    Conversely, $B_n\IncludedIn U$ gives $q(B_n)\le q(U)$, so any witness on the right is also a witness on the left.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For countable unions, §{sec:internal-random-union-tests} constructs the required decision sets inside $M$.
    A generic filter contains a condition below the class of an internal union exactly when it contains a condition
    below the class of one term.
-/
theorem modelGeneric_union_witness (hD : D ∈ M) (hF : F ∈ M) (hca : h.CountablyAdditiveOn M)
    (B : ℕ → ZFSet.{u}) (hBM : sequenceGraph B ∈ M) (hB : ∀ n, B n ∈ D) (hU : sequenceUnion B ∈ D)
    (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G)) :
    (∃ p ∈ G, η (internalConditionClass η p) ≤ η (nullClassOf (F := F) ⟨sequenceUnion B, hU⟩)) ↔
      ∃ n, ∃ q ∈ G, η (internalConditionClass η q) ≤ η (nullClassOf (F := F) ⟨B n, hB n⟩) := by
  have hE : graphRange (sequenceGraph B) ⊆ D := by
    intro C hC
    obtain ⟨n, rfl⟩ := (mem_sequenceRange B C).mp hC
    exact hB n
  constructor
  · rintro ⟨p, hp, hpu⟩
    have hS := internalFamilyCone_mem hM hpair hunion hpower hsep hrep ⟨D, hD⟩ ⟨F, hF⟩
      ⟨_, graphRange_mem hM hunion (hsep _) hBM⟩ h hE
    obtain ⟨q, hq, hqS⟩ := pfilter_dense_witness G hp
      (internalFamilyCone_dense_below hM hinf hpair hunion hsep hrep h η hle hD hca B hBM hB hU p hpu)
      (modelGeneric_meets_internalDecision hM hpair hunion hpower hsep hrep h η hle hD hF _ hS G hG)
    obtain ⟨C, hC, hqC⟩ := (mem_internalFamilyCone_iff h η hle _ hE q).mp hqS
    obtain ⟨n, hn⟩ := (mem_sequenceRange B C.val).mp hC
    have he : C = ⟨B n, hB n⟩ := Subtype.ext hn.symm
    exact ⟨n, q, hq, he ▸ hqC⟩
  · rintro ⟨n, q, hq, hqn⟩
    exact ⟨q, hq, hqn.trans (internalCondition_le_class_of_subset h η hle ⟨_, hB n⟩ ⟨_, hU⟩
      (fun _ hx => (mem_sequenceUnion B _).mpr ⟨n, hx⟩))⟩

end PolishSpaceBook.CantorTreeMeasure
