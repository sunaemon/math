module

public import PolishSpaceBook.InternalBorelTruth
public import PolishSpaceBook.ForcingBorelNames

@[expose] public section

/-! # The internal Borel membership test agrees with forcing for the constructed names -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels ForcingAtomic ForcingNames BorelExpression MeasureTheory
universe u

variable {D F : ZFSet.{u}}
  (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)

lemma mem_codedRandomFilter (G : Order.PFilter (InternalRandomCondition D F η))
    (p : Condition (positiveNullQuotient D F)) :
    letI := internalConditionCodedOrder η
    p ∈ codedRandomFilter η G ↔ (internalConditionCoding η).symm p ∈ G := by
  let := internalConditionCodedOrder η
  have hm := image_mem_transportPFilter (internalConditionCoding η).toOrderEmbedding G
    ((internalConditionCoding η).symm p)
  change internalConditionCoding η ((internalConditionCoding η).symm p) ∈ codedRandomFilter η G ↔ _ at hm
  rw [OrderIso.apply_symm_apply] at hm
  exact hm

lemma chosen_codedRandomFilter (G : Order.PFilter (InternalRandomCondition D F η)) :
    @chosen (positiveNullQuotient D F) (internalConditionCodedOrder η) (codedRandomFilter η G) =
      internalFilterSet η G := by
  let := internalConditionCodedOrder η
  ext z
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨(internalConditionCoding η).symm p, (mem_codedRandomFilter η G p).mp hp, he⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨internalConditionCoding η p, (mem_codedRandomFilter η G _).mpr hp, he⟩

lemma codedRandomFilter_surjective : Function.Surjective (codedRandomFilter η) := by
  let := internalConditionCodedOrder η
  intro H
  let G := transportPFilter (internalConditionCoding η).symm.toOrderEmbedding H
  refine ⟨G, ?_⟩
  ext p
  change p ∈ codedRandomFilter η G ↔ p ∈ H
  rw [mem_codedRandomFilter]
  exact image_mem_transportPFilter (internalConditionCoding η).symm.toOrderEmbedding H p

variable {R : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
  (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔ h.value (A.val \ B.val) = 0)

include h hle in
/-- Failure of the internal order test supplies a positive difference, with no strengthening in the cone. -/
lemma internalClass_countercondition (B : D) (p : InternalRandomCondition D F η)
    (hp : ¬ η (internalConditionClass η p) ≤ η (nullClassOf (F := F) B)) :
    ∃ r : InternalRandomCondition D F η, r ≤ p ∧
      ∀ s : InternalRandomCondition D F η, s ≤ r → ¬ η (internalConditionClass η s) ≤ η (nullClassOf (F := F) B) := by
  let A := nullClassRepresentative (internalConditionClass η p)
  have he : nullClassOf (F := F) A = internalConditionClass η p := Subtype.ext (nullClassRepresentative_spec _)
  have hz : h.value (A.val \ B.val) ≠ 0 := by
    intro hz
    exact hp (he ▸ (hle A B).mpr hz)
  let C : D := ⟨A.val \ B.val, h.diff_mem _ A.property _ B.property⟩
  have hc : 0 < h.value C.val := lt_of_le_of_ne (h.value_nonneg C.property) (Ne.symm hz)
  let r : InternalRandomCondition D F η := ⟨(nullClassOf (F := F) C).val,
    (class_mem_positiveNullQuotient_iff h C).mpr hc⟩
  refine ⟨r, ?_, ?_⟩
  · change η (nullClassOf (F := F) C) ≤ η (internalConditionClass η p)
    rw [← he]
    exact internalCondition_le_class_of_subset h η hle C A (fun _ hx => (ZFSet.mem_sdiff.mp hx).1)
  · intro s hsr hsB
    exact internalCondition_not_below_disjoint h η hle C B
      (Set.disjoint_left.mpr (fun _ hx hy => (ZFSet.mem_sdiff.mp hx).2 hy)) s hsr hsB

include h hle in
lemma internalClass_le_iff_all_modelGeneric {M : ZFSet.{u}} (hc : M.toSet.Countable)
    (B : D) (p : InternalRandomCondition D F η) :
    η (internalConditionClass η p) ≤ η (nullClassOf (F := F) B) ↔
      ∀ G : Order.PFilter (InternalRandomCondition D F η),
        @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G) →
        p ∈ G → ∃ q ∈ G, η (internalConditionClass η q) ≤ η (nullClassOf (F := F) B) := by
  let := internalConditionCodedOrder η
  constructor
  · intro hp G _ hpG
    exact ⟨p, hpG, hp⟩
  · intro hall
    by_contra hp
    obtain ⟨r, hrp, hr⟩ := internalClass_countercondition η h hle B p hp
    obtain ⟨H, hrH, hH⟩ := exists_modelGeneric (positiveNullQuotient D F) M hc (internalConditionCoding η r)
    obtain ⟨G, rfl⟩ := codedRandomFilter_surjective η H
    have hrG := (mem_codedRandomFilter η G _).mp hrH
    obtain ⟨q, hqG, hq⟩ := hall G hH (G.mem_of_le hrp hrG)
    obtain ⟨s, _, hsr, hsq⟩ := G.directed r hrG q hqG
    exact hr s hsr ((show η (internalConditionClass η s) ≤ η (internalConditionClass η q) from hsq).trans hq)

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hD : D ∈ M) (hF : F ∈ M)

abbrev internalRandomPoset : M :=
  ⟨_, positiveNullQuotient_mem hM hpair hunion hpower hsep hrep ⟨D, hD⟩ ⟨F, hF⟩ h⟩

abbrev internalRandomOrder : M :=
  ⟨_, internalNullOrder_mem hM hpair hunion hpower hsep hrep ⟨D, hD⟩ ⟨F, hF⟩ h⟩

include h hle in
lemma internalRandomOrder_spec (p q : Condition (positiveNullQuotient D F)) :
    letI := internalConditionCodedOrder η
    pair p.val q.val ∈ internalNullOrder D F ↔ p ≤ q := by
  let := internalConditionCodedOrder η
  exact pair_mem_internalNullOrder h η hle ((internalConditionCoding η).symm p) ((internalConditionCoding η).symm q)

/-- The same uniformly constructed Borel name, specialized to the internal random order. -/
def internalRandomBorelName (c : BorelExpression) (hc : c.labelGraph ∈ M) : Name (positiveNullQuotient D F) M :=
  letI := internalConditionCodedOrder η
  borelInterpretationName hM hinf hpair hunion hpower hsep hrep
    (internalRandomPoset h hM hpair hunion hpower hsep hrep hD hF)
    (internalRandomOrder h hM hpair hunion hpower hsep hrep hD hF)
    (internalRandomOrder_spec η h hle) c hc

variable (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
    pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)

def internalRandomRealName : Name (positiveNullQuotient D F) M :=
  ⟨randomRealName M D F, randomRealName_mem hM hinf hpair hunion hpower hsep hrep ⟨D, hD⟩ ⟨F, hF⟩ h hcyl,
    randomRealName_isName M D F⟩

variable (hη : Function.Injective η) (hpos : ∀ C, η C ≠ ⊥ ↔ C.val ∈ positiveNullQuotient D F)
  (hrepSet : ∀ (X : D) (A : Set (ℕ → Bool)) (hm : MeasurableSet A), InternallyApproximable M A →
    RepresentsInternalSet M X.val A → η (nullClassOf (F := F) X) = MeasureAlgebra.mk A hm)

include h hle hM hinf hpair hunion hpower hsep hrep hcyl hη hpos hrepSet in
lemma internalRandom_named_membership (hca : h.CountablyAdditiveOn M)
    (hY : internalCantor M ∈ D) (hdom : ∀ A ∈ D, A ⊆ internalCantor M)
    (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (hnode : ∀ t, internalCantorNodeSet M c hc.2.2.2.2.2 t ∈ D)
    (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G)) :
    letI := internalConditionCodedOrder η
    value (positiveNullQuotient D F) (codedRandomFilter η G) (randomRealName M D F) ∈
      value (positiveNullQuotient D F) (codedRandomFilter η G)
        (internalRandomBorelName η h hle hM hinf hpair hunion hpower hsep hrep hD hF c hcM).val ↔
      ∃ p ∈ G, η (internalConditionClass η p) ≤ η (nullClassOf (F := F) ⟨_, hnode []⟩) := by
  let := internalConditionCodedOrder η
  have hb := value_borelInterpretationName hM hinf hpair hunion hpower hsep hrep
    (internalRandomPoset h hM hpair hunion hpower hsep hrep hD hF)
    (internalRandomOrder h hM hpair hunion hpower hsep hrep hD hF)
    (internalRandomOrder_spec η h hle) c hc.2.2.2.2.2 hcM (codedRandomFilter η G) hG
  change value _ _ _ ∈ value _ _ (borelInterpretationName _ _ _ _ _ _ _ _ _ _ _ _).val ↔ _
  rw [hb]
  change valuation (chosen _ _) _ ∈ internalBorelCantorSet (extension _ _ (chosen _ _)) _ _ ↔ _
  rw [chosen_codedRandomFilter]
  obtain ⟨x, hv, _, ht⟩ := modelGeneric_internalBorel_truth h η hle hη hpos hM hinf hpair hunion hpower hsep hrep
    hrepSet hD hF hca hY hdom hcyl c hc hcM hnode G hG
  rw [hv]
  exact ht

include h hle hM hinf hpair hunion hpower hsep hrep hcyl hη hpos hrepSet in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Forcing for the internal random-real name
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Write $B:=\BorelInterpretation{c}{M}$.
    The valuation identities of §{sec:internal-random-union-tests} and §{sec:internal-random-filter-valuation},
    together with the internal Borel truth theorem, give for every $M$-generic filter $G$
    $$\begin{aligned}
    \dot r^G\in\bigl(\BorelCodeName{c}\bigr)^G
    &\quad\Longleftrightarrow\quad r_G\in\BorelInterpretation{c}{M[G]}\\
    &\quad\Longleftrightarrow\quad\exists t\in G\ (t\le q(B)).
    \end{aligned}$$
    If $p\le q(B)$, every generic filter containing $p$ satisfies this membership statement, with $p$ itself
    as a witness. By the agreement with semantic forcing proved in §{sec:internal-generic-truth},
    $p$ syntactically forces it.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Conversely, write $p=q(A)$ and suppose $p\not\le q(B)$.
    The order criterion gives $\nu(\SetDifference{A}{B})>0$.
    Hence $r:=q(\SetDifference{A}{B})$ is a condition below $p$.
    No positive condition can lie below both $r$ and $q(B)$, since their representatives are disjoint,
    as proved in the complement lemma above.
    External countability supplies an $M$-generic filter $G$ containing $r$; upward closure also puts $p$ in $G$.
    If the displayed membership statement held, the truth identity would supply a condition $t\in G$ below $q(B)$.
    A common strengthening of $r$ and $t$ would contradict disjointness.
    Thus this generic extension refutes membership, so $p$ does not force it.
    Finally, the null-difference criterion for the internal order proves the last assertion.
-/
theorem force_internalRandomBorel_iff (hcount : M.toSet.Countable) (hca : h.CountablyAdditiveOn M)
    (hY : internalCantor M ∈ D) (hdom : ∀ A ∈ D, A ⊆ internalCantor M)
    (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (hnode : ∀ t, internalCantorNodeSet M c hc.2.2.2.2.2 t ∈ D)
    (p : InternalRandomCondition D F η) :
    letI := internalConditionCodedOrder η
    internalConditionCoding η p ∈ force (positiveNullQuotient D F) M (memberAt (0 : Fin 2) 1)
      ![internalRandomRealName h hM hinf hpair hunion hpower hsep hrep hD hF hcyl,
        internalRandomBorelName η h hle hM hinf hpair hunion hpower hsep hrep hD hF c hcM] ↔
      η (internalConditionClass η p) ≤ η (nullClassOf (F := F) ⟨_, hnode []⟩) := by
  let := internalConditionCodedOrder η
  let σ := internalRandomRealName h hM hinf hpair hunion hpower hsep hrep hD hF hcyl
  let τ := internalRandomBorelName η h hle hM hinf hpair hunion hpower hsep hrep hD hF c hcM
  have hf := force_iff_all_modelGeneric hM hinf hpair hunion hpower hsep hrep
    (internalRandomPoset h hM hpair hunion hpower hsep hrep hD hF)
    (internalRandomOrder h hM hpair hunion hpower hsep hrep hD hF)
    (internalRandomOrder_spec η h hle) hcount (memberAt (0 : Fin 2) 1) ![σ, τ] (internalConditionCoding η p)
  rw [hf, internalClass_le_iff_all_modelGeneric η h hle hcount]
  have ht (G : Order.PFilter (InternalRandomCondition D F η))
      (hG : ModelGeneric (positiveNullQuotient D F) M (codedRandomFilter η G)) :
      (memberAt (0 : Fin 2) 1).Realize Empty.elim
        (fun i => evalName (positiveNullQuotient D F) M (codedRandomFilter η G) (![σ, τ] i)) ↔
        ∃ q ∈ G, η (internalConditionClass η q) ≤ η (nullClassOf (F := F) ⟨_, hnode []⟩) := by
    simp only [realize_memberAt_model, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact internalRandom_named_membership η h hle hM hinf hpair hunion hpower hsep hrep hD hF hcyl hη hpos
      hrepSet hca hY hdom c hc hcM hnode G hG
  constructor
  · intro hall G hG hpG
    exact (ht G hG).mp (hall (codedRandomFilter η G) hG ((mem_codedRandomFilter η G _).mpr hpG))
  · intro hall H hH hpH
    obtain ⟨G, rfl⟩ := codedRandomFilter_surjective η H
    exact (ht G hH).mpr (hall G hH ((mem_codedRandomFilter η G _).mp hpH))

include h hle hM hinf hpair hunion hpower hsep hrep hcyl hη hpos hrepSet in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Forcing for the internal random-real name
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: lemma
  title: Random forcing calculation
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Apply the forcing theorem of §{sec:internal-random-borel-truth} to the two constructed names.
    It identifies forcing with the condition $[B']\le q(\BorelInterpretation{c}{M})$.
    The internal order criterion gives exactly the displayed null-difference condition.
-/
theorem force_internalRandomBorel_null_iff (hcount : M.toSet.Countable) (hca : h.CountablyAdditiveOn M)
    (hY : internalCantor M ∈ D) (hdom : ∀ A ∈ D, A ⊆ internalCantor M)
    (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (hnode : ∀ t, internalCantorNodeSet M c hc.2.2.2.2.2 t ∈ D)
    (A : D) (hA : 0 < h.value A.val) :
    letI := internalConditionCodedOrder η
    internalConditionCoding η ⟨(nullClassOf (F := F) A).val, (class_mem_positiveNullQuotient_iff h A).mpr hA⟩ ∈
      force (positiveNullQuotient D F) M (memberAt (0 : Fin 2) 1)
        ![internalRandomRealName h hM hinf hpair hunion hpower hsep hrep hD hF hcyl,
          internalRandomBorelName η h hle hM hinf hpair hunion hpower hsep hrep hD hF c hcM] ↔
      h.value (A.val \ internalBorelCantorSet M c hc.2.2.2.2.2) = 0 := by
  exact (force_internalRandomBorel_iff η h hle hM hinf hpair hunion hpower hsep hrep hD hF hcyl hη hpos hrepSet
    hcount hca hY hdom c hc hcM hnode ⟨_, (class_mem_positiveNullQuotient_iff h A).mpr hA⟩).trans (hle A ⟨_, hnode []⟩)

end PolishSpaceBook.CantorTreeMeasure
