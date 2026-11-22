module

public import PolishSpaceBook.InternalBorelUnionTests
public import PolishSpaceBook.InternalRandomComplementTests

@[expose] public section

/-! # Borel truth for the real of an internal generic random filter -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory ForcingAtomic
universe u

lemma internalCantorNodeSet_empty (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child)
    (s : List ℕ) (hs : c s = 0) : internalCantorNodeSet M c hw s = ∅ := by
  ext g
  simp only [ZFSet.notMem_empty, iff_false]
  intro hg
  obtain ⟨x, rfl, _⟩ := mem_internalCantor.mp (ZFSet.mem_inter.mp hg).2
  have hx := ((cantorPointGraph_mem_internalCantorNodeSet M c hw s x).mp hg).2
  rw [cantorNodeSet_eq_empty c hw s hs] at hx
  exact hx

lemma internalCantorNodeSet_compl (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child)
    (s t : List ℕ) (he : cantorNodeSet c hw s = (cantorNodeSet c hw t)ᶜ) :
    internalCantorNodeSet M c hw s = internalCantor M \ internalCantorNodeSet M c hw t := by
  ext g
  by_cases hg : g ∈ internalCantor M
  · obtain ⟨x, rfl, hxM⟩ := mem_internalCantor.mp hg
    simp only [ZFSet.mem_sdiff, cantorPointGraph_mem_internalCantorNodeSet, cantorPointGraph_mem_internalCantor,
      hxM, true_and, he, Set.mem_compl_iff]
  · have hs : g ∉ internalCantorNodeSet M c hw s := fun h => hg (ZFSet.mem_inter.mp h).2
    simp only [hs, ZFSet.mem_sdiff, hg, false_and]

lemma cantorNodeSet_complement_child (c : BorelExpression) (hc : c.Valid) (s : List ℕ) (hs : c s = 2) :
    ∃ n, c (s ++ [n]) ≠ 0 ∧
      cantorNodeSet c hc.2.2.2.2.2 s = (cantorNodeSet c hc.2.2.2.2.2 (s ++ [n]))ᶜ := by
  obtain ⟨n, hn, huniq⟩ := hc.2.2.2.2.1 s hs
  refine ⟨n, hn, ?_⟩
  have he : (⋃ j, cantorNodeSet c hc.2.2.2.2.2 (s ++ [j])) = cantorNodeSet c hc.2.2.2.2.2 (s ++ [n]) := by
    apply Set.Subset.antisymm
    · apply Set.iUnion_subset; intro j
      by_cases hj : c (s ++ [j]) = 0
      · rw [cantorNodeSet_eq_empty c hc.2.2.2.2.2 _ hj]; exact Set.empty_subset _
      · rw [huniq j hj]
    · exact Set.subset_iUnion (fun j => cantorNodeSet c hc.2.2.2.2.2 (s ++ [j])) n
  rw [cantorNodeSet_equation, hs]
  norm_num [he]

variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
  (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)
  (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔ h.value (A.val \ B.val) = 0)
  (hη : Function.Injective η) (hpos : ∀ C, η C ≠ ⊥ ↔ C.val ∈ positiveNullQuotient D F)

include h hle in
lemma internalFilter_not_select_empty (G : Order.PFilter (InternalRandomCondition D F η)) :
    ¬ ∃ p ∈ G, η (internalConditionClass η p) ≤ η (nullClassOf (F := F) ⟨∅, h.empty_mem⟩) := by
  rintro ⟨p, _, hp⟩
  exact internalCondition_not_below_disjoint h η hle ⟨∅, h.empty_mem⟩ ⟨∅, h.empty_mem⟩
    (by simp) p hp hp

lemma measurable_cantorInclusion : Measurable cantorInclusion := by
  unfold cantorInclusion
  fun_prop

include hη hpos in
lemma internalFilter_restricted_cylinder (G : Order.PFilter (InternalRandomCondition D F η))
    (x : ℕ → Bool)
    (hx : ∀ s, x ∈ cyl s ↔ randomCoinCylinder s ∈ transportPFilter (internalConditionEmbedding η hη hpos) G)
    (w : List ℕ) :
    x ∈ cantorInclusion ⁻¹' cyl w ↔
      ∃ p ∈ G, η (internalConditionClass η p) ≤
        MeasureAlgebra.mk (cantorInclusion ⁻¹' cyl w)
          ((isOpen_cyl w).measurableSet.preimage measurable_cantorInclusion) := by
  by_cases hw : ∃ v : List Bool, v.map Bool.toNat = w
  · obtain ⟨v, rfl⟩ := hw
    have hh := hx v
    rw [mem_transportPFilter] at hh
    change (x ∈ cyl v ↔ ∃ p ∈ G, η (internalConditionClass η p) ≤
      MeasureAlgebra.mk (cyl v) (isOpen_cyl v).measurableSet) at hh
    simpa only [BorelExpression.cantorInclusion_preimage_cyl] using hh
  · have he : cantorInclusion ⁻¹' cyl w = ∅ := by
      rw [CantorTreeMeasure.cantorInclusion_preimage_cyl]
      have hv : {v : List Bool | v.map Bool.toNat = w} = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        (fun v hv => hw ⟨v, hv⟩)
      rw [hv]
      simp [openFromWords]
    have hz : (MeasureAlgebra.mk (cantorInclusion ⁻¹' cyl w)
        ((isOpen_cyl w).measurableSet.preimage measurable_cantorInclusion) : MeasureAlgebra fairCoinProduct) = ⊥ :=
      (MeasureAlgebra.mk_eq_bot _ _).mpr (by rw [he]; exact measure_empty)
    apply iff_of_false (by rw [he]; exact fun h => h)
    rintro ⟨p, _, hp⟩
    exact ((hpos (internalConditionClass η p)).mpr p.property) (le_bot_iff.mp (hp.trans_eq hz))

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hrepSet : ∀ (X : D) (A : Set (ℕ → Bool)) (hm : MeasurableSet A), InternallyApproximable M A →
    RepresentsInternalSet M X.val A → η (nullClassOf (F := F) X) = MeasureAlgebra.mk A hm)

include hM hinf hpair hunion hpower hsep hrep h hle hη hpos hrepSet in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: theorem
  title: Internal Borel truth at every node
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Induct along the well-founded child relation of the code.
    An absent node has empty interpretation, and no positive condition lies below the empty class.
    At a leaf, restrict the labeled Baire cylinder to binary points.
    If its finite word contains a nonbinary entry, this restriction is empty.
    Otherwise it is a binary cylinder, whose internal class is sent to the actual cylinder class by the
    comparison map. The cylinder decisions of the transported filter therefore give the required equivalence.
    This uses the already constructed filter real, rather than an assumed atomic truth relation.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    At a union node, §{sec:internal-random-union-tests} constructs the entire internal child sequence and proves
    that the filter selects the union exactly when it selects one term. Apply the induction hypothesis to
    that child. Absent children contribute empty sets and may be included in the sequence.
    At a complement node, validity gives exactly one present child. All other children have empty interpretation,
    so the external set is the complement of that child's set and the internal set is its complement in $Y_M$.
    The preceding complement lemma and the induction hypothesis prove the equivalence at this node.
    These cases exhaust the labels, completing the induction.
-/
theorem internalGeneric_node_truth (hD : D ∈ M) (hF : F ∈ M) (hca : h.CountablyAdditiveOn M)
    (hY : internalCantor M ∈ D) (hdom : ∀ A ∈ D, A ⊆ internalCantor M)
    (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (hnode : ∀ t, internalCantorNodeSet M c hc.2.2.2.2.2 t ∈ D)
    (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G))
    (x : ℕ → Bool)
    (hx : ∀ s, x ∈ cyl s ↔ randomCoinCylinder s ∈ transportPFilter (internalConditionEmbedding η hη hpos) G)
    (s : List ℕ) :
    x ∈ cantorNodeSet c hc.2.2.2.2.2 s ↔
      ∃ p ∈ G, η (internalConditionClass η p) ≤ η (nullClassOf (F := F) ⟨_, hnode s⟩) := by
  have hzero (t) (ht : c t = 0) :
      (x ∈ cantorNodeSet c hc.2.2.2.2.2 t ↔
        ∃ p ∈ G, η (internalConditionClass η p) ≤ η (nullClassOf (F := F) ⟨_, hnode t⟩)) := by
    have he : (⟨internalCantorNodeSet M c hc.2.2.2.2.2 t, hnode t⟩ : D) = ⟨∅, h.empty_mem⟩ :=
      Subtype.ext (internalCantorNodeSet_empty M c hc.2.2.2.2.2 t ht)
    rw [he, cantorNodeSet_eq_empty c hc.2.2.2.2.2 t ht]
    exact iff_of_false (fun h => h) (internalFilter_not_select_empty h η hle G)
  induction s using hc.2.2.2.2.2.induction with
  | h s ih =>
    by_cases h0 : c s = 0
    · exact hzero s h0
    have hchildren (n) : x ∈ cantorNodeSet c hc.2.2.2.2.2 (s ++ [n]) ↔
        ∃ p ∈ G, η (internalConditionClass η p) ≤ η (nullClassOf (F := F) ⟨_, hnode (s ++ [n])⟩) := by
      by_cases hn : c (s ++ [n]) = 0
      · exact hzero _ hn
      · exact ih _ ⟨h0, n, rfl, hn⟩
    by_cases h1 : c s = 1
    · rw [modelGeneric_borel_union_witness hM hinf hpair hunion hpower hsep hrep h η hle hD hF hca
        c hc.2.2.2.2.2 hcM s h1 hnode G hG, cantorNodeSet_equation]
      simp only [h1, Nat.one_ne_zero, ite_false, ite_true, Set.mem_iUnion]
      exact exists_congr hchildren
    by_cases h2 : c s = 2
    · obtain ⟨n, _, he⟩ := cantorNodeSet_complement_child c hc s h2
      have hi := internalCantorNodeSet_compl M c hc.2.2.2.2.2 s (s ++ [n]) he
      have hsub : (⟨internalCantorNodeSet M c hc.2.2.2.2.2 s, hnode s⟩ : D) =
          ⟨internalCantor M \ internalCantorNodeSet M c hc.2.2.2.2.2 (s ++ [n]),
            h.diff_mem _ hY _ (hnode (s ++ [n]))⟩ := Subtype.ext hi
      rw [hsub, modelGeneric_complement_witness h η hle hM hpair hunion hpower hsep hrep hD hF
        ⟨_, hY⟩ ⟨_, hnode (s ++ [n])⟩ hdom G hG, he, Set.mem_compl_iff, ← hchildren n]
    · have he : cantorNodeSet c hc.2.2.2.2.2 s = cantorInclusion ⁻¹' cyl (NamedLambda.NatListCode.decode (c s - 3)) := by
        rw [cantorNodeSet_equation]
        simp only [h0, h1, h2, ite_false]
        rfl
      have hm : MeasurableSet (cantorInclusion ⁻¹' cyl (NamedLambda.NatListCode.decode (c s - 3))) :=
        (isOpen_cyl _).measurableSet.preimage measurable_cantorInclusion
      have hr : RepresentsInternalSet M (internalCantorNodeSet M c hc.2.2.2.2.2 s)
          (cantorInclusion ⁻¹' cyl (NamedLambda.NatListCode.decode (c s - 3))) :=
        ⟨fun _ hg => (ZFSet.mem_inter.mp hg).2,
          fun y => (cantorPointGraph_mem_internalCantorNodeSet M c hc.2.2.2.2.2 s y).trans (by rw [he])⟩
      rw [hrepSet ⟨_, hnode s⟩ _ hm (internallyApproximable_cylinder hM hinf hpair hunion hpower hsep _) hr, he]
      exact internalFilter_restricted_cylinder η hη hpos G x hx _

include hM hinf hpair hunion hpower hsep hrep h hle hη hpos hrepSet in
/-- The real is constructed from the generic filter; its atomic truth is not an additional assumption. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: corollary
  title: Internal random Borel truth
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The random-real name evaluates to the graph of $r_G$, so this graph belongs to $M[G]$ by
    §{sec:internal-random-filter-valuation}. The Borel interpretation in the extension consists exactly of
    its point graphs satisfying the full external interpretation. Apply the theorem at the root to obtain the
    identity. If the internal measure is zero, the comparison map sends its class to zero.
    No positive condition can lie below that value, so the right-hand side is false.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The node induction in §{sec:internal-random-borel-truth} combines the union test with the complement decision.
    It applies to the actual real constructed from the generic filter and gives
    $$r_G\in\BorelInterpretation{c}{M[G]}
    \quad\Longleftrightarrow\quad
    \exists p\in G\ (p\le q(\BorelInterpretation{c}{M})).$$
-/
theorem modelGeneric_internalBorel_truth (hD : D ∈ M) (hF : F ∈ M) (hca : h.CountablyAdditiveOn M)
    (hY : internalCantor M ∈ D) (hdom : ∀ A ∈ D, A ⊆ internalCantor M)
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)
    (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (hnode : ∀ t, internalCantorNodeSet M c hc.2.2.2.2.2 t ∈ D)
    (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G)) :
    ∃ x : ℕ → Bool,
      ForcingNames.valuation (internalFilterSet η G) (randomRealName M D F) = cantorPointGraph x ∧
      cantorPointGraph x ∈ ForcingNames.extension (positiveNullQuotient D F) M (internalFilterSet η G) ∧
      (cantorPointGraph x ∈ internalBorelCantorSet
        (ForcingNames.extension (positiveNullQuotient D F) M (internalFilterSet η G)) c hc.2.2.2.2.2 ↔
        ∃ p ∈ G, η (internalConditionClass η p) ≤ η (nullClassOf (F := F) ⟨_, hnode []⟩)) := by
  obtain ⟨x, hx, hval, hmem⟩ := modelGeneric_randomReal hM hinf hpair hunion hpower hsep hrep h η hle hcyl
    hD hF hdom hη hpos hrepSet G hG
  refine ⟨x, hval, hmem, ?_⟩
  rw [cantorPointGraph_mem_internalBorelCantorSet, and_iff_right hmem]
  exact internalGeneric_node_truth h η hle hη hpos hM hinf hpair hunion hpower hsep hrep hrepSet
    hD hF hca hY hdom c hc hcM hnode G hG x hx []

include hM hinf hpair hunion hpower hsep hrep h hle hη hpos hrepSet in
/-- A code null in the ground model cannot contain the evaluated random real in the extension. -/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: corollary
  title: Internal random Borel truth
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: statement
  kind: proposition
  title: Null-set avoidance
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    By the internal Borel truth theorem of §{sec:internal-random-borel-truth}, membership would give a
    positive condition below $q(\BorelInterpretation{c_N}{M})$.
    The measure is zero, so this class is zero, a contradiction.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termuseas{random forcing}{Random forcing}, the nonzero part of the Boolean algebra of Borel sets modulo
        Lebesgue-null sets,
        ordered by inclusion modulo null sets, adds a
        *random real*: one that avoids every null Borel set coded in the ground model — a *Lebesgue-generic* point.
-/
theorem modelGeneric_internalBorel_null_avoidance (hD : D ∈ M) (hF : F ∈ M) (hca : h.CountablyAdditiveOn M)
    (hY : internalCantor M ∈ D) (hdom : ∀ A ∈ D, A ⊆ internalCantor M)
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)
    (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (hnode : ∀ t, internalCantorNodeSet M c hc.2.2.2.2.2 t ∈ D)
    (hz : h.value (internalBorelCantorSet M c hc.2.2.2.2.2) = 0)
    (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G)) :
    ForcingNames.valuation (internalFilterSet η G) (randomRealName M D F) ∉ internalBorelCantorSet
      (ForcingNames.extension (positiveNullQuotient D F) M (internalFilterSet η G)) c hc.2.2.2.2.2 := by
  obtain ⟨x, hval, _, ht⟩ := modelGeneric_internalBorel_truth h η hle hη hpos hM hinf hpair hunion hpower hsep hrep
    hrepSet hD hF hca hY hdom hcyl c hc hcM hnode G hG
  rw [hval]
  intro hx
  obtain ⟨p, _, hp⟩ := ht.mp hx
  have hzero : η (nullClassOf (F := F) ⟨_, hnode []⟩) = ⊥ := by
    by_contra hn
    have hpos' := (class_mem_positiveNullQuotient_iff h ⟨_, hnode []⟩).mp ((hpos _).mp hn)
    exact (ne_of_gt hpos') hz
  exact ((hpos (internalConditionClass η p)).mpr p.property) (le_bot_iff.mp (hp.trans_eq hzero))

end PolishSpaceBook.CantorTreeMeasure
