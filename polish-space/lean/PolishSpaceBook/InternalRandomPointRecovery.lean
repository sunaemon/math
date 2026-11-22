module

public import PolishSpaceBook.InternalRandomPointFilter
public import PolishSpaceBook.InternalBorelTruth

@[expose] public section

/-! # The point construction recovers an existing internal generic filter -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory ForcingAtomic
universe u

variable {M D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
  (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)
  (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔ h.value (A.val \ B.val) = 0)
  (hη : Function.Injective η) (hpos : ∀ C, η C ≠ ⊥ ↔ C.val ∈ positiveNullQuotient D F)
  (hM : M.IsTransitive) (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
  (hrepSet : ∀ (X : D) (A : Set (ℕ → Bool)) (hm : MeasurableSet A), InternallyApproximable M A →
    RepresentsInternalSet M X.val A → η (nullClassOf (F := F) X) = MeasureAlgebra.mk A hm)
  (hD : D ∈ M) (hF : F ∈ M) (hca : h.CountablyAdditiveOn M)
  (hY : internalCantor M ∈ D) (hdom : ∀ A ∈ D, A ⊆ internalCantor M)
  (hcode : ∀ (c : Code), c.val.labelGraph ∈ M → internalBorelCantorSet M c.val c.property.2.2.2.2.2 ∈ D)
  (himage : ∀ (c : Code) (hc : c.val.labelGraph ∈ M),
    η (nullClassOf (F := F) ⟨_, hcode c hc⟩) = c.measureClass)

include hM hinf hpair hunion hpower hsep hrep hcode in
lemma internalBorelNode_mem_domain (c : Code) (hc : c.val.labelGraph ∈ M) (s : List ℕ) :
    internalCantorNodeSet M c.val c.property.2.2.2.2.2 s ∈ D := by
  have hh := hcode ⟨c.val.nodeCode s, valid_nodeCode c.val c.property s⟩
    (nodeCode_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c.val hc s)
  change internalInterpretation M (c.val.nodeCode s) _ NamedLambda.NatListCode.decode [] ∩ internalCantor M ∈ D at hh
  rw [internalInterpretation_nodeCode M c.val c.property NamedLambda.NatListCode.decode
    (by simp [NamedLambda.NatListCode.decode]) s] at hh
  exact hh

include h hle hη hpos hM hinf hpair hunion hpower hsep hrep hrepSet hD hF hca hY hdom hcode himage in
lemma generic_coded_membership (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G))
    (x : ℕ → Bool)
    (hx : ∀ s, x ∈ cyl s ↔ randomCoinCylinder s ∈ transportPFilter (internalConditionEmbedding η hη hpos) G)
    (c : Code) (hc : c.val.labelGraph ∈ M) :
    x ∈ c.cantor ↔ ∃ p ∈ G, η (internalConditionClass η p) ≤ c.measureClass := by
  have ht := internalGeneric_node_truth h η hle hη hpos hM hinf hpair hunion hpower hsep hrep hrepSet
    hD hF hca hY hdom c.val c.property hc
    (internalBorelNode_mem_domain hM hinf hpair hunion hpower hsep hrep hcode c hc) G hG x hx []
  change x ∈ c.cantor ↔ ∃ p ∈ G, η (internalConditionClass η p) ≤
    η (nullClassOf (F := F) ⟨_, hcode c hc⟩) at ht
  rwa [himage c hc] at ht

include h hle hη hpos hM hinf hpair hunion hpower hsep hrep hrepSet hD hF hca hY hdom hcode himage in
lemma generic_real_avoidsNullCodes (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G))
    (x : ℕ → Bool)
    (hx : ∀ s, x ∈ cyl s ↔ randomCoinCylinder s ∈ transportPFilter (internalConditionEmbedding η hη hpos) G) :
    AvoidsNullCodes M x := by
  intro c hc hz hxc
  obtain ⟨p, _, hp⟩ := (generic_coded_membership h η hle hη hpos hM hinf hpair hunion hpower hsep hrep
    hrepSet hD hF hca hY hdom hcode himage G hG x hx c hc).mp hxc
  rw [(Code.measureClass_eq_bot_iff c).mpr hz] at hp
  exact ((hpos _).mpr p.property) (le_bot_iff.mp hp)

include h hle hη hpos hM hinf hpair hunion hpower hsep hrep hrepSet hD hF hca hY hdom hcode himage in
theorem internalPointFilter_recovers_generic (hcodes : HasInternalBorelRepresentatives M D)
    (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G))
    (x : ℕ → Bool)
    (hx : ∀ s, x ∈ cyl s ↔ randomCoinCylinder s ∈ transportPFilter (internalConditionEmbedding η hη hpos) G)
    (havoid : AvoidsNullCodes M x) :
    internalPointFilter η hpos hcode himage hM hinf hpair hunion hpower hsep hrep havoid = G := by
  ext p
  let A := nullClassRepresentative (internalConditionClass η p)
  have heA : nullClassOf (F := F) A = internalConditionClass η p := Subtype.ext (nullClassRepresentative_spec _)
  obtain ⟨c, hc, hcM, hcA⟩ := hcodes A
  let d : Code := ⟨c, hc⟩
  have hed : η (internalConditionClass η p) = d.measureClass := by
    have he : (⟨internalBorelCantorSet M c hc.2.2.2.2.2, hcode d hcM⟩ : D) = A := Subtype.ext hcA
    rw [← heA, ← he]
    exact himage d hcM
  change p ∈ internalPointFilter η hpos hcode himage hM hinf hpair hunion hpower hsep hrep havoid ↔ p ∈ G
  rw [mem_internalPointFilter_iff η hpos hcode himage hM hinf hpair hunion hpower hsep hrep havoid p d hcM hed,
    generic_coded_membership h η hle hη hpos hM hinf hpair hunion hpower hsep hrep hrepSet
      hD hF hca hY hdom hcode himage G hG x hx d hcM, ← hed]
  exact ⟨fun ⟨q, hq, hqp⟩ => G.mem_of_le hqp hq, fun hp => ⟨p, hp, le_rfl⟩⟩

include h hle hη hpos hM hinf hpair hunion hpower hsep hrep hrepSet hD hF hca hY hdom hcode himage in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: corollary
  title: Recovery of an internal generic filter
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Now suppose a real $r$ avoids every Borel null set coded in $M$.
    The construction in §{sec:internal-random-point-filters} puts the complement, intersection, and symmetric-difference
    codes in $M$ and uses their null defects to build a filter $G_r$ on the internal positive order.
    For every ground-model coded representative $B$ of a condition $p$,
    $$p\in G_r\quad\Longleftrightarrow\quad r\in B.$$
    The filter is independent of the representatives. Applied to the real of an existing $M$-generic filter $G$,
    the same construction recovers $G$ exactly.
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    The random-real construction supplies the actual real and its cylinder decisions.
    Every node of a ground-model code has an internal re-rooted code, so its interpretation belongs to $D$.
    Thus §{sec:internal-random-borel-truth} applies to every such code and proves the asserted null-set avoidance.
    For a condition $p$, choose a coded representative $c$. The point-filter criterion and Borel truth give
    $$p\in G_{r_G}\ \Longleftrightarrow\ r_G\in A_c
    \ \Longleftrightarrow\ \exists t\in G\ (t\le p)
    \ \Longleftrightarrow\ p\in G.$$
    The last equivalence is upward closure, with $p$ itself witnessing the reverse implication.
-/
theorem modelGeneric_pointFilter_recovery (hcodes : HasInternalBorelRepresentatives M D)
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)
    (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G)) :
    ∃ x : ℕ → Bool, ∃ havoid : AvoidsNullCodes M x,
      ForcingNames.valuation (internalFilterSet η G) (randomRealName M D F) = cantorPointGraph x ∧
      internalPointFilter η hpos hcode himage hM hinf hpair hunion hpower hsep hrep havoid = G := by
  obtain ⟨x, hx, hv, _⟩ := modelGeneric_randomReal hM hinf hpair hunion hpower hsep hrep h η hle hcyl
    hD hF hdom hη hpos hrepSet G hG
  have havoid := generic_real_avoidsNullCodes h η hle hη hpos hM hinf hpair hunion hpower hsep hrep hrepSet
    hD hF hca hY hdom hcode himage G hG x hx
  exact ⟨x, havoid, hv, internalPointFilter_recovers_generic h η hle hη hpos hM hinf hpair hunion hpower hsep hrep
    hrepSet hD hF hca hY hdom hcode himage hcodes G hG x hx havoid⟩

end PolishSpaceBook.CantorTreeMeasure
