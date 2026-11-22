module

public import PolishSpaceBook.InternalBorelTruth
public import PolishSpaceBook.InternalCohenBorelCodes
public import PolishSpaceBook.InternalCohenRequirements

@[expose] public section

/-! # Old singleton codes and newness of the internal generic random real

The code is the complement of the open union of finite words disagreeing with
the old real. Its whole label graph belongs to the ground model. Cylinder
normalization proves its internal value zero, before generic null avoidance
is applied to the actual random-real name.
-/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory ForcingAtomic
open Filter Topology
open NamedLambda
universe u

lemma diagonal_cylinderCode_compl (x : ℕ → Bool) :
    (cylinderCode (cohenDiagonalRequirement x))ᶜ = {x} := by
  ext y
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro hy
    funext n
    have hprefix : prefixOfSeq (seqPrefix y (n + 1)) x := by
      by_contra hn
      exact hy (mem_cylinderCode.mpr ⟨seqPrefix y (n + 1),
        fun h => hn ((cohenAgrees_iff_prefixOfSeq _ _).mp h), mem_cyl_seqPrefix y (n + 1)⟩)
    exact (seqPrefix_get y _).symm.trans (hprefix n (by simp)).symm
  · intro he hy
    subst y
    obtain ⟨s, hs, hxs⟩ := mem_cylinderCode.mp hy
    exact hs ((cohenAgrees_iff_prefixOfSeq s x).mpr hxs)

/-- A concrete code, including a fixed nonempty diagonal word for the enumeration. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, $M[G]$ sees that $r_G$ is not equal to any ground-model real. For each
    $x \in M \cap \CantorSpace$, the singleton $\{x\}$ is a Borel null set coded in $M$, ruling out $r_G = x$.
-/
def oldSingletonCode (x : ℕ → Bool) : Code :=
  cohenClosedCode (cohenDiagonalRequirement x)
    (NatListCode.encode ([!(x 0)].map Bool.toNat))

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, $M[G]$ sees that $r_G$ is not equal to any ground-model real. For each
    $x \in M \cap \CantorSpace$, the singleton $\{x\}$ is a Borel null set coded in $M$, ruling out $r_G = x$.
-/
theorem oldSingletonCode_cantor (x : ℕ → Bool) :
    (oldSingletonCode x).cantor = {x} := by
  have hs : [!(x 0)] ∈ cohenDiagonalRequirement x := by
    intro h
    have hn := h 0 (by simp)
    simp at hn
  exact (cohenClosedCode_cantor hs).trans (diagonal_cylinderCode_compl x)

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, $M[G]$ sees that $r_G$ is not equal to any ground-model real. For each
    $x \in M \cap \CantorSpace$, the singleton $\{x\}$ is a Borel null set coded in $M$, ruling out $r_G = x$.
-/
theorem oldSingletonCode_labelGraph_mem (x : ℕ → Bool) (hx : cantorPointGraph x ∈ M) :
    (oldSingletonCode x).val.labelGraph ∈ M :=
  cohenClosedCode_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _
    (cohenDiagonalRequirement_mem hM hinf hpair hunion hpower hsep x hx) _

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, $M[G]$ sees that $r_G$ is not equal to any ground-model real. For each
    $x \in M \cap \CantorSpace$, the singleton $\{x\}$ is a Borel null set coded in $M$, ruling out $r_G = x$.
-/
theorem internal_oldSingletonCode (x : ℕ → Bool) (hx : cantorPointGraph x ∈ M) :
    internalBorelCantorSet M (oldSingletonCode x).val (oldSingletonCode x).property.2.2.2.2.2 =
      {cantorPointGraph x} := by
  apply ZFSet.ext
  intro g
  constructor
  · intro hg
    obtain ⟨y, rfl, _⟩ := mem_internalCantor.mp (ZFSet.mem_inter.mp hg).2
    have hy := ((cantorPointGraph_mem_internalBorelCantorSet M _ _ y).mp hg).2
    change y ∈ (oldSingletonCode x).cantor at hy
    have he : y = x := by simpa only [oldSingletonCode_cantor, Set.mem_singleton_iff] using hy
    simp [he]
  · intro hg
    have he : g = cantorPointGraph x := ZFSet.mem_singleton.mp hg
    subst g
    apply (cantorPointGraph_mem_internalBorelCantorSet M _ _ x).mpr
    exact ⟨hx, by change x ∈ (oldSingletonCode x).cantor; rw [oldSingletonCode_cantor]; exact Set.mem_singleton x⟩

variable {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)

/-- The singleton's value is derived from finite-cylinder bounds, not assumed. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, $M[G]$ sees that $r_G$ is not equal to any ground-model real. For each
    $x \in M \cap \CantorSpace$, the singleton $\{x\}$ is a Borel null set coded in $M$, ruling out $r_G = x$.
-/
theorem internal_singleton_value_zero (x : ℕ → Bool) (hx : cantorPointGraph x ∈ M)
    (hsingle : ({cantorPointGraph x} : ZFSet.{u}) ∈ D)
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F) :
    h.value {cantorPointGraph x} = 0 := by
  apply le_antisymm _ (h.value_nonneg hsingle)
  have ht : Tendsto (fun n => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply ge_of_tendsto ht
  apply Eventually.of_forall
  intro n
  have hsub : ({cantorPointGraph x} : ZFSet.{u}) ⊆ internalWordCylinder M (seqPrefix x n) := by
    intro g hg
    rw [ZFSet.mem_singleton.mp hg]
    exact (cantorPointGraph_mem_internalWordCylinder M _ x).mpr ⟨hx, mem_cyl_seqPrefix x n⟩
  have he : h.value (internalWordCylinder M (seqPrefix x n)) = (1 / 2 : ℝ) ^ n := by
    simpa only [seqPrefix_length] using h.value_of_code (hcyl (seqPrefix x n)).1
      (show (0 : ℝ) ≤ (1 / 2) ^ (seqPrefix x n).length by positivity) (hcyl _).2
  exact (h.value_mono hsingle (hcyl _).1 hsub).trans_eq he

variable
  (η : relationQuotient D (nullRelation D F) → MeasureAlgebra fairCoinProduct)
  (hle : ∀ A B : D, η (nullClassOf (F := F) A) ≤ η (nullClassOf (F := F) B) ↔ h.value (A.val \ B.val) = 0)
  (hη : Function.Injective η) (hpos : ∀ C, η C ≠ ⊥ ↔ C.val ∈ positiveNullQuotient D F)
  (hrepSet : ∀ (X : D) (A : Set (ℕ → Bool)) (hm : MeasurableSet A), InternallyApproximable M A →
    RepresentsInternalSet M X.val A → η (nullClassOf (F := F) X) = MeasureAlgebra.mk A hm)

include hM hinf hpair hunion hpower hsep hrep h hle hη hpos hrepSet in
/-- For the full internal Borel measure domain, the actual generic name is new.
The domain hypothesis is uniform over internal codes; neither singleton
nullness nor a singleton avoidance test is an input. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular, $M[G]$ sees that $r_G$ is not equal to any ground-model real. For each
    $x \in M \cap \CantorSpace$, the singleton $\{x\}$ is a Borel null set coded in $M$, ruling out $r_G = x$.
-/
theorem modelGeneric_random_real_new (hD : D ∈ M) (hF : F ∈ M) (hca : h.CountablyAdditiveOn M)
    (hY : internalCantor M ∈ D) (hdom : ∀ A ∈ D, A ⊆ internalCantor M)
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)
    (hBorel : ∀ (c : Code), c.val.labelGraph ∈ M →
      ∀ t, internalCantorNodeSet M c.val c.property.2.2.2.2.2 t ∈ D)
    (G : Order.PFilter (InternalRandomCondition D F η))
    (hG : @ModelGeneric (positiveNullQuotient D F) M (internalConditionCodedOrder η) (codedRandomFilter η G)) :
    ∃ r : ℕ → Bool,
      ForcingNames.valuation (internalFilterSet η G) (randomRealName M D F) = cantorPointGraph r ∧
      cantorPointGraph r ∈ ForcingNames.extension (positiveNullQuotient D F) M (internalFilterSet η G) ∧
      ∀ x : ℕ → Bool, cantorPointGraph x ∈ M → r ≠ x := by
  obtain ⟨r, _, hval, hmem⟩ := modelGeneric_randomReal hM hinf hpair hunion hpower hsep hrep h η hle hcyl
    hD hF hdom hη hpos hrepSet G hG
  refine ⟨r, hval, hmem, ?_⟩
  intro x hx heq
  let c := oldSingletonCode x
  have hcM : c.val.labelGraph ∈ M := oldSingletonCode_labelGraph_mem hM hinf hpair hunion hpower hsep hrep x hx
  have hn := hBorel c hcM
  have hs : ({cantorPointGraph x} : ZFSet.{u}) ∈ D := by
    rw [← internal_oldSingletonCode x hx]
    exact hn []
  have hz : h.value (internalBorelCantorSet M c.val c.property.2.2.2.2.2) = 0 := by
    rw [internal_oldSingletonCode x hx]
    exact internal_singleton_value_zero h x hx hs hcyl
  have havoid := modelGeneric_internalBorel_null_avoidance h η hle hη hpos hM hinf hpair hunion hpower hsep hrep
    hrepSet hD hF hca hY hdom hcyl c.val c.property hcM hn hz G hG
  apply havoid
  rw [hval, heq]
  exact (cantorPointGraph_mem_internalBorelCantorSet _ _ _ x).mpr
    ⟨heq ▸ hmem, by change x ∈ c.cantor; rw [oldSingletonCode_cantor]; exact Set.mem_singleton x⟩

end PolishSpaceBook.CantorTreeMeasure
