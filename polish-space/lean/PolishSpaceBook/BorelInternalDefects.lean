module

public import PolishSpaceBook.BorelInternalConstructors
public import PolishSpaceBook.BorelRankMeasureBounds
public import PolishSpaceBook.RandomPointFilters

@[expose] public section

/-! # Coded null defects and coherent point filters -/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels MeasureTheory
open scoped symmDiff
universe u

namespace Code

def cantor (c : Code) : Set (ℕ → Bool) := cantorSet c.val c.property.2.2.2.2.2
lemma measurable_cantor (c : Code) : MeasurableSet c.cantor := measurableSet_cantorSet c.val _

def measureClass (c : Code) : MeasureAlgebra fairCoinProduct := MeasureAlgebra.mk c.cantor c.measurable_cantor

lemma cantor_compl (c : Code) : c.compl.cantor = c.cantorᶜ := by
  change cantorInclusion ⁻¹' c.compl.value cylinderBasis = (cantorInclusion ⁻¹' c.value cylinderBasis)ᶜ
  rw [value_compl]
  rfl

lemma cantor_sup (c d : Code) : (sup c d).cantor = c.cantor ∪ d.cantor := by
  change cantorInclusion ⁻¹' (sup c d).value cylinderBasis = _
  rw [value_sup]
  rfl

lemma cantor_inf (c d : Code) : (inf c d).cantor = c.cantor ∩ d.cantor := by
  change cantorInclusion ⁻¹' (inf c d).value cylinderBasis = _
  rw [value_inf]
  rfl

lemma cantor_diff (c d : Code) : (diff c d).cantor = c.cantor \ d.cantor := by
  change cantorInclusion ⁻¹' (diff c d).value cylinderBasis = _
  rw [value_diff]
  rfl

lemma cantor_symmDiff (c d : Code) : (symmDiff c d).cantor = c.cantor ∆ d.cantor := by
  change cantorInclusion ⁻¹' (symmDiff c d).value cylinderBasis = _
  rw [value_symmDiff]
  rfl

lemma cantor_iUnion (c : ℕ → Code) : (iUnion c).cantor = ⋃ n, (c n).cantor := by
  change cantorInclusion ⁻¹' (iUnion c).value cylinderBasis = _
  rw [value_iUnion, Set.preimage_iUnion]
  rfl

lemma cantor_empty : empty.cantor = ∅ := by
  change cantorInclusion ⁻¹' empty.value cylinderBasis = _
  rw [value_empty cylinderBasis (by simp [cylinderBasis, NamedLambda.NatListCode.decode])]
  rfl

lemma measureClass_compl (c : Code) : c.compl.measureClass = c.measureClassᶜ := by
  simp only [measureClass, cantor_compl]
  rfl

lemma measureClass_inf (c d : Code) : (inf c d).measureClass = c.measureClass ⊓ d.measureClass := by
  simp only [measureClass, cantor_inf]
  rfl

lemma measureClass_sup (c d : Code) : (sup c d).measureClass = c.measureClass ⊔ d.measureClass := by
  simp only [measureClass, cantor_sup]
  rfl

lemma measureClass_eq_bot_iff (c : Code) : c.measureClass = ⊥ ↔ fairCoinProduct c.cantor = 0 :=
  MeasureAlgebra.mk_eq_bot _ _

/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Coded null defects
-/
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: prose
  excerpt: |
    Apply the preceding constructors to the zero and one representatives, or to the symmetric differences
    between the representative of an operation and that operation on representatives.
    Equality of measure classes makes each symmetric difference null; the zero representative and the
    complement of the one representative are null as well. Countable subadditivity makes the coded union null.
    For the order assertion, the difference $\SetDifference{A_c}{A_d}$ has a code in $M$ and is null.
    The point $r$ cannot belong to that difference. Applying this in both directions proves the equality case.
-/
lemma symmDiff_null_of_measureClass_eq (c d : Code) (h : c.measureClass = d.measureClass) :
    fairCoinProduct (symmDiff c d).cantor = 0 := by
  rw [cantor_symmDiff]
  exact measure_symmDiff_eq_zero_iff.mpr ((MeasureAlgebra.mk_eq_mk c.measurable_cantor d.measurable_cantor).mp h)

end Code

/-- Nullness refers to the full external interpretation of a code belonging to the model. -/
def AvoidsNullCodes (M : ZFSet.{u}) (x : ℕ → Bool) : Prop :=
  ∀ c : Code, c.val.labelGraph ∈ M → fairCoinProduct c.cantor = 0 → x ∉ c.cantor

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)

include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Coded null defects
-/
lemma AvoidsNullCodes.congr {x : ℕ → Bool} (hx : AvoidsNullCodes M x)
    (c d : Code) (hc : c.val.labelGraph ∈ M) (hd : d.val.labelGraph ∈ M)
    (he : c.measureClass = d.measureClass) : x ∈ c.cantor ↔ x ∈ d.cantor := by
  have hn := hx (Code.symmDiff c d)
    (Code.symmDiff_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c d hc hd)
    (Code.symmDiff_null_of_measureClass_eq c d he)
  rw [Code.cantor_symmDiff] at hn
  simp only [Set.mem_symmDiff] at hn
  tauto

include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Coded null defects
-/
lemma AvoidsNullCodes.mono {x : ℕ → Bool} (hx : AvoidsNullCodes M x)
    (c d : Code) (hc : c.val.labelGraph ∈ M) (hd : d.val.labelGraph ∈ M)
    (he : c.measureClass ≤ d.measureClass) : x ∈ c.cantor → x ∈ d.cantor := by
  have hz : fairCoinProduct (Code.diff c d).cantor = 0 := by
    rw [Code.cantor_diff]
    exact (MeasureAlgebra.mk_le_mk_iff_null_sdiff _ _ c.measurable_cantor d.measurable_cantor).mp he
  have hn := hx (Code.diff c d) (Code.diff_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c d hc hd) hz
  rw [Code.cantor_diff] at hn
  intro hxc
  by_contra hxd
  exact hn ⟨hxc, hxd⟩

include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Coded null defects
-/
lemma coded_null_iUnion (c : ℕ → Code) (hc : sequenceGraph (fun n => (c n).val.labelGraph) ∈ M)
    (hz : ∀ n, fairCoinProduct (c n).cantor = 0) :
    (Code.iUnion c).val.labelGraph ∈ M ∧ fairCoinProduct (Code.iUnion c).cantor = 0 := by
  refine ⟨Code.iUnion_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c hc, ?_⟩
  rw [Code.cantor_iUnion, measure_iUnion_null_iff]
  exact hz

/-- The chosen representative for each algebra element is an entire code in the model. -/
def codeRepresentatives (A : BooleanSubalgebra (MeasureAlgebra fairCoinProduct)) (c : A → Code) :
    A → MeasuredSets fairCoinProduct := fun a => ⟨(c a).cantor, (c a).measurable_cantor⟩

include hM hinf hpair hunion hpower hsep hrep in
/-@ booklink:
  source: polish-space-book/appendix-random-forcing.md
  target: statement
  kind: lemma
  title: Coded null defects
-/
lemma AvoidsNullCodes.outside_defects {x : ℕ → Bool} (hx : AvoidsNullCodes M x)
    (A : BooleanSubalgebra (MeasureAlgebra fairCoinProduct)) (c : A → Code)
    (hc : ∀ a, (c a).val.labelGraph ∈ M) (hr : ∀ a, (c a).measureClass = a.val) :
    x ∉ MeasureAlgebra.representativeDefect A (codeRepresentatives A c) := by
  have hb : x ∉ (c ⊥).cantor := hx _ (hc _) ((Code.measureClass_eq_bot_iff _).mp (hr _))
  have ht : x ∈ (c ⊤).cantor := by
    have hn := hx (c ⊤).compl (Code.compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _ (hc _))
      ((Code.measureClass_eq_bot_iff _).mp (by rw [Code.measureClass_compl, hr]; exact compl_top))
    simpa only [Code.cantor_compl, Set.mem_compl_iff, not_not] using hn
  have hi (a b : A) : x ∈ (c (a ⊓ b)).cantor ↔ x ∈ (c a).cantor ∧ x ∈ (c b).cantor := by
    have he := hx.congr hM hinf hpair hunion hpower hsep hrep (c (a ⊓ b)) (Code.inf (c a) (c b)) (hc _)
      (Code.inf_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _ _ (hc a) (hc b))
      (by rw [Code.measureClass_inf, hr, hr, hr]; rfl)
    simpa only [Code.cantor_inf, Set.mem_inter_iff] using he
  have hcomp (a : A) : x ∈ (c aᶜ).cantor ↔ x ∉ (c a).cantor := by
    have he := hx.congr hM hinf hpair hunion hpower hsep hrep (c aᶜ) (c a).compl (hc _)
      (Code.compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _ (hc a))
      (by rw [Code.measureClass_compl, hr, hr]; rfl)
    simpa only [Code.cantor_compl, Set.mem_compl_iff] using he
  simp only [MeasureAlgebra.representativeDefect, codeRepresentatives, Set.mem_union, Set.mem_compl_iff,
    Set.mem_iUnion, Set.mem_symmDiff, Set.mem_inter_iff, not_or, not_exists]
  exact ⟨⟨⟨hb, not_not.mpr ht⟩, fun a b => by have := hi a b; tauto⟩,
    fun a => by have := hcomp a; tauto⟩

/-- This filter is obtained from the actual point-membership tests in the chosen coded representatives. -/
def codedPointFragmentFilter {x : ℕ → Bool} (hx : AvoidsNullCodes M x)
    (A : BooleanSubalgebra (MeasureAlgebra fairCoinProduct)) (c : A → Code)
    (hc : ∀ a, (c a).val.labelGraph ∈ M) (hr : ∀ a, (c a).measureClass = a.val) :
    Order.PFilter (MeasureAlgebra.FragmentPositive A) :=
  MeasureAlgebra.pointFragmentFilter A (codeRepresentatives A c) x
    (hx.outside_defects hM hinf hpair hunion hpower hsep hrep A c hc hr)

lemma mem_codedPointFragmentFilter {x : ℕ → Bool} (hx : AvoidsNullCodes M x)
    (A : BooleanSubalgebra (MeasureAlgebra fairCoinProduct)) (c : A → Code)
    (hc : ∀ a, (c a).val.labelGraph ∈ M) (hr : ∀ a, (c a).measureClass = a.val)
    (a : MeasureAlgebra.FragmentPositive A) :
    a ∈ codedPointFragmentFilter hM hinf hpair hunion hpower hsep hrep hx A c hc hr ↔ x ∈ (c a.val).cantor := Iff.rfl

end PolishSpaceBook.BorelExpression
