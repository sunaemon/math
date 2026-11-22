module

public import PolishSpaceBook.BorelLabelDescriptions
public import PolishSpaceBook.BorelCylinderLimits

@[expose] public section

/-! # Internal nonconvergence codes from an internal comparison relation

The comparison relation records which triples (tolerance, tail bound, cylinder)
pass the deviation test. A single bounded label definition constructs the
whole nested union/intersection code. Internality of that comparison relation
must be proved from the particular real-valued cylinder data.
-/

noncomputable section
namespace PolishSpaceBook.BorelExpression
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BoundedSetPredicate
open NamedLambda
open scoped Classical
universe u

/-- Shared label-description parameters, then tolerance and tail bound. -/
def limitLabelValues (D : ZFSet.{u}) : Fin 11 → ZFSet.{u} :=
  ![Ordinal.omega0.toZFSet, natOrdinal 0, finiteSequences, wordGraph [],
    natOrdinal 1, natOrdinal 2, natOrdinal 3, naturalBinaryGraph (fun a b => a + b),
    Code.empty.val.labelGraph, D, graphRange D]

/-- The candidate triple lies in the comparison relation. -/
def deviationTriplePredicate : BoundedSetPredicate 16 :=
  .ex 10 (.conj (.pairMember 9 11 16) (.orderedPair 16 12 13))

lemma eval_deviationTriplePredicate (D : ZFSet.{u}) (k N j : ℕ) (s : List ℕ) (y : ZFSet.{u}) :
    deviationTriplePredicate.eval
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (limitLabelValues D)
        (natOrdinal k)) (natOrdinal N)) (natOrdinal j)) (wordGraph s)) y) ↔
      pair (natOrdinal k) (pair (natOrdinal N) (natOrdinal j)) ∈ D := by
  change (∃ t ∈ graphRange D, pair (natOrdinal k) t ∈ D ∧
    t = pair (natOrdinal N) (natOrdinal j)) ↔ _
  constructor
  · rintro ⟨t, _, ht, rfl⟩
    exact ht
  · intro h
    exact ⟨_, mem_graphRange.mpr ⟨_, h⟩, h, rfl⟩

/-- A selected leaf is basic j; a discarded leaf is the fixed empty code. -/
def selectedLimitLeafDescription : BoundedSetPredicate 16 :=
  .disj (.conj deviationTriplePredicate
      (.disj (.conj (.equal 14 3) (binaryMemberAt 7 13 6 15))
        (.conj (.neg (.equal 14 3)) (.equal 15 1))))
    (.conj (.neg deviationTriplePredicate) (.pairMember 8 14 15))

lemma eval_selectedLimitLeafDescription (D : ZFSet.{u}) (k N j : ℕ) (s : List ℕ) (y : ZFSet.{u}) :
    selectedLimitLeafDescription.eval
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (limitLabelValues D)
        (natOrdinal k)) (natOrdinal N)) (natOrdinal j)) (wordGraph s)) y) ↔
      y = natOrdinal ((if pair (natOrdinal k) (pair (natOrdinal N) (natOrdinal j)) ∈ D
        then Code.leaf j else Code.empty).val s) := by
  simp only [selectedLimitLeafDescription, eval, eval_deviationTriplePredicate]
  change ((pair (natOrdinal k) (pair (natOrdinal N) (natOrdinal j)) ∈ D ∧
    ((wordGraph s = wordGraph [] ∧
      (binaryMemberAt 7 13 6 15).eval
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (limitLabelValues D)
          (natOrdinal k)) (natOrdinal N)) (natOrdinal j)) (wordGraph s)) y)) ∨
      (wordGraph s ≠ wordGraph [] ∧ y = natOrdinal 0))) ∨
    (pair (natOrdinal k) (pair (natOrdinal N) (natOrdinal j)) ∉ D ∧
      pair (wordGraph s) y ∈ Code.empty.val.labelGraph)) ↔ _
  rw [eval_binaryMemberAt]
  change ((_ ∧ ((wordGraph s = wordGraph [] ∧
    pair (pair (natOrdinal j) (natOrdinal 3)) y ∈ naturalBinaryGraph (fun a b => a + b)) ∨
      (wordGraph s ≠ wordGraph [] ∧ y = natOrdinal 0))) ∨ (_ ∧ _)) ↔ _
  rw [pair_mem_naturalBinaryGraph, pair_mem_labelGraph]
  by_cases h : pair (natOrdinal k) (pair (natOrdinal N) (natOrdinal j)) ∈ D
  · cases s <;> simp [h, Code.leaf, basic, wordGraph_injective.eq_iff]
  · simp [h]

def deviationTailDescription : BoundedSetPredicate 15 :=
  graftLabelDescription selectedLimitLeafDescription 0 1 2 3 4

def complementedTailDescription : BoundedSetPredicate 15 :=
  complementLabelDescription deviationTailDescription 0 1 2 3 5

def tailUnionDescription : BoundedSetPredicate 14 :=
  graftLabelDescription complementedTailDescription 0 1 2 3 4

def tailIntersectionDescription : BoundedSetPredicate 14 :=
  complementLabelDescription tailUnionDescription 0 1 2 3 5

def nonconvergenceDescription : BoundedSetPredicate 13 :=
  graftLabelDescription tailIntersectionDescription 0 1 2 3 4

variable (D : ZFSet.{u}) (f : List ℕ → ℝ) (b : ℝ)
  (hD : ∀ k N j, pair (natOrdinal k) (pair (natOrdinal N) (natOrdinal j)) ∈ D ↔
    N ≤ (NatListCode.decode j).length ∧ 1 / (k + 1 : ℝ) ≤ dist (f (NatListCode.decode j)) b)

include hD

lemma eval_deviationTailDescription (k N : ℕ) (s : List ℕ) (y : ZFSet.{u}) :
    deviationTailDescription.eval
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (limitLabelValues D) (natOrdinal k))
        (natOrdinal N)) (wordGraph s)) y) ↔
      y = natOrdinal ((Code.deviationTail f b k N).val s) := by
  dsimp only [deviationTailDescription, Code.deviationTail, Code.selectedCylinders, Code.iUnion, union]
  refine (eval_graftLabelDescription selectedLimitLeafDescription 0 1 2 3 4
    (Fin.snoc (Fin.snoc (limitLabelValues D) (natOrdinal k)) (natOrdinal N)) 1 rfl rfl rfl rfl rfl
    (fun j => (@ite Code (N ≤ (NatListCode.decode j).length ∧
      1 / (k + 1 : ℝ) ≤ dist (f (NatListCode.decode j)) b)
        (Classical.propDecidable _) (Code.leaf j) Code.empty).val)
    ?_ s y)
  intro j t v
  have h := eval_selectedLimitLeafDescription D k N j t v
  by_cases htest : N ≤ (NatListCode.decode j).length ∧
      1 / (k + 1 : ℝ) ≤ dist (f (NatListCode.decode j)) b
  · have hmem := (hD k N j).mpr htest
    simpa only [ite_eq_left hmem, ite_eq_left htest] using h
  · have hmem := mt (hD k N j).mp htest
    simpa only [ite_eq_right hmem, ite_eq_right htest] using h

lemma eval_complementedTailDescription (k N : ℕ) (s : List ℕ) (y : ZFSet.{u}) :
    complementedTailDescription.eval
      (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc (limitLabelValues D) (natOrdinal k))
        (natOrdinal N)) (wordGraph s)) y) ↔
      y = natOrdinal ((Code.deviationTail f b k N).compl.val s) := by
  exact eval_complementLabelDescription deviationTailDescription 0 1 2 3 5
    (Fin.snoc (Fin.snoc (limitLabelValues D) (natOrdinal k)) (natOrdinal N)) rfl rfl rfl rfl rfl
    (Code.deviationTail f b k N).val (eval_deviationTailDescription D f b hD k N) s y

lemma eval_tailUnionDescription (k : ℕ) (s : List ℕ) (y : ZFSet.{u}) :
    tailUnionDescription.eval
      (Fin.snoc (Fin.snoc (Fin.snoc (limitLabelValues D) (natOrdinal k)) (wordGraph s)) y) ↔
      y = natOrdinal ((Code.iUnion fun N => (Code.deviationTail f b k N).compl).val s) := by
  exact eval_graftLabelDescription complementedTailDescription 0 1 2 3 4
    (Fin.snoc (limitLabelValues D) (natOrdinal k)) 1 rfl rfl rfl rfl rfl
    (fun N => (Code.deviationTail f b k N).compl.val)
    (eval_complementedTailDescription D f b hD k) s y

lemma eval_tailIntersectionDescription (k : ℕ) (s : List ℕ) (y : ZFSet.{u}) :
    tailIntersectionDescription.eval
      (Fin.snoc (Fin.snoc (Fin.snoc (limitLabelValues D) (natOrdinal k)) (wordGraph s)) y) ↔
      y = natOrdinal ((Code.iInter fun N => Code.deviationTail f b k N).val s) := by
  exact eval_complementLabelDescription tailUnionDescription 0 1 2 3 5
    (Fin.snoc (limitLabelValues D) (natOrdinal k)) rfl rfl rfl rfl rfl
    (Code.iUnion fun N => (Code.deviationTail f b k N).compl).val
    (eval_tailUnionDescription D f b hD k) s y

theorem eval_nonconvergenceDescription (s : List ℕ) (y : ZFSet.{u}) :
    nonconvergenceDescription.eval (Fin.snoc (Fin.snoc (limitLabelValues D) (wordGraph s)) y) ↔
      y = natOrdinal ((Code.nonconvergence f b).val s) := by
  exact eval_graftLabelDescription tailIntersectionDescription 0 1 2 3 4
    (limitLabelValues D) 1 rfl rfl rfl rfl rfl
    (fun k => (Code.iInter fun N => Code.deviationTail f b k N).val)
    (eval_tailIntersectionDescription D f b hD) s y

variable {M : ZFSet.{u}} (hM : M.IsTransitive)
  (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
  (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
  (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
  (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)

include hM hinf hpair hunion hpower hsep hrep

omit hD in
lemma limitLabelValues_mem (hDM : D ∈ M) (i : Fin 11) : limitLabelValues D i ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hn (n : ℕ) : natOrdinal n ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) hΩ
  have hW := finiteSequences_mem hM hinf hpair hunion hpower hsep
  have hempty : (Code.empty.val.labelGraph : ZFSet.{u}) ∈ M :=
    Code.compl_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _
      (basic_labelGraph_mem hM hinf hpair hunion hpower hsep hrep 0)
  fin_cases i
  · exact hΩ
  · exact hn 0
  · exact hW
  · exact hM.mem_trans (mem_finiteSequences.mpr ⟨[], rfl⟩) hW
  · exact hn 1
  · exact hn 2
  · exact hn 3
  · exact naturalAdditionGraph_mem hM hinf hpair hunion hpower hsep
  · exact hempty
  · exact hDM
  · exact graphRange_mem hM hunion (hsep _) hDM

/-- The outer union uses a collected internal sequence of entire intersection-code graphs. -/
theorem tailIntersection_labelGraphs_mem (hDM : D ∈ M) :
    sequenceGraph (fun k => (Code.iInter fun N => Code.deviationTail f b k N).val.labelGraph) ∈ M := by
  let ps : Fin 11 → M := fun i => ⟨limitLabelValues D i,
    limitLabelValues_mem D hM hinf hpair hunion hpower hsep hrep hDM i⟩
  apply bounded_labelGraphFamily_mem hM hinf hpair hunion hpower hsep hrep
    tailIntersectionDescription ps 2 0 rfl rfl
    (fun k => (Code.iInter fun N => Code.deviationTail f b k N).val)
  intro k s y
  exact eval_tailIntersectionDescription D f b hD k s y

/-- An internal comparison relation suffices to construct the entire nonconvergence code. -/
theorem Code.nonconvergence_labelGraph_mem (hDM : D ∈ M) :
    (Code.nonconvergence f b).val.labelGraph ∈ M :=
  Code.iUnion_labelGraph_mem hM hinf hpair hunion hpower hsep hrep _
    (tailIntersection_labelGraphs_mem D f b hD hM hinf hpair hunion hpower hsep hrep hDM)

end PolishSpaceBook.BorelExpression
