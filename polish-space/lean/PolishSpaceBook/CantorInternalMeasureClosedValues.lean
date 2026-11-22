module

public import PolishSpaceBook.CantorInternalMeasureFiniteValues
public import PolishSpaceBook.InternalCountableAdditivity

@[expose] public section

/-! # Closed values of the internal measure from its countable-additivity instances -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ForcingFormulas ZFSet SetTheoryModels BorelExpression MeasureTheory
universe u

lemma finiteMeasure_level_domain {D R F : ZFSet.{u}} (h : FiniteAdditiveCutGraph D R F)
    (M : ZFSet.{u}) (T : Set (List Bool)) (n : ℕ)
    (hcyl : ∀ s ∈ level T n, internalWordCylinder M (List.ofFn s) ∈ D) :
    internalLevelSet M T n ∈ D := by
  rw [← listUnion_levelCylinderList]
  exact h.listUnion_mem _ ((forall_levelCylinderList M T n (fun A => A ∈ D)).mpr hcyl)

lemma sequenceIntersection_internalLevelSet (M : ZFSet.{u}) (T : Set (List Bool)) :
    sequenceIntersection (internalLevelSet M T) = internalLevelIntersection M T := by
  ext g
  rw [mem_sequenceIntersection]
  unfold internalLevelIntersection
  rw [ZFSet.mem_sep]
  refine ⟨fun hg => ⟨?_, hg⟩, fun hg => hg.2⟩
  have hg0 := hg 0
  unfold internalLevelSet internalCylinderUnion at hg0
  exact (ZFSet.mem_sep.mp hg0).1

/-- The usual internal measure's closed value, not merely an externally constructed cut. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Closed values from the internal measure axioms
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Apply continuity from above to $A_n=\InternalTreeLevel{M}{T}{n}$.
    The entire decreasing family is internal by §{sec:internal-borel-measure-cut}, and its
    intersection is $\InternalTreeBody{M}{T}$. Each level lies in $D$ as a finite union of basic cylinders.
    Its value code is $\TreeLevelMeasureCode{T}{n}$ by §{sec:internal-finite-measure-laws}.
    Consequently the code at the intersection is the rounded infimum of this sequence, which equals
    $\NonnegativeRealCut{\mu(\TreeBody{T})}$ by §{sec:internal-real-cut-addition}.
    Decode this equality to obtain the numerical identity.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Work first in $M$. Finite additivity and the fair-coin cylinder values give the measure of every finite
    union of cylinders. Internal countable additivity gives continuity from above for the decreasing
    finite-level approximations to a closed tree. §{sec:internal-finite-measure-laws} verifies
    that the entire families used here belong to $M$, and identifies their closed-set value codes with the
    external closed measures.
-/
theorem countableMeasure_code_closed {M D R F : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (h : FiniteAdditiveCutGraph D R F) (hca : h.ModelsCountableAdditivity M)
    (T : Set (List Bool)) (hT : IsSubtree T) (hTM : wordTreeSet (binaryLift T) ∈ M)
    (hcyl : ∀ n, ∀ s ∈ level T n, internalWordCylinder M (List.ofFn s) ∈ D ∧
      pair (internalWordCylinder M (List.ofFn s)) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ n)) ∈ F) :
    internalLevelIntersection M T ∈ D ∧
      h.code (internalLevelIntersection M T) = nonnegativeRealCutCode (fairCoinProduct.real (treeBody T)) := by
  have hG := internalLevelSet_sequence_mem hM hinf hpair hunion hpower hsep hrep T hTM
  have hA n := finiteMeasure_level_domain h M T n (fun s hs => (hcyl n s hs).1)
  have ha : Antitone (fun n => (internalLevelSet M T n : Set ZFSet)) :=
    fun _ _ hmn => internalLevelSet_antitone M hT hmn
  have hc := h.countablyAdditiveOn_of_model hM hca
  have hi := (h.continuity_from_above hM hinf hpair hunion hsep hrep hc _ hG hA ha).1
  have he := h.code_intersection_eq_infimum hM hinf hpair hunion hsep hrep hc _ hG hA ha
  rw [sequenceIntersection_internalLevelSet] at hi he
  refine ⟨hi, he.trans ?_⟩
  have hs : (fun n => h.code (internalLevelSet M T n)) = levelMeasureCode T :=
    funext (fun n => finiteMeasure_code_level h M T n (hcyl n))
  rw [hs, roundedInf_levelMeasureCode hT]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Closed values from the internal measure axioms
-/
theorem countableMeasure_value_closed {M D R F : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (h : FiniteAdditiveCutGraph D R F) (hca : h.ModelsCountableAdditivity M)
    (T : Set (List Bool)) (hT : IsSubtree T) (hTM : wordTreeSet (binaryLift T) ∈ M)
    (hcyl : ∀ n, ∀ s ∈ level T n, internalWordCylinder M (List.ofFn s) ∈ D ∧
      pair (internalWordCylinder M (List.ofFn s)) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ n)) ∈ F) :
    h.value (internalLevelIntersection M T) = fairCoinProduct.real (treeBody T) := by
  unfold FiniteAdditiveCutGraph.value
  rw [(countableMeasure_code_closed hM hinf hpair hunion hpower hsep hrep h hca T hT hTM hcyl).2,
    decode_nonnegativeRealCutCode measureReal_nonneg]


/-- Package the closed-value theorem uniformly over all internal binary trees. -/
theorem countableMeasure_closed_values {M D R F : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (h : FiniteAdditiveCutGraph D R F) (hca : h.ModelsCountableAdditivity M)
    (hcyl : ∀ s : List Bool, internalWordCylinder M s ∈ D ∧
      pair (internalWordCylinder M s) (nonnegativeRealCutCode ((1 / 2 : ℝ) ^ s.length)) ∈ F)
    (T : Set (List Bool)) (hT : IsSubtree T) (hTM : wordTreeSet (binaryLift T) ∈ M) :
    internalLevelIntersection M T ∈ D ∧
      h.value (internalLevelIntersection M T) = fairCoinProduct.real (treeBody T) := by
  have hn n (s : Fin n → Bool) (_ : s ∈ level T n) := hcyl (List.ofFn s)
  simp only [List.length_ofFn] at hn
  exact ⟨(countableMeasure_code_closed hM hinf hpair hunion hpower hsep hrep h hca T hT hTM hn).1,
    countableMeasure_value_closed hM hinf hpair hunion hpower hsep hrep h hca T hT hTM hn⟩

end PolishSpaceBook.CantorTreeMeasure
