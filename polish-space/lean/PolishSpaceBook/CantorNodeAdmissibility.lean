module

public import PolishSpaceBook.BorelNodeCodes
public import PolishSpaceBook.CantorApproximationAdmissibility

@[expose] public section

/-! # The same admissibility test at every Borel node, including absent nodes -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
universe u

/-- The external binary interpretation at a specified node. -/
def cantorNodeSet (c : BorelExpression) (hw : WellFounded c.Child) (s : List ℕ) : Set (ℕ → Bool) :=
  cantorInclusion ⁻¹' c.evaluate hw cylinderBasis s

lemma cantorNodeSet_eq_empty (c : BorelExpression) (hw : WellFounded c.Child)
    (s : List ℕ) (hs : c s = 0) : cantorNodeSet c hw s = ∅ := by
  unfold cantorNodeSet
  rw [c.evaluate_isEvaluation]
  simp [hs]

lemma cantorSet_nodeCode (c : BorelExpression) (hc : c.Valid) (s : List ℕ) :
    cantorSet (c.nodeCode s) (valid_nodeCode c hc s).2.2.2.2.2 = cantorNodeSet c hc.2.2.2.2.2 s := by
  unfold BorelExpression.cantorSet cantorNodeSet
  rw [evaluate_nodeCode c hc cylinderBasis (by
    change cyl (NamedLambda.NatListCode.decode 0) = Set.univ
    rw [show NamedLambda.NatListCode.decode 0 = [] from NamedLambda.NatListCode.decode_encode [], cyl_nil])]

lemma nodeApproximationValues_eq (M : ZFSet.{u}) (c : BorelExpression) (hc : c.Valid)
    (s : List ℕ) (T S : Set (List Bool)) (a b : ℕ) :
    nodeApproximationValues M c hc.2.2.2.2.2 s (wordTreeSet (binaryLift T)) (wordTreeSet (binaryLift S)) a b =
      approximationParams M (c.nodeCode s) (valid_nodeCode c hc s).2.2.2.2.2 T S a b := by
  simp only [approximationParams, nodeApproximationValues,
    internalInterpretation_nodeCode M c hc NamedLambda.NatListCode.decode (NamedLambda.NatListCode.decode_encode []) s]

/-- Re-rooting reduces the complete nodewise test to the already proved root theorem. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Admissibility at every node
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The bounded tree tests decode each accepted set as the full code of a downward-closed binary tree.
    Apply the root admissibility theorem to $\eta_s$ from the proposition. Its internal and external
    interpretations are exactly $B_s$ and $A_s$, while all arithmetic, word, and point parameters remain
    the same. This proves the equivalence, including for absent nodes. The internal-totality lemma of
    §{sec:internal-approximation-errors}, applied to the same code, proves the final assertion.
-/
theorem node_approximationAdmissible_absolute {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (s : List ℕ) (T S : Set (List Bool))
    (hT : wordTreeSet (binaryLift T) ∈ M) (hS : wordTreeSet (binaryLift S) ∈ M)
    (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (p : Fin 12 → M)
    (hp : Subtype.val ∘ p = nodeApproximationValues M c hc.2.2.2.2.2 s
      (wordTreeSet (binaryLift T)) (wordTreeSet (binaryLift S)) a b) :
    approximationAdmissibleFormula.Realize Empty.elim p ↔
      IsSubtree T ∧ IsSubtree S ∧
        (treeBody T ⊆ cantorNodeSet c hc.2.2.2.2.2 s ∧
          cantorNodeSet c hc.2.2.2.2.2 s ⊆ (treeBody S)ᶜ) ∧
        fairCoinProduct.real (treeBody T ∪ treeBody S)ᶜ < (a : ℝ) / b := by
  have hc' := nodeCode_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c hcM s
  let q : Fin 12 → M := fun i => ⟨approximationParams M (c.nodeCode s) (valid_nodeCode c hc s).2.2.2.2.2 T S a b i,
    approximationParams_mem hM hinf hpair hunion hpower hsep _ _ hc' T S hT hS a b i⟩
  have he : p = q := by
    funext i
    apply Subtype.ext
    exact congrFun (hp.trans (nodeApproximationValues_eq M c hc s T S a b)) i
  rw [he]
  simpa only [cantorSet_nodeCode c hc s] using
    approximationAdmissible_absolute hM hinf hpair hunion hpower hsep hrep hchoice
      (c.nodeCode s) (valid_nodeCode c hc s) hc' T S hT hS a b hb hab

/-- The induction hypothesis supplies internal witnesses even at absent children. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Admissibility at every node
-/
theorem exists_admissible_at_node {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (s : List ℕ) (hA : InternallyApproximable M (cantorNodeSet c hc.2.2.2.2.2 s))
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    ∃ T S : Set (List Bool), ∃ _ : wordTreeSet (binaryLift T) ∈ M,
      ∃ _ : wordTreeSet (binaryLift S) ∈ M,
      ∃ p : Fin 12 → M,
        Subtype.val ∘ p = nodeApproximationValues M c hc.2.2.2.2.2 s
          (wordTreeSet (binaryLift T)) (wordTreeSet (binaryLift S)) a b ∧
        approximationAdmissibleFormula.Realize Empty.elim p := by
  have hc' := nodeCode_labelGraph_mem hM hinf hpair hunion hpower hsep hrep c hcM s
  obtain ⟨T, S, hT, hS, ht⟩ := exists_admissible_of_approximable hM hinf hpair hunion hpower hsep hrep hchoice
    (c.nodeCode s) (valid_nodeCode c hc s) hc' (by rwa [cantorSet_nodeCode c hc s]) a b ha hb hab
  refine ⟨T, S, hT, hS, _, ?_, ht⟩
  exact (nodeApproximationValues_eq M c hc s T S a b).symm

/-- Accepted arbitrary sets decode as actual trees, so selected witnesses have external meaning. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Admissibility at every node
-/
theorem decode_node_admissible {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (s : List ℕ) (W V : M) (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (p : Fin 12 → M)
    (hp : Subtype.val ∘ p = nodeApproximationValues M c hc.2.2.2.2.2 s W.val V.val a b)
    (h : approximationAdmissibleFormula.Realize Empty.elim p) :
    ∃ T S : Set (List Bool), W.val = wordTreeSet (binaryLift T) ∧ V.val = wordTreeSet (binaryLift S) ∧
      IsSubtree T ∧ IsSubtree S ∧
      (treeBody T ⊆ cantorNodeSet c hc.2.2.2.2.2 s ∧ cantorNodeSet c hc.2.2.2.2.2 s ⊆ (treeBody S)ᶜ) ∧
      fairCoinProduct.real (treeBody T ∪ treeBody S)ᶜ < (a : ℝ) / b := by
  have hshapes := h
  simp only [approximationAdmissibleFormula, BoundedFormula.realize_inf, realize_reindex,
    binaryTreePredicate.realize_compile hM] at hshapes
  have hW : binaryTreePredicate.eval ![wordTreeSet (binaryLift Set.univ), W.val] := by
    convert hshapes.1 using 1
    funext i
    fin_cases i
    · exact (congrFun hp 7).symm
    · exact (congrFun hp 8).symm
  have hV : binaryTreePredicate.eval ![wordTreeSet (binaryLift Set.univ), V.val] := by
    convert hshapes.2.1 using 1
    funext i
    fin_cases i
    · exact (congrFun hp 7).symm
    · exact (congrFun hp 9).symm
  obtain ⟨T, ht, hT⟩ := (binaryTreePredicate_iff W.val).mp hW
  obtain ⟨S, hs, hS⟩ := (binaryTreePredicate_iff V.val).mp hV
  refine ⟨T, S, hT, hS, ?_⟩
  apply (node_approximationAdmissible_absolute hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM s T S
    (hT ▸ W.property) (hS ▸ V.property) a b hb hab p (by rwa [hT, hS] at hp)).mp h

end PolishSpaceBook.CantorTreeMeasure
