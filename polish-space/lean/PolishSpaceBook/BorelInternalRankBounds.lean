module

public import PolishSpaceBook.SetTheoryInternalTreeBranches
public import PolishSpaceBook.SetTheoryTreeRanks
public import PolishSpaceBook.BorelRankMeasureBounds

@[expose] public section

/-! # Internal rank certificates give bounds on the external Borel interpretation

An internal rank, internal subset minima, or absence of an internal branch
suffices for the external measure bound. Closure of the particular node-set
construction and its internal counterexample interpretation remain separate.
-/

namespace PolishSpaceBook.BorelExpression
open SetTheoryModels FirstOrder Language ZFSet ForcingFormulas CantorTreeMeasure
universe u

/-- An internal rank controls inclusion at all external binary points. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Borel measure bounds from internal ranks
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    A failure of inclusion would give a branch in the counterexample tree, which the theorem excludes.
-/
theorem binary_closed_subset_of_internal_rank {M : ZFSet.{u}} (hM : M.IsTransitive)
    (c : BorelExpression) (hc : c.Valid) (T : Set (List Bool)) (W R α f : M)
    (hW : W.val = wordTreeSet (inclusionTree c (binaryLift T)))
    (hR : R.val = wordExtensionRelation W.val)
    (hr : rankCertificateFormula.Realize Empty.elim ![W, R, α, f]) :
    treeBody T ⊆ cantorSet c hc.2.2.2.2.2 := by
  have hn := no_branch_of_internal_tree_rank hM _ (inclusionTree_isSubtree c _) W R α f hW hR hr
  have hw := (prefixTreeWellFounded_iff _ (inclusionTree_isSubtree c _)).mp hn
  have hs := (closed_subset_iff_inclusionTree_wellFounded c hc (binaryLift T)).mpr hw
  intro x hx
  exact hs (cantorInclusion_mem_binaryLift_body hx)

/-- Numerical finite-level bounds and the internally checked graph certify the external measure. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Borel measure bounds from internal ranks
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The finite-level lower bounds then give $q<r\le\mu(\TreeBody{T})\le\mu(A_c)$, exactly as in
    §{sec:coded-measure-bounds}.
-/
theorem rational_measure_bound_of_internal_rank {M : ZFSet.{u}} (hM : M.IsTransitive)
    (c : BorelExpression) (hc : c.Valid) (T : Set (List Bool)) (hT : IsSubtree T)
    (W R α f : M) (hW : W.val = wordTreeSet (inclusionTree c (binaryLift T)))
    (hR : R.val = wordExtensionRelation W.val)
    (hrank : rankCertificateFormula.Realize Empty.elim ![W, R, α, f])
    (q r : ℚ) (hqr : q < r) (hr : ∀ n, r ≤ levelWeight T n) :
    (q : ℝ) < fairCoinProduct.real (cantorSet c hc.2.2.2.2.2) := by
  apply (borel_lower_cut (measurableSet_cantorSet c _) q).mpr
  exact ⟨T, hT, binary_closed_subset_of_internal_rank hM c hc T W R α f hW hR hrank, r, hqr, hr⟩

/-- Internal well-foundedness now constructs the rank required for the measure bound. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Borel measure bounds from internal well-foundedness
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The internal rank-existence corollary constructs the graph required by the Borel measure-bound corollary in
    §{sec:internal-rank-certificates}. Apply that corollary with the given finite-level bounds.
-/
theorem rational_measure_bound_of_internal_minima {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid)
    (T : Set (List Bool)) (hT : IsSubtree T) (W R : M)
    (hW : W.val = wordTreeSet (inclusionTree c (binaryLift T)))
    (hR : R.val = wordExtensionRelation W.val)
    (hmin : internalOrderMinimaFormula.Realize Empty.elim ![W, R])
    (q r : ℚ) (hqr : q < r) (hr : ∀ n, r ≤ levelWeight T n) :
    (q : ℝ) < fairCoinProduct.real (cantorSet c hc.2.2.2.2.2) := by
  obtain ⟨α, f, hf⟩ := internal_rank_certificate hM hinf hpair hunion hpower hsep hrep hchoice W R hmin
  exact rational_measure_bound_of_internal_rank hM c hc T hT W R α f hW hR hf q r hqr hr

/-- No internal counterexample branch suffices for the external numerical bound. -/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: statement
  kind: corollary
  title: Measure bounds from absence of internal counterexample branches
-/
/-@ booklink:
  source: polish-space-book/appendix-borel-absoluteness.md
  target: proof
  excerpt: |
    The theorem gives the internal subset-minimum assertion for $Q$. Apply the measure-bound corollary of
    §{sec:internal-rank-existence}.
-/
theorem rational_measure_bound_of_no_internal_branch {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid)
    (T : Set (List Bool)) (hT : IsSubtree T) (W R : M)
    (hW : W.val = wordTreeSet (inclusionTree c (binaryLift T)))
    (hR : R.val = wordExtensionRelation W.val)
    (hno : ¬ ∃ p : ℕ → ℕ, p ∈ treeBody (inclusionTree c (binaryLift T)) ∧ pointGraph p ∈ M)
    (q r : ℚ) (hqr : q < r) (hr : ∀ n, r ≤ levelWeight T n) :
    (q : ℝ) < fairCoinProduct.real (cantorSet c hc.2.2.2.2.2) := by
  have hmin := internal_tree_minima_of_no_internal_branch hM hinf hpair hunion hpower hsep hchoice
    _ (inclusionTree_isSubtree c _) W R hW hR hno
  exact rational_measure_bound_of_internal_minima hM hinf hpair hunion hpower hsep hrep hchoice
    c hc T hT W R hW hR hmin q r hqr hr

end PolishSpaceBook.BorelExpression
