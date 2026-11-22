module

public import PolishSpaceBook.CantorInternalRegularity
public import PolishSpaceBook.CantorApproximationPredicates
public import PolishSpaceBook.CantorInternalMeasureFormula
public import PolishSpaceBook.BorelCanonicalBasis

@[expose] public section

/-! # Internal admissibility for two-sided Borel approximations

The tree shapes, both inclusions, and the strict measure error are tested by a
single first-order formula. Its interpretation is equivalent to the external
approximation conditions; existence of such codes is a separate assertion.
-/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
universe u

/-- Arithmetic, finite words, internal points and Borel set, binary words, two trees, error fraction. -/
def nodeApproximationValues (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child)
    (s : List ℕ) (W V : ZFSet.{u}) (a b : ℕ) : Fin 12 → ZFSet.{u} :=
  ![Ordinal.omega0.toZFSet, naturalBinaryGraph (fun x y => x * y),
    sequenceGraph (fun n => natOrdinal (2 ^ n)), naturalBinaryGraph (fun x y => x + y),
    finiteSequences, internalBaire M, internalInterpretation M c hw NamedLambda.NatListCode.decode s,
    wordTreeSet (binaryLift Set.univ), W, V,
    natOrdinal a, natOrdinal b]

/-- No internal code is assumed for the family of all approximations. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Assume that $M$ is transitive and satisfies Infinity, Pairing, Union, Power Set, Separation, Replacement,
    and Choice. Fix a valid Borel expression $c$ whose label graph belongs to $M$. Let
    $$B=\BorelInterpretation{c}{M},\qquad A=i^{-1}(B_c),$$
    where $B_c$ uses the standard Baire cylinders and $i:\CantorSpace\to\BaireSpace$ is the inclusion.
    The internal interpretation $B$, internal Baire space $X_M$, finite-word set $F$, and binary-word set $F_2$
    are all elements of $M$ by the preceding constructions. Retain these sets and the arithmetic graphs
    from §{sec:internal-approximation-errors} as parameters.
-/
theorem nodeApproximationValues_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (hcM : c.labelGraph ∈ M)
    (s : List ℕ) (W V : ZFSet.{u}) (hW : W ∈ M) (hV : V ∈ M)
    (a b : ℕ) : ∀ i, nodeApproximationValues M c hw s W V a b i ∈ M := by
  have hΩ := omegaOrdinal_mem hM hinf (hsep _)
  have hn (n : ℕ) : natOrdinal n ∈ M := hM.mem_trans (mem_omegaOrdinal.mpr ⟨n, rfl⟩) hΩ
  have hm := naturalMultiplicationGraph_mem hM hinf hpair hunion hpower hsep
  have hp := naturalTwoPowerGraph_mem hM hinf hpair hunion hpower hsep
  have ha := naturalAdditionGraph_mem hM hinf hpair hunion hpower hsep
  have hf := finiteSequences_mem hM hinf hpair hunion hpower hsep
  have hx := internalBaire_mem hM hinf hpair hunion hpower hsep
  have hb := canonical_internalInterpretation_mem hM hinf hpair hunion hpower hsep c hw hcM s
  have h2 := binaryWords_mem hM hinf hpair hunion hpower hsep
  intro i
  fin_cases i <;> simp only [nodeApproximationValues] <;>
    first | exact hΩ | exact hm | exact hp | exact ha | exact hf | exact hx | exact hb | exact h2 |
      exact hW | exact hV | exact hn _

/-- Root-level parameters are the special case with the empty node address. -/
def approximationParams (M : ZFSet.{u}) (c : BorelExpression) (hw : WellFounded c.Child)
    (T S : Set (List Bool)) (a b : ℕ) : Fin 12 → ZFSet.{u} :=
  nodeApproximationValues M c hw [] (wordTreeSet (binaryLift T)) (wordTreeSet (binaryLift S)) a b

theorem approximationParams_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (c : BorelExpression) (hw : WellFounded c.Child) (hcM : c.labelGraph ∈ M)
    (T S : Set (List Bool)) (hT : wordTreeSet (binaryLift T) ∈ M) (hS : wordTreeSet (binaryLift S) ∈ M)
    (a b : ℕ) : ∀ i, approximationParams M c hw T S a b i ∈ M :=
  nodeApproximationValues_mem hM hinf hpair hunion hpower hsep c hw hcM [] _ _ hT hS a b

/-- Tree shape and inclusion are bounded tests; the numerical test quantifies its finite witnesses. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Combine these conditions with the error test:
    $$\begin{aligned}
    \mathrm{Adm}(B,W,V,a,b):\equiv{}&\mathrm{Tree}(W)\land\mathrm{Tree}(V)\\
    &{}\land\mathrm{Inc}(B,W,V)\land E(W,V,a,b).
    \end{aligned}$$
    Here the second tree describes the complement of the outer open approximant.
-/
def approximationAdmissibleFormula : ForcingFormulas.Formula 12 :=
  reindex binaryTreePredicate.compile ![7, 8] ⊓
    (reindex binaryTreePredicate.compile ![7, 9] ⊓
      (reindex approximationInclusionPredicate.compile ![4, 5, 6, 8, 9] ⊓
        reindex smallErrorFormula ![0, 1, 2, 3, 8, 9, 10, 11]))

/-- Internal admissibility has exactly the intended meaning on every external binary point. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal admissibility of approximations
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The uniform interpretation principle identifies the two internal tree tests with actual downward closure.
    It identifies the internal inclusion test with its assertions about all point graphs in $X_M$.
    Agreement of the internal Borel interpretation with $B_c$ on those points turns these assertions into
    closed inclusion and closed disjointness on internal points. Both transfer to external points by
    §{sec:internal-closed-inclusions}. Restricting to binary points gives the two stated inclusions.
    Conversely, the external inclusions imply the assertions on internal points, so the bounded test holds
    in $M$. Finally, §{sec:internal-approximation-errors} identifies the internal error test with the displayed
    strict measure bound in both directions.
-/
theorem approximationAdmissible_absolute {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (T S : Set (List Bool)) (hT : wordTreeSet (binaryLift T) ∈ M) (hS : wordTreeSet (binaryLift S) ∈ M)
    (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) :
    approximationAdmissibleFormula.Realize Empty.elim
      (fun i => ⟨approximationParams M c hc.2.2.2.2.2 T S a b i,
        approximationParams_mem hM hinf hpair hunion hpower hsep c hc.2.2.2.2.2 hcM T S hT hS a b i⟩ : Fin 12 → M) ↔
      IsSubtree T ∧ IsSubtree S ∧
        (treeBody T ⊆ cantorSet c hc.2.2.2.2.2 ∧ cantorSet c hc.2.2.2.2.2 ⊆ (treeBody S)ᶜ) ∧
        fairCoinProduct.real (treeBody T ∪ treeBody S)ᶜ < (a : ℝ) / b := by
  let p : Fin 12 → M := fun i => ⟨approximationParams M c hc.2.2.2.2.2 T S a b i,
    approximationParams_mem hM hinf hpair hunion hpower hsep c hc.2.2.2.2.2 hcM T S hT hS a b i⟩
  change approximationAdmissibleFormula.Realize Empty.elim p ↔ _
  simp only [approximationAdmissibleFormula, BoundedFormula.realize_inf, realize_reindex,
    binaryTreePredicate.realize_compile hM, approximationInclusionPredicate.realize_compile hM]
  change binaryTreePredicate.eval ![wordTreeSet (binaryLift Set.univ), wordTreeSet (binaryLift T)] ∧
    binaryTreePredicate.eval ![wordTreeSet (binaryLift Set.univ), wordTreeSet (binaryLift S)] ∧
    approximationInclusionPredicate.eval ![finiteSequences, internalBaire M,
      internalInterpretation M c hc.2.2.2.2.2 NamedLambda.NatListCode.decode [],
      wordTreeSet (binaryLift T), wordTreeSet (binaryLift S)] ∧
    smallErrorFormula.Realize Empty.elim (p ∘ ![0, 1, 2, 3, 8, 9, 10, 11]) ↔ _
  rw [eval_binaryTreePredicate, eval_binaryTreePredicate,
    approximationInclusion_absolute hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM T S hT hS]
  have he : p ∘ ![(0 : Fin 12), 1, 2, 3, 8, 9, 10, 11] =
      ![p 0, p 1, p 2, p 3, p 8, p 9, p 10, p 11] := by funext i; fin_cases i <;> rfl
  rw [he]
  have herr (ht : IsSubtree T) (hs : IsSubtree S) :=
    realize_smallErrorFormula hM hinf hpair hunion hsep T S ht hs a b hb hab
      (p 0) (p 1) (p 2) (p 3) (p 8) (p 9) (p 10) (p 11) rfl rfl rfl rfl rfl rfl rfl rfl
  exact ⟨fun ⟨ht, hs, hi, he⟩ => ⟨ht, hs, hi, (herr ht hs).mp he⟩,
    fun ⟨ht, hs, hi, he⟩ => ⟨ht, hs, hi, (herr ht hs).mpr he⟩⟩


/-- The external approximation property supplies internal witnesses for every positive rational error. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: lemma
  title: Internal totality from coded approximations
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Apply the definition of $\mathcal R_M$ with error $a/b$. It supplies an inner tree $T$ and an outer open
    code $O$, both internal. Put $S=D(O)$. Then $W_S\in M$ and
    $$\TreeBody{T}\IncludedIn A\IncludedIn\TreeBody{S}^c,
    \qquad\SetDifference{\CantorSpace}{\TreeBody{T}\cup\TreeBody{S}}
    =\SetDifference{U(O)}{\TreeBody{T}}.$$
    The admissibility theorem therefore supplies the required internal witnesses $W_T,W_S$.
-/
theorem exists_admissible_of_approximable {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (happrox : InternallyApproximable M (cantorSet c hc.2.2.2.2.2))
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    ∃ T S : Set (List Bool), ∃ hT : wordTreeSet (binaryLift T) ∈ M,
      ∃ hS : wordTreeSet (binaryLift S) ∈ M,
      approximationAdmissibleFormula.Realize Empty.elim
        (fun i => ⟨approximationParams M c hc.2.2.2.2.2 T S a b i,
          approximationParams_mem hM hinf hpair hunion hpower hsep c hc.2.2.2.2.2 hcM T S hT hS a b i⟩ :
          Fin 12 → M) := by
  have hε : (0 : ℝ) < (a : ℝ) / b := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  obtain ⟨T, O, ht, hTM, hOM, hsub, houter, hgap⟩ := happrox _ hε
  have hSM := avoidWords_mem hM hinf hpair hunion hpower hsep O hOM
  refine ⟨T, avoidWords O, hTM, hSM,
    (approximationAdmissible_absolute hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM
      T (avoidWords O) hTM hSM a b hb hab).mpr ?_⟩
  refine ⟨ht, avoidWords_isSubtree O, ⟨hsub, ?_⟩, ?_⟩
  · simpa only [treeBody_avoidWords, compl_compl] using houter
  · rwa [complement_treeBody_union_avoidWords]


/-- The earlier open approximation now supplies witnesses for the internal admissibility formula. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: corollary
  title: Internal admissible approximations for open codes
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    The open case of §{sec:internal-finite-measure-bounds} gives $A\in\mathcal R_M$. Apply the lemma.
-/
theorem exists_admissible_openCode {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (O : Set (List Bool)) (hO : wordTreeSet (binaryLift O) ∈ M)
    (hA : cantorSet c hc.2.2.2.2.2 = openFromWords O) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    ∃ T S : Set (List Bool), ∃ hT : wordTreeSet (binaryLift T) ∈ M,
      ∃ hS : wordTreeSet (binaryLift S) ∈ M,
      approximationAdmissibleFormula.Realize Empty.elim
        (fun i => ⟨approximationParams M c hc.2.2.2.2.2 T S a b i,
          approximationParams_mem hM hinf hpair hunion hpower hsep c hc.2.2.2.2.2 hcM T S hT hS a b i⟩ :
          Fin 12 → M) := by
  apply exists_admissible_of_approximable hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM
    _ a b ha hb hab
  rw [hA]
  exact internallyApproximable_openCode hM hinf hpair hunion hpower hsep O hO

end PolishSpaceBook.CantorTreeMeasure
