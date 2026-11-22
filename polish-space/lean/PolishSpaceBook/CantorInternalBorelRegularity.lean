module

public import PolishSpaceBook.CantorInternalUnionApproximation

@[expose] public section

/-! # Internal two-sided approximation at every node of an internal Borel code -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory
universe u

/-- Restrict a Baire cylinder to binary points, allowing the empty cylinder restriction. -/
lemma cantorInclusion_preimage_cyl (w : List ℕ) :
    cantorInclusion ⁻¹' cyl w = openFromWords {v : List Bool | v.map Bool.toNat = w} := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion₂.mpr ⟨seqPrefix x w.length, ?_, mem_cyl_seqPrefix x w.length⟩
    change (seqPrefix x w.length).map Bool.toNat = w
    have he : (seqPrefix x w.length).map Bool.toNat = seqPrefix (cantorInclusion x) w.length := by
      simp only [seqPrefix, List.map_ofFn, cantorInclusion, Function.comp_def]
    rw [he]
    exact seqPrefix_eq_of_mem_cyl hx
  · intro hx
    obtain ⟨v, hv, hx⟩ := Set.mem_iUnion₂.mp hx
    change v.map Bool.toNat = w at hv
    rw [← hv]
    intro i hi
    have hi' : i < v.length := by simpa using hi
    simpa [cantorInclusion] using congrArg Bool.toNat (hx i hi')

/-- The restricted cylinder code is obtained by equality separation from all binary words. -/
lemma restrictedCylinderCode_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (w : List ℕ) : wordTreeSet (binaryLift {v : List Bool | v.map Bool.toNat = w}) ∈ M := by
  have hw : wordGraph w ∈ M := hM.mem_trans (mem_finiteSequences.mpr ⟨w, rfl⟩)
    (finiteSequences_mem hM hinf hpair hunion hpower hsep)
  have he : wordTreeSet (binaryLift {v : List Bool | v.map Bool.toNat = w}) =
      (wordTreeSet (binaryLift Set.univ)).sep (fun x => x = wordGraph w) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ⟨v, hv, rfl⟩, rfl⟩ := mem_wordTreeSet.mp hx
      exact ZFSet.mem_sep.mpr ⟨wordGraph_mem_wordTreeSet.mpr ⟨v, Set.mem_univ _, rfl⟩,
        congrArg wordGraph hv⟩
    · intro hx
      obtain ⟨hx, he⟩ := ZFSet.mem_sep.mp hx
      obtain ⟨a, ⟨v, _, rfl⟩, rfl⟩ := mem_wordTreeSet.mp hx
      exact mem_wordTreeSet.mpr ⟨v.map Bool.toNat, ⟨v, wordGraph_injective he, rfl⟩, rfl⟩
  rw [he]
  exact (BoundedSetPredicate.equal (1 : Fin 2) 0).separation_mem hM (hsep _) ![⟨_, hw⟩]
    (binaryWords_mem hM hinf hpair hunion hpower hsep)

lemma internallyApproximable_cylinder {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (w : List ℕ) : InternallyApproximable M (cantorInclusion ⁻¹' cyl w) := by
  rw [cantorInclusion_preimage_cyl]
  exact internallyApproximable_openCode hM hinf hpair hunion hpower hsep _
    (restrictedCylinderCode_mem hM hinf hpair hunion hpower hsep w)

lemma cantorNodeSet_presentChildren (c : BorelExpression) (hw : WellFounded c.Child) (s : List ℕ) :
    (⋃ (n : ℕ) (_ : c (s ++ [n]) ≠ 0), cantorNodeSet c hw (s ++ [n])) =
      ⋃ n, cantorNodeSet c hw (s ++ [n]) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨n, _, hx⟩
    exact ⟨n, hx⟩
  · rintro ⟨n, hx⟩
    by_cases hn : c (s ++ [n]) = 0
    · rw [cantorNodeSet_eq_empty c hw _ hn] at hx
      exact hx.elim
    · exact ⟨n, hn, hx⟩

lemma cantorNodeSet_equation (c : BorelExpression) (hw : WellFounded c.Child) (s : List ℕ) :
    cantorNodeSet c hw s = if c s = 0 then ∅ else
      if c s = 1 then ⋃ n, cantorNodeSet c hw (s ++ [n]) else
      if c s = 2 then (⋃ n, cantorNodeSet c hw (s ++ [n]))ᶜ else
      cantorInclusion ⁻¹' cylinderBasis (c s - 3) := by
  have he := c.evaluate_isEvaluation hw cylinderBasis s
  have hp := cantorNodeSet_presentChildren c hw s
  unfold cantorNodeSet at hp ⊢
  rw [he]
  split_ifs <;> simp only [Set.preimage_empty, Set.preimage_iUnion, Set.preimage_compl, hp]

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal approximation of Borel interpretations
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Induct along the well-founded child relation of $c$. An absent node has empty interpretation, and the
    empty open code gives the approximation property there.
    For a leaf whose basic open set is $\cyl{w}$, put
    $$O_w=\{w\}\cap\finseq{2},\qquad
    W_{O_w}=\{\sigma\in F_2:\sigma=e(w)\}.$$
    The finite-word graph $e(w)$ belongs to $M$. Equality is a bounded predicate, so Separation puts this
    code in $M$. Its open interpretation is $i^{-1}(\cyl{w})$: it is empty if $w$ has an entry outside
    $\{0,1\}$, and otherwise it is the binary cylinder determined by $w$.
    The internal open-code approximation theorem therefore handles the leaf case.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    At a complement node, validity supplies a unique present child. All absent children have empty
    interpretation, so the node evaluates to the complement of that child's interpretation. Apply the
    complementation result of §{sec:internal-finite-measure-bounds} to the induction hypothesis at this child.
    At a union node, apply the preceding theorem to the induction hypotheses at all present children.
    These cases exhaust the evaluation equations and complete the induction. The root gives the final assertion.
-/
theorem internallyApproximable_cantorNodeSet {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M)
    (s : List ℕ) : InternallyApproximable M (cantorNodeSet c hc.2.2.2.2.2 s) := by
  induction s using hc.2.2.2.2.2.induction with
  | h s ih =>
    by_cases h0 : c s = 0
    · rw [cantorNodeSet_eq_empty c hc.2.2.2.2.2 s h0]
      exact internallyApproximable_empty hM hinf hpair hunion hpower hsep
    have hchildren (n : ℕ) (hn : c (s ++ [n]) ≠ 0) := ih _ ⟨h0, n, rfl, hn⟩
    rw [cantorNodeSet_equation]
    simp only [h0, ite_false]
    by_cases h1 : c s = 1
    · simp only [h1, ite_true]
      exact internallyApproximable_childUnion hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM s hchildren
    simp only [h1, ite_false]
    by_cases h2 : c s = 2
    · simp only [h2, ite_true]
      obtain ⟨n, hn, huniq⟩ := hc.2.2.2.2.1 s h2
      have he : (⋃ j, cantorNodeSet c hc.2.2.2.2.2 (s ++ [j])) =
          cantorNodeSet c hc.2.2.2.2.2 (s ++ [n]) := by
        apply Set.Subset.antisymm
        · apply Set.iUnion_subset
          intro j
          by_cases hj : c (s ++ [j]) = 0
          · rw [cantorNodeSet_eq_empty c hc.2.2.2.2.2 _ hj]
            exact Set.empty_subset _
          · rw [huniq j hj]
        · exact Set.subset_iUnion (fun j => cantorNodeSet c hc.2.2.2.2.2 (s ++ [j])) n
      rw [he]
      exact internallyApproximable_compl hM hinf hpair hunion hpower hsep (hchildren n hn)
    · simp only [h2, ite_false]
      exact internallyApproximable_cylinder hM hinf hpair hunion hpower hsep _

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal approximation of Borel interpretations
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The approximation class $\mathcal R_M$ now contains every externally interpreted Borel set with a valid
    internal code. The admissibility theorem converts these approximations into internal witnesses.
-/
theorem internallyApproximable_cantorSet {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 1)), M ⊨ separationSentence φ)
    (hrep : ∀ {j : ℕ} (φ : ForcingFormulas.Formula (j + 2)), M ⊨ replacementSentence φ)
    (hchoice : M ⊨ choiceSentence) (c : BorelExpression) (hc : c.Valid) (hcM : c.labelGraph ∈ M) :
    InternallyApproximable M (BorelExpression.cantorSet c hc.2.2.2.2.2) :=
  internallyApproximable_cantorNodeSet hM hinf hpair hunion hpower hsep hrep hchoice c hc hcM []

end PolishSpaceBook.CantorTreeMeasure
