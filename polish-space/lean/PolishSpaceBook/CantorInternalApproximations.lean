module

public import PolishSpaceBook.CantorInternalWords
public import PolishSpaceBook.CantorLevelComplements

@[expose] public section

/-! # Internal clopen approximations to complements of internal closed trees -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
universe u

lemma mem_binaryLift_avoidWords (O : Set (List Bool)) (s : List ℕ) :
    s ∈ binaryLift (avoidWords O) ↔
      s ∈ binaryLift Set.univ ∧ s ∈ avoidWords (binaryLift O) := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, Set.mem_univ _, rfl⟩, ?_⟩
    intro t ht hp
    obtain ⟨v, hv, rfl⟩ := ht
    exact hw v hv ((List.prefix_map_iff_of_injective bool_toNat_injective).mp hp)
  · rintro ⟨⟨w, _, rfl⟩, hw⟩
    refine ⟨w, ?_, rfl⟩
    intro v hv hp
    exact hw (v.map Bool.toNat) ⟨v, hv, rfl⟩ (hp.map Bool.toNat)

/-- Parameters forbidden words and candidate word; membership is just prefix avoidance. -/
def avoidWordsPredicate : BoundedSetPredicate 2 := .all 0 (.neg (.subset 2 1))

lemma eval_avoidWordsPredicate (O : Set (List ℕ)) (s : List ℕ) :
    avoidWordsPredicate.eval ![wordTreeSet.{u} O, wordGraph s] ↔ s ∈ avoidWords O := by
  change (∀ t ∈ wordTreeSet O, ¬t ⊆ wordGraph s) ↔ _
  constructor
  · intro h t ht hp
    exact h (wordGraph t) (wordGraph_mem_wordTreeSet.mpr ht) (wordGraph_subset_iff.mpr hp)
  · intro h t ht hts
    obtain ⟨w, hw, rfl⟩ := mem_wordTreeSet.mp ht
    exact h w hw (wordGraph_subset_iff.mp hts)

/-- Closed complements of open word codes are constructed by bounded Separation. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Internal avoidance trees
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    For the internal construction, separate from $F_2$
    the graphs $\sigma$ satisfying
    $$\forall \tau\in W_O\;\neg(\tau\IncludedIn \sigma).$$
    Graph inclusion is the prefix relation, so the same bounded-recognition lemma gives the required node set.
    This also covers $O=\emptyset$ and families containing the empty word.
-/
theorem avoidWords_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (O : Set (List Bool)) (hO : wordTreeSet (binaryLift O) ∈ M) :
    wordTreeSet (binaryLift (avoidWords O)) ∈ M := by
  let W : M := ⟨wordTreeSet (binaryLift O), hO⟩
  apply avoidWordsPredicate.subset_mem hM (hsep _) ![W]
    (binaryWords_mem hM hinf hpair hunion hpower hsep)
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_wordTreeSet.mp hx
    exact wordGraph_mem_wordTreeSet.mpr ((mem_binaryLift_avoidWords O s).mp hs).1
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_wordTreeSet.mp hx
    have he : Fin.snoc (Subtype.val ∘ ![W]) (wordGraph s) =
        ![wordTreeSet (binaryLift O), wordGraph s] := by funext i; fin_cases i <;> rfl
    rw [he, eval_avoidWordsPredicate, wordGraph_mem_wordTreeSet,
      mem_binaryLift_avoidWords, and_iff_right hs]

lemma finiteWordLevel_binaryLift (T : Set (List Bool)) (n : ℕ) :
    finiteWordLevel.{u} (binaryLift T) n = wordTreeSet (binaryLift {s | s ∈ T ∧ s.length = n}) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hT, hlen⟩ := ZFSet.mem_sep.mp hx
    obtain ⟨s, ⟨w, hw, rfl⟩, rfl⟩ := mem_wordTreeSet.mp hT
    exact wordGraph_mem_wordTreeSet.mpr ⟨w, ⟨hw,
      by simpa using ((wordLength_iff (w.map Bool.toNat) n).mp hlen).symm⟩, rfl⟩
  · intro hx
    obtain ⟨s, ⟨w, ⟨hw, hlen⟩, rfl⟩, rfl⟩ := mem_wordTreeSet.mp hx
    exact (wordGraph_mem_finiteWordLevel _ _ _).mpr ⟨⟨w, hw, rfl⟩, by simpa using hlen⟩

/-- The finite-level complement reuses the same avoidance construction. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal clopen approximations
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    §{sec:internal-finite-measure-bounds} constructs the entire finite-level node set inside $M$.
    Apply the avoidance-tree proposition to that set.
-/
theorem levelComplement_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T : Set (List Bool)) (hT : wordTreeSet (binaryLift T) ∈ M) (n : ℕ) :
    wordTreeSet (binaryLift (levelComplement T n)) ∈ M := by
  rw [levelComplement_eq_avoidWords]
  apply avoidWords_mem hM hinf hpair hunion hpower hsep
  rw [← finiteWordLevel_binaryLift]
  exact finiteWordLevel_mem hM hinf hsep (binaryLift T) hT n

/-- A genuine internal-code existence theorem for the open base case of regularity. -/
theorem exists_internal_open_approximation {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T : Set (List Bool)) (hT : IsSubtree T) (hTM : wordTreeSet (binaryLift T) ∈ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set (List Bool), IsSubtree S ∧ wordTreeSet (binaryLift S) ∈ M ∧
      treeBody S ⊆ (treeBody T)ᶜ ∧ IsClopen (treeBody S) ∧
      fairCoinProduct.real ((treeBody T)ᶜ \ treeBody S) < ε := by
  obtain ⟨n, hn⟩ := exists_levelComplement_approximation hT hε
  refine ⟨levelComplement T n, levelComplement_isSubtree T n,
    levelComplement_mem hM hinf hpair hunion hpower hsep T hTM n,
    levelComplement_body_subset T n, ?_, hn⟩
  rw [treeBody_levelComplement]
  exact (isClopen_levelSet T n).compl

/-- Every internal open word code has arbitrarily accurate internal clopen inner approximants. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: theorem
  title: Internal clopen approximations
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    For the last assertion, take $T=D(O)$ and choose a finite stage at which this
    error is below $\varepsilon$. Every stage already has its code in $M$; no external regularity witness is
    assumed to belong to $M$.
-/
theorem exists_internal_openCode_approximation {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (O : Set (List Bool)) (hO : wordTreeSet (binaryLift O) ∈ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set (List Bool), IsSubtree S ∧ wordTreeSet (binaryLift S) ∈ M ∧
      treeBody S ⊆ openFromWords O ∧ IsClopen (treeBody S) ∧
      fairCoinProduct.real (openFromWords O \ treeBody S) < ε := by
  have h := exists_internal_open_approximation hM hinf hpair hunion hpower hsep
    (avoidWords O) (avoidWords_isSubtree O) (avoidWords_mem hM hinf hpair hunion hpower hsep O hO) hε
  simpa only [treeBody_avoidWords, compl_compl] using h

end PolishSpaceBook.CantorTreeMeasure
