module

public import PolishSpaceBook.CantorInternalApproximations

@[expose] public section

/-! # Internal open-code unions, closed complements, and finite closed unions -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression BoundedSetPredicate
universe u

lemma wordTreeSet_union (T S : Set (List ℕ)) :
    wordTreeSet.{u} (T ∪ S) = wordTreeSet T ∪ wordTreeSet S := by
  ext x
  simp only [mem_wordTreeSet, Set.mem_union, or_and_right, exists_or, ZFSet.mem_union]

lemma wordTreeSet_diff (T S : Set (List ℕ)) :
    wordTreeSet.{u} (T \ S) = (wordTreeSet T).sep (fun x => x ∉ wordTreeSet S) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, rfl⟩ := mem_wordTreeSet.mp hx
    exact ZFSet.mem_sep.mpr ⟨wordGraph_mem_wordTreeSet.mpr hs.1,
      fun h => hs.2 (wordGraph_mem_wordTreeSet.mp h)⟩
  · intro hx
    obtain ⟨ht, hnot⟩ := ZFSet.mem_sep.mp hx
    obtain ⟨s, hs, rfl⟩ := mem_wordTreeSet.mp ht
    exact wordGraph_mem_wordTreeSet.mpr ⟨hs, fun h => hnot (wordGraph_mem_wordTreeSet.mpr h)⟩

lemma mem_sUnion_graphRange_sequenceGraph (s : ℕ → ZFSet.{u}) (x : ZFSet.{u}) :
    x ∈ ZFSet.sUnion (graphRange (sequenceGraph s)) ↔ ∃ n, x ∈ s n := by
  constructor
  · intro hx
    obtain ⟨Y, hY, hxy⟩ := ZFSet.mem_sUnion.mp hx
    obtain ⟨a, ha⟩ := mem_graphRange.mp hY
    obtain ⟨n, hn⟩ := ZFSet.mem_range.mp ha
    exact ⟨n, (ZFSet.pair_inj.mp hn).2 ▸ hxy⟩
  · rintro ⟨n, hn⟩
    exact ZFSet.mem_sUnion.mpr ⟨s n,
      mem_graphRange.mpr ⟨natOrdinal n, (pair_mem_sequenceGraph s n _).mpr rfl⟩, hn⟩

lemma wordTreeSet_iUnion (T : ℕ → Set (List ℕ)) :
    wordTreeSet.{u} (⋃ n, T n) = ZFSet.sUnion (graphRange (sequenceGraph (fun n => wordTreeSet (T n)))) := by
  ext x
  rw [mem_sUnion_graphRange_sequenceGraph]
  simp only [mem_wordTreeSet, Set.mem_iUnion, exists_and_right, exists_comm]

/-- A countable code family must itself have an internal graph; internality of each value is insufficient. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Operations on internal approximation codes
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    For the first assertion, separate from $F_2$ the graphs absent from $W_T$. A point is outside
    $\TreeBody{T}$ exactly when one of its prefixes is missing from $T$.
    For the second assertion, internal range construction and Union give the displayed node set; taking the
    union of its cylinders gives the required open union. The hypothesis is on the entire graph $G$.
    For the last assertion, finite unions of node sets belong to $M$ by Pairing and Union.
    For two downward-closed trees, if a branch through their union leaves the first tree at some length, then
    all its longer prefixes must belong to the second tree. Downward closure puts all shorter prefixes there
    as well. This proves the body identity for two trees; finite induction proves the stated formula.
-/
theorem openUnion_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (O : ℕ → Set (List Bool))
    (hO : sequenceGraph (fun n => wordTreeSet (binaryLift (O n))) ∈ M) :
    wordTreeSet (binaryLift (⋃ n, O n)) ∈ M := by
  have he : binaryLift (⋃ n, O n) = ⋃ n, binaryLift (O n) := by
    simp only [binaryLift, Set.image_iUnion]
  rw [he, wordTreeSet_iUnion]
  exact union_mem hM hunion (graphRange_mem hM hunion (hsep _) hO)

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the selected downward-closed trees, these codes have the external meanings
    $$\begin{gathered}
    U\!\left(\bigcup_n O_n\right)=\bigcup_n\TreeBody{S_n}^c,\\
    \TreeBody{\bigcup_{n\le N}T_n}=\bigcup_{n\le N}\TreeBody{T_n}.
    \end{gathered}$$
    Both identities were proved in §{sec:internal-finite-measure-bounds}. The combined internal codes
    are therefore ready for the finite-tail estimate in §{sec:internal-approximation-errors}.
-/
lemma openFromWords_iUnion (O : ℕ → Set (List Bool)) :
    openFromWords (⋃ n, O n) = ⋃ n, openFromWords (O n) := by
  ext x
  simp only [openFromWords, Set.mem_iUnion, exists_prop, exists_and_right, exists_comm]

lemma wordTreeSet_binary_compl (T : Set (List Bool)) :
    wordTreeSet.{u} (binaryLift Tᶜ) = (wordTreeSet (binaryLift Set.univ)).sep
      (fun x => x ∉ wordTreeSet (binaryLift T)) := by
  have he : binaryLift Tᶜ = binaryLift Set.univ \ binaryLift T := by
    have hc : Tᶜ = Set.univ \ T := by ext s; simp
    unfold binaryLift
    rw [hc]
    exact Set.image_sdiff (List.map_injective_iff.mpr bool_toNat_injective) Set.univ T
  rw [he, wordTreeSet_diff]

/-- The words absent from a closed tree form an internal code for its open complement. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Operations on internal approximation codes
-/
theorem missingWords_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence)
    (hunion : M ⊨ unionSentence) (hpower : M ⊨ powerSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (T : Set (List Bool)) (hT : wordTreeSet (binaryLift T) ∈ M) :
    wordTreeSet (binaryLift Tᶜ) ∈ M := by
  rw [wordTreeSet_binary_compl]
  exact (BoundedSetPredicate.neg (.member (1 : Fin 2) 0)).separation_mem hM (hsep _) ![⟨_, hT⟩]
    (binaryWords_mem hM hinf hpair hunion hpower hsep)

lemma openFromWords_compl (T : Set (List Bool)) : openFromWords Tᶜ = (treeBody T)ᶜ := by
  ext x
  constructor
  · intro hx hT
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    exact hs (seqPrefix_eq_of_mem_cyl hxs ▸ hT s.length)
  · intro hx
    have hn : ∃ n, seqPrefix x n ∉ T := by simpa only [Set.mem_compl_iff, mem_treeBody, not_forall] using hx
    obtain ⟨n, hn⟩ := hn
    exact Set.mem_iUnion₂.mpr ⟨seqPrefix x n, hn, mem_cyl_seqPrefix x n⟩

lemma subtree_union {α : Type*} {T S : Set (List α)} (hT : IsSubtree T) (hS : IsSubtree S) :
    IsSubtree (T ∪ S) := by
  intro s t hs ht
  exact hs.elim (fun hs => Or.inl (hT hs ht)) (fun hs => Or.inr (hS hs ht))

/-- Finiteness and downward closure are essential: this identity does not extend to countable unions. -/
lemma treeBody_union {α : Type*} {T S : Set (List α)} (hT : IsSubtree T) (hS : IsSubtree S) :
    treeBody (T ∪ S) = treeBody T ∪ treeBody S := by
  classical
  ext x
  constructor
  · intro hx
    by_cases ht : x ∈ treeBody T
    · exact Or.inl ht
    · right
      obtain ⟨n, hn⟩ : ∃ n, seqPrefix x n ∉ T := by simpa only [mem_treeBody, not_forall] using ht
      intro m
      rcases hx (max n m) with ht | hs
      · exact False.elim (hn (hT ht (seqPrefix_prefixOf_of_le x (le_max_left n m))))
      · exact hS hs (seqPrefix_prefixOf_of_le x (le_max_right n m))
  · rintro (hx | hx) n
    · exact Or.inl (hx n)
    · exact Or.inr (hx n)

theorem treeUnion_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    (T S : Set (List Bool)) (hT : wordTreeSet (binaryLift T) ∈ M)
    (hS : wordTreeSet (binaryLift S) ∈ M) : wordTreeSet (binaryLift (T ∪ S)) ∈ M := by
  have he : binaryLift (T ∪ S) = binaryLift T ∪ binaryLift S := by
    simp only [binaryLift, Set.image_union]
  rw [he, wordTreeSet_union]
  exact SetTheoryModels.binaryUnion_mem hM hpair hunion hT hS

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Operations on internal approximation codes
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the selected downward-closed trees, these codes have the external meanings
    $$\begin{gathered}
    U\!\left(\bigcup_n O_n\right)=\bigcup_n\TreeBody{S_n}^c,\\
    \TreeBody{\bigcup_{n\le N}T_n}=\bigcup_{n\le N}\TreeBody{T_n}.
    \end{gathered}$$
    Both identities were proved in §{sec:internal-finite-measure-bounds}. The combined internal codes
    are therefore ready for the finite-tail estimate in §{sec:internal-approximation-errors}.
-/
lemma treeBody_finiteUnion {ι α : Type*} (I : Finset ι) (T : ι → Set (List α))
    (hT : ∀ i, IsSubtree (T i)) :
    treeBody (⋃ i ∈ I, T i) = ⋃ i ∈ I, treeBody (T i) := by
  classical
  induction I using Finset.induction with
  | empty => ext x; simp [treeBody]
  | @insert i I hi ih =>
    have he : (⋃ j ∈ insert i I, T j) = T i ∪ ⋃ j ∈ I, T j := by ext s; simp
    have hsub : IsSubtree (⋃ j ∈ I, T j) := by
      intro s t hs ht
      obtain ⟨j, hj, hs⟩ := Set.mem_iUnion₂.mp hs
      exact Set.mem_iUnion₂.mpr ⟨j, hj, hT j hs ht⟩
    rw [he, treeBody_union (hT i) hsub, ih]
    ext x; simp

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Operations on internal approximation codes
-/
theorem finiteTreeUnion_mem {M : ZFSet.{u}} (hM : M.IsTransitive)
    (hinf : M ⊨ infinitySentence) (hpair : M ⊨ pairingSentence) (hunion : M ⊨ unionSentence)
    {ι : Type*} (I : Finset ι) (T : ι → Set (List Bool))
    (hT : ∀ i ∈ I, wordTreeSet (binaryLift (T i)) ∈ M) :
    wordTreeSet (binaryLift (⋃ i ∈ I, T i)) ∈ M := by
  classical
  induction I using Finset.induction with
  | empty =>
    have he : wordTreeSet (binaryLift (⋃ i ∈ (∅ : Finset ι), T i)) = (∅ : ZFSet.{u}) := by
      ext x; simp [mem_wordTreeSet, binaryLift]
    rw [he]
    exact empty_mem_of_infinity hM hinf
  | @insert i I hi ih =>
    have he : (⋃ j ∈ insert i I, T j) = T i ∪ ⋃ j ∈ I, T j := by ext s; simp
    rw [he]
    exact treeUnion_mem hM hpair hunion (T i) _ (hT i (by simp))
      (ih (fun j hj => hT j (by simp [hj])))

end PolishSpaceBook.CantorTreeMeasure
