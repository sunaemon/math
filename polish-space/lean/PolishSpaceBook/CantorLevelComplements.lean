module

public import PolishSpaceBook.CantorTreeMeasure

@[expose] public section

/-! # Clopen inner approximations to a tree complement -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open Set MeasureTheory Filter Topology

/-- An open code is a set of words whose cylinders are taken in union. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Encode binary words as finite graphs with values in $2=\{0,1\}$, and write
    $$W_O:=\{e(s):s\in O\},\qquad U(O):=\bigcup_{s\in O}\cyl{s}$$
    for a family $O\IncludedIn\finseq{2}$. An internal open code means that $W_O\in M$.
-/
def openFromWords {α : Type*} (O : Set (List α)) : Set (ℕ → α) := ⋃ s ∈ O, cyl s

/-- Avoid every forbidden word, including the empty word if it is present. -/
def avoidWords {α : Type*} (O : Set (List α)) : Set (List α) :=
  {s | ∀ t ∈ O, ¬t.IsPrefix s}

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    A prefix of a word avoiding every member of $O$ also avoids every member of $O$.
-/
lemma avoidWords_isSubtree {α : Type*} (O : Set (List α)) : IsSubtree (avoidWords O) := by
  intro s t hs hts v hv hvt
  exact hs v hv (hvt.trans hts)

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
    A branch lies in $\TreeBody{D(O)}$ exactly when none of its prefixes lies in $O$, which is equivalent to
    belonging to no cylinder in the union defining $U(O)$.
-/
lemma treeBody_avoidWords {α : Type*} (O : Set (List α)) :
    treeBody (avoidWords O) = (openFromWords O)ᶜ := by
  ext x
  constructor
  · intro hx hxO
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hxO
    exact hx s.length s hs (by rw [seqPrefix_eq_of_mem_cyl hxs])
  · intro hx n s hs hsn
    exact hx (Set.mem_iUnion₂.mpr ⟨s, hs, prefixOfSeq_of_prefix hsn (mem_cyl_seqPrefix x n)⟩)

/-- A word is allowed unless one of its length-`n` prefixes belongs to the forbidden level. -/
def levelComplement {α : Type*} (T : Set (List α)) (n : ℕ) : Set (List α) :=
  {s | ∀ t, t.IsPrefix s → t.length = n → t ∉ T}

lemma levelComplement_eq_avoidWords {α : Type*} (T : Set (List α)) (n : ℕ) :
    levelComplement T n = avoidWords {s | s ∈ T ∧ s.length = n} := by
  ext s
  simp only [levelComplement, avoidWords, Set.mem_ofPred_eq]
  constructor
  · intro h t ht hp
    exact h t hp ht.2 ht.1
  · intro h t hp hlen ht
    exact h t ⟨ht, hlen⟩ hp

lemma levelComplement_isSubtree {α : Type*} (T : Set (List α)) (n : ℕ) :
    IsSubtree (levelComplement T n) := by
  rw [levelComplement_eq_avoidWords]
  exact avoidWords_isSubtree _

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    A branch survives precisely when its length-$n$ prefix is
    absent from $T$, proving the displayed identity.
-/
lemma treeBody_levelComplement (T : Set (List Bool)) (n : ℕ) :
    treeBody (levelComplement T n) = (levelSet T n)ᶜ := by
  ext x
  rw [Set.mem_compl_iff, mem_levelSet]
  constructor
  · intro hx
    exact hx n (seqPrefix x n) (List.prefix_refl _) (seqPrefix_length x n)
  · intro hx m t ht hlen htT
    have hnm : n ≤ m := by simpa [hlen, seqPrefix_length] using ht.length_le
    have he : t = seqPrefix x n := by
      rw [List.prefix_iff_eq_take] at ht
      rw [hlen, seqPrefix_take_of_le x hnm] at ht
      exact ht
    exact hx (he ▸ htT)

lemma levelComplement_body_subset (T : Set (List Bool)) (n : ℕ) :
    treeBody (levelComplement T n) ⊆ (treeBody T)ᶜ := by
  rw [treeBody_levelComplement]
  exact compl_subset_compl.mpr (fun x hx => (mem_levelSet T n x).mpr (hx n))

/-- The error is precisely the excess of the finite-level mass over the closed measure. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    It contains $\TreeBody{T}$, so the discarded part has measure $d_n(T)-\mu(\TreeBody{T})$.
-/
lemma measureReal_levelComplement_error (T : Set (List Bool)) (n : ℕ) :
    fairCoinProduct.real ((treeBody T)ᶜ \ treeBody (levelComplement T n)) =
      (levelWeight T n : ℝ) - fairCoinProduct.real (treeBody T) := by
  rw [treeBody_levelComplement]
  have he : (treeBody T)ᶜ \ (levelSet T n)ᶜ = levelSet T n \ treeBody T := by
    ext x; simp only [Set.mem_sdiff, mem_compl_iff]; tauto
  have hsub : treeBody T ⊆ levelSet T n := fun x hx => (mem_levelSet T n x).mpr (hx n)
  rw [he, measureReal_sdiff hsub
    (isClosed_treeBody T).measurableSet, levelWeight_eq_measureReal]

/-- The finite-level approximation error tends to zero for a downward-closed tree. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: proof
  excerpt: |
    By §{sec:coded-measure-bounds}, this difference tends to $0$.
-/
lemma levelComplement_error_tendsto {T : Set (List Bool)} (hT : IsSubtree T) :
    Tendsto (fun n => fairCoinProduct.real ((treeBody T)ᶜ \ treeBody (levelComplement T n)))
      atTop (nhds 0) := by
  simp only [measureReal_levelComplement_error]
  simpa only [sub_self] using (levelWeight_tendsto hT).sub_const (fairCoinProduct.real (treeBody T))

/-- The fixed family approximates every open tree complement, without selecting a new closed set. -/
theorem exists_levelComplement_approximation {T : Set (List Bool)} (hT : IsSubtree T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, fairCoinProduct.real ((treeBody T)ᶜ \ treeBody (levelComplement T n)) < ε := by
  exact ((levelComplement_error_tendsto hT).eventually (eventually_lt_nhds hε)).exists

end PolishSpaceBook.CantorTreeMeasure
