module

public import PolishSpaceBook.SetTheoryInternalSequenceSets

@[expose] public section

/-! # Disjoint differences of a decreasing sequence -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas BoundedSetPredicate
universe u

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a sequence $A=\Sequence{A_n}{n\in\omega}$, put
    $$\begin{gathered}
    G_A=\{\langle n,A_n\rangle:n\in\omega\},\qquad
    P_n(A)=\bigcup_{i<n}A_i,\\
    B_n=\SetDifference{A_n}{A_{n+1}},\qquad I=\bigcap_n A_n.
    \end{gathered}$$
-/
def sequenceIntersection (A : ℕ → ZFSet.{u}) : ZFSet.{u} := (A 0).sep (fun x => ∀ n, x ∈ A n)

lemma mem_sequenceIntersection (A : ℕ → ZFSet.{u}) (x : ZFSet.{u}) :
    x ∈ sequenceIntersection A ↔ ∀ n, x ∈ A n := by
  rw [sequenceIntersection, ZFSet.mem_sep]
  exact ⟨And.right, fun h => ⟨h 0, h⟩⟩

lemma sequenceIntersection_mem {M : ZFSet.{u}} (hM : M.IsTransitive) (hunion : M ⊨ unionSentence)
    (hsep : ∀ {k : ℕ} (φ : ForcingFormulas.Formula (k + 1)), M ⊨ separationSentence φ)
    (A : ℕ → ZFSet.{u}) (hG : sequenceGraph A ∈ M) : sequenceIntersection A ∈ M := by
  let R : M := ⟨_, graphRange_mem hM hunion (hsep _) hG⟩
  let p : BoundedSetPredicate 2 := .all 0 (.member 1 2)
  apply p.subset_mem hM (hsep _) ![R] (B := sequenceIntersection A)
    (sequence_term_mem hM hunion A hG 0) (fun _ hx => (ZFSet.mem_sep.mp hx).1)
  intro x _
  change (∀ B ∈ graphRange (sequenceGraph A), x ∈ B) ↔ x ∈ sequenceIntersection A
  rw [mem_sequenceIntersection]
  constructor
  · intro h n
    exact h _ ((mem_sequenceRange A _).mpr ⟨n, rfl⟩)
  · intro h B hB
    obtain ⟨n, rfl⟩ := (mem_sequenceRange A B).mp hB
    exact h n

lemma partialUnion_zero (A : ℕ → ZFSet.{u}) : partialUnion A 0 = ∅ := by
  ext x
  simp only [mem_partialUnion, Nat.not_lt_zero, false_and, exists_false, ZFSet.notMem_empty]

lemma partialUnion_succ (A : ℕ → ZFSet.{u}) (n : ℕ) : partialUnion A (n + 1) = partialUnion A n ∪ A n := by
  ext x
  simp only [mem_partialUnion, ZFSet.mem_union, Nat.lt_succ_iff_lt_or_eq]
  constructor
  · rintro ⟨i, hi | rfl, hx⟩
    · exact Or.inl ⟨i, hi, hx⟩
    · exact Or.inr hx
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, Or.inl hi, hx⟩
    · exact ⟨n, Or.inr rfl, hx⟩

lemma partialUnion_mono (A : ℕ → ZFSet.{u}) {m n : ℕ} (hmn : m ≤ n) : partialUnion A m ⊆ partialUnion A n := by
  intro x hx
  obtain ⟨i, hi, hx⟩ := (mem_partialUnion A m x).mp hx
  exact (mem_partialUnion A n x).mpr ⟨i, hi.trans_le hmn, hx⟩

lemma mem_sequenceUnion_iff_partial (A : ℕ → ZFSet.{u}) (x : ZFSet.{u}) :
    x ∈ sequenceUnion A ↔ ∃ n, x ∈ partialUnion A n := by
  rw [mem_sequenceUnion]
  constructor
  · rintro ⟨n, hx⟩
    exact ⟨n + 1, (mem_partialUnion A (n + 1) x).mpr ⟨n, Nat.lt_succ_self n, hx⟩⟩
  · rintro ⟨n, hx⟩
    obtain ⟨i, _, hi⟩ := (mem_partialUnion A n x).mp hx
    exact ⟨i, hi⟩

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: lemma
  title: Disjoint differences of a decreasing family
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    For $i<j$, $B_j\IncludedIn A_{i+1}$ whereas $B_i$ is disjoint from $A_{i+1}$.
    The finite-union identity follows by induction, starting from $P_0(B)=\emptyset$.
    A point of $A_0$ is outside $I$ exactly when it is outside some $A_n$; taking the union of the finite
    identities gives the second equality.
-/
theorem adjacentDifference_pairwise (A : ℕ → ZFSet.{u})
    (hA : Antitone (fun n => (A n : Set ZFSet))) :
    Pairwise (fun i j => Disjoint ((adjacentDifference A i : ZFSet) : Set ZFSet)
      ((adjacentDifference A j : ZFSet) : Set ZFSet)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx hy
  obtain ⟨hxi, hxi'⟩ := ZFSet.mem_sdiff.mp hx
  obtain ⟨hxj, hxj'⟩ := ZFSet.mem_sdiff.mp hy
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hxi' (hA (Nat.succ_le_of_lt hlt) hxj)
  · exact hxj' (hA (Nat.succ_le_of_lt hgt) hxi)

lemma partialUnion_adjacentDifference (A : ℕ → ZFSet.{u})
    (hA : Antitone (fun n => (A n : Set ZFSet))) (n : ℕ) :
    partialUnion (adjacentDifference A) n = A 0 \ A n := by
  induction n with
  | zero =>
    rw [partialUnion_zero]
    ext x
    simp
  | succ n ih =>
    rw [partialUnion_succ, ih, adjacentDifference]
    ext x
    simp only [ZFSet.mem_union, ZFSet.mem_sdiff]
    have hn : x ∈ A n → x ∈ A 0 := fun hx => hA (Nat.zero_le n) hx
    have hn' : x ∈ A (n + 1) → x ∈ A n := fun hx => hA (Nat.le_succ n) hx
    tauto

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: lemma
  title: Disjoint differences of a decreasing family
-/
theorem sequenceUnion_adjacentDifference (A : ℕ → ZFSet.{u})
    (hA : Antitone (fun n => (A n : Set ZFSet))) :
    sequenceUnion (adjacentDifference A) = A 0 \ sequenceIntersection A := by
  ext x
  simp only [mem_sequenceUnion_iff_partial, partialUnion_adjacentDifference A hA,
    ZFSet.mem_sdiff, mem_sequenceIntersection]
  classical
  simp only [not_forall]
  exact ⟨fun ⟨n, ha, hn⟩ => ⟨ha, n, hn⟩, fun ⟨ha, n, hn⟩ => ⟨n, ha, hn⟩⟩

end PolishSpaceBook.SetTheoryModels
