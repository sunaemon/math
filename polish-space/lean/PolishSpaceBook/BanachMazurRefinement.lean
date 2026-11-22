module

public import PolishSpaceBook.BanachMazurGame
public import Mathlib.Topology.Bases

@[expose] public section

/-!
# Countable disjoint response families

Visit a countable basis in order. Keep the response to a basic open set precisely
when that basic open set misses all responses already kept. The selected responses
are pairwise disjoint and have dense union. Applying this at a fixed history
provides the successor families in the Banach–Mazur converse proof.
-/
noncomputable section
namespace PolishSpaceBook.BanachMazurGame
open Set Topology TopologicalSpace
open scoped Classical
variable {X : Type*}

/-- Empty pieces record skipped basic opens, without changing the enumeration. -/
def greedyPiece (B R : ℕ → Set X) (n : ℕ) : Set X :=
  if Disjoint (B n) (⋃ i : Fin n, greedyPiece B R i.val) then R n else ∅
termination_by n

theorem greedyPiece_rule (B R : ℕ → Set X) (n : ℕ) :
    greedyPiece B R n =
      if Disjoint (B n) (⋃ i : Fin n, greedyPiece B R i.val) then R n else ∅ := by
  rw [greedyPiece]

lemma greedyPiece_subset (B R : ℕ → Set X) (n : ℕ) : greedyPiece B R n ⊆ R n := by
  rw [greedyPiece_rule]
  split_ifs <;> simp

lemma greedyPiece_eq_of_nonempty (B R : ℕ → Set X) {n : ℕ}
    (hn : (greedyPiece B R n).Nonempty) : greedyPiece B R n = R n := by
  rw [greedyPiece_rule] at hn ⊢
  split_ifs at hn ⊢ with h
  · rfl
  · exact (Set.not_nonempty_empty hn).elim

lemma greedyPiece_disjoint_of_lt (B R : ℕ → Set X) (hRB : ∀ n, R n ⊆ B n)
    {m n : ℕ} (hmn : m < n) : Disjoint (greedyPiece B R m) (greedyPiece B R n) := by
  rw [greedyPiece_rule B R n]
  split_ifs with hn
  · exact (hn.mono (hRB n) (subset_iUnion_of_subset ⟨m, hmn⟩ Subset.rfl)).symm
  · simp

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Disjoint response refinement
-/
lemma greedyPiece_pairwise (B R : ℕ → Set X) (hRB : ∀ n, R n ⊆ B n) :
    Pairwise (fun m n => Disjoint (greedyPiece B R m) (greedyPiece B R n)) := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact greedyPiece_disjoint_of_lt B R hRB h
  · exact (greedyPiece_disjoint_of_lt B R hRB h).symm

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Disjoint response refinement
-/
lemma greedyPiece_isOpen [TopologicalSpace X] (B R : ℕ → Set X)
    (hR : ∀ n, IsOpen (R n)) (n : ℕ) : IsOpen (greedyPiece B R n) := by
  rw [greedyPiece_rule]
  split_ifs
  · exact hR n
  · exact isOpen_empty

/-- Every nonempty open test set meets an accepted response, or an earlier one that blocked it. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Disjoint response refinement
-/
theorem greedyPiece_dense [TopologicalSpace X] (W : Set X) (hW : IsOpen W)
    (B R : ℕ → Set X) (hR : ∀ n, (R n).Nonempty) (hRB : ∀ n, R n ⊆ B n)
    (hbase : ∀ U, IsOpen U → U.Nonempty → U ⊆ W → ∃ n, B n ⊆ U) :
    W ⊆ closure (⋃ n, greedyPiece B R n) := by
  intro x hx
  rw [mem_closure_iff]
  intro O hO hxO
  obtain ⟨n, hn⟩ := hbase (O ∩ W) (hO.inter hW) ⟨x, hxO, hx⟩ inter_subset_right
  by_cases h : Disjoint (B n) (⋃ i : Fin n, greedyPiece B R i.val)
  · obtain ⟨y, hy⟩ := hR n
    refine ⟨y, (hn (hRB n hy)).1, mem_iUnion.mpr ⟨n, ?_⟩⟩
    rw [greedyPiece_rule, ite_eq_left h]
    exact hy
  · obtain ⟨y, hyB, hy⟩ := Set.not_disjoint_iff.mp h
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    exact ⟨y, (hn hyB).1, mem_iUnion.mpr ⟨i.val, hi⟩⟩

section Metric
variable [MetricSpace X] [SecondCountableTopology X]

/-- The countable basis has enough nonempty members with closure inside the parent open set. -/
theorem exists_refining_basis (W : Move X) :
    ∃ B : ℕ → Move X, (∀ n, closure (B n).openSet ⊆ W.openSet) ∧
      ∀ U, IsOpen U → U.Nonempty → U ⊆ W.openSet → ∃ n, (B n).openSet ⊆ U := by
  let S : Set (Set X) := {s ∈ countableBasis X | closure s ⊆ W.openSet}
  have hc : S.Countable := (countable_countableBasis X).mono (fun _ h => h.1)
  have hn : S.Nonempty := by
    obtain ⟨x, hx⟩ := W.nonempty
    obtain ⟨s, hs, _, hsub⟩ := (isBasis_countableBasis X).exists_closure_subset (W.isOpen.mem_nhds hx)
    exact ⟨s, hs, hsub⟩
  obtain ⟨b, hb⟩ := hc.exists_eq_range hn
  have hmem (n : ℕ) : b n ∈ S := by rw [hb]; exact mem_range_self n
  let B : ℕ → Move X := fun n =>
    ⟨b n, isOpen_of_mem_countableBasis (hmem n).1, nonempty_of_mem_countableBasis (hmem n).1⟩
  refine ⟨B, fun n => (hmem n).2, fun U hU hUn hUW => ?_⟩
  obtain ⟨x, hx⟩ := hUn
  obtain ⟨s, hs, _, hsub⟩ := (isBasis_countableBasis X).exists_closure_subset (hU.mem_nhds hx)
  have hsS : s ∈ S := ⟨hs, hsub.trans hUW⟩
  rw [hb] at hsS
  obtain ⟨n, rfl⟩ := hsS
  exact ⟨n, subset_closure.trans hsub⟩

/-- A countable family of legal next moves with disjoint, relatively dense responses. -/
structure ResponseFamily (σ : Strategy X) (history : List (Move X)) (W : Move X) where
  moves : ℕ → Move X
  selected : Set ℕ
  closure_subset : ∀ n, closure (moves n).openSet ⊆ W.openSet
  disjoint : selected.Pairwise (fun m n =>
    Disjoint (σ history (moves m)).openSet (σ history (moves n)).openSet)
  dense : W.openSet ⊆ closure (⋃ n ∈ selected, (σ history (moves n)).openSet)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Every nonempty open $O\IncludedIn W$ contains some $B_j$ of this enumeration: choose a small open ball with
    closure in $O$, and then a basic open set inside that ball. The nonempty sets $C_j$ are disjoint by construction.
    To see that their union meets $O$, choose $B_j\IncludedIn O$. If the rule accepts $R_j$, then
    $R_j\IncludedIn O$ is a nonempty part of the union. If the rule rejects it, then $B_j$ meets some earlier $C_i$,
    so again $O$ meets the union. The union is open because all its nonempty pieces are open.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Disjoint response refinement
-/
def responseFamily (σ : Strategy X) (history : List (Move X)) (W : Move X) :
    ResponseFamily σ history W := by
  let B := (exists_refining_basis W).choose
  have hBW := (exists_refining_basis W).choose_spec.1
  have hbase := (exists_refining_basis W).choose_spec.2
  let R : ℕ → Set X := fun n => (σ history (B n)).openSet
  let C := greedyPiece (fun n => (B n).openSet) R
  let I : Set ℕ := {n | (C n).Nonempty}
  have hRB (n : ℕ) : R n ⊆ (B n).openSet :=
    subset_closure.trans (σ history (B n)).closure_subset
  have hCi {n : ℕ} (hn : n ∈ I) : C n = R n := greedyPiece_eq_of_nonempty _ _ hn
  have hUnion : (⋃ n, C n) = ⋃ n ∈ I, R n := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      have hne : n ∈ I := ⟨x, hn⟩
      exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hne, hCi hne ▸ hn⟩⟩
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      obtain ⟨hi, hxR⟩ := mem_iUnion.mp hn
      exact mem_iUnion.mpr ⟨n, (hCi hi).symm ▸ hxR⟩
  refine ⟨B, I, hBW, ?_, ?_⟩
  · intro m hm n hn hmn
    change Disjoint (R m) (R n)
    rw [← hCi hm, ← hCi hn]
    exact greedyPiece_pairwise _ _ hRB hmn
  · rw [← hUnion]
    exact greedyPiece_dense W.openSet W.isOpen _ R (fun n => (σ history (B n)).nonempty) hRB hbase

omit [SecondCountableTopology X] in
lemma ResponseFamily.union_subset {σ : Strategy X} {h : List (Move X)} {W : Move X}
    (F : ResponseFamily σ h W) :
    (⋃ n ∈ F.selected, (σ h (F.moves n)).openSet) ⊆ W.openSet := by
  intro x hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp hx
  obtain ⟨_, hxR⟩ := mem_iUnion.mp hn
  exact F.closure_subset n (subset_closure ((σ h (F.moves n)).closure_subset (subset_closure hxR)))

omit [SecondCountableTopology X] in
lemma ResponseFamily.isOpen_union {σ : Strategy X} {h : List (Move X)} {W : Move X}
    (F : ResponseFamily σ h W) : IsOpen (⋃ n ∈ F.selected, (σ h (F.moves n)).openSet) :=
  isOpen_iUnion fun n => isOpen_iUnion fun _ => (σ h (F.moves n)).isOpen

end Metric
end PolishSpaceBook.BanachMazurGame
