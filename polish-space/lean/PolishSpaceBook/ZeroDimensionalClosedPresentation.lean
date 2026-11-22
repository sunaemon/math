module

public import PolishSpaceBook.CantorBaireSpace

@[expose] public section

/-!
# Closed Baire presentations from shrinking clopen partitions

Disjointify a countable small clopen cover at each node, then retain exactly
the nonempty pieces. The resulting tree carries the book's clopen scheme;
completeness gives its branch homeomorphism. No perfectness or absence of
compact neighborhoods is needed. Zero-dimensional refinement of a general
Polish space is a separate construction.
-/
namespace PolishSpaceBook
open Set TopologicalSpace
noncomputable section
variable {X : Type} [MetricSpace X] [SecondCountableTopology X]

def closedPresentationStep (hzero : IsZeroDimensional X) (U : Set X) (n : ℕ) : ℕ → Set X := by
  classical
  exact if h : IsClopen U then
    (exists_countable_disjoint_clopen_cover_small_of_open hzero h.isOpen
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1))).choose
    else fun _ => ∅

/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    \begin{enumerate}
    \item $\mathcal P_0=\{X\}$;
    \item $\mathcal P_{n+1}$ refines $\mathcal P_n$;
    \item every member of $\mathcal P_n$ has $d$-diameter at most $2^{-n}$;
    \item every $P\in\mathcal P_n$ is the disjoint union of the members of $\mathcal P_{n+1}$ contained in $P$.
    \end{enumerate}
-/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    Index the refinement tree by finite sequences: the root is $X$, and the children of a node are the clopen pieces into
    which it is partitioned at the next stage. Let $T\IncludedIn\finseq{\omega}$ be the set of finite sequences that
    occur. Every retained piece is nonempty and is covered by the next partition, so it has a nonempty successor. Thus $T$
    is a pruned subtree of $\finseq{\omega}$, and its body $\TreeBody{T}$ is closed in $\BaireSpace$ by
    §{sec:closed-sets-trees}. The family of pieces indexed by $T$ has root $X$, splits each piece into a disjoint union of
    its successors, and gives every level-$n$ piece diameter at most $2^{-n}$. The
    \termuseas{clopen scheme lemma}{clopen-scheme lemma} of §{sec:clopen-scheme-characterizations} therefore gives
    $X\cong\TreeBody{T}$.
-/
private theorem closedPresentationStep_spec (hzero : IsZeroDimensional X)
    {U : Set X} (hU : IsClopen U) (n : ℕ) :
    (∀ i, IsClopen (closedPresentationStep hzero U n i) ∧
      closedPresentationStep hzero U n i ⊆ U ∧
      ∀ x ∈ closedPresentationStep hzero U n i, ∀ y ∈ closedPresentationStep hzero U n i,
        dist x y ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
    Pairwise (fun i j => Disjoint (closedPresentationStep hzero U n i)
      (closedPresentationStep hzero U n j)) ∧
    U ⊆ ⋃ i, closedPresentationStep hzero U n i := by
  simpa [closedPresentationStep, hU] using
    (exists_countable_disjoint_clopen_cover_small_of_open hzero hU.isOpen
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1))).choose_spec

/-- Empty pieces are temporarily allowed so the recursion has total domain. -/
def closedPresentationPiece (hzero : IsZeroDimensional X) : List ℕ → Set X :=
  fun s => s.reverseRecOn univ (fun t i U => closedPresentationStep hzero U t.length i)

@[simp] theorem closedPresentationPiece_nil (hzero : IsZeroDimensional X) :
    closedPresentationPiece hzero [] = univ := by simp [closedPresentationPiece]

@[simp] theorem closedPresentationPiece_snoc (hzero : IsZeroDimensional X) (s : List ℕ) (i : ℕ) :
    closedPresentationPiece hzero (s ++ [i]) =
      closedPresentationStep hzero (closedPresentationPiece hzero s) s.length i := by
  simp [closedPresentationPiece]

theorem closedPresentationPiece_clopen (hzero : IsZeroDimensional X) (s : List ℕ) :
    IsClopen (closedPresentationPiece hzero s) := by
  induction s using List.reverseRecOn with
  | nil => simpa using (isClopen_univ : IsClopen (univ : Set X))
  | append_singleton s i ih =>
    simpa using (closedPresentationStep_spec hzero ih s.length).1 i |>.1

theorem closedPresentationPiece_child_subset (hzero : IsZeroDimensional X) (s : List ℕ) (i : ℕ) :
    closedPresentationPiece hzero (s ++ [i]) ⊆ closedPresentationPiece hzero s := by
  simpa using (closedPresentationStep_spec hzero (closedPresentationPiece_clopen hzero s)
    s.length).1 i |>.2.1

theorem closedPresentationPiece_append_subset (hzero : IsZeroDimensional X) (s r : List ℕ) :
    closedPresentationPiece hzero (s ++ r) ⊆ closedPresentationPiece hzero s := by
  induction r using List.reverseRecOn with
  | nil => simp
  | append_singleton r i ih =>
    simpa only [List.append_assoc] using
      (closedPresentationPiece_child_subset hzero (s ++ r) i).trans ih

/-- Discard precisely the empty differences in each disjointified cover. -/
def closedPresentationTree (hzero : IsZeroDimensional X) : Set (List ℕ) :=
  {s | (closedPresentationPiece hzero s).Nonempty}

theorem closedPresentationTree_subtree (hzero : IsZeroDimensional X) :
    IsSubtree (closedPresentationTree hzero) := by
  rintro s t ⟨x, hx⟩ ⟨r, rfl⟩
  exact ⟨x, closedPresentationPiece_append_subset hzero s r hx⟩

/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    Given $\mathcal P_n$, cover each $P\in\mathcal P_n$ by countably many clopen subsets of diameter at most $2^{-(n+1)}$,
    then disjointify the cover inside $P$ and discard the empty differences. This gives the next partition.
-/
/-- The nested partitions supply all hypotheses of the common scheme lemma. -/
theorem closedPresentationScheme [Nonempty X] (hzero : IsZeroDimensional X)
    (hbounded : ∀ x y : X, dist x y ≤ 1) :
    ClopenSchemeMetricCore (closedPresentationTree hzero) (closedPresentationPiece hzero) where
  root_mem := by simp [closedPresentationTree]
  root_eq := closedPresentationPiece_nil hzero
  nonempty := fun {_} hs => hs
  clopen := fun {s} _ => closedPresentationPiece_clopen hzero s
  children_cover := by
    intro s hs
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp
        ((closedPresentationStep_spec hzero (closedPresentationPiece_clopen hzero s) s.length).2.2 hx)
      have hxi : x ∈ closedPresentationPiece hzero (s ++ [i]) := by simpa using hi
      exact mem_iUnion.mpr ⟨⟨i, ⟨x, hxi⟩⟩, hxi⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact closedPresentationPiece_child_subset hzero s i.val hi
  children_disjoint := by
    intro s hs i j hij
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    simpa [concat] using (closedPresentationStep_spec hzero (closedPresentationPiece_clopen hzero s)
      s.length).2.1 hne
  dist_bound := by
    intro s hs
    induction s using List.reverseRecOn with
    | nil => intro x _ y _; simpa using hbounded x y
    | append_singleton s i ih =>
      simpa using (closedPresentationStep_spec hzero (closedPresentationPiece_clopen hzero s)
        s.length).1 i |>.2.2

/-- Every retained piece lies on the branch coding any of its points. -/
theorem closedPresentationTree_pruned [Nonempty X] (hzero : IsZeroDimensional X)
    (hbounded : ∀ x y : X, dist x y ≤ 1) : IsPruned (closedPresentationTree hzero) := by
  let H := (closedPresentationScheme hzero hbounded).toClopenSchemeCore
  have hpref (s : List ℕ) {x : X} (hx : x ∈ closedPresentationPiece hzero s) :
      seqPrefix (clopenSchemeCore_pointBranch H x) s.length = s := by
    induction s using List.reverseRecOn with
    | nil => simp [seqPrefix]
    | append_singleton s i ih =>
      have hxpar := closedPresentationPiece_child_subset hzero s i hx
      have hs := ih hxpar
      let b := clopenSchemeCore_pointBranch H x
      have hxb : x ∈ closedPresentationPiece hzero (s ++ [b s.length]) := by
        have h := clopenSchemeCore_pointBranch_point_mem H x (s.length + 1)
        simpa only [seqPrefix_succ_eq_concat, hs, concat] using h
      have hi : b s.length = i := by
        by_contra hn
        have hd := (closedPresentationStep_spec hzero
          (closedPresentationPiece_clopen hzero s) s.length).2.1 hn
        exact Set.disjoint_left.mp hd (by simpa using hxb) (by simpa using hx)
      change clopenSchemeCore_pointBranch H x s.length = i at hi
      simp only [List.length_append, List.length_singleton, seqPrefix_succ_eq_concat,
        hs, concat, hi]
  rintro s ⟨x, hx⟩
  refine ⟨clopenSchemeCore_pointBranch H x, clopenSchemeCore_pointBranch_mem_treeBody H x, ?_⟩
  simpa only [hpref s hx] using mem_cyl_seqPrefix (clopenSchemeCore_pointBranch H x) s.length

/-- The explicit shrinking partition tree presents the complete space. -/
theorem exists_closed_presentation_of_bounded_metric [Nonempty X]
    (hcomplete : IsMetricComplete X) (hzero : IsZeroDimensional X)
    (hbounded : ∀ x y : X, dist x y ≤ 1) :
    ∃ F : Set (ℕ → ℕ), IsClosed F ∧ Nonempty (X ≃ₜ F) := by
  exact ⟨treeBody (closedPresentationTree hzero), isClosed_treeBody _,
    ⟨(clopenSchemeMetricCore_branchPointHomeomorph hcomplete
      (closedPresentationTree_subtree hzero) (closedPresentationScheme hzero hbounded)).symm⟩⟩

end

/-- Every zero-dimensional Polish space has a closed Baire presentation,
using the canonical small-inductive-dimension predicate in the public API. -/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: statement
  excerpt: |
    \begin{theorem*}[\termdefineas{compatible Polish topologies theorem}{Compatible Polish topologies}] Let $(X, \mathcal
-/
/-@ booklink:
  source: polish-space-book/polish-embeddings-borel-refinements.md
  target: prose
  excerpt: |
    First prove the zero-dimensional statement. The empty space is homeomorphic to the empty closed
    subset of $\BaireSpace$, so assume that $X$ is nonempty. Fix a complete compatible metric $d\le 1$. To obtain a
    countable clopen base, cover each member of a countable base by clopen subsets contained in it, take a countable
    subcover by Lindelöfness, and unite these subcovers. Recursively build countable clopen partitions $\mathcal P_n$ of $X$
    such that:
-/
theorem exists_zero_dimensional_closed_presentation (X : Type) [t : TopologicalSpace X]
    [PolishSpace X] (hzero : HasSmallInductiveDimensionLE X 0) :
    ∃ F : Set (ℕ → ℕ), IsClosed F ∧ Nonempty (X ≃ₜ F) := by
  classical
  cases isEmpty_or_nonempty X with
  | inl he =>
    let := he
    exact ⟨∅, isClosed_empty, ⟨Homeomorph.empty⟩⟩
  | inr hn =>
    let := hn
    let := upgradeIsCompletelyMetrizable X
    have hcomplete : IsMetricComplete X := (isMetricComplete_iff_completeSpace X).mpr inferInstance
    obtain ⟨m, ht, hm, _, hb⟩ := complete_compatible_metric_bounded_by_one X hcomplete
    let m' := m.replaceTopology ht.symm
    have hmeq : m' = m := MetricSpace.replaceTopology_eq m ht.symm
    let : MetricSpace X := m'
    have hm' : IsMetricComplete X := by
      change @IsMetricComplete X m'
      rw [hmeq]
      exact hm
    have hb' : ∀ x y : X, dist x y ≤ 1 := by
      change ∀ x y : X, @dist X m'.toDist x y ≤ 1
      rw [hmeq]
      exact hb
    exact exists_closed_presentation_of_bounded_metric hm'
      ((zero_dimensional_iff_small_inductive X).mpr hzero) hb'

end PolishSpaceBook
