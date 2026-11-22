module

public import PolishSpaceBook.LambdaHKLLevels
public import PolishSpaceBook.HKLDenseScheduling

@[expose] public section

/-!
# Scheduling dense families in the relative HKL construction

The countable schedules and all levels stay in the fixed-parameter catalog.
Every requested node and edge family is met eventually at every node/edge;
infinitely differing branches meet every compatible rectangle family cofinally.
This module does not infer inequivalence without the generic-pair theorem.
-/

namespace PolishSpaceBook
namespace LambdaTree
open Set

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    A coherent system on this tree consists of nonempty analytic node sets $A_s\IncludedIn H$ and nonempty analytic
    edge relations $R_{s,t}\IncludedIn E\cap(A_s\times A_t)$ whose coordinate projections are exactly $A_s,A_t$.
-/
structure ParameterHKLScheduledSystem (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (F : Set (Set (parameterAnalyticCatalog ε).Condition))
    (J : Set (Set (ParameterCompatibleRectangle ε E)))
    (K : Set (Set (parameterAnalyticCatalog ε).Condition)) where
  level : ∀ n, ParameterTreeSystem ε (crucialPairGraph n)
  edgesIn : ∀ n, (level n).val.EdgesIn E
  node_subset : ∀ n s, (level n).val.node s ⊆ equivalenceGapKernel E (invariantSetoid ε E)
  node_parent : ∀ n s b, (level (n + 1)).val.node (Fin.snoc s b) ⊆ (level n).val.node s
  edge_parent : ∀ n s t b,
    (level (n + 1)).val.edge (Fin.snoc s b) (Fin.snoc t b) ⊆ (level n).val.edge s t
  disjoint : ∀ n r s, Disjoint ((level (n + 1)).val.node (Fin.snoc r false))
    ((level (n + 1)).val.node (Fin.snoc s true))
  node_eventually : ∀ D ∈ F, ∃ N, ∀ n, N ≤ n → ∀ s, (level n).nodeCondition s ∈ D
  edge_eventually : ∀ D ∈ K, ∃ N, ∀ n, N ≤ n → ∀ s t (h : (crucialPairGraph n).Adj s t),
    (level n).edgeCondition h ∈ D
  rectangle_eventually : ∀ D ∈ J, ∃ N, ∀ n, N ≤ n → ∀ r s,
    (level (n + 1)).rectangleCondition (crucialPairGraph_isTree (n + 1)).connected E (edgesIn _)
      (Fin.snoc r false) (Fin.snoc s true) ∈ D ∧
    (level (n + 1)).rectangleCondition (crucialPairGraph_isTree (n + 1)).connected E (edgesIn _)
      (Fin.snoc s true) (Fin.snoc r false) ∈ D

/-- Apply the decreasing schedules to all three finite refinement stages.
Every requirement is eventually met uniformly over its finite level.
The actual kernel supplies the initial condition and all splitting steps. -/
theorem parameter_hkl_scheduled_system_from_kernel (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (hns : ¬ Smooth E.r)
    (F : Set (Set (parameterAnalyticCatalog ε).Condition)) (hFc : F.Countable)
    (hFd : ∀ D ∈ F, IsCoinitial D) (hFl : ∀ D ∈ F, IsLowerSet D)
    (J : Set (Set (ParameterCompatibleRectangle ε E))) (hJc : J.Countable)
    (hJd : ∀ D ∈ J, IsCoinitial D) (hJl : ∀ D ∈ J, IsLowerSet D)
    (K : Set (Set (parameterAnalyticCatalog ε).Condition)) (hKc : K.Countable)
    (hKd : ∀ D ∈ K, IsCoinitial D) (hKl : ∀ D ∈ K, IsLowerSet D) :
    Nonempty (ParameterHKLScheduledSystem ε E F J K) := by
  obtain ⟨d, _, hdd, hdl, hdF⟩ := countable_dense_schedule F hFc hFd hFl
  obtain ⟨j, _, hjd, hjl, hjJ⟩ := countable_dense_schedule J hJc hJd hJl
  obtain ⟨k, _, hkd, hkl, hkK⟩ := countable_dense_schedule K hKc hKd hKl
  obtain ⟨S, hSE, hSΩ, hSd, hSk, hstep⟩ := parameter_hkl_coherent_levels_from_kernel
    E hE hneE hns d hdd hdl j hjd hjl k hkd hkl
  refine ⟨{
    level := S
    edgesIn := hSE
    node_subset := hSΩ
    node_parent := fun n => (hstep n).1
    edge_parent := fun n => (hstep n).2.1
    disjoint := ?_
    node_eventually := ?_
    edge_eventually := ?_
    rectangle_eventually := ?_ }⟩
  · intro n r s
    obtain ⟨_, hpair⟩ := (hstep n).2.2.2.2
    exact (hpair r s).2.2
  · intro D hD
    obtain ⟨N, hN⟩ := hdF D hD
    exact ⟨N, fun n hn s => hN n hn (hSd n s)⟩
  · intro D hD
    obtain ⟨N, hN⟩ := hkK D hD
    exact ⟨N, fun n hn s t h => hN n hn (hSk n s t h)⟩
  · intro D hD
    obtain ⟨N, hN⟩ := hjJ D hD
    refine ⟨N, ?_⟩
    intro n hn r s
    obtain ⟨hTE, hpair⟩ := (hstep n).2.2.2.2
    exact ⟨hN (n + 1) (by omega) (hpair r s).1,
      hN (n + 1) (by omega) (hpair r s).2.1⟩

namespace ParameterHKLScheduledSystem
variable {ε : ℕ → ℕ} {E : Setoid FusionReal}
  {F : Set (Set (parameterAnalyticCatalog ε).Condition)}
  {J : Set (Set (ParameterCompatibleRectangle ε E))}
  {K : Set (Set (parameterAnalyticCatalog ε).Condition)}

/-- Coherence makes every branch rectangle a compatible condition, even at
levels where the last bits agree. -/
def branchRectangle (S : ParameterHKLScheduledSystem ε E F J K) (a b : ℕ → Bool) (n : ℕ) :
    ParameterCompatibleRectangle ε E :=
  (S.level n).rectangleCondition (crucialPairGraph_isTree n).connected E (S.edgesIn n)
    (binaryBranchPrefix a n) (binaryBranchPrefix b n)

theorem branchRectangle_antitone (S : ParameterHKLScheduledSystem ε E F J K) (a b : ℕ → Bool) :
    Antitone (S.branchRectangle a b) := by
  intro n m hnm
  exact ⟨branch_conditions_antitone (fun n => (S.level n).val) S.node_parent a hnm,
    branch_conditions_antitone (fun n => (S.level n).val) S.node_parent b hnm⟩

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Suppose first that $a$ and $b$ differ infinitely often. At the unboundedly many levels where their last bits
    differ, their rectangle lies in $J_n$. Rectangles at all intervening levels remain conditions of
    $\RestrictedGHProduct{E}$ because the level system is coherent.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Thus the descending rectangle sequence is generic,
-/
/-- Infinitely many differing last bits occur beyond the stage assigned to
any dense requirement, so the decreasing rectangle sequence meets it. -/
theorem branchRectangle_meets_of_not_e0 (S : ParameterHKLScheduledSystem ε E F J K)
    {a b : ℕ → Bool} (hab : ¬ E0 a b) :
    ∀ D ∈ J, ∀ N, ∃ n, N ≤ n ∧ S.branchRectangle a b n ∈ D := by
  classical
  have hdiff (N : ℕ) : ∃ n, N ≤ n ∧ a n ≠ b n := by
    by_contra h
    push Not at h
    exact hab ⟨N, h⟩
  intro D hD N
  obtain ⟨M, hM⟩ := S.rectangle_eventually D hD
  obtain ⟨n, hn, hne⟩ := hdiff (max M N)
  refine ⟨n + 1, by omega, ?_⟩
  have hm : M ≤ n := (le_max_left M N).trans hn
  change (S.level (n + 1)).rectangleCondition _ E _ _ _ ∈ D
  rw [binaryBranchPrefix_succ, binaryBranchPrefix_succ]
  cases ha : a n <;> cases hb : b n
  · exact False.elim (hne (ha.trans hb.symm))
  · exact (hM n hm (binaryBranchPrefix a n) (binaryBranchPrefix b n)).1
  · exact (hM n hm (binaryBranchPrefix b n) (binaryBranchPrefix a n)).2
  · exact False.elim (hne (ha.trans hb.symm))

end ParameterHKLScheduledSystem
end LambdaTree
end PolishSpaceBook
