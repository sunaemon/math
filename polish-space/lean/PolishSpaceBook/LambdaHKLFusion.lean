module

public import PolishSpaceBook.LambdaHKLScheduling

@[expose] public section

/-!
# Actual relative HKL branch and edge fusion

The parameter catalog supplies every closed witness presentation. Its own
countable fusion requirements therefore give actual unique branch members
and actual pair witnesses, without new presentation assumptions. Node
uniqueness identifies the pair coordinates and proves the forward E0
implication. The converse still requires the HKL generic-pair truth theorem.
-/

namespace PolishSpaceBook
namespace LambdaTree
open Set Function

namespace ParameterHKLScheduledSystem
variable {ε : ℕ → ℕ} {E : Setoid FusionReal}
  {F : Set (Set (parameterAnalyticCatalog ε).Condition)}
  {J : Set (Set (ParameterCompatibleRectangle ε E))}
  {K : Set (Set (parameterAnalyticCatalog ε).Condition)}

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For each branch $a$, analytic-condition fusion gives a unique actual member
    $$\pi(a)\in\bigcap_n A_{\restrict{a}{n}}.$$
-/
/-- Each branch has a unique actual member, with its analytic witnesses. -/
theorem branch_unique (S : ParameterHKLScheduledSystem ε E F J K)
    (hF : (parameterAnalyticCatalog ε).requirements ⊆ F) (a : ℕ → Bool) :
    ∃! x : FusionReal, ∀ n, x ∈ (S.level n).val.node (binaryBranchPrefix a n) := by
  apply (parameterAnalyticCatalog ε).fusion
    (fun n => (S.level n).nodeCondition (binaryBranchPrefix a n))
    (fun n m hnm => branch_conditions_antitone (fun n => (S.level n).val) S.node_parent a hnm)
  intro D hD
  obtain ⟨N, hN⟩ := S.node_eventually D (hF hD)
  exact ⟨N, hN N le_rfl _⟩

/-- Uniform prefix smallness and actual membership give a continuous injection. -/
theorem branch_embedding (S : ParameterHKLScheduledSystem ε E F J K)
    (hF : (parameterAnalyticCatalog ε).requirements ⊆ F) :
    ∃ π : (ℕ → Bool) → FusionReal, Continuous π ∧ Injective π ∧
      (∀ a n, π a ∈ (S.level n).val.node (binaryBranchPrefix a n)) ∧
      ∀ a x, (∀ n, x ∈ (S.level n).val.node (binaryBranchPrefix a n)) → x = π a := by
  choose π hπ using fun a => (S.branch_unique hF a).exists
  have hsmall k : ∃ n, ∀ s,
      (S.level n).val.nodeCondition s ∈ smallPrefixRequirement (k + 1) := by
    have hmem : {P : (parameterAnalyticCatalog ε).Condition |
        P.val ∈ smallPrefixRequirement (k + 1)} ∈ (parameterAnalyticCatalog ε).requirements :=
      ⟨smallPrefixRequirement (k + 1), Or.inl ⟨k + 1, rfl⟩, rfl⟩
    obtain ⟨N, hN⟩ := S.node_eventually _ (hF hmem)
    exact ⟨N, hN N le_rfl⟩
  exact ⟨π, continuous_of_branch_membership (fun n => (S.level n).val) hsmall π hπ,
    injective_of_branch_membership (fun n => (S.level n).val) S.disjoint π hπ, hπ,
    fun a x hx => (S.branch_unique hF a).unique hx (hπ a)⟩

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    For the other direction, first take
    $$a=0^k\concat(0)\concat c,\qquad b=0^k\concat(1)\concat c.$$
    Their prefixes form a crucial pair at every level after $k$. By requirement (2), the corresponding edge relations
    form a decreasing sequence meeting every $K_n$. Analytic-condition fusion in $X^2$ gives an actual pair in all of
    these relations. Its coordinates must be $\pi(a),\pi(b)$ by node uniqueness. Since every edge relation is contained
    in $E$, this proves $\pi(a)\mathrel E\pi(b)$.
-/
/-- Fuse the encoded edge conditions, decode their actual pair, and identify
both coordinates by the already proved uniqueness of branch membership. -/
theorem elementary_related (S : ParameterHKLScheduledSystem ε E F J K)
    (hK : (parameterAnalyticCatalog ε).requirements ⊆ K)
    (π : (ℕ → Bool) → FusionReal)
    (hunique : ∀ a x, (∀ n, x ∈ (S.level n).val.node (binaryBranchPrefix a n)) → x = π a)
    (k : ℕ) (c : ℕ → Bool) :
    E.r (π (binaryWordTail (zeroBinaryWord k) (binaryCons false c)))
      (π (binaryWordTail (zeroBinaryWord k) (binaryCons true c))) := by
  let a := binaryWordTail (zeroBinaryWord k) (binaryCons false c)
  let b := binaryWordTail (zeroBinaryWord k) (binaryCons true c)
  have hadj j := (elementary_prefix_crucial k c j).adj
  let P (j : ℕ) : (parameterAnalyticCatalog ε).Condition :=
    (S.level (k + 1 + j)).edgeCondition (hadj j)
  have hP : Antitone P := by
    apply antitone_nat_of_succ_le
    intro j p hp
    change (leftBaire p, rightBaire p) ∈ (S.level (k + 1 + (j + 1))).val.edge
      (binaryBranchPrefix a (k + 1 + (j + 1)))
      (binaryBranchPrefix b (k + 1 + (j + 1))) at hp
    rw [Nat.add_succ, binaryBranchPrefix_succ, binaryBranchPrefix_succ] at hp
    have hab : a (k + 1 + j) = b (k + 1 + j) := elementary_branches_agree k c (by omega)
    rw [hab] at hp
    exact S.edge_parent _ _ _ _ hp
  obtain ⟨p, hp, _⟩ := (parameterAnalyticCatalog ε).fusion P hP (by
    intro D hD
    obtain ⟨N, hN⟩ := S.edge_eventually D (hK hD)
    exact ⟨N, hN (k + 1 + N) (by omega) _ _ (hadj N)⟩)
  have hnodes := edge_witness_branch_membership (fun n => (S.level n).val)
    S.node_parent a b (k + 1) hadj (leftBaire p, rightBaire p) hp
  have hl := hunique a (leftBaire p) hnodes.1
  have hr := hunique b (rightBaire p) hnodes.2
  have hrel := S.edgesIn (k + 1 + 0) _ _ (hadj 0) (leftBaire p, rightBaire p) (hp 0)
  simpa only [hl, hr] using hrel

theorem e0_preserved (S : ParameterHKLScheduledSystem ε E F J K)
    (hK : (parameterAnalyticCatalog ε).requirements ⊆ K)
    (π : (ℕ → Bool) → FusionReal)
    (hunique : ∀ a x, (∀ n, x ∈ (S.level n).val.node (binaryBranchPrefix a n)) → x = π a)
    {a b : ℕ → Bool} (hab : E0 a b) : E.r (π a) (π b) := by
  apply e0_preserved_of_crucial_pairs E π _ hab
  exact S.elementary_related hK π hunique

end ParameterHKLScheduledSystem

/-- From the actual nonsmooth kernel obtain a continuous injection preserving
E0, whose infinitely differing branches meet every supplied rectangle test.
No converse, and hence no Borel reduction or dichotomy, is claimed here. -/
theorem parameter_hkl_forward_embedding (ε : ℕ → ℕ) (E : Setoid FusionReal)
    (hE : ProjectedRelation ε E.r)
    (hneE : ProjectedRelation ε (fun x y => ¬ E.r x y))
    (hns : ¬ Smooth E.r)
    (J : Set (Set (ParameterCompatibleRectangle ε E))) (hJc : J.Countable)
    (hJd : ∀ D ∈ J, IsCoinitial D) (hJl : ∀ D ∈ J, IsLowerSet D) :
    ∃ (S : ParameterHKLScheduledSystem ε E (parameterAnalyticCatalog ε).requirements
        J (parameterAnalyticCatalog ε).requirements) (π : (ℕ → Bool) → FusionReal),
      Continuous π ∧ Injective π ∧
      (∀ a n, π a ∈ (S.level n).val.node (binaryBranchPrefix a n)) ∧
      (∀ a b, E0 a b → E.r (π a) (π b)) ∧
      ∀ a b, ¬ E0 a b → ∀ D ∈ J, ∀ N, ∃ n, N ≤ n ∧ S.branchRectangle a b n ∈ D := by
  let C := parameterAnalyticCatalog ε
  obtain ⟨S⟩ := parameter_hkl_scheduled_system_from_kernel ε E hE hneE hns
    C.requirements C.requirements_countable
    (fun D hD => (C.requirements_dense_lower D hD).1)
    (fun D hD => (C.requirements_dense_lower D hD).2)
    J hJc hJd hJl C.requirements C.requirements_countable
    (fun D hD => (C.requirements_dense_lower D hD).1)
    (fun D hD => (C.requirements_dense_lower D hD).2)
  obtain ⟨π, hc, hi, hm, hu⟩ := S.branch_embedding Subset.rfl
  exact ⟨S, π, hc, hi, hm, fun _ _ h => S.e0_preserved Subset.rfl π hu h,
    fun _ _ h => S.branchRectangle_meets_of_not_e0 h⟩

end LambdaTree
end PolishSpaceBook
