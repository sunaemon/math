module

public import PolishSpaceBook.HKLLevelConstruction
public import PolishSpaceBook.AnalyticConditionFusion

@[expose] public section

/-!
# Fusion along branches of the HKL system

This module connects decreasing branch conditions with the proved
closed-witness fusion theorem. Continuity is derived from uniform prefix
smallness of the level sets and injectivity from cross-last-bit disjointness.
The effective presentation codes and the generic-pair theorem remain separate.
-/

namespace PolishSpaceBook
open Set Function Filter Topology MeasureTheory

/-- The finite initial segment of a Cantor-space branch. -/
def binaryBranchPrefix (a : ℕ → Bool) (n : ℕ) : binaryWord n := fun i => a i.val

theorem binaryBranchPrefix_succ (a : ℕ → Bool) (n : ℕ) :
    binaryBranchPrefix a (n + 1) = Fin.snoc (binaryBranchPrefix a n) (a n) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [binaryBranchPrefix]

theorem continuous_binaryBranchPrefix (n : ℕ) : Continuous (fun a => binaryBranchPrefix a n) :=
  continuous_pi (fun i => continuous_apply i.val)

variable {X : Type*} [TopologicalSpace X]

/-- Parent containment becomes monotonicity along every infinite branch. -/
theorem branch_conditions_antitone
    (S : ∀ n, AnalyticTreeSystem (crucialPairGraph n) X)
    (hnest : ∀ n s b, (S (n + 1)).node (Fin.snoc s b) ⊆ (S n).node s)
    (a : ℕ → Bool) : Antitone (fun n => (S n).nodeCondition (binaryBranchPrefix a n)) := by
  apply antitone_nat_of_succ_le
  intro n
  change (S (n + 1)).node (binaryBranchPrefix a (n + 1)) ⊆ (S n).node (binaryBranchPrefix a n)
  rw [binaryBranchPrefix_succ]
  exact hnest n _ _

/-- Encode an analytic condition by a continuous map into Baire space. -/
def encodeAnalyticCondition [PolishSpace X] (f : X → FusionReal) (hf : Continuous f)
    (P : AnalyticCondition X) : AnalyticCondition FusionReal :=
  ⟨f '' P.val, P.property.1.image_of_continuous hf, P.property.2.image f⟩

/-- Pulling a lower family back along continuous encoding preserves lowerness. -/
theorem encodeAnalyticCondition_preimage_lower [PolishSpace X]
    (f : X → FusionReal) (hf : Continuous f)
    {D : Set (AnalyticCondition FusionReal)} (hD : IsLowerSet D) :
    IsLowerSet (encodeAnalyticCondition f hf ⁻¹' D) := by
  intro P Q hPQ hQ
  exact hD (Set.image_mono hPQ) hQ

/-- Every refinement of an encoded condition can be pulled back exactly.
Thus dense families stay dense under continuous injective encoding. -/
theorem encodeAnalyticCondition_preimage_coinitial [PolishSpace X]
    (f : X → FusionReal) (hf : Continuous f) (hinj : Injective f)
    {D : Set (AnalyticCondition FusionReal)} (hD : IsCoinitial D) :
    IsCoinitial (encodeAnalyticCondition f hf ⁻¹' D) := by
  intro P
  obtain ⟨Q, hQD, hQP⟩ := hD (encodeAnalyticCondition f hf P)
  have hnonempty : (f ⁻¹' Q.val).Nonempty := by
    obtain ⟨y, hy⟩ := Q.property.2
    obtain ⟨x, _, hxy⟩ := hQP hy
    exact ⟨x, by simpa only [Set.mem_preimage, hxy] using hy⟩
  let R : AnalyticCondition X := ⟨f ⁻¹' Q.val, Q.property.1.preimage hf, hnonempty⟩
  have hR : encodeAnalyticCondition f hf R = Q := by
    apply Subtype.ext
    apply Set.Subset.antisymm (Set.image_preimage_subset _ _)
    intro y hy
    obtain ⟨x, _, hxy⟩ := hQP hy
    exact ⟨x, by simpa only [Set.mem_preimage, hxy] using hy, hxy⟩
  refine ⟨R, ?_, ?_⟩
  · change encodeAnalyticCondition f hf R ∈ D
    rwa [hR]
  · intro x hx
    obtain ⟨z, hz, hzx⟩ := hQP hx
    simpa only [hinj hzx] using hz

/-- Fusion of encoded conditions produces a point in the original space:
actual membership in the first image supplies a preimage, and injectivity
makes that preimage belong to every subsequent condition. -/
theorem analytic_fusion_of_encoding [PolishSpace X]
    (f : X → FusionReal) (hf : Continuous f) (hinj : Injective f)
    (K : ℕ → Set (FusionReal × FusionReal)) (hK : ∀ i, IsClosed (K i))
    (P : ℕ → AnalyticCondition X) (hP : Antitone P)
    (hpres : ∀ r, ∃ i, f '' (P r).val = Prod.fst '' K i)
    (hmeet : ∀ D ∈ analyticFusionRequirements K,
      ∃ m, encodeAnalyticCondition f hf (P m) ∈ D) :
    ∃! x : X, ∀ r, x ∈ (P r).val := by
  obtain ⟨y, hy, huniq⟩ := analytic_fusion_of_meets_countable_requirements K hK
    (fun r => encodeAnalyticCondition f hf (P r))
    (fun i j hij => Set.image_mono (hP hij)) hpres hmeet
  obtain ⟨x, _, hfx⟩ := hy 0
  refine ⟨x, ?_, ?_⟩
  · intro r
    obtain ⟨z, hz, hfz⟩ := hy r
    have hzx : z = x := hinj (hfz.trans hfx.symm)
    simpa only [hzx] using hz
  · intro z hz
    apply hinj
    exact (huniq (f z) (fun r => ⟨z, hz r, rfl⟩)).trans hfx.symm

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Distinct branches differ at some coordinate, and the corresponding level's
    node sets are disjoint by requirement (3), so $\pi$ is injective.
-/
/-- Actual branch membership and cross-last-bit disjointness give injectivity. -/
theorem injective_of_branch_membership
    (S : ∀ n, AnalyticTreeSystem (crucialPairGraph n) X)
    (hdisj : ∀ n r s, Disjoint ((S (n + 1)).node (Fin.snoc r false))
      ((S (n + 1)).node (Fin.snoc s true)))
    (π : (ℕ → Bool) → X) (hπ : ∀ a n, π a ∈ (S n).node (binaryBranchPrefix a n)) :
    Injective π := by
  intro a b hab
  funext k
  have ha := hπ a (k + 1)
  have hb := hπ b (k + 1)
  rw [binaryBranchPrefix_succ] at ha hb
  rw [← hab] at hb
  cases hka : a k <;> cases hkb : b k
  · rfl
  · exact False.elim (Set.disjoint_left.mp (hdisj k (binaryBranchPrefix a k) (binaryBranchPrefix b k))
      (by simpa only [hka] using ha) (by simpa only [hkb] using hb))
  · exact False.elim (Set.disjoint_left.mp (hdisj k (binaryBranchPrefix b k) (binaryBranchPrefix a k))
      (by simpa only [hkb] using hb) (by simpa only [hka] using ha))
  · rfl

/-- Prefix smallness makes output digits locally constant for any binary
scheme of analytic conditions, independently of the HKL edge structure. -/
theorem continuous_of_binary_condition_membership
    (A : ∀ n, binaryWord n → AnalyticCondition FusionReal)
    (hsmall : ∀ k, ∃ n, ∀ s, A n s ∈ smallPrefixRequirement (k + 1))
    (π : (ℕ → Bool) → FusionReal)
    (hπ : ∀ a n, π a ∈ (A n (binaryBranchPrefix a n)).val) : Continuous π := by
  apply continuous_pi
  intro k
  rw [continuous_iff_continuousAt]
  intro a
  obtain ⟨n, hn⟩ := hsmall k
  have hc := continuous_binaryBranchPrefix n
  have hopen : IsOpen {b : ℕ → Bool | binaryBranchPrefix b n = binaryBranchPrefix a n} :=
    (isOpen_discrete ({binaryBranchPrefix a n} : Set (binaryWord n))).preimage hc
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [hopen.mem_nhds (by rfl : a ∈ {b | binaryBranchPrefix b n = binaryBranchPrefix a n})] with b hb
  have hpb := hπ b n
  rw [hb] at hpb
  exact hn (binaryBranchPrefix a n) (π b) hpb (π a) (hπ a n) k (Nat.lt_succ_self k)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Shrinking diameters give continuity.
-/
/-- Uniformly small level sets make each output digit locally constant on a
sufficiently long input cylinder. This is continuity in the Baire topology. -/
theorem continuous_of_branch_membership
    (S : ∀ n, AnalyticTreeSystem (crucialPairGraph n) FusionReal)
    (hsmall : ∀ k, ∃ n, ∀ s, (S n).nodeCondition s ∈ smallPrefixRequirement (k + 1))
    (π : (ℕ → Bool) → FusionReal)
    (hπ : ∀ a n, π a ∈ (S n).node (binaryBranchPrefix a n)) : Continuous π :=
  continuous_of_binary_condition_membership (fun n => (S n).nodeCondition) hsmall π hπ

/-- Uniform encounters with the countable fusion family give actual unique
points along every branch, and hence a continuous injection. Each node must
have a closed presentation in the supplied list. -/
theorem hkl_branch_embedding_baire
    (S : ∀ n, AnalyticTreeSystem (crucialPairGraph n) FusionReal)
    (hnest : ∀ n s b, (S (n + 1)).node (Fin.snoc s b) ⊆ (S n).node s)
    (hdisj : ∀ n r s, Disjoint ((S (n + 1)).node (Fin.snoc r false))
      ((S (n + 1)).node (Fin.snoc s true)))
    (K : ℕ → Set (FusionReal × FusionReal)) (hK : ∀ i, IsClosed (K i))
    (hpres : ∀ n s, ∃ i, (S n).node s = Prod.fst '' K i)
    (hmeet : ∀ D ∈ analyticFusionRequirements K, ∃ n, ∀ s, (S n).nodeCondition s ∈ D) :
    ∃ π : (ℕ → Bool) → FusionReal, Continuous π ∧ Injective π ∧
      ∀ a n, π a ∈ (S n).node (binaryBranchPrefix a n) := by
  have hpoint a : ∃! x : FusionReal, ∀ n, x ∈ (S n).node (binaryBranchPrefix a n) := by
    apply analytic_fusion_of_meets_countable_requirements K hK
      (fun n => (S n).nodeCondition (binaryBranchPrefix a n)) (branch_conditions_antitone S hnest a)
      (fun n => hpres n _)
    intro D hD
    obtain ⟨n, hn⟩ := hmeet D hD
    exact ⟨n, hn _⟩
  choose π hπ using fun a => (hpoint a).exists
  have hsmall k : ∃ n, ∀ s, (S n).nodeCondition s ∈ smallPrefixRequirement (k + 1) :=
    hmeet _ (Or.inl ⟨k + 1, rfl⟩)
  exact ⟨π, continuous_of_branch_membership S hsmall π hπ,
    injective_of_branch_membership S hdisj π hπ, hπ⟩

end PolishSpaceBook
