module

public import PolishSpaceBook.HKLEdgeFusion

@[expose] public section

/-!
# Scheduling the countable dense requirements of HKL

Finite initial intersections turn a countable family of lower dense sets into
a decreasing schedule. Every requirement then holds at all sufficiently late
levels. The construction uses the proved three-stage refinement and retains
the explicit analytic-kernel splitting hypothesis. It does not supply the
effective closed presentations or the nonsmooth-kernel theorem.
-/

namespace PolishSpaceBook
open Set Function MeasureTheory

section Scheduling
variable {P : Type*} [Preorder P]

/-- The first `n + 1` requirements, imposed simultaneously. -/
def cumulativeDenseRequirements (D : ℕ → Set P) (n : ℕ) : Set P :=
  {p | ∀ i ≤ n, p ∈ D i}

theorem cumulativeDenseRequirements_lower (D : ℕ → Set P)
    (hDl : ∀ n, IsLowerSet (D n)) (n : ℕ) :
    IsLowerSet (cumulativeDenseRequirements D n) := by
  intro p q hpq hq i hi
  exact hDl i hpq (hq i hi)

theorem cumulativeDenseRequirements_coinitial (D : ℕ → Set P)
    (hDd : ∀ n, IsCoinitial (D n)) (hDl : ∀ n, IsLowerSet (D n)) (n : ℕ) :
    IsCoinitial (cumulativeDenseRequirements D n) := by
  induction n with
  | zero =>
    intro p
    obtain ⟨q, hq, hqp⟩ := hDd 0 p
    exact ⟨q, fun i hi => by simpa only [show i = 0 by omega] using hq, hqp⟩
  | succ n ih =>
    intro p
    obtain ⟨q, hq, hqp⟩ := ih p
    obtain ⟨r, hr, hrq⟩ := hDd (n + 1) q
    refine ⟨r, ?_, hrq.trans hqp⟩
    intro i hi
    by_cases hin : i ≤ n
    · exact hDl i hrq (hq i hin)
    · simpa only [show i = n + 1 by omega] using hr

omit [Preorder P] in
theorem cumulativeDenseRequirements_antitone (D : ℕ → Set P) :
    Antitone (cumulativeDenseRequirements D) := by
  intro n m hnm p hp i hi
  exact hp i (hi.trans hnm)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    taking successive finite intersections.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    First work on Baire space and its nonempty kernel $H$. Enumerate decreasing sequences $(D_n),(K_n),(J_n)$
    of downward-closed dense families for $\GHConditions{1}$, $\GHConditions{2}$, and $\RestrictedGHProduct{E}$,
    respectively. Use the countable witness families from analytic-condition fusion for the first two orders and
    the family from the HKL generic-pair lemma for the third,
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Include
    diameter at most $2^{-n}$ in $D_n$.
-/
/-- Every member of a countable lower dense family is included in every
sufficiently late stage. Empty families are handled by adding the trivial
requirement, so no nonemptiness assumption on the family is hidden. -/
theorem countable_dense_schedule (F : Set (Set P)) (hFc : F.Countable)
    (hFd : ∀ D ∈ F, IsCoinitial D) (hFl : ∀ D ∈ F, IsLowerSet D) :
    ∃ D : ℕ → Set P, Antitone D ∧ (∀ n, IsCoinitial (D n)) ∧
      (∀ n, IsLowerSet (D n)) ∧ ∀ A ∈ F, ∃ N, ∀ n, N ≤ n → D n ⊆ A := by
  obtain ⟨e, he⟩ := (hFc.insert Set.univ).exists_eq_range (Set.insert_nonempty _ _)
  have hem n : e n ∈ insert Set.univ F := by rw [he]; exact ⟨n, rfl⟩
  have hed n : IsCoinitial (e n) := by
    rcases hem n with h | h
    · rw [h]; exact fun p => ⟨p, Set.mem_univ p, le_rfl⟩
    · exact hFd _ h
  have hel n : IsLowerSet (e n) := by
    rcases hem n with h | h
    · rw [h]; exact fun _ _ _ _ => Set.mem_univ _
    · exact hFl _ h
  refine ⟨cumulativeDenseRequirements e, cumulativeDenseRequirements_antitone e,
    cumulativeDenseRequirements_coinitial e hed hel,
    cumulativeDenseRequirements_lower e hel, ?_⟩
  intro A hA
  have hAe : A ∈ Set.range e := by rw [← he]; exact Or.inr hA
  obtain ⟨N, rfl⟩ := hAe
  exact ⟨N, fun n hn p hp => hp N hn⟩

end Scheduling

variable {X : Type*} [TopologicalSpace X] [PolishSpace X]

/-- A coherent HKL system meeting each given requirement at every sufficiently
late level. Rectangles are required at opposite last bits, in both orders. -/
structure HKLScheduledSystem (E : Setoid X) (Ω : Set X)
    (F : Set (Set (AnalyticCondition X)))
    (J : Set (Set (CompatibleAnalyticRectangle E)))
    (K : Set (Set (AnalyticCondition (X × X)))) where
  level : ∀ n, AnalyticTreeSystem (crucialPairGraph n) X
  edgesIn : ∀ n, (level n).EdgesIn E
  node_subset : ∀ n s, (level n).node s ⊆ Ω
  node_parent : ∀ n s b, (level (n + 1)).node (Fin.snoc s b) ⊆ (level n).node s
  edge_parent : ∀ n s t b,
    (level (n + 1)).edge (Fin.snoc s b) (Fin.snoc t b) ⊆ (level n).edge s t
  disjoint : ∀ n r s, Disjoint ((level (n + 1)).node (Fin.snoc r false))
    ((level (n + 1)).node (Fin.snoc s true))
  node_eventually : ∀ D ∈ F, ∃ N, ∀ n, N ≤ n → ∀ s, (level n).nodeCondition s ∈ D
  edge_eventually : ∀ D ∈ K, ∃ N, ∀ n, N ≤ n → ∀ s t (h : (crucialPairGraph n).Adj s t),
    (level n).edgeCondition h ∈ D
  rectangle_eventually : ∀ D ∈ J, ∃ N, ∀ n, N ≤ n → ∀ r s,
    (level (n + 1)).rectangleCondition (crucialPairGraph_isTree (n + 1)).connected E (edgesIn _)
      (Fin.snoc r false) (Fin.snoc s true) ∈ D ∧
    (level (n + 1)).rectangleCondition (crucialPairGraph_isTree (n + 1)).connected E (edgesIn _)
      (Fin.snoc s true) (Fin.snoc r false) ∈ D

/-- Apply the decreasing schedules to all three finite refinement stages.
Every condition in each countable input family is eventually met uniformly
over its relevant finite level. The kernel splitting property remains explicit. -/
theorem hkl_scheduled_system_from_kernel (E : Setoid X)
    (hE : AnalyticSet {p : X × X | E.r p.1 p.2}) (Ω : Set X)
    (hΩa : AnalyticSet Ω) (hΩn : Ω.Nonempty)
    (F : Set (Set (AnalyticCondition X))) (hFc : F.Countable)
    (hFd : ∀ D ∈ F, IsCoinitial D) (hFl : ∀ D ∈ F, IsLowerSet D)
    (J : Set (Set (CompatibleAnalyticRectangle E))) (hJc : J.Countable)
    (hJd : ∀ D ∈ J, IsCoinitial D) (hJl : ∀ D ∈ J, IsLowerSet D)
    (K : Set (Set (AnalyticCondition (X × X)))) (hKc : K.Countable)
    (hKd : ∀ D ∈ K, IsCoinitial D) (hKl : ∀ D ∈ K, IsLowerSet D)
    (hsplit : ∀ Q : CompatibleAnalyticRectangle E, Q.val.1.val ⊆ Ω → Q.val.2.val ⊆ Ω →
      ∃ x ∈ Q.val.1.val, ∃ y ∈ Q.val.2.val, E.r x y ∧ x ≠ y) :
    Nonempty (HKLScheduledSystem E Ω F J K) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  obtain ⟨d, _, hdd, hdl, hdF⟩ := countable_dense_schedule F hFc hFd hFl
  obtain ⟨j, _, hjd, hjl, hjJ⟩ := countable_dense_schedule J hJc hJd hJl
  obtain ⟨k, _, hkd, hkl, hkK⟩ := countable_dense_schedule K hKc hKd hKl
  obtain ⟨S, hSE, hSΩ, hSd, hSk, hstep⟩ := hkl_coherent_levels_from_kernel
    E hE Ω hΩa hΩn d hdd hdl j hjd hjl k hkd hkl hsplit
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

/-- The countable fusion family transported to a continuously encoded space. -/
def encodedFusionRequirements (f : X → FusionReal) (hf : Continuous f)
    (K : ℕ → Set (FusionReal × FusionReal)) : Set (Set (AnalyticCondition X)) :=
  (fun D => encodeAnalyticCondition f hf ⁻¹' D) '' analyticFusionRequirements K

theorem encodedFusionRequirements_countable (f : X → FusionReal) (hf : Continuous f)
    (K : ℕ → Set (FusionReal × FusionReal)) : (encodedFusionRequirements f hf K).Countable :=
  (analyticFusionRequirements_countable K).image _

theorem encodedFusionRequirements_dense_lower (f : X → FusionReal) (hf : Continuous f)
    (hinj : Injective f) (K : ℕ → Set (FusionReal × FusionReal)) (hK : ∀ i, IsClosed (K i)) :
    ∀ D ∈ encodedFusionRequirements f hf K, IsCoinitial D ∧ IsLowerSet D := by
  rintro _ ⟨D, hD, rfl⟩
  have hd := analyticFusionRequirements_dense_lower K hK D hD
  exact ⟨encodeAnalyticCondition_preimage_coinitial f hf hinj hd.1,
    encodeAnalyticCondition_preimage_lower f hf hd.2⟩

namespace HKLScheduledSystem
variable {E : Setoid X} {Ω : Set X}
  {F : Set (Set (AnalyticCondition X))} {J : Set (Set (CompatibleAnalyticRectangle E))}
  {K : Set (Set (AnalyticCondition (X × X)))}

/-- Coherence makes every branch rectangle a compatible condition, even at
levels where the last bits agree. -/
def branchRectangle (S : HKLScheduledSystem E Ω F J K) (a b : ℕ → Bool) (n : ℕ) :
    CompatibleAnalyticRectangle E :=
  (S.level n).rectangleCondition (crucialPairGraph_isTree n).connected E (S.edgesIn n)
    (binaryBranchPrefix a n) (binaryBranchPrefix b n)

omit [PolishSpace X] in
theorem branchRectangle_antitone (S : HKLScheduledSystem E Ω F J K) (a b : ℕ → Bool) :
    Antitone (S.branchRectangle a b) := by
  intro n m hnm
  exact ⟨branch_conditions_antitone S.level S.node_parent a hnm,
    branch_conditions_antitone S.level S.node_parent b hnm⟩

omit [PolishSpace X] in
/-- Infinitely many differing last bits occur beyond the stage assigned to
any dense requirement, so the decreasing rectangle sequence meets it. -/
theorem branchRectangle_meets_of_not_e0 (S : HKLScheduledSystem E Ω F J K)
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

end HKLScheduledSystem

/-- The scheduled node and edge families supply all dense encounters needed
by the branch and pair fusion theorems. Closed presentations of the chosen
nodes and edges are still explicit inputs. The reverse implication requires
the generic-pair theorem for the rectangle family. -/
theorem hkl_scheduled_forward_embedding
    (E : Setoid FusionReal) (Ω : Set FusionReal)
    (J : Set (Set (CompatibleAnalyticRectangle E)))
    (N K : ℕ → Set (FusionReal × FusionReal)) (hN : ∀ i, IsClosed (N i))
    (hK : ∀ i, IsClosed (K i))
    (f : FusionReal × FusionReal → FusionReal) (hf : Continuous f) (hinj : Injective f)
    (S : HKLScheduledSystem E Ω (analyticFusionRequirements N) J (encodedFusionRequirements f hf K))
    (hnode : ∀ n s, ∃ i, (S.level n).node s = Prod.fst '' N i)
    (hedge : ∀ n s t, (crucialPairGraph n).Adj s t →
      ∃ i, f '' (S.level n).edge s t = Prod.fst '' K i) :
    ∃ π : (ℕ → Bool) → FusionReal, Continuous π ∧ Injective π ∧
      (∀ a n, π a ∈ (S.level n).node (binaryBranchPrefix a n)) ∧
      ∀ a b, E0 a b → E.r (π a) (π b) := by
  have hmeet : ∀ D ∈ analyticFusionRequirements N, ∃ n, ∀ s, (S.level n).nodeCondition s ∈ D := by
    intro D hD
    obtain ⟨n, hn⟩ := S.node_eventually D hD
    exact ⟨n, hn n le_rfl⟩
  obtain ⟨π, hπc, hπi, hπ⟩ := hkl_branch_embedding_baire S.level S.node_parent S.disjoint N hN hnode hmeet
  have hunique a x (hx : ∀ n, x ∈ (S.level n).node (binaryBranchPrefix a n)) : x = π a := by
    have hu := analytic_fusion_of_meets_countable_requirements N hN
      (fun n => (S.level n).nodeCondition (binaryBranchPrefix a n))
      (branch_conditions_antitone S.level S.node_parent a) (fun n => hnode n _)
      (fun D hD => by obtain ⟨n, hn⟩ := hmeet D hD; exact ⟨n, hn _⟩)
    exact hu.unique hx (hπ a)
  refine ⟨π, hπc, hπi, hπ, ?_⟩
  intro a b hab
  apply hkl_e0_preserved_of_edge_fusion S.level S.node_parent S.edge_parent E S.edgesIn
    π hunique f hf hinj K hK hedge ?_ hab
  intro D hD M
  obtain ⟨m, hm⟩ := S.edge_eventually (encodeAnalyticCondition f hf ⁻¹' D) ⟨D, hD, rfl⟩
  exact ⟨max m M, le_max_right _ _, hm _ (le_max_left _ _)⟩

end PolishSpaceBook
