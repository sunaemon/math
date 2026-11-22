module

public import PolishSpaceBook.HKLDenseScheduling

@[expose] public section

/-!
# Finite product refinements and the Silver fusion scheme

The ordinary product conditions used here have independently refinable
coordinates. Finite refinement constructs the binary analytic scheme.
The effective kernel and Silver generic-pair splitting are separate inputs,
not consequences of the combinatorial construction. The full boldface
condition order cannot itself instantiate the splitting input: its singleton
atoms obstruct this, as proved in `AnalyticConditionCatalog.lean`. That module
reuses the generic finite refinement in a restricted countable catalog and
proves the catalog version of Silver fusion.
-/

namespace PolishSpaceBook
open Set Function MeasureTheory

section FiniteRefinement
variable {P I V : Type*} [Preorder P]

/-- Process finitely many lower dense requirements one at a time. -/
theorem finite_lower_dense_refinement (F : Finset I) (D : I → Set P)
    (hDd : ∀ i ∈ F, IsCoinitial (D i)) (hDl : ∀ i ∈ F, IsLowerSet (D i)) (p : P) :
    ∃ q ≤ p, ∀ i ∈ F, q ∈ D i := by
  classical
  induction F using Finset.induction_on generalizing p with
  | empty => exact ⟨p, le_rfl, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨q, hqp, hq⟩ := ih (fun j hj => hDd j (Finset.mem_insert_of_mem hj))
      (fun j hj => hDl j (Finset.mem_insert_of_mem hj)) p
    obtain ⟨r, hr, hrq⟩ := hDd i (Finset.mem_insert_self _ _) q
    refine ⟨r, hrq.trans hqp, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hr
    · exact hDl j (Finset.mem_insert_of_mem hj) hrq (hq j hj)

theorem node_requirement_coinitial (v : V) {D : Set P} (hD : IsCoinitial D) :
    IsCoinitial {A : V → P | A v ∈ D} := by
  classical
  intro A
  obtain ⟨p, hp, hpA⟩ := hD (A v)
  refine ⟨Function.update A v p, by simpa using hp, ?_⟩
  intro w
  by_cases hw : w = v
  · subst w; simpa using hpA
  · simp [Function.update_of_ne hw]

theorem rectangle_requirement_coinitial {u v : V} (huv : u ≠ v)
    {D : Set (P × P)} (hD : IsCoinitial D) :
    IsCoinitial {A : V → P | (A u, A v) ∈ D} := by
  classical
  intro A
  obtain ⟨p, hp, hpA⟩ := hD (A u, A v)
  let B : V → P := fun w => if w = u then p.1 else if w = v then p.2 else A w
  refine ⟨B, ?_, ?_⟩
  · simpa [B, huv, Ne.symm huv] using hp
  · intro w
    by_cases hwu : w = u
    · subst w; simpa [B] using hpA.1
    · by_cases hwv : w = v
      · subst w; simpa [B, Ne.symm huv] using hpA.2
      · simp [B, hwu, hwv]

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    At a new level, copy each old condition twice. Refine each of the finitely many node conditions into $D_n$ and
    then each ordered rectangle of distinct nodes into $J_n$. Ordinary product forcing allows its two coordinates to
    be refined independently. Every later refinement preserves previously achieved requirements because the dense
    families are downward closed. All node conditions remain nonempty subsets of $H$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Construct nonempty analytic sets $A_s$ for $s\in\finseq{2}$, beginning with $A_\emptyset\IncludedIn H$, so that
    $$
    A_{s\concat(i)}\IncludedIn A_s,\qquad A_s\in D_{|s|},\qquad
    A_s\times A_t\in J_n\quad(s\ne t\in 2^n).
-/
/-- First refine each node, then every ordered pair of distinct nodes.
Later changes preserve all previously attained lower requirements. -/
theorem finite_nodes_rectangles_refinement [Fintype V]
    (A : V → P) (D : Set P) (hDd : IsCoinitial D) (hDl : IsLowerSet D)
    (J : Set (P × P)) (hJd : IsCoinitial J) (hJl : IsLowerSet J) :
    ∃ B : V → P, B ≤ A ∧ (∀ v, B v ∈ D) ∧ ∀ u v, u ≠ v → (B u, B v) ∈ J := by
  classical
  obtain ⟨B, hBA, hBD⟩ := finite_lower_dense_refinement Finset.univ
    (fun v => {A : V → P | A v ∈ D})
    (fun v _ => node_requirement_coinitial v hDd)
    (fun v _ _ _ h hmem => hDl (h v) hmem) A
  let pairs : Finset (V × V) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  obtain ⟨C, hCB, hCJ⟩ := finite_lower_dense_refinement pairs
    (fun p => {A : V → P | (A p.1, A p.2) ∈ J})
    (fun p hp => rectangle_requirement_coinitial (Finset.mem_filter.mp hp).2 hJd)
    (fun p _ _ _ h hmem => hJl ⟨h p.1, h p.2⟩ hmem) B
  exact ⟨C, hCB.trans hBA, fun v => hDl (hCB v) (hBD v (Finset.mem_univ v)),
    fun u v huv => hCJ (u, v) (by simp [pairs, huv])⟩

end FiniteRefinement

/-- Duplicate each condition and perform the finite node/product refinement
at every level. Unlike HKL, no edge relation or equal-saturation constraint
is imposed on the ordinary product conditions. -/
theorem silver_binary_levels {P : Type*} [Preorder P] (p : P)
    (D : ℕ → Set P) (hDd : ∀ n, IsCoinitial (D n)) (hDl : ∀ n, IsLowerSet (D n))
    (J : ℕ → Set (P × P)) (hJd : ∀ n, IsCoinitial (J n)) (hJl : ∀ n, IsLowerSet (J n)) :
    ∃ A : ∀ n, binaryWord n → P,
      (∀ s, A 0 s ≤ p) ∧
      (∀ n s b, A (n + 1) (Fin.snoc s b) ≤ A n s) ∧
      (∀ n s, A n s ∈ D n) ∧
      ∀ n s t, s ≠ t → (A n s, A n t) ∈ J n := by
  classical
  obtain ⟨c, hcD, hcp⟩ := hDd 0 p
  have hnext n (A : binaryWord n → P) := finite_nodes_rectangles_refinement
    (fun w : binaryWord (n + 1) => A (Fin.init w))
    (D (n + 1)) (hDd _) (hDl _) (J (n + 1)) (hJd _) (hJl _)
  let A : ∀ n, binaryWord n → P := fun n =>
    Nat.rec (motive := fun n => binaryWord n → P) (fun _ => c)
      (fun n B => (hnext n B).choose) n
  have hstep n :
      (∀ w, A (n + 1) w ≤ A n (Fin.init w)) ∧
      (∀ w, A (n + 1) w ∈ D (n + 1)) ∧
      ∀ u v, u ≠ v → (A (n + 1) u, A (n + 1) v) ∈ J (n + 1) :=
    (hnext n (A n)).choose_spec
  refine ⟨A, fun _ => hcp, ?_, ?_, ?_⟩
  · intro n s b
    simpa using (hstep n).1 (Fin.snoc s b)
  · intro n s
    cases n with
    | zero => exact hcD
    | succ n => exact (hstep n).2.1 s
  · intro n s t hst
    cases n with
    | zero => exact False.elim (hst (Subsingleton.elim s t))
    | succ n => exact (hstep n).2.2 s t hst

variable {X : Type*} [TopologicalSpace X]

/-- The Silver node scheme with eventual uniform dense encounters. -/
structure SilverScheduledSystem (Ω : Set X)
    (F : Set (Set (AnalyticCondition X)))
    (J : Set (Set (AnalyticCondition X × AnalyticCondition X))) where
  node : ∀ n, binaryWord n → AnalyticCondition X
  node_subset : ∀ n s, (node n s).val ⊆ Ω
  node_parent : ∀ n s b, node (n + 1) (Fin.snoc s b) ≤ node n s
  node_eventually : ∀ D ∈ F, ∃ N, ∀ n, N ≤ n → ∀ s, node n s ∈ D
  rectangle_eventually : ∀ D ∈ J, ∃ N, ∀ n, N ≤ n → ∀ s t, s ≠ t → (node n s, node n t) ∈ D

/-- The countable scheduling argument constructs a Silver scheme inside
any nonempty analytic starting set. Splitting and effective coding are not
assumed to follow from this purely analytic construction. -/
theorem silver_scheduled_system (Ω : Set X) (hΩa : AnalyticSet Ω) (hΩn : Ω.Nonempty)
    (F : Set (Set (AnalyticCondition X))) (hFc : F.Countable)
    (hFd : ∀ D ∈ F, IsCoinitial D) (hFl : ∀ D ∈ F, IsLowerSet D)
    (J : Set (Set (AnalyticCondition X × AnalyticCondition X))) (hJc : J.Countable)
    (hJd : ∀ D ∈ J, IsCoinitial D) (hJl : ∀ D ∈ J, IsLowerSet D) :
    Nonempty (SilverScheduledSystem Ω F J) := by
  obtain ⟨d, _, hdd, hdl, hdF⟩ := countable_dense_schedule F hFc hFd hFl
  obtain ⟨j, _, hjd, hjl, hjJ⟩ := countable_dense_schedule J hJc hJd hJl
  obtain ⟨A, hA0, hparent, hAd, hAj⟩ := silver_binary_levels
    (⟨Ω, hΩa, hΩn⟩ : AnalyticCondition X) d hdd hdl j hjd hjl
  have hsub n : ∀ s, (A n s).val ⊆ Ω := by
    induction n with
    | zero => exact hA0
    | succ n ih =>
      intro s
      have h := hparent n (Fin.init s) (s (Fin.last n))
      rw [Fin.snoc_init_self] at h
      exact (show (A (n + 1) s).val ⊆ (A n (Fin.init s)).val from h).trans (ih _)
  refine ⟨{
    node := A
    node_subset := hsub
    node_parent := hparent
    node_eventually := ?_
    rectangle_eventually := ?_ }⟩
  · intro D hD
    obtain ⟨N, hN⟩ := hdF D hD
    exact ⟨N, fun n hn s => hN n hn (hAd n s)⟩
  · intro D hD
    obtain ⟨N, hN⟩ := hjJ D hD
    exact ⟨N, fun n hn s t hst => hN n hn (hAj n s t hst)⟩

namespace SilverScheduledSystem
variable {Ω : Set X} {F : Set (Set (AnalyticCondition X))}
  {J : Set (Set (AnalyticCondition X × AnalyticCondition X))}

theorem branch_antitone (S : SilverScheduledSystem Ω F J) (a : ℕ → Bool) :
    Antitone (fun n => S.node n (binaryBranchPrefix a n)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [binaryBranchPrefix_succ]
  exact S.node_parent n _ _

/-- Ordinary product conditions along two branches. -/
def branchRectangle (S : SilverScheduledSystem Ω F J) (a b : ℕ → Bool) (n : ℕ) :
    AnalyticCondition X × AnalyticCondition X :=
  (S.node n (binaryBranchPrefix a n), S.node n (binaryBranchPrefix b n))

theorem branchRectangle_antitone (S : SilverScheduledSystem Ω F J) (a b : ℕ → Bool) :
    Antitone (S.branchRectangle a b) :=
  fun _ _ h => ⟨S.branch_antitone a h, S.branch_antitone b h⟩

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    If $a\ne b$, their node labels are distinct at every sufficiently
    large level. The sequence of their rectangles therefore meets every $J_n$, so $(\pi(a),\pi(b))$ is product generic.
-/
/-- Distinct branches have distinct labels at every sufficiently late level,
so their rectangles eventually satisfy each product requirement. -/
theorem branchRectangle_eventually (S : SilverScheduledSystem Ω F J)
    {a b : ℕ → Bool} (hab : a ≠ b) :
    ∀ D ∈ J, ∃ N, ∀ n, N ≤ n → S.branchRectangle a b n ∈ D := by
  classical
  have hdiff : ∃ k, a k ≠ b k := by
    by_contra h
    push Not at h
    exact hab (funext h)
  obtain ⟨k, hk⟩ := hdiff
  intro D hD
  obtain ⟨M, hM⟩ := S.rectangle_eventually D hD
  refine ⟨max M (k + 1), ?_⟩
  intro n hn
  apply hM n ((le_max_left _ _).trans hn)
  intro heq
  have hkn : k < n := by omega
  exact hk (congrFun heq ⟨k, hkn⟩)

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: prose
  excerpt: |
    Analytic-condition fusion gives a unique point
    $$\pi(a)\in\bigcap_n A_{\restrict{a}{n}}$$
    for each $a\in\CantorSpace$.
-/
/-- Actual point fusion for the Silver nodes, with the supplied closed
presentations and the already scheduled countable witness requirements. -/
theorem branch_fusion {Ω : Set FusionReal}
    {K : ℕ → Set (FusionReal × FusionReal)} (hK : ∀ i, IsClosed (K i))
    {J : Set (Set (AnalyticCondition FusionReal × AnalyticCondition FusionReal))}
    (S : SilverScheduledSystem Ω (analyticFusionRequirements K) J)
    (hpres : ∀ n s, ∃ i, (S.node n s).val = Prod.fst '' K i) (a : ℕ → Bool) :
    ∃! x : FusionReal, ∀ n, x ∈ (S.node n (binaryBranchPrefix a n)).val := by
  apply analytic_fusion_of_meets_countable_requirements K hK
    (fun n => S.node n (binaryBranchPrefix a n)) (S.branch_antitone a) (fun n => hpres n _)
  intro D hD
  obtain ⟨n, hn⟩ := S.node_eventually D hD
  exact ⟨n, hn n le_rfl _⟩

end SilverScheduledSystem

/-- The generic-pair splitting input, stated for actual members of descending
ordinary product conditions. It makes no claim about ordinary closures. -/
def SilverPairSplitting (E : Setoid X) (Ω : Set X)
    (J : Set (Set (AnalyticCondition X × AnalyticCondition X))) : Prop :=
  ∀ Q : ℕ → AnalyticCondition X × AnalyticCondition X, Antitone Q →
    (∀ n, (Q n).1.val ⊆ Ω ∧ (Q n).2.val ⊆ Ω) →
    (∀ D ∈ J, ∃ n, Q n ∈ D) →
    ∀ x y, (∀ n, x ∈ (Q n).1.val) → (∀ n, y ∈ (Q n).2.val) → ¬ E.r x y

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    The proof in §{sec:edst-silver-fusion} defines $\pi(a)$ as an actual member of every analytic condition along its
    branch, using retained tree witnesses. Distinct branches give product-generic pairs, to which the proved Silver
    splitting lemma applies. It does not require the ordinary closures of the conditions to be $E$-separated.
-/
/-- Fusion yields the continuous perfect-antichain parametrization once the
Silver generic-pair splitting lemma and closed presentations are supplied.
Neither of those inputs is asserted by this conditional theorem. -/
theorem silver_fusion_of_generic_splitting (E : Setoid FusionReal) (Ω : Set FusionReal)
    (K : ℕ → Set (FusionReal × FusionReal)) (hK : ∀ i, IsClosed (K i))
    (J : Set (Set (AnalyticCondition FusionReal × AnalyticCondition FusionReal)))
    (S : SilverScheduledSystem Ω (analyticFusionRequirements K) J)
    (hpres : ∀ n s, ∃ i, (S.node n s).val = Prod.fst '' K i)
    (hsplit : SilverPairSplitting E Ω J) :
    ∃ π : (ℕ → Bool) → FusionReal, Continuous π ∧ Injective π ∧
      (∀ a n, π a ∈ (S.node n (binaryBranchPrefix a n)).val) ∧
      ∀ a b, a ≠ b → ¬ E.r (π a) (π b) := by
  choose π hπ using fun a => (S.branch_fusion hK hpres a).exists
  have hc : Continuous π := by
    apply continuous_of_binary_condition_membership S.node _ π hπ
    intro k
    obtain ⟨n, hn⟩ := S.node_eventually (smallPrefixRequirement (k + 1)) (Or.inl ⟨k + 1, rfl⟩)
    exact ⟨n, hn n le_rfl⟩
  have hanti a b (hab : a ≠ b) : ¬ E.r (π a) (π b) := by
    apply hsplit (S.branchRectangle a b) (S.branchRectangle_antitone a b)
      (fun n => ⟨S.node_subset n _, S.node_subset n _⟩) _ (π a) (π b) (hπ a) (hπ b)
    intro D hD
    obtain ⟨n, hn⟩ := S.branchRectangle_eventually hab D hD
    exact ⟨n, hn n le_rfl⟩
  have hi : Injective π := by
    intro a b heq
    by_contra hab
    exact hanti a b hab (heq ▸ E.refl (π a))
  exact ⟨π, hc, hi, hπ, hanti⟩

end PolishSpaceBook
