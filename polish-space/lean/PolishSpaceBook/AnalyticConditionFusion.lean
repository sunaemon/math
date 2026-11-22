module

public import PolishSpaceBook.HKLDenseRefinements

@[expose] public section

/-!
# Closed witnesses in analytic-condition fusion

Finite point and witness prefixes are extended together. The limiting pair
belongs to the original closed presentation, so projection gives membership
in the analytic condition itself. The countable dense family is constructed
for a supplied countable list of closed presentations. Smallness is expressed
by agreement on finite prefixes. Effective codes, numerical diameter bounds,
transport to the closed presentation of a general Polish space, and forcing
semantics remain separate obligations.
-/

namespace PolishSpaceBook
open Set Function Filter Topology MeasureTheory

abbrev FusionReal := ℕ → ℕ
abbrev FusionPrefix (n : ℕ) := Fin n → ℕ

def fusionCylinder {n : ℕ} (s : FusionPrefix n) : Set FusionReal :=
  {x | ∀ i : Fin n, x i.val = s i}

def witnessProjection {n : ℕ} (K : Set (FusionReal × FusionReal))
    (s t : FusionPrefix n) : Set FusionReal :=
  {x | x ∈ fusionCylinder s ∧ ∃ y ∈ fusionCylinder t, (x, y) ∈ K}

/-- Extending prefixes keeps every already chosen digit. -/
theorem coherentPrefix_stable (s : ∀ n, FusionPrefix n)
    (hs : ∀ n (i : Fin n), s (n + 1) i.castSucc = s n i)
    {n m : ℕ} (hnm : n ≤ m) (i : Fin n) :
    s m ⟨i.val, lt_of_lt_of_le i.isLt hnm⟩ = s n i := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    exact (hs m ⟨i.val, lt_of_lt_of_le i.isLt hnm⟩).trans ih

/-- The diagonal digit is independent of the later level where it is read. -/
def coherentPrefixLimit (s : ∀ n, FusionPrefix n) : FusionReal :=
  fun k => s (k + 1) (Fin.last k)

theorem coherentPrefixLimit_mem (s : ∀ n, FusionPrefix n)
    (hs : ∀ n (i : Fin n), s (n + 1) i.castSucc = s n i) (n : ℕ) :
    coherentPrefixLimit s ∈ fusionCylinder (s n) := by
  intro i
  exact (coherentPrefix_stable s hs (by omega : i.val + 1 ≤ n) (Fin.last i.val)).symm

/-- Any choices in successively longer cylinders converge to the prefix limit. -/
theorem tendsto_of_fusionCylinders (s : ∀ n, FusionPrefix n)
    (hs : ∀ n (i : Fin n), s (n + 1) i.castSucc = s n i)
    (x : ℕ → FusionReal) (hx : ∀ n, x n ∈ fusionCylinder (s n)) :
    Tendsto x atTop (𝓝 (coherentPrefixLimit s)) := by
  apply tendsto_pi_nhds.mpr
  intro k
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  have hk : k < n := by omega
  exact ((coherentPrefixLimit_mem s hs n) ⟨k, hk⟩).trans (hx n ⟨k, hk⟩).symm

/-- Closed witness membership follows from actual witnesses at every prefix,
not from membership in the closure of the projected analytic set. -/
theorem closed_witness_prefix_fusion (K : Set (FusionReal × FusionReal)) (hK : IsClosed K)
    (s t : ∀ n, FusionPrefix n)
    (hs : ∀ n (i : Fin n), s (n + 1) i.castSucc = s n i)
    (ht : ∀ n (i : Fin n), t (n + 1) i.castSucc = t n i)
    (hne : ∀ n, (witnessProjection K (s n) (t n)).Nonempty) :
    (coherentPrefixLimit s, coherentPrefixLimit t) ∈ K := by
  choose x hx using hne
  choose y hy hxy using fun n => (hx n).2
  have hxl := tendsto_of_fusionCylinders s hs x (fun n => (hx n).1)
  have hyl := tendsto_of_fusionCylinders t ht y hy
  exact hK.mem_of_tendsto (hxl.prodMk_nhds hyl) (Eventually.of_forall hxy)

theorem isClosed_fusionCylinder {n : ℕ} (s : FusionPrefix n) : IsClosed (fusionCylinder s) := by
  have heq : fusionCylinder s = ⋂ i : Fin n, {x : FusionReal | x i.val = s i} := by
    ext x; simp [fusionCylinder]
  rw [heq]
  exact isClosed_iInter (fun i => isClosed_eq (continuous_apply i.val) continuous_const)

theorem analyticSet_witnessProjection {n : ℕ} {K : Set (FusionReal × FusionReal)}
    (hK : IsClosed K) (s t : FusionPrefix n) : AnalyticSet (witnessProjection K s t) := by
  have hc := hK.inter ((isClosed_fusionCylinder s).prod (isClosed_fusionCylinder t))
  have heq : Prod.fst '' (K ∩ (fusionCylinder s ×ˢ fusionCylinder t)) = witnessProjection K s t := by
    ext x
    constructor
    · rintro ⟨⟨x, y⟩, ⟨hxy, hx, hy⟩, rfl⟩
      exact ⟨hx, y, hy, hxy⟩
    · rintro ⟨hx, y, hy, hxy⟩
      exact ⟨(x, y), ⟨hxy, hx, hy⟩, rfl⟩
  rw [← heq]
  exact hc.measurableSet.analyticSet.image_of_continuous continuous_fst

/-- The dense requirement that either excludes a trace or extends both prefixes. -/
def witnessRequirement {n : ℕ} (K : Set (FusionReal × FusionReal)) (s t : FusionPrefix n) :
    Set (AnalyticCondition FusionReal) :=
  {P | Disjoint P.val (witnessProjection K s t) ∨
    ∃ i j, P.val ⊆ witnessProjection K (Fin.snoc s i) (Fin.snoc t j)}

theorem witnessRequirement_lower {n : ℕ} (K : Set (FusionReal × FusionReal)) (s t : FusionPrefix n) :
    IsLowerSet (witnessRequirement K s t) := by
  intro P Q hQP hP
  rcases hP with hP | ⟨i, j, hP⟩
  · exact Or.inl (hP.mono_left hQP)
  · exact Or.inr ⟨i, j, fun x hx => hP (hQP hx)⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    It is dense because a nonempty intersection on the left has a point and a witness whose next digits can be fixed;
    intersecting with the corresponding projection gives a stronger analytic condition.
-/
/-- A nonempty trace has a point and a witness whose next digits can be fixed. -/
theorem witnessRequirement_coinitial {n : ℕ} {K : Set (FusionReal × FusionReal)}
    (hK : IsClosed K) (s t : FusionPrefix n) : IsCoinitial (witnessRequirement K s t) := by
  classical
  intro P
  by_cases hd : Disjoint P.val (witnessProjection K s t)
  · exact ⟨P, Or.inl hd, le_refl _⟩
  · obtain ⟨x, hxP, hx⟩ := Set.not_disjoint_iff.mp hd
    obtain ⟨hxs, y, hyt, hxy⟩ := hx
    have hext {u : FusionPrefix n} {z : FusionReal} (hz : z ∈ fusionCylinder u) :
        z ∈ fusionCylinder (Fin.snoc u (z n)) := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simpa using hz j
    let A := witnessProjection K (Fin.snoc s (x n)) (Fin.snoc t (y n))
    have hxA : x ∈ A := ⟨hext hxs, y, hext hyt, hxy⟩
    let Q : AnalyticCondition FusionReal := ⟨P.val ∩ A,
      analyticSet_inter P.property.1 (analyticSet_witnessProjection hK _ _), ⟨x, hxP, hxA⟩⟩
    exact ⟨Q, Or.inr ⟨x n, y n, inter_subset_right⟩, inter_subset_left⟩

/-- A positive set contains some condition of the decreasing sequence. -/
def PositiveAlong (P : ℕ → AnalyticCondition FusionReal) (A : Set FusionReal) : Prop :=
  ∃ n, (P n).val ⊆ A

/-- The exclusion alternative cannot occur for a positive trace: a later
nonempty condition lies in both sets. Thus a positive trace extends. -/
theorem positive_witness_extension (P : ℕ → AnalyticCondition FusionReal) (hP : Antitone P)
    {n : ℕ} (K : Set (FusionReal × FusionReal)) (s t : FusionPrefix n)
    (hpos : PositiveAlong P (witnessProjection K s t))
    (hmeet : ∃ m, P m ∈ witnessRequirement K s t) :
    ∃ i j, PositiveAlong P (witnessProjection K (Fin.snoc s i) (Fin.snoc t j)) := by
  obtain ⟨r, hr⟩ := hpos
  obtain ⟨m, hm⟩ := hmeet
  rcases hm with hd | ⟨i, j, hij⟩
  · obtain ⟨x, hx⟩ := (P (max r m)).property.2
    exact False.elim (Set.disjoint_left.mp hd
      (hP (le_max_right r m) hx) (hr (hP (le_max_left r m) hx)))
  · exact ⟨i, j, m, hij⟩

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Whenever
    $\pi_0(K_{s,t})$ is positive, a later encounter with the requirement for $K,s,t$ must take its second alternative.
    We therefore extend both prefixes indefinitely. Their limits $(x,y)$ belong to $K$, since $K$ is closed, so
    $x\in P_r$.
-/
/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    Let $\Sequence{P_n}{n\in\omega}$ meet these requirements. Call a set positive along the sequence when it contains some
    $P_n$.
    Fix $r$ and a recursive closed presentation $P_r=\pi_0(K)$. Its empty-prefix projection is positive.
-/
/-- Extend positive point and witness prefixes indefinitely, and take their
limits in the closed presentation. The positive point cylinders will later
identify this point with the limits obtained for the other conditions. -/
theorem positive_closed_witness_fusion (P : ℕ → AnalyticCondition FusionReal) (hP : Antitone P)
    (K : Set (FusionReal × FusionReal)) (hK : IsClosed K)
    (hstart : PositiveAlong P (Prod.fst '' K))
    (hmeet : ∀ n (s t : FusionPrefix n), ∃ m, P m ∈ witnessRequirement K s t) :
    ∃ x y, (x, y) ∈ K ∧ ∀ n, PositiveAlong P (fusionCylinder (fun i : Fin n => x i.val)) := by
  classical
  let State (n : ℕ) := {st : FusionPrefix n × FusionPrefix n //
    PositiveAlong P (witnessProjection K st.1 st.2)}
  let emptyPrefix : FusionPrefix 0 := Fin.elim0
  have hzero : PositiveAlong P (witnessProjection K emptyPrefix emptyPrefix) := by
    obtain ⟨m, hm⟩ := hstart
    refine ⟨m, ?_⟩
    intro x hx
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := hm hx
    exact ⟨fun i => Fin.elim0 i, y, (fun i => Fin.elim0 i), hxy⟩
  have hnext (n : ℕ) (q : State n) : ∃ r : State (n + 1),
      (∀ i : Fin n, r.val.1 i.castSucc = q.val.1 i) ∧
      (∀ i : Fin n, r.val.2 i.castSucc = q.val.2 i) := by
    obtain ⟨i, j, hij⟩ := positive_witness_extension P hP K q.val.1 q.val.2 q.property (hmeet _ _ _)
    exact ⟨⟨(Fin.snoc q.val.1 i, Fin.snoc q.val.2 j), hij⟩,
      (fun k => @Fin.snoc_castSucc n (fun _ => ℕ) i q.val.1 k),
      (fun k => @Fin.snoc_castSucc n (fun _ => ℕ) j q.val.2 k)⟩
  let states : (n : ℕ) → State n := fun n => Nat.rec (motive := State)
    ⟨(emptyPrefix, emptyPrefix), hzero⟩ (fun n q => (hnext n q).choose) n
  let s := fun n => (states n).val.1
  let t := fun n => (states n).val.2
  have hs : ∀ n (i : Fin n), s (n + 1) i.castSucc = s n i := fun n => (hnext n (states n)).choose_spec.1
  have ht : ∀ n (i : Fin n), t (n + 1) i.castSucc = t n i := fun n => (hnext n (states n)).choose_spec.2
  have hne n : (witnessProjection K (s n) (t n)).Nonempty := by
    obtain ⟨m, hm⟩ := (states n).property
    exact (P m).property.2.mono hm
  refine ⟨coherentPrefixLimit s, coherentPrefixLimit t, closed_witness_prefix_fusion K hK s t hs ht hne, ?_⟩
  intro n
  have heq : (fun i : Fin n => coherentPrefixLimit s i.val) = s n := funext (coherentPrefixLimit_mem s hs n)
  rw [heq]
  obtain ⟨m, hm⟩ := (states n).property
  exact ⟨m, fun x hx => (hm hx).1⟩

/-- A cylinder smallness requirement in the usual Baire-space presentation. -/
def smallPrefixRequirement (n : ℕ) : Set (AnalyticCondition FusionReal) :=
  {P | ∀ x ∈ P.val, ∀ y ∈ P.val, ∀ k < n, x k = y k}

theorem smallPrefixRequirement_lower (n : ℕ) : IsLowerSet (smallPrefixRequirement n) := by
  intro P Q hQP hP x hx y hy k hk
  exact hP x (hQP hx) y (hQP hy) k hk

theorem smallPrefixRequirement_coinitial (n : ℕ) : IsCoinitial (smallPrefixRequirement n) := by
  intro P
  obtain ⟨x, hx⟩ := P.property.2
  let s : FusionPrefix n := fun i => x i.val
  let Q : AnalyticCondition FusionReal := ⟨P.val ∩ fusionCylinder s,
    analyticSet_inter P.property.1 (isClosed_fusionCylinder s).measurableSet.analyticSet,
    ⟨x, hx, fun _ => rfl⟩⟩
  refine ⟨Q, ?_, inter_subset_left⟩
  intro y hy z hz k hk
  exact (hy.2 ⟨k, hk⟩).trans (hz.2 ⟨k, hk⟩).symm

/-- Shrinking conditions identify the points obtained from separate closed
presentations. Positive cylinders supply points in a common small condition. -/
theorem positive_prefix_limits_unique (P : ℕ → AnalyticCondition FusionReal) (hP : Antitone P)
    (hsmall : ∀ n, ∃ m, P m ∈ smallPrefixRequirement n) {x y : FusionReal}
    (hx : ∀ n, PositiveAlong P (fusionCylinder (fun i : Fin n => x i.val)))
    (hy : ∀ n, PositiveAlong P (fusionCylinder (fun i : Fin n => y i.val))) : x = y := by
  funext k
  obtain ⟨m, hm⟩ := hsmall (k + 1)
  obtain ⟨r, hr⟩ := hx (k + 1)
  obtain ⟨s, hs⟩ := hy (k + 1)
  obtain ⟨u, hu⟩ := (P (max r m)).property.2
  obtain ⟨v, hv⟩ := (P (max s m)).property.2
  have hux := hr (hP (le_max_left r m) hu) (Fin.last k)
  have hvy := hs (hP (le_max_left s m) hv) (Fin.last k)
  exact hux.symm.trans ((hm u (hP (le_max_right r m) hu) v
    (hP (le_max_right s m) hv) k (Nat.lt_succ_self k)).trans hvy)

/-@ booklink:
  source: polish-space-book/effective-dst-ranks-effective-refinements.md
  target: prose
  excerpt: |
    The small-diameter requirements force the same $x$ for every $r$: all positive point cylinders intersect
    every sufficiently late $P_n$. Thus $x\in\bigcap_n P_n$, and diameter shrinking proves uniqueness. Notice that the
    witness $y$ is constructed separately for every condition $P_r$; membership in a closure is not substituted for
    membership in $P_r$.
-/
/-- Closed presentations and the listed dense requirements give one actual
point in every condition. Presentations may be chosen separately for every
condition; no common witness for all conditions is assumed. -/
theorem analytic_condition_fusion (P : ℕ → AnalyticCondition FusionReal) (hP : Antitone P)
    (K : ℕ → Set (FusionReal × FusionReal)) (hK : ∀ r, IsClosed (K r))
    (hpres : ∀ r, (P r).val = Prod.fst '' K r)
    (hmeet : ∀ r n (s t : FusionPrefix n), ∃ m, P m ∈ witnessRequirement (K r) s t)
    (hsmall : ∀ n, ∃ m, P m ∈ smallPrefixRequirement n) :
    ∃! x : FusionReal, ∀ r, x ∈ (P r).val := by
  have heach r : ∃ x : FusionReal, x ∈ (P r).val ∧
      ∀ n, PositiveAlong P (fusionCylinder (fun i : Fin n => x i.val)) := by
    have hstart : PositiveAlong P (Prod.fst '' K r) := ⟨r, (hpres r).subset⟩
    obtain ⟨x, y, hxy, hx⟩ := positive_closed_witness_fusion P hP (K r) (hK r) hstart (hmeet r)
    refine ⟨x, ?_, hx⟩
    rw [hpres r]
    exact ⟨(x, y), hxy, rfl⟩
  choose x hx hpos using heach
  have heq r : x 0 = x r := positive_prefix_limits_unique P hP hsmall (hpos 0) (hpos r)
  refine ⟨x 0, fun r => (heq r).symm ▸ hx r, ?_⟩
  intro y hy
  funext k
  obtain ⟨m, hm⟩ := hsmall (k + 1)
  obtain ⟨r, hr⟩ := hpos 0 (k + 1)
  obtain ⟨u, hu⟩ := (P (max r m)).property.2
  exact (hm y (hy m) u (hP (le_max_right r m) hu) k (Nat.lt_succ_self k)).trans
    (hr (hP (le_max_left r m) hu) (Fin.last k))

/-- All witness-prefix requirements for a countable list of presentations,
together with all finite-prefix smallness requirements. -/
def analyticFusionRequirements (K : ℕ → Set (FusionReal × FusionReal)) :
    Set (Set (AnalyticCondition FusionReal)) :=
  Set.range smallPrefixRequirement ∪ Set.range
    (fun q : Σ _ : ℕ, Σ n : ℕ, FusionPrefix n × FusionPrefix n =>
      witnessRequirement (K q.1) q.2.2.1 q.2.2.2)

theorem analyticFusionRequirements_countable (K : ℕ → Set (FusionReal × FusionReal)) :
    (analyticFusionRequirements K).Countable :=
  (Set.countable_range smallPrefixRequirement).union (Set.countable_range _)

theorem analyticFusionRequirements_dense_lower (K : ℕ → Set (FusionReal × FusionReal))
    (hK : ∀ r, IsClosed (K r)) :
    ∀ D ∈ analyticFusionRequirements K, IsCoinitial D ∧ IsLowerSet D := by
  intro D hD
  rcases hD with ⟨n, rfl⟩ | ⟨⟨r, n, s, t⟩, rfl⟩
  · exact ⟨smallPrefixRequirement_coinitial n, smallPrefixRequirement_lower n⟩
  · exact ⟨witnessRequirement_coinitial (hK r) s t, witnessRequirement_lower (K r) s t⟩

/-- Meeting the countable family gives fusion whenever each condition has a
presentation in the chosen list. The lightface coding step that supplies
such a list is not replaced by arbitrary codes or additional axioms. -/
theorem analytic_fusion_of_meets_countable_requirements
    (K : ℕ → Set (FusionReal × FusionReal)) (hK : ∀ r, IsClosed (K r))
    (P : ℕ → AnalyticCondition FusionReal) (hP : Antitone P)
    (hpres : ∀ r, ∃ i, (P r).val = Prod.fst '' K i)
    (hmeet : ∀ D ∈ analyticFusionRequirements K, ∃ m, P m ∈ D) :
    ∃! x : FusionReal, ∀ r, x ∈ (P r).val := by
  choose i hi using hpres
  apply analytic_condition_fusion P hP (fun r => K (i r)) (fun r => hK (i r)) hi
  · intro r n s t
    exact hmeet _ (Or.inr ⟨⟨i r, n, s, t⟩, rfl⟩)
  · intro n
    exact hmeet _ (Or.inl ⟨n, rfl⟩)

end PolishSpaceBook
