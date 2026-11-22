module

public import PolishSpaceBook.KondoScaleSelection
public import PolishSpaceBook.EquivalenceRelationSeparation

@[expose] public section

/-! # Coanalyticity of the successive-minimum graph

The analytic and coanalytic norm comparisons are the cited input. All
finite-history tests, bad-witness projections, and the graph complement are
constructed here.
-/
namespace PolishSpaceBook.Kondo
noncomputable section
open Set Topology MeasureTheory
variable {X : Type} [TopologicalSpace X] [PolishSpace X]
variable {A : Set (X × baire_space)} {F : Set baire_space}

theorem analytic_union {P : Type} [TopologicalSpace P] {U V : Set P}
    (hU : AnalyticSet U) (hV : AnalyticSet V) : AnalyticSet (U ∪ V) := by
  have hu := AnalyticSet.iUnion (fun b : Bool =>
    show AnalyticSet (cond b U V) from by cases b <;> assumption)
  have he : (⋃ b : Bool, cond b U V) = U ∪ V := by
    ext p
    constructor
    · rintro ⟨_, ⟨b, rfl⟩, hp⟩
      cases b
      · exact Or.inr hp
      · exact Or.inl hp
    · rintro (hp | hp)
      · exact mem_iUnion.mpr ⟨true, hp⟩
      · exact mem_iUnion.mpr ⟨false, hp⟩
  exact he ▸ hu

abbrev Witness (X : Type) := (X × baire_space) × baire_space

def swap (t : Witness X) : Witness X := ((t.1.1, t.2), t.1.2)

omit [PolishSpace X] in
theorem continuous_swap : Continuous (swap (X := X)) :=
  ((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
    (continuous_snd.comp continuous_fst)

/-- Norm-comparison clauses of a coanalytic scale. The second point is the
candidate and the first point is the target. No graph or selector is assumed. -/
structure Comparisons (s : Scale A F) where
  sigma : ℕ → Set (Witness X)
  pi : ℕ → Set (Witness X)
  analytic_sigma : ∀ n, AnalyticSet (sigma n)
  coanalytic_pi : ∀ n, CoanalyticSet (pi n)
  sigma_spec : ∀ n x y z, (x, y) ∈ A →
    (((x, y), z) ∈ sigma n ↔ (x, z) ∈ A ∧ s.rank n (x, z) ≤ s.rank n (x, y))
  pi_spec : ∀ n x y z, (x, y) ∈ A →
    (((x, y), z) ∈ pi n ↔ (x, z) ∈ A ∧ s.rank n (x, z) ≤ s.rank n (x, y))

variable {s : Scale A F} (c : Comparisons s)

def equalTest (i : ℕ) : Set (Witness X) :=
  if i % 2 = 0 then c.sigma (i / 2) ∩ swap ⁻¹' c.sigma (i / 2)
  else {t | t.2 (i / 2) = t.1.2 (i / 2)}

def lessTest (i : ℕ) : Set (Witness X) :=
  if i % 2 = 0 then c.sigma (i / 2) ∩ (swap ⁻¹' c.pi (i / 2))ᶜ
  else {t | t.2 (i / 2) < t.1.2 (i / 2)}

theorem analytic_equalTest (i : ℕ) : AnalyticSet (equalTest c i) := by
  unfold equalTest
  split
  · exact analyticSet_inter (c.analytic_sigma _) ((c.analytic_sigma _).preimage continuous_swap)
  · exact (isClosed_eq ((continuous_apply _).comp continuous_snd)
      ((continuous_apply _).comp (continuous_snd.comp continuous_fst))).analyticSet

theorem analytic_lessTest (i : ℕ) : AnalyticSet (lessTest c i) := by
  unfold lessTest
  split
  · exact analyticSet_inter (c.analytic_sigma _)
      ((c.coanalytic_pi _).preimage continuous_swap)
  · let : MeasurableSpace (Witness X) := borel _
    let : BorelSpace (Witness X) := ⟨rfl⟩
    exact (isOpen_lt ((continuous_apply _).comp continuous_snd)
      ((continuous_apply _).comp (continuous_snd.comp continuous_fst))).measurableSet.analyticSet

omit [PolishSpace X] in
theorem equalTest_spec (i : ℕ) {x : X} {y z : baire_space}
    (hy : (x, y) ∈ A) (hz : (x, z) ∈ A) :
    ((x, y), z) ∈ equalTest c i ↔ key s x i z = key s x i y := by
  unfold equalTest key
  split
  · simp only [mem_inter_iff, mem_preimage, swap,
      c.sigma_spec _ _ _ _ hy, c.sigma_spec _ _ _ _ hz, hy, hz, true_and]
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  · simp only [mem_ofPred_eq, Nat.cast_inj]

omit [PolishSpace X] in
theorem lessTest_spec (i : ℕ) {x : X} {y z : baire_space}
    (hy : (x, y) ∈ A) (hz : (x, z) ∈ A) :
    ((x, y), z) ∈ lessTest c i ↔ key s x i z < key s x i y := by
  unfold lessTest key
  split
  · simp only [mem_inter_iff, mem_compl_iff, mem_preimage, swap,
      c.sigma_spec _ _ _ _ hy, c.pi_spec _ _ _ _ hz, hy, hz, true_and, not_le]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  · simp only [mem_ofPred_eq, Nat.cast_lt]

def badWitness (n : ℕ) : Set (Witness X) :=
  c.sigma 0 ∩ ((⋂ i : Fin n, equalTest c i.val) ∩ lessTest c n)

def bad : Set (X × baire_space) := ⋃ n, Prod.fst '' badWitness c n

theorem analytic_bad : AnalyticSet (bad c) := by
  apply AnalyticSet.iUnion
  intro n
  have hp : AnalyticSet (⋂ i : Fin n, equalTest c i.val) := by
    by_cases hn : n = 0
    · subst n
      have he : (⋂ i : Fin 0, equalTest c i.val) = univ := by simp
      rw [he]
      exact isClosed_univ.analyticSet
    · have : NeZero n := ⟨hn⟩
      exact AnalyticSet.iInter fun i => analytic_equalTest c i.val
  exact (analyticSet_inter (c.analytic_sigma 0)
    (analyticSet_inter hp (analytic_lessTest c n))).image_of_continuous continuous_fst

omit [PolishSpace X] in
theorem bad_iff {x : X} {y : baire_space} (hy : (x, y) ∈ A) :
    (x, y) ∈ bad c ↔ ∃ n z, (x, z) ∈ A ∧
      (∀ i < n, key s x i z = key s x i y) ∧ key s x n z < key s x n y := by
  constructor
  · intro hb
    obtain ⟨n, ⟨⟨p, z⟩, ⟨hg, hp, hl⟩, he⟩⟩ := mem_iUnion.mp hb
    change p = (x, y) at he
    subst p
    have hz := ((c.sigma_spec 0 x y z hy).mp hg).1
    exact ⟨n, z, hz, fun i hi => (equalTest_spec c i hy hz).mp
      (mem_iInter.mp hp ⟨i, hi⟩), (lessTest_spec c n hy hz).mp hl⟩
  · rintro ⟨n, z, hz, hp, hl⟩
    apply mem_iUnion.mpr
    refine ⟨n, ((x, y), z), ?_, rfl⟩
    have hzero : s.rank 0 (x, z) ≤ s.rank 0 (x, y) := by
      by_cases hn : n = 0
      · subst n
        simpa [key] using hl.le
      · have he := hp 0 (Nat.pos_of_ne_zero hn)
        simpa [key] using he.le
    exact ⟨(c.sigma_spec 0 x y z hy).mpr ⟨hz, hzero⟩,
      mem_iInter.mpr (fun i => (equalTest_spec c i hy hz).mpr (hp i.val i.isLt)),
      (lessTest_spec c n hy hz).mpr hl⟩

omit [PolishSpace X] in
theorem good_iff {x : X} {y : baire_space} :
    Good s x y ↔ (x, y) ∈ A ∩ (bad c)ᶜ := by
  constructor
  · rintro ⟨hy, hm⟩
    refine ⟨hy, fun hb => ?_⟩
    obtain ⟨n, z, hz, hp, hl⟩ := (bad_iff c hy).mp hb
    exact (not_lt_of_ge (hm n z hz hp)) hl
  · rintro ⟨hy, hb⟩
    refine ⟨hy, fun n z hz hp => le_of_not_gt fun hl => ?_⟩
    exact hb ((bad_iff c hy).mpr ⟨n, z, hz, hp, hl⟩)

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    We verify the complexity of this construction rather than assuming that the graph of successive minima has the
    required complexity. The cited norm-comparison machinery supplies analytic relations $L_n$ and coanalytic relations
    $P_n$ such that, whenever $(x,y)\in A$,
    $$\begin{aligned}
    L_n(x,z,y)&\Longleftrightarrow
     (x,z)\in A\ \land\ \varphi_n(x,z)\le\varphi_n(x,y)\\
    &\Longleftrightarrow P_n(x,z,y).
    \end{aligned}$$
    For points in the same section of $A$, equality of the $n$th ranks is expressed analytically by
    $L_n(x,z,y)\land L_n(x,y,z)$, and strict inequality by
    $L_n(x,z,y)\land\neg P_n(x,y,z)$. Coordinate equality and strict inequality are Borel.
    For each $i$, let $B_i$ consist of the triples $(x,y,z)$ satisfying $L_0(x,z,y)$, equality of the keys before $i$
    through these tests, and strict inequality of the $i$th key. Each $B_i$ is analytic.
    For $(x,y)\in A$, its witnesses are exactly the points $z\in A_x$ with the same earlier keys and a smaller $i$th key:
    the $L_0$ condition ensures membership in $A_x$, and it is automatic for such a competitor, either by the smaller
    zeroth key or by equality of that key. Hence
    $$G:=\SetDifference{A}{\bigcup_{i\in\omega}\{(x,y):\exists z\ (x,y,z)\in B_i\}}$$
    is coanalytic. Its points are precisely those realizing every successive minimum. The existence and uniqueness
    already proved show that $G$ is a graph contained in $A$ with domain $\pi_X(A)$.
    Only scale existence, its closure property, and the analytic/coanalytic norm comparisons are imported inputs.
    \end{proof}
-/
include c in
theorem coanalytic_good (hA : CoanalyticSet A) :
    CoanalyticSet {p : X × baire_space | Good s p.1 p.2} := by
  have he : {p : X × baire_space | Good s p.1 p.2} = A ∩ (bad c)ᶜ := by
    ext p
    exact good_iff c
  rw [he]
  change AnalyticSet (A ∩ (bad c)ᶜ)ᶜ
  rw [compl_inter, compl_compl]
  exact analytic_union hA (analytic_bad c)

end
end PolishSpaceBook.Kondo
