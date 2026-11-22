module

public import PolishSpaceBook.SeparationUniformizationLusinSuslin
public import Mathlib.Topology.MetricSpace.Polish

@[expose] public section

/-! # Least-index open refinements and their closed-section limits

The choice at each stage depends only on analytic hit sets. Keeping the chosen
indices, rather than just the open sets they name, handles repeated basis elements.
-/
namespace PolishSpaceBook.JankovVonNeumann

noncomputable section
open Set Metric Filter TopologicalSpace
open scoped Topology

variable {Z : Type*} [MetricSpace Z]

/-- Every countable basis admits arbitrarily small refinements with closure
inside the prescribed open neighborhood. Extended diameter retains boundedness. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    Fix a countable basis $\{W_i:i\in\omega\}$ for $Z$. This basis has arbitrarily small refinements whose closures stay
    inside a prescribed open set: given an open set $W$, a point $z\in W$, and $\epsilon>0$, choose $r>0$ such that
    $\Ball{z}{2r}\IncludedIn W$ and $2r<\epsilon$. Choose $W_i$ with $z\in W_i\IncludedIn\Ball{z}{r}$. Then
    $\Closure{W_i}\IncludedIn\Closure{\Ball{z}{r}}\IncludedIn\Ball{z}{2r}\IncludedIn W$ and
    $\Diameter{W_i}\le 2r<\epsilon$.
-/
theorem basis_refinement {W : ℕ → Set Z} (hW : IsTopologicalBasis (range W))
    {U : Set Z} (hU : IsOpen U) {z : Z} (hz : z ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ i, z ∈ W i ∧ closure (W i) ⊆ U ∧ ediam (W i) < ENNReal.ofReal ε := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z hz
  let δ := min (r / 2) (ε / 4)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨V, ⟨i, rfl⟩, hzV, hV⟩ := hW.mem_nhds_iff.mp (ball_mem_nhds z hδ)
  refine ⟨i, hzV, ?_, ?_⟩
  · intro a ha
    apply hball
    have hd := mem_closedBall.mp (closure_ball_subset_closedBall (closure_mono hV ha))
    have hδr : δ ≤ r / 2 := min_le_left _ _
    exact mem_ball.mpr (by linarith)
  · have hd : ediam (W i) ≤ ENNReal.ofReal (2 * δ) := by
      apply ediam_le_of_forall_dist_le
      intro a ha b hb
      have ha' := mem_ball.mp (hV ha)
      have hb' := mem_ball.mp (hV hb)
      have ht := dist_triangle a z b
      rw [dist_comm z b] at ht
      linarith
    apply hd.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
    have hδε : δ ≤ ε / 4 := min_le_right _ _
    linarith

/-- A closure has the same diameter bound as its open set. -/
theorem closure_dist_le {U : Set Z} {ε : ℝ} (hε : 0 ≤ ε)
    (hU : ediam U < ENNReal.ofReal ε) {a b : Z}
    (ha : a ∈ closure U) (hb : b ∈ closure U) : dist a b ≤ ε := by
  have h := (edist_le_ediam_of_mem ha hb).trans (by simpa only [ediam_closure] using hU.le)
  rw [edist_dist] at h
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp h

variable {X : Type*} (F : X → Set Z) (W : ℕ → Set Z)

/-- A stage retains an open neighborhood meeting the relevant closed section. -/
structure Node (x : X) where
  carrier : Set Z
  isOpen : IsOpen carrier
  meets : (F x ∩ carrier).Nonempty

variable (hW : IsTopologicalBasis (range W))

/-- Eligibility is a fixed topological condition and a section-hit condition. -/
def Eligible (x : X) (U : Set Z) (n i : ℕ) : Prop :=
  closure (W i) ⊆ U ∧ ediam (W i) < ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) ∧
    (F x ∩ W i).Nonempty

include hW

theorem exists_eligible {x : X} (N : Node F x) (n : ℕ) :
    ∃ i, Eligible F W x N.carrier n i := by
  obtain ⟨z, hzF, hzN⟩ := N.meets
  obtain ⟨i, hzi, hiU, hiε⟩ := basis_refinement hW N.isOpen hzN
    (pow_pos (by norm_num : 0 < (1 / 2 : ℝ)) (n + 1))
  exact ⟨i, hiU, hiε, z, hzF, hzi⟩

noncomputable def nextIndex {x : X} (N : Node F x) (n : ℕ) : ℕ :=
  @Nat.find _ (Classical.decPred _) (exists_eligible F W hW N n)

theorem nextIndex_spec {x : X} (N : Node F x) (n : ℕ) :
    Eligible F W x N.carrier n (nextIndex F W hW N n) :=
  by classical exact Nat.find_spec (exists_eligible F W hW N n)

noncomputable def step {x : X} (N : Node F x) (n : ℕ) : Node F x where
  carrier := W (nextIndex F W hW N n)
  isOpen := hW.isOpen (mem_range_self _)
  meets := (nextIndex_spec F W hW N n).2.2

variable (hne : ∀ x, (F x).Nonempty)

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    We build, for each $x\in D$, a nested sequence
    $$
    Z=U_0(x)\supseteq \Closure{U_1(x)}\supseteq U_1(x)\supseteq \Closure{U_2(x)}\supseteq\cdots
    $$
    with $\Diameter{U_n(x)}<2^{-n}$ for $n\ge 1$ and
    $$C_x\cap U_n(x)\ne\emptyset,$$
    where $C_x:=\{z\in Z:(x,z)\in C\}$.
-/
noncomputable def node (x : X) : ℕ → Node F x
  | 0 => ⟨univ, isOpen_univ, by simpa using hne x⟩
  | n + 1 => step F W hW (node x n) n

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    Assume $U_n(x)$ has been chosen. Let $i_{n+1}(x)$ be the least index $i$ such that
    $$
    \Closure{W_i}\IncludedIn U_n(x),\qquad
    \Diameter{W_i}<2^{-(n+1)},\qquad
    C_x\cap W_i\ne\emptyset,
    $$
    and put $U_{n+1}(x):=W_{i_{n+1}(x)}$. We record the index itself, since different indices may name the same basis
    set.
-/
noncomputable def index (n : ℕ) (x : X) : ℕ := nextIndex F W hW (node F W hW hne x n) n

theorem node_succ (x : X) (n : ℕ) :
    (node F W hW hne x (n + 1)).carrier = W (index F W hW hne n x) := rfl

theorem node_nested (x : X) (n : ℕ) :
    closure (node F W hW hne x (n + 1)).carrier ⊆ (node F W hW hne x n).carrier :=
  (nextIndex_spec F W hW _ n).1

theorem node_antitone (x : X) : Antitone (fun n => closure (node F W hW hne x n).carrier) :=
  antitone_nat_of_succ_le fun n => (node_nested F W hW hne x n).trans subset_closure

theorem node_dist (x : X) (n : ℕ) {a b : Z}
    (ha : a ∈ closure (node F W hW hne x (n + 1)).carrier)
    (hb : b ∈ closure (node F W hW hne x (n + 1)).carrier) :
    dist a b ≤ (1 / 2 : ℝ) ^ (n + 1) :=
  closure_dist_le (by positivity) (nextIndex_spec F W hW _ n).2.1 ha hb

noncomputable def sample (x : X) (n : ℕ) : Z := (node F W hW hne x (n + 1)).meets.choose

theorem sample_mem (x : X) (n : ℕ) : sample F W hW hne x n ∈ F x ∧
    sample F W hW hne x n ∈ closure (node F W hW hne x (n + 1)).carrier := by
  have h := (node F W hW hne x (n + 1)).meets.choose_spec
  exact ⟨h.1, subset_closure h.2⟩

theorem sample_cauchy (x : X) : CauchySeq (sample F W hW hne x) := by
  refine cauchySeq_of_le_tendsto_0 (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) ?_ ?_
  · intro n m N hNn hNm
    exact node_dist F W hW hne x N
      (node_antitone F W hW hne x (Nat.add_le_add_right hNn 1) (sample_mem F W hW hne x n).2)
      (node_antitone F W hW hne x (Nat.add_le_add_right hNm 1) (sample_mem F W hW hne x m).2)
  · exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).comp (tendsto_add_atTop_nat 1)

variable [CompleteSpace Z]

noncomputable def point (x : X) : Z := (cauchySeq_tendsto_of_complete (sample_cauchy F W hW hne x)).choose

theorem sample_tendsto (x : X) : Tendsto (sample F W hW hne x) atTop (𝓝 (point F W hW hne x)) :=
  (cauchySeq_tendsto_of_complete (sample_cauchy F W hW hne x)).choose_spec

theorem point_mem_node (x : X) (n : ℕ) :
    point F W hW hne x ∈ closure (node F W hW hne x (n + 1)).carrier := by
  apply isClosed_closure.mem_of_tendsto (sample_tendsto F W hW hne x)
  exact (eventually_ge_atTop n).mono fun m hm =>
    node_antitone F W hW hne x (Nat.add_le_add_right hm 1) (sample_mem F W hW hne x m).2

/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    To see that $z(x)\in C_x$, choose
    $z_n\in C_x\cap U_n(x)$. The nesting and diameter bounds force $z_n\to z(x)$, and $C_x$ is closed.
-/
theorem point_mem (hclosed : ∀ x, IsClosed (F x)) (x : X) : point F W hW hne x ∈ F x :=
  (hclosed x).mem_of_tendsto (sample_tendsto F W hW hne x)
    (Eventually.of_forall fun n => (sample_mem F W hW hne x n).1)


/-- Completeness supplies existence; shrinking diameters supply uniqueness. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    The closures $\Closure{U_n(x)}$ are nested nonempty closed sets with diameters tending to $0$ in a
    complete space, so their intersection is a singleton. Call it $z(x)$.
-/
theorem node_intersection (x : X) :
    (⋂ n : ℕ, closure (node F W hW hne x (n + 1)).carrier) = {point F W hW hne x} := by
  ext z
  constructor
  · intro hz
    apply mem_singleton_iff.mpr
    by_contra hne'
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (dist_pos.mpr hne')
      (by norm_num : (1 / 2 : ℝ) < 1)
    have hbound := node_dist F W hW hne x n (mem_iInter.mp hz n) (point_mem_node F W hW hne x n)
    have hpow : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : 0 < (1 / 2 : ℝ)) n]
    exact not_lt_of_ge (hbound.trans hpow) hn
  · rintro rfl
    exact mem_iInter.mpr (point_mem_node F W hW hne x)


section Measurability
variable [MeasurableSpace X]
variable (hE : ∀ i, MeasurableSet {x | (F x ∩ W i).Nonempty})

omit [CompleteSpace Z] [MeasurableSpace X] in
/-- Least-index decisions use only the current eligibility set and finitely
many complements of earlier eligibility sets. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    At every stage, the least-index rule gives the finite exclusion formula
    $$
    D_{n,i}=\SetDifference{P_{n,i}}{\bigcup_{k<i}P_{n,k}}.
    $$
-/
theorem index_fiber (n i : ℕ) :
    {x | index F W hW hne n x = i} =
      {x | Eligible F W x (node F W hW hne x n).carrier n i} ∩
        ⋂ j, ⋂ (_ : j < i), {x | Eligible F W x (node F W hW hne x n).carrier n j}ᶜ := by
  classical
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_compl_iff]
  exact Nat.find_eq_iff _

omit [CompleteSpace Z] in
include hE in
/-- The selected basis index is measurable at every finite stage. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    For $n\ge 1$ and $i\in\omega$, put
    $$D_{n,i}:=\{x\in D:i_n(x)=i\}.$$
    We prove by induction on $n$ that these decision sets belong to the $\sigma$-algebra generated by analytic subsets of
    $X$. Let $P_{n,i}\IncludedIn D$ be the set of points for which index $i$ is eligible at stage $n$. Initially,
    $P_{1,i}=E(W_i)$ if $\Diameter{W_i}<2^{-1}$, and $P_{1,i}=\emptyset$ otherwise. Thus all the initial eligibility sets
    are measurable. At later stages,
    $$
    P_{n+1,i}=E(W_i)\cap
    \bigcup_{\substack{j\in\omega\\\Closure{W_i}\IncludedIn W_j\\\Diameter{W_i}<2^{-(n+1)}}}D_{n,j}.
    $$
    This is a countable union of measurable sets intersected with an analytic set, so it is measurable whenever the
    previous decision sets are.
-/
theorem index_measurable (n : ℕ) : Measurable (index F W hW hne n) := by
  classical
  induction n with
  | zero =>
    have hp : ∀ i, MeasurableSet {x | Eligible F W x (node F W hW hne x 0).carrier 0 i} := by
      intro i
      by_cases h : ediam (W i) < ENNReal.ofReal ((1 / 2 : ℝ) ^ (0 + 1))
      · simpa only [Eligible, node, subset_univ, true_and, h] using hE i
      · have heq : {x | Eligible F W x (node F W hW hne x 0).carrier 0 i} = ∅ := by
          ext x
          simp only [Eligible, node, mem_ofPred_eq, mem_empty_iff_false, h, false_and, and_false]
        rw [heq]
        exact MeasurableSet.empty
    apply measurable_to_countable'
    intro i
    change MeasurableSet {x | index F W hW hne 0 x = i}
    rw [index_fiber]
    exact (hp i).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hp j).compl)
  | succ n ih =>
    have hp : ∀ i, MeasurableSet {x | Eligible F W x (node F W hW hne x (n + 1)).carrier (n + 1) i} := by
      intro i
      let T := {j : ℕ | closure (W i) ⊆ W j ∧
        ediam (W i) < ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1 + 1))}
      have heq : {x | Eligible F W x (node F W hW hne x (n + 1)).carrier (n + 1) i} =
          ⋃ j : ℕ, ⋃ (_ : j ∈ T), {x | index F W hW hne n x = j} ∩
            {x | (F x ∩ W i).Nonempty} := by
        ext x
        simp only [Eligible, node_succ, mem_ofPred_eq, mem_iUnion, mem_inter_iff]
        constructor
        · rintro ⟨hsub, hdiam, hhit⟩
          exact ⟨index F W hW hne n x, ⟨hsub, hdiam⟩, rfl, hhit⟩
        · rintro ⟨j, ⟨hsub, hdiam⟩, hij, hhit⟩
          exact ⟨hij ▸ hsub, hdiam, hhit⟩
      rw [heq]
      exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
        (ih (measurableSet_singleton j)).inter (hE i)
    apply measurable_to_countable'
    intro i
    change MeasurableSet {x | index F W hW hne (n + 1) x = i}
    rw [index_fiber]
    exact (hp i).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hp j).compl)

/-- A history records indices, even when different indices name the same open set. -/
def history (s : List ℕ) : Set X :=
  {x | ∀ k : Fin s.length, index F W hW hne k x = s[k]}

omit [CompleteSpace Z] in
include hE in
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    This proves the induction. For a finite history $s=(j_1,\ldots,j_n)$, the set
    $$D_s:=\{x\in D:i_1(x)=j_1,\ldots,i_n(x)=j_n\}=\bigcap_{k=1}^n D_{k,j_k}$$
    is therefore measurable as well; the empty history gives $D_\emptyset=D$, which is analytic.
-/
theorem history_measurable (s : List ℕ) : MeasurableSet (history F W hW hne s) := by
  have heq : history F W hW hne s = ⋂ k : Fin s.length, (index F W hW hne k) ⁻¹' {s[k]} := by
    ext x; simp [history]
  rw [heq]
  exact MeasurableSet.iInter fun k => (index_measurable F W hW hne hE k) (measurableSet_singleton _)

omit [MeasurableSpace X] in
/-- Open preimages are exactly the countable union of decisions whose chosen
closure lies in the target open set. -/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    For an open set $O\IncludedIn Z$,
    $$
    z^{-1}(O)=\bigcup\{\,D_{n,i}: n\ge 1,\ i\in\omega,\ \Closure{W_i}\IncludedIn O\,\}.
    $$
    The inclusion from right to left follows from $z(x)\in\Closure{U_n(x)}$. Conversely, if $z(x)\in O$, then some ball
    around $z(x)$ is contained in $O$; for all sufficiently large $n$, the nested closed set $\Closure{U_n(x)}$ has diameter
    small enough and contains $z(x)$, so $\Closure{U_n(x)}\IncludedIn O$.
-/
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: prose
  excerpt: |
    Composing
    $z(x)=(y(x),p(x))$ with the first projection gives the required uniformizing function $u(x)=y(x)$.
-/
theorem point_preimage_open {O : Set Z} (hO : IsOpen O) :
    point F W hW hne ⁻¹' O = ⋃ n : ℕ, ⋃ i : ℕ,
      ⋃ (_ : closure (W i) ⊆ O), {x | index F W hW hne n x = i} := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO _ hx
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
    have hpow : (1 / 2 : ℝ) ^ (n + 1) < r := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : 0 < (1 / 2 : ℝ)) n]
    refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨index F W hW hne n x, mem_iUnion.mpr ⟨?_, rfl⟩⟩⟩
    intro z hz
    apply hball
    apply mem_ball.mpr
    exact (node_dist F W hW hne x n hz (point_mem_node F W hW hne x n)).trans_lt hpow
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hn
    obtain ⟨hio, hxi⟩ := mem_iUnion.mp hi
    apply hio
    have h := point_mem_node F W hW hne x n
    rw [node_succ, show index F W hW hne n x = i from hxi] at h
    exact h

variable [MeasurableSpace Z] [BorelSpace Z]

include hE in
/-@ booklink:
  source: polish-space-book/separation-uniformization-lusin-souslin.md
  target: proof
  excerpt: |
    The right-hand side is a countable union of the
    measurable decision sets $D_{n,i}$, so $z$ is measurable for the analytic-generated $\sigma$-algebra on $D$.
-/
theorem point_measurable : Measurable (point F W hW hne) := by
  apply measurable_of_isOpen
  intro O hO
  rw [point_preimage_open F W hW hne hO]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun i =>
    MeasurableSet.iUnion fun _ => (index_measurable F W hW hne hE n) (measurableSet_singleton i)

end Measurability
end
end PolishSpaceBook.JankovVonNeumann
