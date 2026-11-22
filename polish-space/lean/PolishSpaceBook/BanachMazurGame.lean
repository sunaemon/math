module

public import PolishSpaceBook.StrongChoquetMetric
public import Mathlib.Topology.GDelta.Basic

@[expose] public section

/-!
# The shrinking-open-set Banach–Mazur game

Response bounds include boundedness: real-valued `Metric.diam` alone would also
allow unbounded sets. Every legal play has a unique outcome. A countable nowhere
dense cover supplies an avoiding strategy, also for relative meagreness.
-/
noncomputable section
namespace PolishSpaceBook.BanachMazurGame
open Set Metric Filter Topology
open scoped Classical
variable {X : Type*} [MetricSpace X]

/-- An open move does not include a designated point. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Let $X$ be Polish, let $A \IncludedIn X$, and let $W \IncludedIn X$ be nonempty and open. The
    \termdefineas{Banach--Mazur game}{Banach–Mazur game}
    $G^{**}(A; W)$ is played as follows. Fix a compatible complete metric on $X$. Players alternate choosing nonempty open
    subsets
    $$W \supseteq U_0 \supseteq V_0 \supseteq U_1 \supseteq V_1 \supseteq \cdots,$$
    with I playing the $U_n$ and II playing the $V_n$, subject to the additional rules
    $$
    \Closure{V_n}\IncludedIn U_n,\qquad
    \Closure{U_{n+1}}\IncludedIn V_n,\qquad
    \Diameter{V_n}\le 2^{-n}.
    $$
-/
structure Move (X : Type*) [TopologicalSpace X] where
  openSet : Set X
  isOpen : IsOpen openSet
  nonempty : openSet.Nonempty

/-- II shrinks the closure and the diameter at the current round. -/
structure Response (n : ℕ) (U : Move X) extends Move X where
  closure_subset : closure openSet ⊆ U.openSet
  bounded : Bornology.IsBounded openSet
  diam_le : diam openSet ≤ (1 / 2 : ℝ) ^ n

abbrev Strategy (X : Type*) [MetricSpace X] :=
  (history : List (Move X)) → (U : Move X) → Response history.length U

def responseAt (σ : Strategy X) (p : ℕ → Move X) (n : ℕ) : Response n (p n) := by
  let V := σ ((List.range n).map p) (p n)
  exact {
    toMove := V.toMove
    closure_subset := V.closure_subset
    bounded := V.bounded
    diam_le := by simpa only [List.length_map, List.length_range] using V.diam_le }

def Legal (W : Set X) (σ : Strategy X) (p : ℕ → Move X) : Prop :=
  (p 0).openSet ⊆ W ∧ ∀ n, closure (p (n + 1)).openSet ⊆ (responseAt σ p n).openSet

def IsOutcome (σ : Strategy X) (p : ℕ → Move X) (x : X) : Prop :=
  ∀ n, x ∈ closure (responseAt σ p n).openSet

lemma response_closures_antitone {W : Set X} {σ : Strategy X} {p : ℕ → Move X}
    (hp : Legal W σ p) : Antitone (fun n => closure (responseAt σ p n).openSet) := by
  apply antitone_nat_of_succ_le
  intro n
  exact (responseAt σ p (n + 1)).closure_subset.trans
    (subset_closure.trans ((hp.2 n).trans subset_closure))

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Unique outcome
-/
lemma IsOutcome.mem_response {W : Set X} {σ : Strategy X} {p : ℕ → Move X} {x : X}
    (hx : IsOutcome σ p x) (hp : Legal W σ p) (n : ℕ) :
    x ∈ (responseAt σ p n).openSet :=
  hp.2 n (subset_closure ((responseAt σ p (n + 1)).closure_subset (hx (n + 1))))

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Unique outcome
-/
lemma IsOutcome.mem_initial {W : Set X} {σ : Strategy X} {p : ℕ → Move X} {x : X}
    (hx : IsOutcome σ p x) (hp : Legal W σ p) : x ∈ W :=
  hp.1 ((responseAt σ p 0).closure_subset (hx 0))

/-- The Cauchy construction depends only on nested bounded response closures. -/
theorem exists_unique_nested_closures [CompleteSpace X] (V : ℕ → Move X)
    (hmono : Antitone (fun n => closure (V n).openSet))
    (hbounded : ∀ n, Bornology.IsBounded (V n).openSet)
    (hdiam : ∀ n, diam (V n).openSet ≤ (1 / 2 : ℝ) ^ n) :
    ∃! x, ∀ n, x ∈ closure (V n).openSet := by
  let K : ℕ → Set X := fun n => closure (V n).openSet
  let y : ℕ → X := fun n => (V n).nonempty.choose
  have hy (n : ℕ) : y n ∈ K n := subset_closure (V n).nonempty.choose_spec
  have htail {m n : ℕ} (h : n ≤ m) : y m ∈ K n := hmono h (hy m)
  have hb (n : ℕ) : Bornology.IsBounded (K n) := (hbounded n).closure
  have hd (n : ℕ) : diam (K n) ≤ (1 / 2 : ℝ) ^ n := by
    simpa only [K, Metric.diam_closure] using hdiam n
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hc : CauchySeq y := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hpow).2 ε hε)
    exact ⟨N, fun m hm n hn => ((dist_le_diam_of_mem (hb N) (htail hm)
      (htail hn)).trans (hd N)).trans_lt (hN N le_rfl)⟩
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  have hxK : ∀ n, x ∈ closure (V n).openSet := fun n =>
    isClosed_closure.mem_of_tendsto hx ((eventually_ge_atTop n).mono fun m hm => htail hm)
  refine ⟨x, hxK, fun z hz => ?_⟩
  apply dist_le_zero.mp
  exact ge_of_tendsto hpow (Eventually.of_forall fun n =>
    (dist_le_diam_of_mem (hb n) (hz n) (hxK n)).trans (hd n))

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Put $K_n:=\Closure{V_n}$ and choose $y_n\in V_n$. The rules give
    $$
    K_{n+1}\IncludedIn U_{n+1}\IncludedIn V_n\IncludedIn K_n,\qquad
    \Diameter{K_n}=\Diameter{V_n}\le 2^{-n}.
    $$
    For $m,k\ge n$, both $y_m$ and $y_k$ lie in $K_n$, so $d(y_m,y_k)\le 2^{-n}$.
    Thus $\Sequence{y_n}{n\in\omega}$ is Cauchy and converges to some $x$ by completeness. Each closed set $K_n$ contains
    all sufficiently late terms, hence contains $x$. If $z$ also belongs to every $K_n$, then
    $d(x,z)\le 2^{-n}$ for every $n$, so $x=z$. Finally, $x\in K_{n+1}\IncludedIn V_n$, and the remaining
    inclusions follow from the rules.
    \end{proof}
-/
/-- Chosen points in nested response closures form a Cauchy sequence. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Unique outcome
-/
theorem exists_unique_outcome [CompleteSpace X] {W : Set X} {σ : Strategy X}
    {p : ℕ → Move X} (hp : Legal W σ p) : ∃! x, IsOutcome σ p x :=
  exists_unique_nested_closures (fun n => (responseAt σ p n).toMove)
    (response_closures_antitone hp) (fun n => (responseAt σ p n).bounded)
    (fun n => (responseAt σ p n).diam_le)

/-- Every legal play following II's strategy has an outcome outside the payoff. -/
def Winning (A W : Set X) (σ : Strategy X) : Prop :=
  ∀ p, Legal W σ p → ∃ x, IsOutcome σ p x ∧ x ∉ A

/-- Reuse the small-ball construction inside a nonempty open set. -/
def smallResponse (n : ℕ) (U : Move X) : Response n U := by
  let m : StrongChoquetGame.Move X :=
    ⟨U.nonempty.choose, U.openSet, U.isOpen, U.nonempty.choose_spec⟩
  let V := StrongChoquetGame.metricResponse n m
  exact {
    openSet := V.openSet
    isOpen := V.isOpen
    nonempty := ⟨m.point, V.mem⟩
    closure_subset := StrongChoquetGame.metricResponse_closure_subset n m
    bounded := (StrongChoquetGame.metricResponse_bounded_closure n m).subset subset_closure
    diam_le := (diam_mono subset_closure
      (StrongChoquetGame.metricResponse_bounded_closure n m)).trans
        (StrongChoquetGame.metricResponse_diam_closure n m) }

lemma exists_next_move (n : ℕ) (U : Move X) (V : Response n U) :
    ∃ U' : Move X, closure U'.openSet ⊆ V.openSet :=
  ⟨(smallResponse (n + 1) V.toMove).toMove, (smallResponse (n + 1) V.toMove).closure_subset⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    A strategy for II assigns a legal response to the current open move and the finite history of I's earlier moves;
    its own earlier responses are recovered from that history. Such a strategy always admits a legal infinite play.
    Start with $U_0=W$. After each response $V_n$, choose a nonempty open ball $U_{n+1}$ with
    $\Closure{U_{n+1}}\IncludedIn V_n$. The same small-ball construction used for the
    \termuseas{metric strong Choquet strategy}{metric strong Choquet strategy} gives such a move at every round.
-/
/-- Choose I's successive moves recursively against an arbitrary finite-history strategy. -/
def compatibleMove (σ : Strategy X) (W : Move X) : ℕ → Move X
  | 0 => W
  | n + 1 =>
    let history := (List.range n).attach.map fun i => compatibleMove σ W i.val
    (smallResponse (n + 1) (σ history (compatibleMove σ W n)).toMove).toMove
termination_by n => n
decreasing_by
  · have := List.mem_range.mp i.property
    omega
  · omega

lemma compatibleMove_zero (σ : Strategy X) (W : Move X) : compatibleMove σ W 0 = W := by
  rw [compatibleMove]

lemma compatibleMove_succ (σ : Strategy X) (W : Move X) (n : ℕ) :
    compatibleMove σ W (n + 1) =
      (smallResponse (n + 1) (responseAt σ (compatibleMove σ W) n).toMove).toMove := by
  rw [compatibleMove]
  have hh : (List.range n).attach.map (fun i => compatibleMove σ W i.val) =
      (List.range n).map (compatibleMove σ W) := by
    exact List.attach_map_val
  exact congrArg (fun h => (smallResponse (n + 1)
    (σ h (compatibleMove σ W n)).toMove).toMove) hh

/-- Winning is tested on a nonempty collection of legal plays. -/
theorem exists_legal_play (σ : Strategy X) (W : Move X) : ∃ p, Legal W.openSet σ p := by
  refine ⟨compatibleMove σ W, ?_, fun n => ?_⟩
  · rw [compatibleMove_zero]
  · rw [compatibleMove_succ]
    exact (smallResponse (n + 1) (responseAt σ (compatibleMove σ W) n).toMove).closure_subset

/-- Removing a nowhere dense closure leaves room to choose a small ball. -/
def avoidingOpen (U : Move X) {N : Set X} (hN : IsNowhereDense N) : Move X where
  openSet := U.openSet \ closure N
  isOpen := U.isOpen.sdiff isClosed_closure
  nonempty := by
    have hd : Dense (closure N)ᶜ := interior_eq_empty_iff_dense_compl.mp hN
    obtain ⟨x, hx, hU⟩ := hd.inter_open_nonempty U.openSet U.isOpen U.nonempty
    exact ⟨x, hx, hU⟩

def avoidingResponse (n : ℕ) (U : Move X) {N : Set X} (hN : IsNowhereDense N) :
    Response n U where
  toMove := (smallResponse n (avoidingOpen U hN)).toMove
  closure_subset := (smallResponse n (avoidingOpen U hN)).closure_subset.trans
    (fun _ hx => hx.1)
  bounded := (smallResponse n (avoidingOpen U hN)).bounded
  diam_le := (smallResponse n (avoidingOpen U hN)).diam_le

lemma avoidingResponse_avoids (n : ℕ) (U : Move X) {N : Set X} (hN : IsNowhereDense N) :
    Disjoint (closure (avoidingResponse n U hN).openSet) N := by
  rw [Set.disjoint_left]
  intro x hx hNx
  exact ((smallResponse n (avoidingOpen U hN)).closure_subset hx).2 (subset_closure hNx)

/-- At round `n`, avoid the `n`th nowhere dense set. -/
def avoidingStrategy (N : ℕ → Set X) (hN : ∀ n, IsNowhereDense (N n)) : Strategy X :=
  fun history U => avoidingResponse history.length U (hN history.length)

lemma avoidingStrategy_responseAt (N : ℕ → Set X) (hN : ∀ n, IsNowhereDense (N n))
    (p : ℕ → Move X) (n : ℕ) :
    (responseAt (avoidingStrategy N hN) p n).openSet =
      (avoidingResponse n (p n) (hN n)).openSet := by
  change (avoidingResponse ((List.range n).map p).length (p n)
    (hN ((List.range n).map p).length)).openSet = _
  exact congrArg (fun k => (avoidingResponse k (p n) (hN k)).openSet)
    (by simp only [List.length_map, List.length_range])

theorem avoidingStrategy_winning [CompleteSpace X] {A W : Set X} (N : ℕ → Set X)
    (hN : ∀ n, IsNowhereDense (N n)) (hcover : A ∩ W ⊆ ⋃ n, N n) :
    Winning A W (avoidingStrategy N hN) := by
  intro p hp
  obtain ⟨x, hx, _⟩ := exists_unique_outcome hp
  refine ⟨x, hx, fun hxA => ?_⟩
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover ⟨hxA, hx.mem_initial hp⟩)
  have hxV := hx n
  rw [avoidingStrategy_responseAt] at hxV
  exact (Set.disjoint_left.mp (avoidingResponse_avoids n (p n) (hN n))) hxV hn

/-- Fill unused indices of a countable nowhere dense cover with the empty set. -/
lemma exists_nowhereDense_cover {A : Set X} (hA : IsMeagre A) :
    ∃ N : ℕ → Set X, (∀ n, IsNowhereDense (N n)) ∧ A ⊆ ⋃ n, N n := by
  obtain ⟨S, hS, hc, hsub⟩ := isMeagre_iff_countable_union_isNowhereDense.mp hA
  refine ⟨enumerateCountable hc ∅, fun n => ?_, ?_⟩
  · have hn := range_enumerateCountable_subset hc ∅ (mem_range_self n)
    rcases hn with hn | hn
    · rw [hn]; exact isNowhereDense_empty
    · exact hS _ hn
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := hsub hx
    obtain ⟨n, rfl⟩ := subset_range_enumerate hc ∅ hs
    exact mem_iUnion.mpr ⟨n, hxs⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof] \emph{($\Leftarrow$).}
    Choose sets $N_n\IncludedIn W$ that are nowhere dense in $W$ and cover $A\cap W$.
    Regarded as subsets of $X$, they are still nowhere dense: a nonempty ambient open set contained in
    $\Closure{N_n}$ would meet $W$ and yield a nonempty relatively open subset of the closure of $N_n$ in $W$.
    All closures below are taken in $X$.
    
    At round $n$, the set $O_n:=\SetDifference{U_n}{\Closure{N_n}}$ is nonempty and open.
    Choose $a_n\in O_n$ and $\varepsilon_n>0$ with $\Ball{a_n}{\varepsilon_n}\IncludedIn O_n$, and set
    $$
    r_n:=\min\{\varepsilon_n/2,2^{-n}/2\},\qquad V_n:=\Ball{a_n}{r_n}.
    $$
    Then
    $$
    \Closure{V_n}\IncludedIn O_n\IncludedIn U_n,\qquad
    \Diameter{V_n}\le 2r_n\le 2^{-n},\qquad
    \Closure{V_n}\cap N_n=\emptyset.
    $$
    Fixing these choices for each round and each possible current open set defines II's strategy on all finite
    histories. The outcome $x$ belongs to $W$ and to every $\Closure{V_n}$, hence avoids every $N_n$.
    Since the $N_n$ cover $A\cap W$, we have $x\notin A$, so II wins.
-/
/-- Relative meagreness suffices, with all response closures taken in the ambient space. -/
theorem exists_winning_of_isMeagre [CompleteSpace X] {A : Set X} (W : Move X)
    (hA : IsMeagre (Subtype.val ⁻¹' A : Set W.openSet)) :
    ∃ σ : Strategy X, Winning A W.openSet σ := by
  have hAW : IsMeagre (A ∩ W.openSet) := by
    convert hA.image_val using 1
    ext x
    simp only [mem_inter_iff, mem_image, mem_preimage]
    constructor
    · rintro ⟨ha, hw⟩
      exact ⟨⟨x, hw⟩, ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
  obtain ⟨N, hN, hcover⟩ := exists_nowhereDense_cover hAW
  exact ⟨avoidingStrategy N hN, avoidingStrategy_winning N hN hcover⟩

end PolishSpaceBook.BanachMazurGame
