module

public import PolishSpaceBook.TreeGames
public import Mathlib.SetTheory.Ordinal.FixedPointApproximants

@[expose] public section

/-!
# Open and closed determinacy by transfinite backward induction

The growing regions start at the finite certificates for an open payoff. At a
turn of the pursuing player one child suffices; at an opponent turn all children
must have entered. Least entry stages give a decreasing-rank strategy, while the
complement of the stable region gives the avoiding strategy.
-/
noncomputable section
namespace PolishSpaceBook.TreeGames
namespace GameTree
open Set Function OrdinalApprox
open scoped Classical
universe u
variable {M : Type u} (T : GameTree M)

/-- The predecessor operation, including positions already reached. -/
def reachStep (p : Bool) : Set T.Position →o Set T.Position where
  toFun W := W ∪ {s | if turn s.val = p then ∃ a : T.LegalMove s, T.child s a ∈ W
    else ∀ a : T.LegalMove s, T.child s a ∈ W}
  monotone' := by
    intro W V h s hs
    rcases hs with hs | hs
    · exact Or.inl (h hs)
    · right
      by_cases ht : turn s.val = p
      · simp only [Set.mem_ofPred_eq, ite_eq_left ht] at hs ⊢
        obtain ⟨a, ha⟩ := hs; exact ⟨a, h ha⟩
      · simp only [Set.mem_ofPred_eq, ite_eq_right ht] at hs ⊢
        exact fun a => h (hs a)

lemma le_reachStep (p : Bool) (W : Set T.Position) : W ⊆ T.reachStep p W :=
  fun _ h => Or.inl h

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Define, by transfinite recursion,
    $$
    \begin{aligned}
    W_0&:=S,\\
    W_{\alpha+1}&:=W_\alpha
      \cup\{s\in T: |s|\text{ is even and }s\concat(a)\in W_\alpha\text{ for some legal }a\}\\
    &\hspace{2.8em}\cup\{s\in T: |s|\text{ is odd and }s\concat(a)\in W_\alpha\text{ for every legal }a\},\\
    W_\lambda&:=\bigcup_{\alpha<\lambda}W_\alpha\quad\text{for limit }\lambda.
    \end{aligned}
    $$
-/
/-- Transfinite stages, with the finite winning certificates as stage zero. -/
def reachStage (p : Bool) (S : Set T.Position) (α : Ordinal.{u}) : Set T.Position :=
  lfpApprox (T.reachStep p) S α

lemma reachStage_zero (p : Bool) (S : Set T.Position) : T.reachStage p S 0 = S :=
  lfpApprox_zero _

lemma reachStage_succ (p : Bool) (S : Set T.Position) (α : Ordinal.{u}) :
    T.reachStage p S (α + 1) = T.reachStep p (T.reachStage p S α) :=
  lfpApprox_add_one _ (T.le_reachStep p S) α

lemma reachStage_limit (p : Bool) (S : Set T.Position) {α : Ordinal.{u}}
    (hα : Order.IsSuccLimit α) :
    T.reachStage p S α = ⋃ β : Set.Iio α, T.reachStage p S β :=
  lfpApprox_of_isSuccLimit _ hα

lemma reachStage_mono (p : Bool) (S : Set T.Position) : Monotone (T.reachStage p S) :=
  lfpApprox_mono_right _

lemma seed_subset_stage (p : Bool) (S : Set T.Position) (α : Ordinal.{u}) :
    S ⊆ T.reachStage p S α := le_lfpApprox _

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    This increasing sequence stabilizes. Indeed, its values are subsets of $T$. Choose an ordinal whose
    cardinality exceeds that of $\PowerSet{T}$; two stages below it must have the same value. If
    $\alpha<\beta$ and $W_\alpha=W_\beta$, then
    $$
    W_\alpha\IncludedIn W_{\alpha+1}\IncludedIn W_\beta=W_\alpha.
    $$
    Thus $W_{\alpha+1}=W_\alpha$. The successor rule and the union rule at limit stages imply that all later
    stages have this same value. Write $W$ for the stable value; in particular, $S\IncludedIn W$.
-/
/-- A cardinal bound on the collection of subsets forces two stages to coincide. -/
theorem exists_reachStage_fixed (p : Bool) (S : Set T.Position) :
    ∃ α : Ordinal.{u}, T.reachStep p (T.reachStage p S α) = T.reachStage p S α := by
  obtain ⟨α, _, β, _, hne, heq⟩ := exists_lfpApprox_eq_lfpApprox (T.reachStep p) S
  have fix {a b : Ordinal.{u}} (hab : a < b)
      (h : T.reachStage p S a = T.reachStage p S b) :
      T.reachStep p (T.reachStage p S a) = T.reachStage p S a := by
    rw [← T.reachStage_succ]
    apply Set.Subset.antisymm
    · rw [h]
      exact T.reachStage_mono p S (Order.add_one_le_of_lt hab)
    · exact T.reachStage_mono p S (lt_add_one a).le
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨α, fix h heq⟩
  · exact ⟨β, fix h heq.symm⟩

def stableStage (p : Bool) (S : Set T.Position) : Ordinal.{u} :=
  (T.exists_reachStage_fixed p S).choose

def winningRegion (p : Bool) (S : Set T.Position) : Set T.Position :=
  T.reachStage p S (T.stableStage p S)

lemma winningRegion_fixed (p : Bool) (S : Set T.Position) :
    T.reachStep p (T.winningRegion p S) = T.winningRegion p S :=
  (T.exists_reachStage_fixed p S).choose_spec

lemma seed_subset_region (p : Bool) (S : Set T.Position) : S ⊆ T.winningRegion p S :=
  T.seed_subset_stage p S _

lemma stage_subset_region (p : Bool) (S : Set T.Position) (α : Ordinal.{u}) :
    T.reachStage p S α ⊆ T.winningRegion p S :=
  lfpApprox_le_of_mem_fixedPoints _ (T.winningRegion_fixed p S) (T.seed_subset_region p S) α

/-- Once a stage is fixed, all later stages have the same value. -/
lemma reachStage_eq_region_of_ge (p : Bool) (S : Set T.Position) {α : Ordinal.{u}}
    (hα : T.stableStage p S ≤ α) : T.reachStage p S α = T.winningRegion p S :=
  lfpApprox_eq_of_mem_fixedPoints _ hα (T.winningRegion_fixed p S)

/-- The least entry stage; used only on the winning region. -/
def entryRank (p : Bool) (S : Set T.Position) (s : T.Position) : Ordinal.{u} :=
  sInf {α | s ∈ T.reachStage p S α}

lemma mem_entryRank {p : Bool} {S : Set T.Position} {s : T.Position}
    (hs : s ∈ T.winningRegion p S) : s ∈ T.reachStage p S (T.entryRank p S s) :=
  csInf_mem (s := {α | s ∈ T.reachStage p S α}) ⟨T.stableStage p S, hs⟩

lemma entryRank_le {p : Bool} {S : Set T.Position} {s : T.Position} {α : Ordinal.{u}}
    (h : s ∈ T.reachStage p S α) : T.entryRank p S s ≤ α := csInf_le' h

/-- A non-seed position enters through an earlier predecessor stage. -/
lemma earlier_predecessor {p : Bool} {S : Set T.Position} {s : T.Position}
    (hs : s ∈ T.winningRegion p S) (hS : s ∉ S) :
    ∃ β < T.entryRank p S s,
      if turn s.val = p then ∃ a : T.LegalMove s, T.child s a ∈ T.reachStage p S β
      else ∀ a : T.LegalMove s, T.child s a ∈ T.reachStage p S β := by
  have h := T.mem_entryRank hs
  change s ∈ lfpApprox (T.reachStep p) S (T.entryRank p S s) at h
  rw [lfpApprox] at h
  rcases h with h | h
  · exact (hS h).elim
  simp only [Set.iSup_eq_iUnion, mem_iUnion] at h
  obtain ⟨β, hβ, hstep⟩ := h
  refine ⟨β, hβ, ?_⟩
  rcases hstep with hprev | hprev
  · exact (not_le_of_gt hβ (T.entryRank_le hprev)).elim
  · exact hprev

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    For $s\in W$, let $r(s)$ be the least stage at which $s$ enters. If $s\notin S$, this stage is nonzero.
    It cannot be a limit stage, since membership in a union already holds at an earlier stage. Hence
    $r(s)=\beta+1$ for some $\beta$, and $s\notin W_\beta$. The successor rule now gives two possibilities:
    at an I-turn there is a legal child in $W_\beta$, while at a II-turn every legal child lies in $W_\beta$.
    In either case, the indicated children belong to $W$ and have entry stage strictly below $r(s)$.
-/
/-- A least entry stage outside the seed is a successor, with the predecessor rule at its predecessor. -/
lemma entryRank_successor {p : Bool} {S : Set T.Position} {s : T.Position}
    (hs : s ∈ T.winningRegion p S) (hS : s ∉ S) :
    ∃ β, T.entryRank p S s = β + 1 ∧
      if turn s.val = p then ∃ a : T.LegalMove s, T.child s a ∈ T.reachStage p S β
      else ∀ a : T.LegalMove s, T.child s a ∈ T.reachStage p S β := by
  obtain ⟨β, hβ, hp⟩ := T.earlier_predecessor hs hS
  refine ⟨β, ?_, hp⟩
  apply le_antisymm
  · apply T.entryRank_le
    rw [T.reachStage_succ]
    exact Or.inr hp
  · exact Order.add_one_le_of_lt hβ

lemma exists_lower_child {p : Bool} {S : Set T.Position} {s : T.Position}
    (hs : s ∈ T.winningRegion p S) (hS : s ∉ S) (ht : turn s.val = p) :
    ∃ a : T.LegalMove s, T.child s a ∈ T.winningRegion p S ∧
      T.entryRank p S (T.child s a) < T.entryRank p S s := by
  obtain ⟨β, hβ, h⟩ := T.earlier_predecessor hs hS
  rw [ite_eq_left ht] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, T.stage_subset_region p S β ha, (T.entryRank_le ha).trans_lt hβ⟩

lemma every_child_lower {p : Bool} {S : Set T.Position} {s : T.Position}
    (hs : s ∈ T.winningRegion p S) (hS : s ∉ S) (ht : turn s.val ≠ p)
    (a : T.LegalMove s) : T.child s a ∈ T.winningRegion p S ∧
      T.entryRank p S (T.child s a) < T.entryRank p S s := by
  obtain ⟨β, hβ, h⟩ := T.earlier_predecessor hs hS
  rw [ite_eq_right ht] at h
  exact ⟨T.stage_subset_region p S β (h a), (T.entryRank_le (h a)).trans_lt hβ⟩

/-- Choose a lower-stage child until a finite certificate has been reached. -/
def pursuingStrategy (p : Bool) (S : Set T.Position) : T.Strategy p := fun s ht =>
  if h : s ∈ T.winningRegion p S ∧ s ∉ S then
    (T.exists_lower_child h.1 h.2 ht).choose
  else T.defaultPolicy s

lemma pursuingStrategy_lower {p : Bool} {S : Set T.Position} {s : T.Position}
    (hs : s ∈ T.winningRegion p S) (hS : s ∉ S) (ht : turn s.val = p) :
    T.child s (T.pursuingStrategy p S s ht) ∈ T.winningRegion p S ∧
      T.entryRank p S (T.child s (T.pursuingStrategy p S s ht)) < T.entryRank p S s := by
  simpa only [pursuingStrategy, dite_eq_left (show s ∈ T.winningRegion p S ∧ s ∉ S from ⟨hs, hS⟩)] using
    (T.exists_lower_child hs hS ht).choose_spec

/-- The next coordinate of an allowed play is a legal move. -/
def playedMove (x : T.Play) (n : ℕ) : T.LegalMove (T.prefixPosition x n) :=
  ⟨x.val n, by simpa only [prefixPosition, seqPrefix_succ_eq_concat] using x.property (n + 1)⟩

lemma prefix_succ_child (x : T.Play) (n : ℕ) :
    T.prefixPosition x (n + 1) = T.child (T.prefixPosition x n) (T.playedMove x n) := by
  apply Subtype.ext
  exact seqPrefix_succ_eq_concat x.val n

lemma playedMove_follows {p : Bool} {σ : T.Strategy p} {x : T.Play} (hx : T.Follows σ x)
    (n : ℕ) (ht : turn (T.prefixPosition x n).val = p) :
    T.playedMove x n = σ (T.prefixPosition x n) ht := by
  apply Subtype.ext
  exact hx n ht

lemma pursuing_next_lower {p : Bool} {S : Set T.Position} {x : T.Play}
    (hx : T.Follows (T.pursuingStrategy p S) x) (n : ℕ)
    (hn : T.prefixPosition x n ∈ T.winningRegion p S) (hS : T.prefixPosition x n ∉ S) :
    T.prefixPosition x (n + 1) ∈ T.winningRegion p S ∧
      T.entryRank p S (T.prefixPosition x (n + 1)) < T.entryRank p S (T.prefixPosition x n) := by
  rw [T.prefix_succ_child]
  by_cases ht : turn (T.prefixPosition x n).val = p
  · rw [T.playedMove_follows hx n ht]
    exact T.pursuingStrategy_lower hn hS ht
  · exact T.every_child_lower hn hS ht _

/-- The open payoff specified by finite winning certificates. -/
def reaches (S : Set T.Position) : Set T.Play := {x | ∃ n, T.prefixPosition x n ∈ S}

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    At each I-position in $\SetDifference{W}{S}$, choose a legal child of smaller entry stage. At all other
    I-positions, choose any legal move. A play starting in $W$ and following this strategy must reach $S$:
    otherwise its entry stages would decrease strictly at every move. The set of these stages has a least element,
    and the next move would have a still smaller stage, a contradiction. Thus every position of $W$ is winning
    for I; in particular, $\emptyset\in W$ gives I a winning strategy for $U$.
-/
/-- The rank strategy reaches a certificate from any position in the winning region.
Only compliance after that position is required. -/
theorem pursuingStrategy_reaches_from {p : Bool} {S : Set T.Position} {x : T.Play}
    (k : ℕ) (hk : T.prefixPosition x k ∈ T.winningRegion p S)
    (hx : ∀ n, k ≤ n → ∀ ht : turn (T.prefixPosition x n).val = p,
      x.val n = (T.pursuingStrategy p S (T.prefixPosition x n) ht).val) :
    ∃ n, k ≤ n ∧ T.prefixPosition x n ∈ S := by
  by_contra h
  have hn (n : ℕ) : T.prefixPosition x (k + n) ∉ S :=
    fun hS => h ⟨k + n, Nat.le_add_right k n, hS⟩
  have step (n : ℕ) (hr : T.prefixPosition x (k + n) ∈ T.winningRegion p S) :
      T.prefixPosition x (k + n + 1) ∈ T.winningRegion p S ∧
      T.entryRank p S (T.prefixPosition x (k + n + 1)) <
        T.entryRank p S (T.prefixPosition x (k + n)) := by
    rw [T.prefix_succ_child]
    by_cases ht : turn (T.prefixPosition x (k + n)).val = p
    · have he : T.playedMove x (k + n) = T.pursuingStrategy p S (T.prefixPosition x (k + n)) ht :=
        Subtype.ext (hx (k + n) (Nat.le_add_right k n) ht)
      rw [he]
      exact T.pursuingStrategy_lower hr (hn n) ht
    · exact T.every_child_lower hr (hn n) ht _
  have hr (n : ℕ) : T.prefixPosition x (k + n) ∈ T.winningRegion p S := by
    induction n with
    | zero => exact hk
    | succ n ih => exact (step n ih).1
  let r : ℕ → Ordinal.{u} := fun n => T.entryRank p S (T.prefixPosition x (k + n))
  obtain ⟨α, ⟨n, rfl⟩, hmin⟩ := wellFounded_lt.has_min (Set.range r) ⟨r 0, 0, rfl⟩
  exact hmin (r (n + 1)) ⟨n + 1, rfl⟩ (step n (hr n)).2

/-- From a winning root, an infinite play cannot decrease entry ranks forever. -/
theorem pursuingStrategy_reaches {p : Bool} {S : Set T.Position}
    (hroot : T.root ∈ T.winningRegion p S) {x : T.Play}
    (hx : T.Follows (T.pursuingStrategy p S) x) : x ∈ T.reaches S := by
  obtain ⟨n, _, hn⟩ := T.pursuingStrategy_reaches_from 0 hroot (fun n _ ht => hx n ht)
  exact ⟨n, hn⟩

lemma exists_child_outside {p : Bool} {S : Set T.Position} {s : T.Position}
    (hs : s ∉ T.winningRegion p S) (ht : turn s.val ≠ p) :
    ∃ a : T.LegalMove s, T.child s a ∉ T.winningRegion p S := by
  by_contra h
  push Not at h
  apply hs
  rw [← T.winningRegion_fixed p S]
  exact Or.inr (by simpa only [Set.mem_ofPred_eq, ite_eq_right ht] using h)

lemma every_child_outside {p : Bool} {S : Set T.Position} {s : T.Position}
    (hs : s ∉ T.winningRegion p S) (ht : turn s.val = p) (a : T.LegalMove s) :
    T.child s a ∉ T.winningRegion p S := by
  intro ha
  apply hs
  rw [← T.winningRegion_fixed p S]
  exact Or.inr (by simpa only [Set.mem_ofPred_eq, ite_eq_left ht] using (show ∃ a : T.LegalMove s,
    T.child s a ∈ T.winningRegion p S from ⟨a, ha⟩))

/-- Outside the stable region, the opponent can keep every position outside it. -/
def avoidingStrategy (p : Bool) (S : Set T.Position) : T.Strategy (!p) := fun s ht =>
  if h : s ∉ T.winningRegion p S then
    (T.exists_child_outside h (by cases p <;> simpa using ht)).choose
  else T.defaultPolicy s

lemma avoidingStrategy_outside {p : Bool} {S : Set T.Position} {s : T.Position}
    (hs : s ∉ T.winningRegion p S) (ht : turn s.val = !p) :
    T.child s (T.avoidingStrategy p S s ht) ∉ T.winningRegion p S := by
  simp only [avoidingStrategy, dite_eq_left hs]
  exact (T.exists_child_outside hs (by cases p <;> simpa using ht)).choose_spec

lemma avoiding_next_outside {p : Bool} {S : Set T.Position} {x : T.Play}
    (hx : T.Follows (T.avoidingStrategy p S) x) (n : ℕ)
    (hn : T.prefixPosition x n ∉ T.winningRegion p S) :
    T.prefixPosition x (n + 1) ∉ T.winningRegion p S := by
  rw [T.prefix_succ_child]
  by_cases ht : turn (T.prefixPosition x n).val = !p
  · rw [T.playedMove_follows hx n ht]
    exact T.avoidingStrategy_outside hn ht
  · exact T.every_child_outside hn (by cases p <;> simpa using ht) _

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    If $\emptyset\notin W$, the fixed-point property gives the opposite strategy. At an II-position outside
    $W$, some legal child must remain outside $W$, since otherwise the successor rule would put the position
    in $W$. At an I-position outside $W$, every legal child remains outside $W$, since one child in $W$
    would suffice to put the position in $W$. Player II chooses a child outside $W$ whenever possible and uses
    an arbitrary legal move at other positions. Induction on the length of the play shows that all positions
    stay outside $W$, hence outside $S$. No finite prefix then certifies membership in $U$, so II wins.
-/
theorem avoidingStrategy_avoids {p : Bool} {S : Set T.Position}
    (hroot : T.root ∉ T.winningRegion p S) {x : T.Play}
    (hx : T.Follows (T.avoidingStrategy p S) x) : x ∉ T.reaches S := by
  have hr (n : ℕ) : T.prefixPosition x n ∉ T.winningRegion p S := by
    induction n with
    | zero => exact hroot
    | succ n ih => exact T.avoiding_next_outside hx n ih
  rintro ⟨n, hn⟩
  exact hr n (T.seed_subset_region p S hn)

/-- Backward induction works with either player as the one pursuing the open target. -/
theorem reach_or_avoid (p : Bool) (S : Set T.Position) :
    (∃ σ : T.Strategy p, ∀ x, T.Follows σ x → x ∈ T.reaches S) ∨
    (∃ τ : T.Strategy (!p), ∀ x, T.Follows τ x → x ∉ T.reaches S) := by
  by_cases h : T.root ∈ T.winningRegion p S
  · exact Or.inl ⟨T.pursuingStrategy p S, fun _ hx => T.pursuingStrategy_reaches h hx⟩
  · exact Or.inr ⟨T.avoidingStrategy p S, fun _ hx => T.avoidingStrategy_avoids h hx⟩

/-- Positions whose relative cylinder is contained in the payoff. -/
def openCertificates (A : Set T.Play) : Set T.Position :=
  {s | ∀ x : T.Play, x.val ∈ cyl s.val → x ∈ A}

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    First take an open payoff $U\IncludedIn\TreeBody{T}$. Write
    $$
    U=\bigcup_{s\in S}\bigl(\cyl{s}\cap\TreeBody{T}\bigr)
    $$
    for some $S\IncludedIn T$. If a legal partial play has a prefix in $S$, then Player I has already won. We identify
    Player I's winning partial plays by backtracking from these finite certificates.
-/
/-- An open payoff in the branch space is precisely a union of relative cylinders. -/
theorem open_eq_reaches [TopologicalSpace M] [DiscreteTopology M]
    {A : Set T.Play} (hA : IsOpen A) : A = T.reaches (T.openCertificates A) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨U, hU, hUA⟩ := isOpen_induced_iff.mp hA
    have hxU : x.val ∈ U := by rw [← hUA] at hx; exact hx
    obtain ⟨s, hxs, hsU⟩ := exists_cyl_subset_of_mem_open hxU hU
    refine ⟨s.length, ?_⟩
    intro y hy
    change y.val ∈ cyl (seqPrefix x.val s.length) at hy
    rw [seqPrefix_eq_of_mem_cyl hxs] at hy
    rw [← hUA]
    exact hsU hy
  · rintro x ⟨n, hn⟩
    exact hn x (mem_cyl_seqPrefix x.val n)

/-- The open half of Gale--Stewart, with Player I pursuing the open payoff. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: theorem
  title: Gale–Stewart
-/
theorem open_determined [TopologicalSpace M] [DiscreteTopology M]
    {A : Set T.Play} (hA : IsOpen A) : T.Determined A := by
  have he := T.open_eq_reaches hA
  rcases T.reach_or_avoid true (T.openCertificates A) with ⟨σ, hσ⟩ | ⟨τ, hτ⟩
  · refine Or.inl ⟨σ, fun x hx => ?_⟩
    change x ∈ A
    rw [he]
    exact hσ x hx
  · refine Or.inr ⟨τ, fun x hx => ?_⟩
    change x ∉ A
    simpa only [← he] using hτ x hx

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    For a closed payoff $A\IncludedIn\TreeBody{T}$, apply the same construction with Player II as the player
    trying to reach the open set $\SetDifference{\TreeBody{T}}{A}$. In the recursion, the existential predecessor
    clause now applies at odd-length positions and the universal clause at even-length positions. If the root enters
    the resulting winning region, II forces the open complement; otherwise I keeps the play outside that region and
    wins in $A$. The turn order is unchanged throughout.
    \end{proof}
-/
/-- For a closed payoff II pursues its open complement; the turn order never changes. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: theorem
  title: Gale–Stewart
-/
theorem closed_determined [TopologicalSpace M] [DiscreteTopology M]
    {A : Set T.Play} (hA : IsClosed A) : T.Determined A := by
  have he := T.open_eq_reaches hA.isOpen_compl
  rcases T.reach_or_avoid false (T.openCertificates Aᶜ) with ⟨τ, hτ⟩ | ⟨σ, hσ⟩
  · refine Or.inr ⟨τ, fun x hx => ?_⟩
    change x ∈ Aᶜ
    rw [he]
    exact hτ x hx
  · refine Or.inl ⟨σ, fun x hx => ?_⟩
    change x ∈ A
    have h := hσ x hx
    simpa only [← he, mem_compl_iff, not_not] using h

end GameTree

/-- Open payoffs are determined in the original Baire-space formulation. -/
theorem baire_open_determined {A : Set (ℕ → ℕ)} (hA : IsOpen A) : BaireDetermined A :=
  (determined_full_iff A).mp (fullBaireTree.open_determined (hA.preimage continuous_subtype_val))

/-- Closed payoffs are determined in the original Baire-space formulation. -/
theorem baire_closed_determined {A : Set (ℕ → ℕ)} (hA : IsClosed A) : BaireDetermined A :=
  (determined_full_iff A).mp (fullBaireTree.closed_determined (hA.preimage continuous_subtype_val))

end PolishSpaceBook.TreeGames
