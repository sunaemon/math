module

public import PolishSpaceBook.BanachMazurConverse

@[expose] public section

/-!
# First-player strategies in the Banach–Mazur game

Player I chooses an initial open set and responds to each II-move by shrinking
its closure, with no diameter restriction on I's own move. Before swapping roles,
small-ball refinements make the simulated II-moves obey their diameter bounds.
-/
noncomputable section
namespace PolishSpaceBook.BanachMazurGame
open Set Metric Topology
open scoped Classical
variable {X : Type*} [MetricSpace X]

/-- I's response has a closure condition but no independent diameter bound. -/
structure FirstResponse (V : Move X) extends Move X where
  closure_subset : closure openSet ⊆ V.openSet

structure FirstStrategy (X : Type*) [MetricSpace X] where
  first : Move X
  reply : (history : List (Move X)) → (V : Move X) → FirstResponse V

def firstMoveAt (σ : FirstStrategy X) (q : ℕ → Move X) : ℕ → Move X
  | 0 => σ.first
  | n + 1 => (σ.reply ((List.range n).map q) (q n)).toMove

def FirstLegal (σ : FirstStrategy X) (q : ℕ → Move X) : Prop :=
  ∀ n, closure (q n).openSet ⊆ (firstMoveAt σ q n).openSet ∧
    Bornology.IsBounded (q n).openSet ∧ diam (q n).openSet ≤ (1 / 2 : ℝ) ^ n

def FirstOutcome (q : ℕ → Move X) (x : X) : Prop := ∀ n, x ∈ closure (q n).openSet

lemma FirstLegal.exists_unique_outcome [CompleteSpace X] {σ : FirstStrategy X}
    {q : ℕ → Move X} (hq : FirstLegal σ q) : ∃! x, FirstOutcome q x := by
  apply exists_unique_nested_closures q ?_ (fun n => (hq n).2.1) (fun n => (hq n).2.2)
  apply antitone_nat_of_succ_le
  intro n
  exact (hq (n + 1)).1.trans (subset_closure.trans
    ((σ.reply ((List.range n).map q) (q n)).closure_subset.trans subset_closure))

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    This point $x$ is the outcome of the play, and *I wins* iff $x\in A$.
    Write $G^{**}(A):=G^{**}(A;X)$.
-/
def FirstWinning (A W : Set X) (σ : FirstStrategy X) : Prop :=
  σ.first.openSet ⊆ W ∧ ∀ q, FirstLegal σ q → ∃ x, FirstOutcome q x ∧ x ∈ A

/-- A responder strategy becomes a first-player strategy by choosing the initial open set. -/
def firstFromResponder (V : Move X) (τ : Strategy X) : FirstStrategy X where
  first := V
  reply := fun h U => {
    toMove := (τ h U).toMove
    closure_subset := (τ h U).closure_subset }

lemma responder_legal_of_first_legal (V : Move X) (τ : Strategy X) {q : ℕ → Move X}
    (hq : FirstLegal (firstFromResponder V τ) q) : Legal V.openSet τ q := by
  refine ⟨subset_closure.trans (hq 0).1, fun n => ?_⟩
  exact (hq (n + 1)).1

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Conversely, suppose $A\cap V$ is comeager in a nonempty open $V\IncludedIn W$.
    Choose a winning responder strategy $\rho$ for $G^{**}(\SetDifference{X}{A};V)$.
    I starts with $V$. After the original II-move $V_n$, feed $V_n$ to $\rho$ as an opening move in the auxiliary
    game, and use its response as $U_{n+1}$. The original rules ensure that these auxiliary opening moves are
    legal. The auxiliary outcome belongs to every $\Closure{U_{n+1}}\IncludedIn V_n$, so it is also the original
    outcome. It lies in $A$ because $\rho$ wins, proving that I wins the original game.
    \end{proof}
-/
lemma firstFromResponder_winning {A W : Set X} (V : Move X) (hVW : V.openSet ⊆ W)
    {τ : Strategy X} (hτ : Winning Aᶜ V.openSet τ) :
    FirstWinning A W (firstFromResponder V τ) := by
  refine ⟨hVW, fun q hq => ?_⟩
  obtain ⟨x, hx, hxA⟩ := hτ q (responder_legal_of_first_legal V τ hq)
  refine ⟨x, fun n => subset_closure ((responseAt τ q n).closure_subset (hx n)), ?_⟩
  exact not_not.mp hxA

theorem exists_firstWinning_of_isMeagre_compl [CompleteSpace X] {A W : Set X}
    (V : Move X) (hVW : V.openSet ⊆ W)
    (hA : IsMeagre (Subtype.val ⁻¹' Aᶜ : Set V.openSet)) :
    ∃ σ : FirstStrategy X, FirstWinning A W σ := by
  obtain ⟨τ, hτ⟩ := exists_winning_of_isMeagre V hA
  exact ⟨firstFromResponder V τ, firstFromResponder_winning V hVW hτ⟩

/-- Refine every earlier simulated opponent move using its own round number. -/
def shrunkHistory (h : List (Move X)) : List (Move X) :=
  h.mapIdx fun n U => (smallResponse n U).toMove

def shrunkPlay (p : ℕ → Move X) (n : ℕ) : Move X := (smallResponse n (p n)).toMove

lemma shrunkHistory_prefix (p : ℕ → Move X) (n : ℕ) :
    shrunkHistory ((List.range n).map p) = (List.range n).map (shrunkPlay p) := by
  apply List.ext_getElem
  · simp [shrunkHistory]
  · intro i hi hj
    simp only [shrunkHistory, List.getElem_mapIdx, List.getElem_map, shrunkPlay]
    exact congrArg₂ (fun k U => (smallResponse k U).toMove) (by simp) (by simp)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Suppose first that $\tau$ is a winning strategy for I, with initial move $U_0$.
    We construct a winning responder strategy in the auxiliary game $G^{**}(\SetDifference{X}{A};U_0)$.
    When its opening player chooses $B_n$, choose a nonempty open ball $V_n$ such that
    $$\Closure{V_n}\IncludedIn B_n,\qquad \Diameter{V_n}\le 2^{-n}.$$
    Feed $V_n$ to $\tau$ as the next move of the original Player II, retaining the entire earlier simulated
    history. Let $R_n$ be $\tau$'s response, namely the original move $U_{n+1}$. Then
    $$
    \Closure{R_n}\IncludedIn V_n\IncludedIn B_n,\qquad
    \Diameter{R_n}\le\Diameter{V_n}\le 2^{-n},
    $$
    so $R_n$ is a legal response in the auxiliary game. Fixing the small-ball choices for each round and each
    possible $B_n$ defines this strategy on every finite history.
-/
/-- Feed small simulated II-moves to I's strategy, keeping the round and history unchanged. -/
def swappedStrategy (σ : FirstStrategy X) : Strategy X := fun h U => by
  let V := smallResponse h.length U
  let R := σ.reply (shrunkHistory h) V.toMove
  have hRV : R.openSet ⊆ V.openSet := subset_closure.trans R.closure_subset
  exact {
    toMove := R.toMove
    closure_subset := R.closure_subset.trans (subset_closure.trans V.closure_subset)
    bounded := V.bounded.subset hRV
    diam_le := (diam_mono hRV V.bounded).trans V.diam_le }

lemma swappedStrategy_response (σ : FirstStrategy X) (p : ℕ → Move X) (n : ℕ) :
    (responseAt (swappedStrategy σ) p n).openSet =
      (firstMoveAt σ (shrunkPlay p) (n + 1)).openSet := by
  change (σ.reply (shrunkHistory ((List.range n).map p))
    (smallResponse ((List.range n).map p).length (p n)).toMove).openSet = _
  have hl : ((List.range n).map p).length = n := by simp
  have hm : (smallResponse ((List.range n).map p).length (p n)).toMove =
      shrunkPlay p n := congrArg (fun k => (smallResponse k (p n)).toMove) hl
  rw [hm, shrunkHistory_prefix]
  rfl

lemma shrunkPlay_legal (σ : FirstStrategy X) {p : ℕ → Move X}
    (hp : Legal σ.first.openSet (swappedStrategy σ) p) : FirstLegal σ (shrunkPlay p) := by
  intro n
  refine ⟨?_, (smallResponse n (p n)).bounded, (smallResponse n (p n)).diam_le⟩
  cases n with
  | zero => exact (smallResponse 0 (p 0)).closure_subset.trans hp.1
  | succ n =>
    rw [← swappedStrategy_response]
    exact (smallResponse (n + 1) (p (n + 1))).closure_subset.trans
      (subset_closure.trans (hp.2 n))

/-- Every first-player strategy has a legal infinite opponent play. -/
theorem exists_firstLegal (σ : FirstStrategy X) : ∃ q, FirstLegal σ q := by
  obtain ⟨p, hp⟩ := exists_legal_play (swappedStrategy σ) σ.first
  exact ⟨shrunkPlay p, shrunkPlay_legal σ hp⟩

lemma swapped_outcome_is_firstOutcome (σ : FirstStrategy X) {p : ℕ → Move X} {x : X}
    (hx : IsOutcome (swappedStrategy σ) p x) : FirstOutcome (shrunkPlay p) x := by
  intro n
  have hxR := hx n
  rw [swappedStrategy_response] at hxR
  exact subset_closure ((σ.reply ((List.range n).map (shrunkPlay p))
    (shrunkPlay p n)).closure_subset hxR)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Every legal auxiliary play produces a legal original play. At the first round,
    $\Closure{V_0}\IncludedIn B_0\IncludedIn U_0$; at later rounds,
    $$\Closure{V_{n+1}}\IncludedIn B_{n+1}\IncludedIn R_n=U_{n+1}.$$
    If $x$ is the auxiliary outcome, then $x\in\Closure{R_n}\IncludedIn V_n$ for every $n$.
    Thus it is also the unique original outcome. Since $\tau$ wins, $x\in A$, so the auxiliary responder avoids
    $\SetDifference{X}{A}$. The Banach–Mazur–Oxtoby theorem gives that $A\cap U_0$ is comeager in $U_0$.
    In particular, the first move of any winning I-strategy already supplies the required open set.
-/
lemma swappedStrategy_winning [CompleteSpace X] {A W : Set X} {σ : FirstStrategy X}
    (hσ : FirstWinning A W σ) : Winning Aᶜ σ.first.openSet (swappedStrategy σ) := by
  intro p hp
  obtain ⟨x, hx, _⟩ := exists_unique_outcome hp
  have hq := shrunkPlay_legal σ hp
  obtain ⟨y, hy, hyA⟩ := hσ.2 _ hq
  obtain ⟨z, _, hu⟩ := hq.exists_unique_outcome
  have hxy : x = y := (hu x (swapped_outcome_is_firstOutcome σ hx)).trans (hu y hy).symm
  exact ⟨x, hx, fun hxA => hxA (hxy.symm ▸ hyA)⟩

/-- The original first move is already a region on which the payoff is comeagre. -/
theorem isMeagre_compl_of_firstWinning [CompleteSpace X] [SecondCountableTopology X]
    {A W : Set X} {σ : FirstStrategy X} (hσ : FirstWinning A W σ) :
    IsMeagre (Subtype.val ⁻¹' Aᶜ : Set σ.first.openSet) :=
  isMeagre_of_winning σ.first (swappedStrategy_winning hσ)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: corollary
  title: First-player criterion
-/
theorem firstWinning_iff_local_comeagre [CompleteSpace X] [SecondCountableTopology X]
    (A W : Set X) :
    (∃ σ : FirstStrategy X, FirstWinning A W σ) ↔
      ∃ V : Move X, V.openSet ⊆ W ∧ IsMeagre (Subtype.val ⁻¹' Aᶜ : Set V.openSet) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ.first, hσ.1, isMeagre_compl_of_firstWinning hσ⟩
  · rintro ⟨V, hVW, hA⟩
    exact exists_firstWinning_of_isMeagre_compl V hVW hA

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    In the dual game $H^{**}(A;W)$, II opens with $V_0\IncludedIn W$, and I responds with $U_0$.
    The subsequent moves satisfy
    $$
    \Closure{U_n}\IncludedIn V_n,\qquad
    \Closure{V_{n+1}}\IncludedIn U_n,\qquad
    \Diameter{U_n}\le 2^{-n}.
    $$
    I wins exactly when the outcome belongs to $A$. This is $G^{**}(\SetDifference{X}{A};W)$ with the player names
    exchanged, so I has a winning strategy in $H^{**}(A;W)$ iff $A\cap W$ is comeager in $W$.
    Here the diameter bound is imposed on I's responses. To compare this game with the play after I's initial move
    in $G^{**}(A;W)$, we use small-ball refinements that preserve the outcome.
-/
/-- In the dual game, II opens and I responds; I wins when the outcome lies in `A`. -/
def DualWinning (A W : Set X) (τ : Strategy X) : Prop := Winning Aᶜ W τ

theorem dualWinning_iff_comeagre [CompleteSpace X] [SecondCountableTopology X]
    (A : Set X) (W : Move X) :
    (∃ τ : Strategy X, DualWinning A W.openSet τ) ↔
      IsMeagre (Subtype.val ⁻¹' Aᶜ : Set W.openSet) := winning_iff_isMeagre W

end PolishSpaceBook.BanachMazurGame
