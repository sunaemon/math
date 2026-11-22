module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Data.List.Range

@[expose] public section

/-! # The strong Choquet game with finite-history strategies

A move of Player I is a point in an open set. A response is an open
neighborhood of that same point contained in the given set. The strategy
remembers all earlier I-moves; its own earlier responses are determined by
that history. Legality of the next I-move is imposed separately.
-/
namespace PolishSpaceBook
namespace StrongChoquetGame
universe u v
variable (X : Type u) [TopologicalSpace X]

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    The \termdefine{strong Choquet game} on a topological space $X$ uses the same move set for both players:
    $$M_X:=\{(x,U):x\in X,\ U\IncludedIn X\text{ is open},\ x\in U\}.$$
    Let $L_X\IncludedIn\funcspace{\omega}{M_X}$ be the set of alternating sequences of pairs
    $$
    (x_0,U_0),\ (x_0,V_0),\ (x_1,U_1),\ (x_1,V_1),\ldots
    $$
    such that
    $$x_n\in V_n\IncludedIn U_n
    \qquad\text{and}\qquad
    U_{n+1}\IncludedIn V_n$$
    for every $n$. Let $A_X\IncludedIn L_X$ consist of those plays for which the open sets chosen by Player I have empty
    intersection:
    $$\bigcap_{n\in\omega} U_n=\emptyset.$$
    The strong Choquet game is $(M_X,L_X,A_X)$. Thus Player I wins exactly on $A_X$, and Player II wins otherwise,
    equivalently when the nested play has a surviving point.
-/
structure Move where
  point : X
  openSet : Set X
  isOpen : IsOpen openSet
  mem : point ∈ openSet

structure Response (m : Move X) where
  openSet : Set X
  isOpen : IsOpen openSet
  mem : m.point ∈ openSet
  subset : openSet ⊆ m.openSet

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    A strategy for Player II can be specified by its response to the finite history of Player I's moves
    and the current move. Its previous responses can be recovered from that history. The response to
    $x\in U$ must be an open set $V$ with $x\in V\IncludedIn U$. A play following the strategy is legal when
    each next open set chosen by Player I is contained in the preceding response. The strategy is winning
    if every such infinite play has a point in all of Player I's open sets.
-/
abbrev Strategy := (history : List (Move X)) → (m : Move X) → Response X m

def responseAt (σ : Strategy X) (p : ℕ → Move X) (n : ℕ) : Response X (p n) :=
  σ ((List.range n).map p) (p n)

def Legal (σ : Strategy X) (p : ℕ → Move X) : Prop :=
  ∀ n, (p (n+1)).openSet ⊆ (responseAt X σ p n).openSet

def Winning (σ : Strategy X) : Prop :=
  ∀ p, Legal X σ p → ∃ x, ∀ n, x ∈ (p n).openSet

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    A topological space $X$ is \termdefine{strong Choquet} if Player II has a winning strategy in the strong Choquet game on
    $X$.
-/
def IsStrongChoquet : Prop := ∃ σ : Strategy X, Winning X σ

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    For the empty space there is no first move. We declare Player II to win without a move, so the empty space
    is strong Choquet. In the strategy formulation below, this holds because there are no plays to test.
-/
/-- With no points, there are no legal moves or plays. -/
theorem isStrongChoquet_of_isEmpty [IsEmpty X] : IsStrongChoquet X := by
  refine ⟨fun _ m => isEmptyElim m.point, ?_⟩
  intro p _
  exact isEmptyElim (p 0).point

/-- Remembering a state is a finite-history strategy, without access to future moves. -/
def stateStrategy {S : Type v} (initial : S) (step : S → Move X → S)
    (reply : (s : S) → (m : Move X) → Response X m) : Strategy X :=
  fun history m => reply (history.foldl step initial) m

def stateRun {S : Type v} (initial : S) (step : S → Move X → S)
    (p : ℕ → Move X) (n : ℕ) : S := ((List.range n).map p).foldl step initial

@[simp] theorem stateRun_zero {S : Type v} (initial : S) (step : S → Move X → S)
    (p : ℕ → Move X) : stateRun X initial step p 0 = initial := rfl

@[simp] theorem stateRun_succ {S : Type v} (initial : S) (step : S → Move X → S)
    (p : ℕ → Move X) (n : ℕ) :
    stateRun X initial step p (n+1) = step (stateRun X initial step p n) (p n) := by
  simp [stateRun,List.range_succ,List.foldl_append]

/-- A state invariant along every legal run proves that the actual history strategy wins. -/
theorem stateStrategy_winning {S : Type v} (initial : S) (step : S → Move X → S)
    (reply : (s : S) → (m : Move X) → Response X m)
    (hwin : ∀ p, (∀ n, (p (n+1)).openSet ⊆ (reply (stateRun X initial step p n) (p n)).openSet) →
      ∃ x, ∀ n, x ∈ (p n).openSet) : Winning X (stateStrategy X initial step reply) :=
  hwin

end StrongChoquetGame
end PolishSpaceBook
