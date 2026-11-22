module

public import PolishSpaceBook.CantorBaireSpace

@[expose] public section

/-!
# Determinacy

Formalization targets for `polish-space/src/polish-space-book/determinacy.md`.

This file formalizes the unrestricted Baire-space game used as the chapter's
basic model, together with the two opening examples. TreeGames supplies legal
tree games, branch extension, unique joint play, and the equivalence with this
unrestricted model. StrongChoquetGame and
StrongChoquetTransport treat the topological game and transport of strategies.
GaleStewart proves open and closed determinacy by transfinite backward induction.
StrongChoquetMetric supplies the shrinking-ball strategy for complete metrics.
BanachMazurGame constructs unique outcomes and the meagre-set avoiding strategy.
BanachMazurConverse proves the converse using countable disjoint response families.
BanachMazurFirstPlayer proves the local comeagreness criterion by small-ball simulation.
BanachMazurCoding constructs the legal code tree and its continuous outcome map.
HarringtonCoveringCoding reduces measurability to the cited covering-game lemma.
DavisStarGame and DavisStarCoding prove the perfect-set game reduction.
UndeterminedGame constructs the Choice-based counterexample by transfinite diagonalization.
Choquet's converse metrization theorem is cited external material. BorelDeterminacy
imports Manthe's checked Borel-determinacy proof and transports its strategies
to this chapter's basic game; its covering architecture is sketched in the text.
-/

namespace PolishSpaceBook

section BaireGame

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    The basic descriptive-set-theoretic case takes $M=\omega$ and allows every play in $\BaireSpace$.
-/
/-- A strategy for Player I in the unrestricted game on Baire space.  At
round `n`, it sees the preceding `2 * n` moves. -/
def BaireIStrategy := (n : ℕ) → (Fin (2 * n) → ℕ) → ℕ

/-- A strategy for Player II in the unrestricted game on Baire space.  At
round `n`, it sees the preceding `2 * n + 1` moves. -/
def BaireIIStrategy := (n : ℕ) → (Fin (2 * n + 1) → ℕ) → ℕ

/-- A play follows a strategy for Player I. -/
def BaireFollowsI (σ : BaireIStrategy) (x : ℕ → ℕ) : Prop :=
  ∀ n, x (2 * n) = σ n (fun i => x i)

/-- A play follows a strategy for Player II. -/
def BaireFollowsII (τ : BaireIIStrategy) (x : ℕ → ℕ) : Prop :=
  ∀ n, x (2 * n + 1) = τ n (fun i => x i)

/-- Player I's strategy wins the game with payoff `A`. -/
def BaireIWinning (A : Set (ℕ → ℕ)) (σ : BaireIStrategy) : Prop :=
  ∀ x, BaireFollowsI σ x → x ∈ A

/-- Player II's strategy wins the game with payoff `A`. -/
def BaireIIWinning (A : Set (ℕ → ℕ)) (τ : BaireIIStrategy) : Prop :=
  ∀ x, BaireFollowsII τ x → x ∉ A

/-- The unrestricted Baire-space game with payoff `A` is determined. -/
def BaireDetermined (A : Set (ℕ → ℕ)) : Prop :=
  (∃ σ, BaireIWinning A σ) ∨ ∃ τ, BaireIIWinning A τ

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    For $A\IncludedIn\BaireSpace$, the corresponding game is denoted $G_A$. A pointclass here is a collection $\Gamma
    \IncludedIn
    \PowerSet{\BaireSpace}$, and $\Gamma$ is \termuseas{determined game}{determined} if every $A \in \Gamma$ is determined.
-/
/-- A pointclass is determined when each of its payoff sets is determined. -/
def BairePointclassDetermined (Γ : Set (Set (ℕ → ℕ))) : Prop :=
  ∀ A ∈ Γ, BaireDetermined A

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Examples clarify the definition. In the ordinary case $M=\omega$ and $L=\BaireSpace$. If
    $$A=\{x\in\BaireSpace:x(0)=0\},$$
    then Player I wins by playing $a_0=0$.
-/
/-- Player I wins the payoff decided by the first coordinate by opening with
zero. -/
theorem firstCoordinateZero_determined :
    BaireDetermined {x : ℕ → ℕ | x 0 = 0} := by
  left
  refine ⟨fun _ _ => 0, ?_⟩
  intro x hx
  simpa using hx 0

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    If instead
    $$A=\{x\in\BaireSpace:x(1)=0\},$$
    then Player II wins by answering $a_1=1$, forcing the final play outside $A$.
-/
/-- Player II wins the payoff decided by the second coordinate by answering
with one. -/
theorem secondCoordinateZero_determined :
    BaireDetermined {x : ℕ → ℕ | x 1 = 0} := by
  right
  refine ⟨fun _ _ => 1, ?_⟩
  intro x hx hzero
  have hone : x 1 = 1 := by simpa using hx 0
  change x 1 = 0 at hzero
  omega

end BaireGame

end PolishSpaceBook
