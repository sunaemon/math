module

public import PolishSpaceBook.MartinMonkArray
public import Mathlib.Order.WellFounded

@[expose] public section

/-!
# The Martin--Monk well-foundedness theorem

Borel determinacy is supplied by the imported, checked theorem and its local
strategy transport. Both failed upward reductions give first-player winning strategies. Their strictly causal output
maps feed the simultaneous array, producing an impossible Borel flip set.
-/

noncomputable section
namespace PolishSpaceBook.MartinMonk
open Set Topology WadgeGame

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    Fix such strategies and call them $\sigma^0_n$ and $\sigma^1_n$ respectively. For $i\in\{0,1\}$ and
    $y\in\BaireSpace$, let $g^i_n(y)$ be I's output when I follows $\sigma^i_n$ and II supplies $y$ without passes.
    At time $t$, I has seen only the first $t$ moves of II. Induction through these rounds therefore gives
    $$
    \restrict{y}{t}=\restrict{y'}{t}
    \quad\Longrightarrow\quad g^i_n(y)(t)=g^i_n(y')(t).
    $$
    The winning conditions give
    $$
    \begin{aligned}
    g^0_n(y)\in A_n&\quad\Longleftrightarrow\quad y\notin A_{n+1},\\
    g^1_n(y)\in A_n&\quad\Longleftrightarrow\quad y\in A_{n+1}.
    \end{aligned}
    $$
-/
lemma firstReductionMap_membership {A B : Set Baire} {σ : FirstStrategy}
    (hσ : FirstWinning A B σ) (y : Baire) : firstReductionMap σ y ∈ A ↔ y ∉ B := by
  have hw := hσ (againstI σ y) (againstI_follows σ y)
  have hn : ¬ (firstOutput (firstInducedPlay σ y).val ∈ A ↔
      secondOutput (firstInducedPlay σ y) ∈ B) :=
    fun h => hw ((mem_secondPayoff (firstInducedPlay σ y)).mpr h)
  rw [secondOutput_firstInducedPlay] at hn
  change firstOutput (firstInducedPlay σ y).val ∈ A ↔ y ∉ B
  tauto

/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof] Suppose toward a contradiction that such a descending sequence exists. For each $n$,
    strictness implies
    $$A_n \not\le_W A_{n+1}
    \qquad\text{and}\qquad
    A_n \not\le_W \SetDifference{\BaireSpace}{A_{n+1}}.$$
    By the Wadge-game lemma in §{sec:wadge-games}, Player II cannot have a winning strategy in either of the two games
    below. Their payoffs are Borel, so Borel determinacy gives Player I winning strategies in both games:
    $$G_W(A_n,A_{n+1})
    \qquad\text{and}\qquad
    G_W(A_n,\SetDifference{\BaireSpace}{A_{n+1}}).$$
-/
/-- There cannot be an infinite sequence with both upward reductions absent at every step. -/
theorem no_reverse_sequence
    (A : ℕ → Set Baire) (hA : ∀ n, MeasurableSet (A n))
    (hnot : ∀ n, ¬ CoarseWadgeReducible (A n) (A (n + 1))) : False := by
  have hchoose : ∀ n (b : Bool), ∃ σ : FirstStrategy,
      FirstWinning (A n) (if b then (A (n + 1))ᶜ else A (n + 1)) σ := by
    intro n b
    cases b with
    | false =>
      exact firstWinning_of_not_reducible
        (determined_of_borel_determinacy (hA n) (hA (n + 1)))
        (fun h => hnot n (Or.inl h))
    | true =>
      exact firstWinning_of_not_reducible
        (determined_of_borel_determinacy (hA n) (hA (n + 1)).compl)
        (fun h => hnot n (Or.inr h))
  choose σ hσ using hchoose
  let F : ℕ → Bool → Baire → Baire := fun n b => firstReductionMap (σ n b)
  have hF : ∀ n b, StrictlyCausal (F n b) := fun n b => firstReductionMap_causal (σ n b)
  have hrel : ∀ n b y, F n b y ∈ A n ↔
      if b then y ∈ A (n + 1) else y ∉ A (n + 1) := by
    intro n b y
    cases b with
    | false =>
      have hw : FirstWinning (A n) (A (n + 1)) (σ n false) := hσ n false
      exact firstReductionMap_membership hw y
    | true =>
      have hw : FirstWinning (A n) (A (n + 1))ᶜ (σ n true) := hσ n true
      change firstReductionMap (σ n true) y ∈ A n ↔ y ∈ A (n + 1)
      simpa only [mem_compl_iff, not_not] using firstReductionMap_membership hw y
  exact no_causal_array F hF A hrel (hA 0)

def StrictCoarse (A B : Set Baire) : Prop :=
  CoarseWadgeReducible A B ∧ ¬ CoarseWadgeReducible B A

/-- The sequence formulation of Martin--Monk, with the book's coarse strict order. -/
theorem no_descending_sequence
    (A : ℕ → Set Baire) (hA : ∀ n, MeasurableSet (A n)) :
    ¬ ∀ n, StrictCoarse (A (n + 1)) (A n) :=
  fun h => no_reverse_sequence A hA (fun n => (h n).2)

/-- Well-foundedness on Borel representatives of the coarse degrees. -/
/-@ booklink:
  source: polish-space-book/wadge-hierarchy.md
  target: statement
  kind: theorem
  title: Martin–Monk
-/
theorem martin_monk :
    WellFounded (fun A B : {A : Set Baire // MeasurableSet A} => StrictCoarse A.val B.val) := by
  apply wellFounded_iff_isEmpty_descending_chain.mpr
  refine ⟨?_⟩
  rintro ⟨A, hA⟩
  exact no_descending_sequence (fun n => (A n).val) (fun n => (A n).property) hA

end PolishSpaceBook.MartinMonk
