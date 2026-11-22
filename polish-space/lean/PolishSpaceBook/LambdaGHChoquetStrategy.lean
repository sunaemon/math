module

public import PolishSpaceBook.LambdaGHChoquetFusion

@[expose] public section

/-! # A winning finite-history strategy in the Gandy--Harrington topology -/
namespace PolishSpaceBook
open Set
namespace LambdaTree.GHChoquet

abbrev Move (ε : ℕ → ℕ) := @StrongChoquetGame.Move FusionReal (parameterGHTopology ε)
abbrev Reply {ε : ℕ → ℕ} (m : Move ε) :=
  @StrongChoquetGame.Response FusionReal (parameterGHTopology ε) m

variable {ε : ℕ → ℕ}

noncomputable def next (q : State ε) (m : Move ε) : State ε := by
  letI : TopologicalSpace FusionReal := parameterGHTopology ε
  classical
  exact if h : m.point ∈ q.trace then (extend q m.point h m.openSet m.isOpen m.mem).choose
    else (extend (initial ε) m.point (by simp) m.openSet m.isOpen m.mem).choose

theorem next_valid (q : State ε) (m : Move ε) :
    letI : TopologicalSpace FusionReal := parameterGHTopology ε
    (next q m).point = m.point ∧ m.point ∈ (next q m).trace ∧ (next q m).trace ⊆ m.openSet := by
  let : TopologicalSpace FusionReal := parameterGHTopology ε
  classical
  by_cases h : m.point ∈ q.trace
  · have hs := (extend q m.point h m.openSet m.isOpen m.mem).choose_spec
    simpa only [next,dite_eq_left h] using And.intro hs.2.1 ⟨hs.2.2.1,hs.2.2.2.1⟩
  · have hs := (extend (initial ε) m.point (by simp) m.openSet m.isOpen m.mem).choose_spec
    simpa only [next,dite_eq_right h] using And.intro hs.2.1 ⟨hs.2.2.1,hs.2.2.2.1⟩

theorem next_extends (q : State ε) (m : Move ε)
    (h : @StrongChoquetGame.Move.point FusionReal (parameterGHTopology ε) m ∈ q.trace) :
    (next q m).level = q.level+1 ∧
      (∀ k < q.level, (next q m).point k = q.point k) ∧
      (∀ i < q.level, (next q m).tree i = q.tree i ∧
        ∀ k < q.level, (next q m).witness i k = q.witness i k) := by
  let : TopologicalSpace FusionReal := parameterGHTopology ε
  classical
  have hs := (extend q m.point h m.openSet m.isOpen m.mem).choose_spec
  simpa only [next,dite_eq_left h] using And.intro hs.1 ⟨hs.2.2.2.2.2.1,hs.2.2.2.2.2.2⟩

noncomputable def reply (q : State ε) (m : Move ε) : Reply m := by
  letI : TopologicalSpace FusionReal := parameterGHTopology ε
  exact ⟨(next q m).trace,(next q m).isOpen,(next_valid q m).2.1,(next_valid q m).2.2⟩

/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    For (2), first work on $\BaireSpace$. We construct a winning strategy in the
    \termuse{strong Choquet game} of §{sec:topological-infinite-games}. At round $n$, Player I has played
    $x_n\in U_n$. For $n>0$, legality gives $x_n\in U_n\IncludedIn V_{n-1}$.
    Choose a basic set and a pair tree presenting it:
    $$x_n\in B_n\IncludedIn U_n,\qquad B_n=\pi_0(\TreeBody{T_n}).$$
    All these tree presentations use the same parameter $\varepsilon$.
-/
noncomputable def strategy (ε : ℕ → ℕ) :
    @StrongChoquetGame.Strategy FusionReal (parameterGHTopology ε) :=
  @StrongChoquetGame.stateStrategy FusionReal (parameterGHTopology ε) (State ε)
    (initial ε) next reply

/-- Legality forces every step to use the extending branch, so the reset
branch never occurs in a play following the strategy. -/
/-@ booklink:
  source: polish-space-book/effective-dst-gandy-harrington-dichotomies.md
  target: proof
  excerpt: |
    In a play following this strategy, the compatible prefixes $u_n$ determine a point $x$, and for
    each fixed $i$ the prefixes $v_{i,n}$ for $n\ge i$ determine a witness $y_i$. To justify membership
    in the tree body, consider the actual pairs $(x_n,y_{i,n})\in\TreeBody{T_i}$ for $n\ge i$. Their fixed initial
    segments grow without bound, so these pairs converge to $(x,y_i)$ in the ordinary product topology.
    The body $\TreeBody{T_i}$ is closed in that topology, hence $(x,y_i)\in\TreeBody{T_i}$. Moreover, $x$ extends every
    $u_n$, and $y_i$ extends $v_{i,n}$ whenever $i\le n$. Thus $x\in V_n\IncludedIn U_n$ for every $n$,
    and Player II wins.
-/
theorem strategy_winning (ε : ℕ → ℕ) :
    @StrongChoquetGame.Winning FusionReal (parameterGHTopology ε) (strategy ε) := by
  let : TopologicalSpace FusionReal := parameterGHTopology ε
  apply StrongChoquetGame.stateStrategy_winning
  intro p hlegal
  let q := @StrongChoquetGame.stateRun FusionReal (parameterGHTopology ε) (State ε)
    (initial ε) next p
  have hzero : q 0 = initial ε := rfl
  have hsucc (n : ℕ) : q (n+1) = next (q n) (p n) :=
    StrongChoquetGame.stateRun_succ _ _ _ _ n
  have hinput (n : ℕ) : (p n).point ∈ (q n).trace := by
    cases n with
    | zero => simp only [hzero,initial_trace,mem_univ]
    | succ n =>
      rw [hsucc]
      exact hlegal n (p (n+1)).mem
  have hlevel : ∀ n, (q n).level = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [hsucc,(next_extends (q n) (p n) (hinput n)).1,ih]
  have hpoint (n k : ℕ) (hk : k < n) : (q (n+1)).point k = (q n).point k := by
    rw [hsucc]
    exact (next_extends (q n) (p n) (hinput n)).2.1 k (by rwa [hlevel])
  have htrees (n i : ℕ) (hi : i < n) : (q (n+1)).tree i = (q n).tree i := by
    rw [hsucc]
    exact ((next_extends (q n) (p n) (hinput n)).2.2 i (by rwa [hlevel])).1
  have hwit (n i k : ℕ) (hi : i < n) (hk : k < n) :
      (q (n+1)).witness i k = (q n).witness i k := by
    rw [hsucc]
    exact ((next_extends (q n) (p n) (hinput n)).2.2 i (by rwa [hlevel])).2 k (by rwa [hlevel])
  have hmem (n : ℕ) : (q n).point ∈ (q n).trace := by
    cases n with
    | zero => simp only [hzero,initial_trace,mem_univ]
    | succ n =>
      rw [hsucc]
      rw [(next_valid (q n) (p n)).1]
      exact (next_valid (q n) (p n)).2.1
  obtain ⟨x,hx⟩ := states_fusion q hlevel hpoint htrees hwit hmem
  refine ⟨x,fun n => ?_⟩
  apply (next_valid (q n) (p n)).2.2
  simpa only [hsucc] using hx (n+1)

theorem strongChoquet (ε : ℕ → ℕ) :
    @StrongChoquetGame.IsStrongChoquet FusionReal (parameterGHTopology ε) :=
  ⟨strategy ε,strategy_winning ε⟩

end LambdaTree.GHChoquet
end PolishSpaceBook
