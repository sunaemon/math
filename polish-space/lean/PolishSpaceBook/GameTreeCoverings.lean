module

public import PolishSpaceBook.GaleStewart
public import PolishSpaceBook.BorelStructure

@[expose] public section

/-! # Coverings of legal tree games

Auxiliary move sets are arbitrary discrete types, with independent universes.
Strategy transport preserves the player. A compatible play downstairs must
have a compatible lift upstairs; no single global section is required.
-/
namespace PolishSpaceBook.TreeGames
open Set Function
universe u v w
variable {M : Type u} {N : Type v} {P : Type w}
variable [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

namespace GameTree

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    The \termuse{tree for play} convention above lets the unraveling architecture change the legal positions while retaining
    the same game semantics.
    The auxiliary move sets need not be countable: a single move may include an entire strategy or subtree.
    Branch spaces carry the product topology of these discrete move sets.
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    For $k \in \omega$, write
    $$T^{(k)} := \{s \in T : |s|=k\}.$$
    A strategy for a game on $T$ is a rule defined on legal positions of the appropriate parity. Let $S(T)$ be the class of
    strategies for either player.
-/
/-- The positions at exactly one finite level. -/
abbrev Level (T : GameTree M) (k : ℕ) := {s : T.Position // s.val.length = k}

/-- Strategies for either player, with the player retained as part of the data. -/
abbrev PlayerStrategy (T : GameTree M) := (p : Bool) × T.Strategy p

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    A \termdefineas{game-tree covering}{covering} of $T$ is a triple $(\tilde T,\pi,\varphi)$ such that:
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{enumerate}
    \item $\tilde T$ is a tree for play.
    \item $\pi : [\tilde T] \to [T]$ is continuous.
    \item $\varphi : S(\tilde T)\to S(T)$ sends strategies for I to strategies for I, and strategies for II to strategies
    for II.
    \item If $x\in [T]$ is a play following $\varphi(\sigma)$, then there is a play $\tilde x\in[\tilde T]$ following
    $\sigma$ with $\pi(\tilde x)=x$.
    \end{enumerate}
-/
/-- A continuous branch map, player-preserving strategy transport, and the
compatible-play lifting condition from the book. -/
structure Covering (S : GameTree N) (T : GameTree M) where
  project : S.Play → T.Play
  continuous_project : Continuous project
  strategy : ∀ p, S.Strategy p → T.Strategy p
  lift : ∀ p (σ : S.Strategy p) (x : T.Play), T.Follows (strategy p σ) x →
    ∃ y : S.Play, S.Follows σ y ∧ project y = x

namespace Covering
variable {T : GameTree M} {S : GameTree N} {R : GameTree P}

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    The covering \termdefineas{unravels a payoff set}{unravels} $A\IncludedIn[T]$ if $\pi^{-1}(A)$ is clopen in $[\tilde
    T]$.
-/
/-- The covering turns the payoff into a clopen set upstairs. -/
def Unravels (C : Covering S T) (A : Set T.Play) : Prop := IsClopen (C.project ⁻¹' A)

/-- Every winning strategy upstairs transports to the same player's winning strategy. -/
theorem winning_down (C : Covering S T) {A : Set T.Play} {p : Bool}
    {σ : S.Strategy p} (hσ : S.Winning (C.project ⁻¹' A) p σ) :
    T.Winning A p (C.strategy p σ) := by
  intro x hx
  obtain ⟨y,hy,he⟩ := C.lift p σ x hx
  simpa only [Set.mem_preimage, he] using hσ y hy

/-- Determinacy transports without any topological assumption on the payoff. -/
theorem determined_down (C : Covering S T) {A : Set T.Play}
    (hA : S.Determined (C.project ⁻¹' A)) : T.Determined A := by
  rcases hA with ⟨σ,hσ⟩ | ⟨τ,hτ⟩
  · exact Or.inl ⟨C.strategy true σ, C.winning_down hσ⟩
  · exact Or.inr ⟨C.strategy false τ, C.winning_down hτ⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  excerpt: |
    \begin{lemma*} If a covering of $T$ unravels $A\IncludedIn[T]$, then $G(A,T)$ is determined.
    
    \end{lemma*}
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: proof
  excerpt: |
    \begin{proof}[Proof] Since $\pi^{-1}(A)$ is clopen, Gale--Stewart determines $G(\pi^{-1}(A),\tilde T)$. Let $\sigma$ be
    a winning strategy there, say for Player I. We show that $\varphi(\sigma)$ wins $G(A,T)$. If $x$ follows
    $\varphi(\sigma)$, condition (4) gives $\tilde x$ following $\sigma$ with $\pi(\tilde x)=x$. Since $\sigma$ wins,
    $\tilde x\in\pi^{-1}(A)$, hence $x\in A$. The proof for a winning strategy for II is the same, replacing membership in
    $A$ by nonmembership.
    \end{proof}
-/
/-- Gale--Stewart upstairs finishes a clopen unraveling downstairs. -/
theorem determined_of_unravels [DiscreteTopology N] (C : Covering S T)
    {A : Set T.Play} (hA : C.Unravels A) : T.Determined A :=
  C.determined_down (S.open_determined hA.isOpen)

/-- Identity transport lifts each play to itself. -/
def refl (T : GameTree M) : Covering T T where
  project := id
  continuous_project := continuous_id
  strategy := fun _ σ => σ
  lift := fun _ _ x hx => ⟨x,hx,rfl⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Coverings compose. If $(T_1,\pi_1,\varphi_1)$ covers $T_0$ and $(T_2,\pi_2,\varphi_2)$ covers $T_1$, then
    $$(T_2,\pi_1\circ\pi_2,\varphi_1\circ\varphi_2)$$
    covers $T_0$. Condition (4) is verified by lifting a play first through $\varphi_1$ and then through $\varphi_2$. Hence
    a later unraveling may be composed with all earlier ones.
-/
/-- Lift a play through the lower covering first, then through the upper one. -/
def comp (C : Covering S T) (D : Covering R S) : Covering R T where
  project := C.project ∘ D.project
  continuous_project := C.continuous_project.comp D.continuous_project
  strategy := fun p σ => C.strategy p (D.strategy p σ)
  lift := by
    intro p σ x hx
    obtain ⟨y,hy,hyx⟩ := C.lift p (D.strategy p σ) x hx
    obtain ⟨z,hz,hzy⟩ := D.lift p σ y hy
    exact ⟨z,hz,by simp only [Function.comp_apply,hzy,hyx]⟩

/-- A later unraveling of the pulled-back payoff unravels the original payoff. -/
theorem Unravels.comp {C : Covering S T} {D : Covering R S} {A : Set T.Play}
    (h : D.Unravels (C.project ⁻¹' A)) : (C.comp D).Unravels A := h

/-- The same covering unravels the complementary payoff. -/
theorem Unravels.compl {C : Covering S T} {A : Set T.Play}
    (h : C.Unravels A) : C.Unravels Aᶜ := by
  simpa only [Unravels, preimage_compl] using IsClopen.compl h

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    We also use two elementary facts. First, if a $k$-covering unravels $A$, it also unravels $\SetDifference{[T]}{A}$,
    because
    clopen sets are closed under complement. Second, if $A$ belongs to a Borel pointclass $\Gamma$ and $\pi$ is continuous,
    then $\pi^{-1}(A)$ belongs to the same pointclass. This is just the closure of Borel classes under continuous preimage.
-/
/-- The covering projection preserves every additive, multiplicative, and
ambiguous Borel level, with the ordinal unchanged. -/
theorem borel_preimages (C : Covering S T) (α : Ordinal) (A : Set T.Play) :
    (A ∈ borelSigma α → C.project ⁻¹' A ∈ borelSigma α) ∧
    (A ∈ borelPi α → C.project ⁻¹' A ∈ borelPi α) ∧
    (A ∈ borelDelta α → C.project ⁻¹' A ∈ borelDelta α) :=
  ⟨borelSigma_preimage _ C.continuous_project α,
    borelPi_preimage _ C.continuous_project α,
    borelDelta_preimage _ C.continuous_project α⟩

end Covering
/-- The finite prefix of a legal branch, viewed at its precise level. -/
def prefixLevel (T : GameTree M) (x : T.Play) (n : ℕ) : T.Level n :=
  ⟨T.prefixPosition x n, seqPrefix_length x.val n⟩

/-- Strategies agree through n when all decisions before level n agree. -/
def StrategyAgree (T : GameTree M) {p : Bool} (n : ℕ) (σ τ : T.Strategy p) : Prop :=
  ∀ s (hp : turn s.val = p), s.val.length < n → (σ s hp).val = (τ s hp).val

/-- The next position selected by a strategy at one fixed level. -/
def nextLevel (T : GameTree M) {p : Bool} (σ : T.Strategy p) {n : ℕ}
    (s : T.Level n) (hp : (n % 2 == 0) = p) : T.Level (n+1) :=
  ⟨T.child s.val (σ s.val (by simpa only [turn,s.property] using hp)), by
    simp only [child,List.length_append,List.length_singleton,s.property]⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    The induction needs coverings that do not disturb a fixed finite opening segment. A covering $(\tilde T,\pi,\varphi)$ of
    $T$ is a \termdefineas{k-covering of a game tree}{$k$-covering} if:
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    1.  $\restrict{\pi(\tilde x)}{n}$ depends only on $\restrict{\tilde x}{n}$ for every $n$.
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    2.  $\varphi(\sigma)$ restricted to positions of length $<n$ depends only on $\sigma$ restricted to positions of length
        $<n$.
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    3.  For every $j\le k$, the prefix map induced by $\pi$ is a bijection $\tilde T^{(j)}\to T^{(j)}$. Under these
        identifications, $\varphi(\sigma)$ agrees with $\sigma$ at positions of length $<k$.
-/
/-- A k-covering has causal branch and strategy maps. Up to level k its
node maps are bijections and carry each selected next position to the
selected next position downstairs. This expresses agreement under the
finite-level identifications even when the move alphabets differ. -/
structure ControlledCovering (S : GameTree N) (T : GameTree M) (k : ℕ)
    extends Covering S T where
  nodeMap : ∀ n, S.Level n → T.Level n
  prefix_project : ∀ x n, T.prefixLevel (project x) n = nodeMap n (S.prefixLevel x n)
  strategy_causal : ∀ p n (σ τ : S.Strategy p), S.StrategyAgree n σ τ →
    T.StrategyAgree n (strategy p σ) (strategy p τ)
  initial_bijective : ∀ n ≤ k, Function.Bijective (nodeMap n)
  initial_strategy : ∀ p n, n < k → ∀ (σ : S.Strategy p) (s : S.Level n)
    (hp : (n % 2 == 0) = p),
    nodeMap (n+1) (S.nextLevel σ s hp) = T.nextLevel (strategy p σ) (nodeMap n s) hp

namespace ControlledCovering
variable {T : GameTree M} {S : GameTree N} {R : GameTree P} {k : ℕ}

/-- The prefix of the image play depends only on the prefix of the source play. -/
theorem project_causal (C : ControlledCovering S T k) (x y : S.Play) (n : ℕ)
    (h : seqPrefix x.val n = seqPrefix y.val n) :
    seqPrefix (C.project x).val n = seqPrefix (C.project y).val n := by
  have hlevel : S.prefixLevel x n = S.prefixLevel y n := by
    apply Subtype.ext
    exact Subtype.ext h
  have he : T.prefixLevel (C.project x) n = T.prefixLevel (C.project y) n := by
    rw [C.prefix_project,C.prefix_project,hlevel]
  exact congrArg (fun s => s.val.val) he

/-- A covering that preserves a longer opening also preserves any shorter one. -/
def restrict (C : ControlledCovering S T k) {j : ℕ} (hj : j ≤ k) : ControlledCovering S T j where
  toCovering := C.toCovering
  nodeMap := C.nodeMap
  prefix_project := C.prefix_project
  strategy_causal := C.strategy_causal
  initial_bijective := fun n hn => C.initial_bijective n (hn.trans hj)
  initial_strategy := fun p n hn => C.initial_strategy p n (hn.trans_le hj)

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Thus a $k$-covering is invisible through level $k$: up to that level the original and auxiliary games have the same
    positions. Composition preserves the relevant control: if $(T_1,\pi_1,\varphi_1)$ is a $k$-covering of $T_0$ and
    $(T_2,\pi_2,\varphi_2)$ is a $k$-covering of $T_1$, then the composite is a $k$-covering of $T_0$.
-/
/-- Finite-level identifications and strategy control compose in the same order
as the branch projections. -/
def comp (C : ControlledCovering S T k) (D : ControlledCovering R S k) :
    ControlledCovering R T k where
  toCovering := C.toCovering.comp D.toCovering
  nodeMap := fun n => C.nodeMap n ∘ D.nodeMap n
  prefix_project := by
    intro x n
    change T.prefixLevel (C.project (D.project x)) n = _
    rw [C.prefix_project,D.prefix_project]
    rfl
  strategy_causal := fun p n σ τ h =>
    C.strategy_causal p n _ _ (D.strategy_causal p n σ τ h)
  initial_bijective := fun n hn =>
    (C.initial_bijective n hn).comp (D.initial_bijective n hn)
  initial_strategy := by
    intro p n hn σ s hp
    change C.nodeMap (n+1) (D.nodeMap (n+1) (R.nextLevel σ s hp)) = _
    rw [D.initial_strategy p n hn σ s hp,C.initial_strategy p n hn]
    rfl

end ControlledCovering
end GameTree
end PolishSpaceBook.TreeGames
