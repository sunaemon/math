module

public import PolishSpaceBook.Determinacy

@[expose] public section

/-!
# Legal tree games and the play of two strategies

Legal positions form a nonempty prefix tree with no terminal nodes. Successive
legal moves construct an infinite branch, from any initial position. On the root
branch, a pair of strategies determines a unique play, so winning is not vacuous.
-/

noncomputable section
namespace PolishSpaceBook.TreeGames
open Set Function
universe u

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    For infinite play, we require the legal finite positions to form a nonempty tree $T\IncludedIn\finseq{M}$
    with no terminal nodes, and we take $L=\TreeBody{T}$. The next lemma shows that this agrees with the
    branch-extension definition of a pruned tree in §{sec:cantor-baire-space}.
-/
/-- The book's tree for play, with an explicit legal successor at every node. -/
structure GameTree (M : Type u) where
  nodes : Set (List M)
  subtree : IsSubtree nodes
  root_mem : [] ∈ nodes
  successor : ∀ s ∈ nodes, ∃ a, s ++ [a] ∈ nodes

namespace GameTree
variable {M : Type u} (T : GameTree M)

abbrev Position := {s : List M // s ∈ T.nodes}
abbrev Play := {x : ℕ → M // x ∈ treeBody T.nodes}
abbrev LegalMove (s : T.Position) := {a : M // s.val ++ [a] ∈ T.nodes}
abbrev Policy := (s : T.Position) → T.LegalMove s

def root : T.Position := ⟨[], T.root_mem⟩
def child (s : T.Position) (a : T.LegalMove s) : T.Position := ⟨s.val ++ [a.val], a.property⟩

def defaultPolicy : T.Policy := fun s => ⟨(T.successor s.val s.property).choose,
  (T.successor s.val s.property).choose_spec⟩

/-- Histories obtained by repeatedly applying a legal policy. -/
def history (δ : T.Policy) (s : T.Position) : ℕ → T.Position
  | 0 => s
  | n + 1 => T.child (history δ s n) (δ (history δ s n))

lemma history_length (δ : T.Policy) (s : T.Position) (n : ℕ) :
    (T.history δ s n).val.length = s.val.length + n := by
  induction n with
  | zero => simp [history]
  | succ n ih => simp [history, child, ih, Nat.add_assoc]

lemma history_prefix (δ : T.Policy) (s : T.Position) {n m : ℕ} (h : n ≤ m) :
    (T.history δ s n).val <+: (T.history δ s m).val := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih => exact ih.trans (List.prefix_append _ _)

/-- Read the compatible finite histories coordinate by coordinate. -/
def branch (δ : T.Policy) (s : T.Position) (n : ℕ) : M :=
  (T.history δ s (n + 1)).val[n]'(by rw [history_length]; omega)

lemma branch_get (δ : T.Policy) (s : T.Position) {n i : ℕ} (hi : i < n) :
    T.branch δ s i = (T.history δ s n).val[i]'(by rw [history_length]; omega) := by
  exact (T.history_prefix δ s (show i + 1 ≤ n by omega)).getElem (by rw [history_length]; omega)

lemma branch_prefix (δ : T.Policy) (s : T.Position) (n : ℕ) :
    seqPrefix (T.branch δ s) n = (T.history δ s n).val.take n := by
  apply List.ext_getElem
  · simp [history_length]
  · intro i hi _
    have hin : i < n := by simpa using hi
    simpa [seqPrefix] using T.branch_get δ s hin

lemma branch_legal (δ : T.Policy) (s : T.Position) : T.branch δ s ∈ treeBody T.nodes := by
  intro n
  rw [branch_prefix]
  exact T.subtree (T.history δ s n).property (List.take_prefix _ _)

lemma branch_extends (δ : T.Policy) (s : T.Position) : T.branch δ s ∈ cyl s.val := by
  intro i hi
  have hp := T.history_prefix δ s (Nat.zero_le (i + 1))
  exact (hp.getElem hi).symm

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Suppose every node has a legal one-step extension. Choose a move $\chi(t)$ with
    $t\concat(\chi(t))\in T$ for each $t\in T$. Starting at any $s\in T$, define
    $$
    t_0:=s,\qquad t_{n+1}:=t_n\concat(\chi(t_n)).
    $$
    Then $t_n\in T$, $\Length{t_n}=\Length{s}+n$, and each word extends its predecessor. These compatible words determine
    an infinite sequence $z$ extending $s$. Every finite prefix of $z$ is a prefix of some $t_n$, hence belongs to
    $T$ because $T$ is a tree. Thus $z\in\TreeBody{T}$. Conversely, the next coordinate of a branch extending a node
    gives a legal one-step extension of that node.
    \end{proof}
-/
/-- No-terminal-node trees are pruned in the earlier branch-extension sense. -/
theorem isPruned : IsPruned T.nodes := by
  intro s hs
  exact ⟨T.branch T.defaultPolicy ⟨s, hs⟩, T.branch_legal _ _, T.branch_extends T.defaultPolicy ⟨s, hs⟩⟩

/-- The converse: branch extension supplies a legal one-step successor. -/
theorem successor_of_isPruned {S : Set (List M)} (hS : IsPruned S) {s : List M} (hs : s ∈ S) :
    ∃ a, s ++ [a] ∈ S := by
  obtain ⟨x, hx, hxs⟩ := hS hs
  refine ⟨x s.length, ?_⟩
  have h := hx (s.length + 1)
  rw [seqPrefix_succ_eq_concat, seqPrefix_eq_of_mem_cyl hxs] at h
  exact h

/-- The two standard formulations of pruning coincide for prefix trees. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: Branch extension
-/
theorem pruned_iff_successor {S : Set (List M)} (hS : IsSubtree S) (hne : S.Nonempty) :
    IsPruned S ↔ ∀ s ∈ S, ∃ a, s ++ [a] ∈ S := by
  constructor
  · intro hp s hs
    exact successor_of_isPruned hp hs
  · intro hs
    let T : GameTree M := ⟨S, hS, hS hne.choose_spec List.nil_prefix, hs⟩
    exact T.isPruned

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    In particular, the nodes of $T$ are exactly the finite prefixes of allowed plays. The requirement
    $L=\TreeBody{T}$ ensures that an infinite sequence of legal moves is itself allowed.
-/
/-- Legal positions are exactly the finite prefixes of allowed infinite plays. -/
lemma position_iff_prefix_play (s : List M) :
    s ∈ T.nodes ↔ ∃ x : T.Play, x.val ∈ cyl s := by
  constructor
  · intro hs
    obtain ⟨x, hx, hxs⟩ := T.isPruned hs
    exact ⟨⟨x, hx⟩, hxs⟩
  · rintro ⟨x, hx⟩
    simpa only [seqPrefix_eq_of_mem_cyl hx] using x.property s.length

/-- Player I moves at even lengths, Player II at odd lengths. -/
def turn (s : List M) : Bool := s.length % 2 == 0

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    A \termdefineas{game strategy}{strategy} for Player I is a function assigning I's next legal move after partial plays of
    even length. A
    strategy for Player II is a function assigning II's next legal move after partial plays of odd length.
-/
/-- A strategy returns a legal move only on positions where its player moves. -/
abbrev Strategy (p : Bool) := (s : T.Position) → turn s.val = p → T.LegalMove s

def defaultStrategy (p : Bool) : T.Strategy p := fun s _ => T.defaultPolicy s

def prefixPosition (x : T.Play) (n : ℕ) : T.Position := ⟨seqPrefix x.val n, x.property n⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Player I \termdefineas{follows a strategy}{follows} $\sigma$ in a play if $a_{2n}=\sigma(a_0,\ldots,a_{2n-1})$ for every $n$, and
    Player II follows $\tau$ if $a_{2n+1}=\tau(a_0,\ldots,a_{2n})$ for every $n$. Equivalently, the play itself is said to
    \termuseas{follows a strategy}{follow} the relevant strategy.
-/
def Follows {p : Bool} (σ : T.Strategy p) (x : T.Play) : Prop :=
  ∀ n (h : turn (seqPrefix x.val n) = p), x.val n = (σ (T.prefixPosition x n) h).val

def combine (σ : T.Strategy true) (τ : T.Strategy false) : T.Policy := fun s =>
  if h : turn s.val = true then σ s h else τ s (by cases e : turn s.val <;> simp_all)

/-- The legal play generated by a pair of strategies. -/
def outcome (σ : T.Strategy true) (τ : T.Strategy false) : T.Play :=
  ⟨T.branch (T.combine σ τ) T.root, T.branch_legal _ _⟩

lemma root_branch_prefix (δ : T.Policy) (n : ℕ) :
    seqPrefix (T.branch δ T.root) n = (T.history δ T.root n).val := by
  rw [branch_prefix]
  apply List.take_of_length_le
  simp [history_length, root]

lemma root_branch_move (δ : T.Policy) (n : ℕ) :
    T.branch δ T.root n = (δ (T.history δ T.root n)).val := by
  unfold branch
  simp only [history, child]
  have hlen : (T.history δ T.root n).val.length = n := by simp [history_length, root]
  simp [hlen]

lemma outcome_prefix (σ : T.Strategy true) (τ : T.Strategy false) (n : ℕ) :
    T.prefixPosition (T.outcome σ τ) n = T.history (T.combine σ τ) T.root n := by
  apply Subtype.ext
  exact T.root_branch_prefix _ n

lemma outcome_follows_I (σ : T.Strategy true) (τ : T.Strategy false) :
    T.Follows σ (T.outcome σ τ) := by
  intro n h
  have he := T.outcome_prefix σ τ n
  change T.branch (T.combine σ τ) T.root n = _
  rw [root_branch_move, ← he]
  simp [combine, show turn (T.prefixPosition (T.outcome σ τ) n).val = true from h]

lemma outcome_follows_II (σ : T.Strategy true) (τ : T.Strategy false) :
    T.Follows τ (T.outcome σ τ) := by
  intro n h
  have he := T.outcome_prefix σ τ n
  change T.branch (T.combine σ τ) T.root n = _
  rw [root_branch_move, ← he]
  simp [combine, show turn (T.prefixPosition (T.outcome σ τ) n).val = false from h]

/-- Alternating the two strategies determines every coordinate of any compatible play. -/
lemma follows_combine (σ : T.Strategy true) (τ : T.Strategy false) (x : T.Play)
    (hσ : T.Follows σ x) (hτ : T.Follows τ x) (n : ℕ) :
    x.val n = (T.combine σ τ (T.prefixPosition x n)).val := by
  unfold combine
  split
  · exact hσ n _
  · exact hτ n _

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    \begin{proof}[Proof]
    Given strategies $\sigma$ for I and $\tau$ for II, define finite positions recursively by
    $$
    s_0:=\emptyset,\qquad
    s_{n+1}:=
    \begin{cases}
    s_n\concat(\sigma(s_n)),&n\text{ even},\\
    s_n\concat(\tau(s_n)),&n\text{ odd}.
    \end{cases}
    $$
    Each position is legal and has length $n$. The compatible positions therefore determine a branch through $T$,
    and this play follows both strategies. Conversely, induction on the length shows that any play following
    both has $s_n$ as its prefix of length $n$. This proves uniqueness.
-/
/-- A pair of strategies has exactly one compatible legal play. -/
theorem outcome_unique (σ : T.Strategy true) (τ : T.Strategy false) (x : T.Play)
    (hσ : T.Follows σ x) (hτ : T.Follows τ x) : x = T.outcome σ τ := by
  have hist (n : ℕ) : T.prefixPosition x n = T.history (T.combine σ τ) T.root n := by
    induction n with
    | zero => apply Subtype.ext; simp [prefixPosition, history, root, seqPrefix]
    | succ n ih =>
      apply Subtype.ext
      change seqPrefix x.val (n + 1) = _
      rw [seqPrefix_succ_eq_concat]
      change seqPrefix x.val n ++ [x.val n] = _
      rw [T.follows_combine σ τ x hσ hτ n, ih]
      exact congrArg (fun s : T.Position => s.val ++ [(T.combine σ τ (T.history _ T.root n)).val]) ih
  apply Subtype.ext
  funext n
  change x.val n = T.branch (T.combine σ τ) T.root n
  rw [root_branch_move, ← hist n]
  exact T.follows_combine σ τ x hσ hτ n

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: The play of two strategies
-/
theorem exists_unique_joint_play (σ : T.Strategy true) (τ : T.Strategy false) :
    ∃! x : T.Play, T.Follows σ x ∧ T.Follows τ x :=
  ⟨T.outcome σ τ, ⟨T.outcome_follows_I σ τ, T.outcome_follows_II σ τ⟩,
    fun x hx => T.outcome_unique σ τ x hx.1 hx.2⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: The play of two strategies
-/
lemma exists_follows (p : Bool) (σ : T.Strategy p) : ∃ x : T.Play, T.Follows σ x := by
  cases p
  · exact ⟨T.outcome (T.defaultStrategy true) σ, T.outcome_follows_II _ _⟩
  · exact ⟨T.outcome σ (T.defaultStrategy false), T.outcome_follows_I _ _⟩

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    A strategy is \termdefineas{winning strategy}{winning} if
    every allowed play in which that player follows it is a win for that player. The game is
    \termdefineas{determined game}{determined} if one of the two players has a winning strategy.
-/
/-- Player-indexed winning, with Player I's payoff specified as a set of legal branches. -/
def Winning (A : Set T.Play) (p : Bool) (σ : T.Strategy p) : Prop :=
  ∀ x, T.Follows σ x → if p then x ∈ A else x ∉ A

def Determined (A : Set T.Play) : Prop :=
  (∃ σ : T.Strategy true, T.Winning A true σ) ∨ ∃ τ : T.Strategy false, T.Winning A false τ

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    Pairing a fixed strategy with any legal strategy for the other player gives an allowed play following it.
    Such a strategy for the other player exists by choosing a legal move at each of that player's positions.
    If both strategies were winning, their common play would belong both to $A$ and to $\SetDifference{L}{A}$,
    a contradiction.
    \end{proof}
-/
/-- Both players cannot have winning strategies for the same payoff. -/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  kind: lemma
  title: The play of two strategies
-/
theorem not_both_winning (A : Set T.Play) (σ : T.Strategy true) (τ : T.Strategy false) :
    ¬ (T.Winning A true σ ∧ T.Winning A false τ) := by
  rintro ⟨hσ, hτ⟩
  exact hτ (T.outcome σ τ) (T.outcome_follows_II σ τ)
    (hσ (T.outcome σ τ) (T.outcome_follows_I σ τ))

end GameTree
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    The two players are called Player I and Player II. A
    \termdefineas{perfect-information game}{two-player infinite perfect-information game} is a tuple $\Tuple{M,L,A}$, where
    $M$ is
    a set of moves, $L\IncludedIn\funcspace{\omega}{M}$ is the
    set of allowed infinite plays, and $A\IncludedIn L$ is the payoff set for Player I. A finite sequence $s\in\finseq{M}$
    is
    a \termdefine{partial play} if it is an initial segment of some element of $L$. A move $a\in M$ is
    \termdefine{legal after} $s$ if $s\concat(a)$ is a partial play. Player I chooses a legal move $a_0$ after $\emptyset$;
    Player II then
    chooses a legal move $a_1$ after seeing $(a_0)$; Player I chooses a legal move $a_2$ after seeing $\Pair{a_0}{a_1}$; and
    so
    on. Thus the players alternate, starting with I:
    $$\underbrace{a_0}_{\mathrm{I}},\ \underbrace{a_1}_{\mathrm{II}},\ \underbrace{a_2}_{\mathrm{I}},\quad
    \underbrace{a_3}_{\mathrm{II}},\ \ldots \qquad (a_n \in M).$$
    The resulting infinite sequence is called a \termdefineas{game play}{play}, and it must lie in $L$. A play is a win for
    Player I if it lies in $A$, and a win for Player II if it lies in $\SetDifference{L}{A}$.
-/
/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    A \termdefine{tree for play} is a nonempty tree $T\IncludedIn\finseq{M}$ with no terminal nodes,
    where $M$ is a set of moves with the discrete topology. We allow arbitrary sets of moves in the auxiliary games
    used in Martin's proof, even when the original game has moves in $\omega$. The game
    $G(A,T)$, for $A\IncludedIn\TreeBody{T}$, uses the nodes of $T$ as its legal finite positions; Player I wins exactly
    when
    the resulting branch lies in $A$. The ordinary game on $\BaireSpace$ is the case $T=\finseq{\omega}$.
-/
/-- A perfect-information game with its legal tree and Player I payoff. -/
structure Game (M : Type u) where
  tree : GameTree M
  payoff : Set tree.Play

/-- The full tree recovers the unrestricted game on Baire space. -/
def fullBaireTree : GameTree ℕ where
  nodes := univ
  subtree := univ_isSubtree
  root_mem := mem_univ _
  successor := fun _ _ => ⟨0, mem_univ _⟩

def fullBairePlay (x : ℕ → ℕ) : fullBaireTree.Play := ⟨x, fun _ => mem_univ _⟩

def toBaireI (σ : fullBaireTree.Strategy true) : BaireIStrategy := fun n s =>
  (σ ⟨List.ofFn s, mem_univ _⟩ (by simp [GameTree.turn])).val

def toBaireII (τ : fullBaireTree.Strategy false) : BaireIIStrategy := fun n s =>
  (τ ⟨List.ofFn s, mem_univ _⟩ (by simp [GameTree.turn])).val

lemma follows_toBaireI (σ : fullBaireTree.Strategy true) (x : ℕ → ℕ) :
    fullBaireTree.Follows σ (fullBairePlay x) ↔ BaireFollowsI (toBaireI σ) x := by
  constructor
  · intro h n
    exact h (2 * n) (by simp [GameTree.turn])
  · intro h n hn
    have heven : n % 2 = 0 := by simpa [GameTree.turn, fullBairePlay] using hn
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    exact h k

lemma follows_toBaireII (τ : fullBaireTree.Strategy false) (x : ℕ → ℕ) :
    fullBaireTree.Follows τ (fullBairePlay x) ↔ BaireFollowsII (toBaireII τ) x := by
  constructor
  · intro h n
    exact h (2 * n + 1) (by simp [GameTree.turn])
  · intro h n hn
    have hodd : n % 2 ≠ 0 := by simpa [GameTree.turn, fullBairePlay] using hn
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    exact h k

/-- Extend an ordinary Player I strategy to the full-tree presentation. -/
def ofBaireI (σ : BaireIStrategy) : fullBaireTree.Strategy true := fun s _h =>
  ⟨σ (s.val.length / 2) (fun i => s.val[i.val]'(by omega)), mem_univ _⟩

/-- Extend an ordinary Player II strategy to the full-tree presentation. -/
def ofBaireII (τ : BaireIIStrategy) : fullBaireTree.Strategy false := fun s h =>
  ⟨τ (s.val.length / 2) (fun i => s.val[i.val]'(by
    have : s.val.length % 2 ≠ 0 := by simpa [GameTree.turn] using h
    omega)), mem_univ _⟩

lemma toBaireI_ofBaireI (σ : BaireIStrategy) : toBaireI (ofBaireI σ) = σ := by
  funext n s
  dsimp only [toBaireI, ofBaireI]
  congr 1
  · simp only [List.length_ofFn]
    omega
  · apply (Fin.heq_fun_iff (by simp only [List.length_ofFn]; omega)).mpr
    intro i
    simp only [List.getElem_ofFn]

lemma toBaireII_ofBaireII (τ : BaireIIStrategy) : toBaireII (ofBaireII τ) = τ := by
  funext n s
  dsimp only [toBaireII, ofBaireII]
  congr 1
  · simp only [List.length_ofFn]
    omega
  · apply (Fin.heq_fun_iff (by simp only [List.length_ofFn]; omega)).mpr
    intro i
    simp only [List.getElem_ofFn]

/-- Every ordinary pair of strategies also produces a compatible Baire-space play. -/
theorem baire_exists_joint_play (σ : BaireIStrategy) (τ : BaireIIStrategy) :
    ∃ x, BaireFollowsI σ x ∧ BaireFollowsII τ x := by
  let x := fullBaireTree.outcome (ofBaireI σ) (ofBaireII τ)
  refine ⟨x.val, ?_, ?_⟩
  · have h := (follows_toBaireI (ofBaireI σ) x.val).mp (fullBaireTree.outcome_follows_I _ _)
    simpa only [toBaireI_ofBaireI] using h
  · have h := (follows_toBaireII (ofBaireII τ) x.val).mp (fullBaireTree.outcome_follows_II _ _)
    simpa only [toBaireII_ofBaireII] using h

theorem baire_not_both_winning (A : Set (ℕ → ℕ)) (σ : BaireIStrategy) (τ : BaireIIStrategy) :
    ¬ (BaireIWinning A σ ∧ BaireIIWinning A τ) := by
  rintro ⟨hσ, hτ⟩
  obtain ⟨x, hxσ, hxτ⟩ := baire_exists_joint_play σ τ
  exact hτ x hxτ (hσ x hxσ)

/-- The payoff and winning predicates agree in the two presentations. -/
lemma winning_toBaireI (A : Set (ℕ → ℕ)) (σ : fullBaireTree.Strategy true) :
    fullBaireTree.Winning {x | x.val ∈ A} true σ ↔ BaireIWinning A (toBaireI σ) := by
  constructor
  · intro h x hx
    exact h (fullBairePlay x) ((follows_toBaireI σ x).mpr hx)
  · intro h x hx
    exact h x.val ((follows_toBaireI σ x.val).mp hx)

lemma winning_toBaireII (A : Set (ℕ → ℕ)) (τ : fullBaireTree.Strategy false) :
    fullBaireTree.Winning {x | x.val ∈ A} false τ ↔ BaireIIWinning A (toBaireII τ) := by
  constructor
  · intro h x hx
    exact h (fullBairePlay x) ((follows_toBaireII τ x).mpr hx)
  · intro h x hx
    exact h x.val ((follows_toBaireII τ x.val).mp hx)

/-- General tree determinacy specializes to the chapter's original Baire definition. -/
theorem determined_full_iff (A : Set (ℕ → ℕ)) :
    fullBaireTree.Determined {x | x.val ∈ A} ↔ BaireDetermined A := by
  constructor
  · rintro (⟨σ, hσ⟩ | ⟨τ, hτ⟩)
    · exact Or.inl ⟨toBaireI σ, (winning_toBaireI A σ).mp hσ⟩
    · exact Or.inr ⟨toBaireII τ, (winning_toBaireII A τ).mp hτ⟩
  · rintro (⟨σ, hσ⟩ | ⟨τ, hτ⟩)
    · apply Or.inl
      refine ⟨ofBaireI σ, (winning_toBaireI A _).mpr ?_⟩
      simpa only [toBaireI_ofBaireI] using hσ
    · apply Or.inr
      refine ⟨ofBaireII τ, (winning_toBaireII A _).mpr ?_⟩
      simpa only [toBaireII_ofBaireII] using hτ

end PolishSpaceBook.TreeGames
