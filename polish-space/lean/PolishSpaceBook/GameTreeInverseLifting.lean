module

public import PolishSpaceBook.GameTreeInverseStrategies

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Lifting compatible strategy plays to the inverse-limit game

A play following a transported strategy is lifted recursively through the given
coverings. Its compatible prefixes give a limit branch. Finite-level strategy
identities show that the limit branch follows the original limit strategy.
-/
noncomputable section
namespace PolishSpaceBook.TreeGames.GameTree.ControlledTower
open Set Function
universe u
variable {A : ℕ → Type u} [∀ i, TopologicalSpace (A i)] {k : ℕ}
variable (C : ControlledTower A k)

/-- Agreement with the concrete approximation holds at every controlled stage,
including early stages whose opening is already long because of k. -/
theorem finiteLimit_at_controlled {p : Bool} (σ : C.limitTree.Strategy p) (n i : ℕ)
    (hn : n ≤ k+i) :
    (C.finiteLimit σ n).val i = (C.tree i).finiteStrategy (C.stageApproximation σ i) n := by
  have down : ∀ d j, n ≤ k+j →
      (C.finiteLimit σ n).val (j+d) = (C.tree (j+d)).finiteStrategy (C.stageApproximation σ (j+d)) n →
      (C.finiteLimit σ n).val j = (C.tree j).finiteStrategy (C.stageApproximation σ j) n := by
    intro d
    induction d with
    | zero => intro j _ h; exact h
    | succ d ih =>
      intro j hj h
      have hnext := ih (j+1) (by omega) (by
        rw [show (j+1)+d = j+(d+1) by omega]
        exact h)
      have hbond : (C.covering j).finiteStrategyMap p n ((C.finiteLimit σ n).val (j+1)) =
          (C.finiteLimit σ n).val j := (C.finiteLimit σ n).property j
      calc
        _ = (C.covering j).finiteStrategyMap p n ((C.finiteLimit σ n).val (j+1)) := hbond.symm
        _ = (C.covering j).finiteStrategyMap p n
            ((C.tree (j+1)).finiteStrategy (C.stageApproximation σ (j+1)) n) := congrArg _ hnext
        _ = _ := Quotient.sound (C.stageApproximation_compatible σ j n hj)
  exact down (n-i) i hn (C.finiteLimit_at_late σ n (i+(n-i)) (by omega))

/-- The limit strategy and its stage-i image choose matching next positions
through the entire preserved opening k+i. -/
theorem strategy_initial {p : Bool} (σ : C.limitTree.Strategy p) (i n : ℕ) (hn : n < k+i)
    (s : C.limitTree.Level n) (hp : (n % 2 == 0) = p) :
    C.limitNodeMap i (n+1) (C.limitTree.nextLevel σ s hp) =
      (C.tree i).nextLevel (C.strategy σ i) (C.limitNodeMap i n s) hp := by
  have he : (C.tree i).finiteStrategy (C.strategy σ i) (n+1) =
      (C.tree i).finiteStrategy (C.stageApproximation σ i) (n+1) := by
    rw [C.strategy_finite,C.finiteLimit_at_controlled σ (n+1) i (by omega)]
  have ht := Quotient.exact he
  let t := C.limitNodeMap i n s
  have hpt : turn t.val.val = p := by simpa only [turn,t.property] using hp
  have hmove := ht t.val hpt (by simp only [t.property]; omega)
  have hnext : (C.tree i).nextLevel (C.strategy σ i) t hp =
      (C.tree i).nextLevel (C.stageApproximation σ i) t hp := by
    apply Subtype.ext
    apply Subtype.ext
    change t.val.val ++ [(C.strategy σ i t.val hpt).val] =
      t.val.val ++ [(C.stageApproximation σ i t.val hpt).val]
    rw [hmove]
  exact (C.stageApproximation_next σ i n hn s hp).symm.trans hnext.symm

/-- Legal stage plays following the image of one fixed limit strategy. -/
abbrev FollowingPlay {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ) :=
  {x : (C.tree i).Play // (C.tree i).Follows (C.strategy σ i) x}

/-- Use the given lifting axiom once, with the commuting strategy maps. -/
def liftFollowing {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ)
    (x : C.FollowingPlay σ i) : C.FollowingPlay σ (i+1) :=
  let h := (C.covering i).lift p (C.strategy σ (i+1)) x.val (by
    rw [C.strategy_commutes]
    exact x.property)
  ⟨h.choose,h.choose_spec.1⟩

theorem project_liftFollowing {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ)
    (x : C.FollowingPlay σ i) :
    (C.covering i).project (C.liftFollowing σ i x).val = x.val :=
  ((C.covering i).lift p (C.strategy σ (i+1)) x.val (by
    rw [C.strategy_commutes]
    exact x.property)).choose_spec.2

/-- Recursively lift the chosen play through all later stages. -/
def followingTail {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ)
    (x : C.FollowingPlay σ i) : (t : ℕ) → C.FollowingPlay σ (i+t)
  | 0 => x
  | t+1 => C.liftFollowing σ (i+t) (followingTail σ i x t)

theorem followingTail_bond {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ)
    (x : C.FollowingPlay σ i) (t : ℕ) :
    (C.covering (i+t)).project (C.followingTail σ i x (t+1)).val =
      (C.followingTail σ i x t).val :=
  C.project_liftFollowing σ (i+t) (C.followingTail σ i x t)

/-- The raw branch system; following a strategy is imposed on the chosen tail. -/
@[reducible] def plays : NatInverseSystem where
  Obj i := (C.tree i).Play
  step i := (C.covering i).project

/-- Fill earlier coordinates by finite projections, retaining the recursively lifted tail. -/
def chosenBranches {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ)
    (x : C.FollowingPlay σ i) (j : ℕ) : (C.tree j).Play :=
  if hj : j ≤ i then C.plays.down i x.val j hj
  else (show i+(j-i)=j by omega) ▸ (C.followingTail σ i x (j-i)).val

@[simp] theorem chosenBranches_add {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ)
    (x : C.FollowingPlay σ i) (t : ℕ) :
    C.chosenBranches σ i x (i+t) = (C.followingTail σ i x t).val := by
  cases t with
  | zero => simp [chosenBranches,followingTail]
  | succ t =>
    simp only [chosenBranches,dite_eq_right (show ¬ i+(t+1) ≤ i by omega)]
    apply eq_of_heq
    have ht : HEq (C.followingTail σ i x (i+(t+1)-i)).val (C.followingTail σ i x (t+1)).val := by
      rw [Nat.add_sub_cancel_left]
    exact (eqRec_heq (φ := fun j => (C.tree j).Play)
      (show i+(i+(t+1)-i) = i+(t+1) by omega) _).trans ht

theorem chosenBranches_compatible {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ)
    (x : C.FollowingPlay σ i) (j : ℕ) :
    (C.covering j).project (C.chosenBranches σ i x (j+1)) = C.chosenBranches σ i x j := by
  by_cases hj : j < i
  · simp only [chosenBranches,dite_eq_left (show j+1 ≤ i by omega),dite_eq_left (show j ≤ i by omega)]
    exact C.plays.step_down i x.val j (by omega)
  · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le (show i ≤ j by omega)
    change (C.covering (i+t)).project (C.chosenBranches σ i x (i+(t+1))) = _
    rw [C.chosenBranches_add,C.chosenBranches_add]
    exact C.followingTail_bond σ i x t

/-- The chosen lifts form a coherent family of legal stage branches. -/
def liftedBranches {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ) (x : C.FollowingPlay σ i) :
    C.plays.Limit := ⟨C.chosenBranches σ i x,C.chosenBranches_compatible σ i x⟩

theorem liftedBranches_seed {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ)
    (x : C.FollowingPlay σ i) : (C.liftedBranches σ i x).val i = x.val := by
  simpa only [Nat.add_zero,liftedBranches,followingTail] using C.chosenBranches_add σ i x 0

theorem liftedBranches_follows {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ)
    (x : C.FollowingPlay σ i) (j : ℕ) (hj : i ≤ j) :
    (C.tree j).Follows (C.strategy σ j) ((C.liftedBranches σ i x).val j) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hj
  change (C.tree (i+t)).Follows (C.strategy σ (i+t)) (C.chosenBranches σ i x (i+t))
  rw [C.chosenBranches_add]
  exact (C.followingTail σ i x t).property

/-- Prefixes of a coherent branch family are coherent finite levels. -/
def branchesLevel (x : C.plays.Limit) (n : ℕ) : C.StableLevel n := by
  refine ⟨fun i => (C.tree i).prefixLevel (x.val i) n, ?_⟩
  intro i
  change (C.covering i).nodeMap n ((C.tree (i+1)).prefixLevel (x.val (i+1)) n) = _
  rw [← (C.covering i).prefix_project]
  exact congrArg (fun y => (C.tree i).prefixLevel y n) (x.property i)

/-- Read the stabilized prefixes of a coherent branch family as one limit branch. -/
def ofBranches (x : C.plays.Limit) : C.limitTree.Play :=
  ⟨fun n i => (x.val i).val n,fun n => by
    refine ⟨n,C.branchesLevel x n, ?_⟩
    apply List.ext_getElem
    · simp only [seqPrefix_length,C.word_length]
    · intro j hj hj'
      funext i
      simp only [seqPrefix,word,List.getElem_ofFn,branchesLevel,prefixLevel,prefixPosition]⟩

@[simp] theorem project_ofBranches (x : C.plays.Limit) (i : ℕ) : C.project (C.ofBranches x) i = x.val i := by
  apply Subtype.ext
  rfl


/-- A play following a strategy realizes its chosen next position at every turn. -/
theorem follows_next_prefix {p : Bool} (i : ℕ) (τ : (C.tree i).Strategy p) (x : (C.tree i).Play)
    (hx : (C.tree i).Follows τ x) (n : ℕ) (hp : (n % 2 == 0) = p) :
    (C.tree i).prefixLevel x (n+1) = (C.tree i).nextLevel τ ((C.tree i).prefixLevel x n) hp := by
  apply Subtype.ext
  apply Subtype.ext
  change seqPrefix x.val (n+1) = seqPrefix x.val n ++ [_]
  rw [seqPrefix_succ_eq_concat]
  exact congrArg (fun a => seqPrefix x.val n ++ [a])
    (hx n (by simpa only [turn,seqPrefix_length] using hp))

/-- Following the stage strategies on a tail forces the limit branch to follow
its original strategy, since any prescribed next decision lies in a late controlled opening. -/
theorem ofBranches_follows {p : Bool} (σ : C.limitTree.Strategy p) (x : C.plays.Limit) (i : ℕ)
    (hx : ∀ j ≥ i, (C.tree j).Follows (C.strategy σ j) (x.val j)) :
    C.limitTree.Follows σ (C.ofBranches x) := by
  intro n hturn
  have hp : (n % 2 == 0) = p := by simpa only [turn,seqPrefix_length] using hturn
  let j := max i (n+1)
  have hij : i ≤ j := le_max_left _ _
  have hn : n < k+j := by dsimp [j]; omega
  have he : C.limitNodeMap j (n+1) (C.limitTree.prefixLevel (C.ofBranches x) (n+1)) =
      C.limitNodeMap j (n+1) (C.limitTree.nextLevel σ (C.limitTree.prefixLevel (C.ofBranches x) n) hp) := by
    rw [← C.limitNodeMap_prefix,C.strategy_initial σ j n hn,
      ← C.limitNodeMap_prefix,C.project_ofBranches]
    exact C.follows_next_prefix j (C.strategy σ j) (x.val j) (hx j hij) n hp
  have hnode := (C.limitNodeMap_bijective j (n+1) (by omega)).injective he
  have hw := congrArg (fun s => s.val.val) hnode
  simpa only [prefixLevel,prefixPosition,nextLevel,child,seqPrefix_succ_eq_concat,concat,
    List.append_cancel_left_eq,List.cons.injEq,and_true] using hw

/-- Lift any compatible stage play to a compatible limit play with exactly the prescribed projection. -/
theorem liftPlay {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ) (x : (C.tree i).Play)
    (hx : (C.tree i).Follows (C.strategy σ i) x) :
    ∃ y : C.limitTree.Play, C.limitTree.Follows σ y ∧ C.project y i = x := by
  let q : C.FollowingPlay σ i := ⟨x,hx⟩
  let b := C.liftedBranches σ i q
  refine ⟨C.ofBranches b,C.ofBranches_follows σ b i (C.liftedBranches_follows σ i q), ?_⟩
  rw [C.project_ofBranches]
  exact C.liftedBranches_seed σ i q

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    To verify the lifting axiom, let $x_i$ follow $\psi_i(\sigma)$. Recursively choose $x_{j+1}$ following
    $\psi_{j+1}(\sigma)$ with $\pi_{j+1}(x_{j+1})=x_j$, using
    $\varphi_{j+1}(\psi_{j+1}(\sigma))=\psi_j(\sigma)$ and the lifting axiom of the given covering.
    For each fixed prefix length, the prefixes of these branches agree under the level bijections
    once $j$ is sufficiently large.
    Their coherent families form a branch $x_\infty\in[T_\infty]$. Agreement of the strategy maps with the identity
    through the controlled levels shows that this branch follows $\sigma$, and the projection construction gives
    $\rho_i(x_\infty)=x_i$. The remaining locality and finite-level identities follow from the same stabilized
    prefixes. Thus the limit has the required $k+i$ control.
    \end{proof}
-/
/-- The inverse-limit tree, branch maps, and strategy maps form the controlled
coverings asserted in the book, at every stage simultaneously. -/
def limitCovering (i : ℕ) :
    letI : TopologicalSpace (∀ i, A i) := limitMoveTopology
    ControlledCovering C.limitTree (C.tree i) (k+i) := by
  letI : TopologicalSpace (∀ i, A i) := limitMoveTopology
  exact {
    project := fun x => C.project x i
    continuous_project := C.project_continuous i
    strategy := fun _ σ => C.strategy σ i
    lift := fun _ σ x hx => C.liftPlay σ i x hx
    nodeMap := C.limitNodeMap i
    prefix_project := fun x n => C.limitNodeMap_prefix x i n
    strategy_causal := fun _ n σ τ h => C.strategy_causal n h i
    initial_bijective := fun n hn => C.limitNodeMap_bijective i n hn
    initial_strategy := fun _ n hn σ s hp => C.strategy_initial σ i n hn s hp }

/-- The limit coverings commute with the original branch and strategy maps. -/
theorem limitCovering_commutes (i : ℕ) (p : Bool) (σ : C.limitTree.Strategy p) (x : C.limitTree.Play) :
    letI : TopologicalSpace (∀ i, A i) := limitMoveTopology
    (C.covering i).project ((C.limitCovering (i+1)).project x) = (C.limitCovering i).project x ∧
    (C.covering i).strategy p ((C.limitCovering (i+1)).strategy p σ) = (C.limitCovering i).strategy p σ :=
  ⟨C.project_commutes x i,C.strategy_commutes σ i⟩


/-@ booklink:
  source: polish-space-book/determinacy.md
  target: statement
  excerpt: |
    \begin{lemma*} Suppose $(T_{i+1},\pi_{i+1},\varphi_{i+1})$ is a $(k+i)$-covering of $T_i$ for every $i\in\omega$. Then
    there is a tree $T_\infty$ and, for each $i$, maps $\rho_i:[T_\infty]\to[T_i]$ and $\psi_i:S(T_\infty)\to S(T_i)$ such
    that $(T_\infty,\rho_i,\psi_i)$ is a $(k+i)$-covering of $T_i$, and the system commutes with the given coverings.
    
    \end{lemma*}
-/
/-- The inverse-limit covering family has every k+i control and both commuting diagrams. -/
theorem inverseLimitCoverings :
    letI : TopologicalSpace (∀ i, A i) := limitMoveTopology
    ∃ D : ∀ i, ControlledCovering C.limitTree (C.tree i) (k+i),
      (∀ i (x : C.limitTree.Play), (C.covering i).project ((D (i+1)).project x) = (D i).project x) ∧
      (∀ i p (σ : C.limitTree.Strategy p),
        (C.covering i).strategy p ((D (i+1)).strategy p σ) = (D i).strategy p σ) := by
  let : TopologicalSpace (∀ i, A i) := limitMoveTopology
  exact ⟨C.limitCovering,fun i x => C.project_commutes x i,fun i p σ => C.strategy_commutes σ i⟩


end PolishSpaceBook.TreeGames.GameTree.ControlledTower
