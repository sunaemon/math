module

public import PolishSpaceBook.GameTreeInverseBranches
public import PolishSpaceBook.GameTreeFiniteStrategies

@[expose] public section

/-! # Finite strategy restrictions in a controlled covering tower

Causality induces bonding maps on finite restrictions. Once the preserved
opening includes the prescribed depth, these maps are bijective. Their inverse
limits implement the same stabilization as the finite-node construction.
-/
noncomputable section
namespace PolishSpaceBook.TreeGames.GameTree.ControlledTower
open Set Function
universe u
variable {A : ℕ → Type u} [∀ i, TopologicalSpace (A i)] {k : ℕ}
variable (C : ControlledTower A k)


/-- The limit's level maps preserve taking shorter prefixes. -/
theorem limitNodeMap_take (i : ℕ) {n : ℕ} (s : C.limitTree.Level n) (m : ℕ) (hm : m ≤ n) :
    (C.tree i).takeLevel (C.limitNodeMap i n s) m hm =
      C.limitNodeMap i m (C.limitTree.takeLevel s m hm) := by
  obtain ⟨x,hx⟩ := (C.limitTree.position_iff_prefix_play s.val.val).mp s.val.property
  have he : C.limitTree.prefixLevel x n = s := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [prefixLevel,prefixPosition,s.property] using seqPrefix_eq_of_mem_cyl hx
  rw [← he, ← C.limitNodeMap_prefix, takeLevel_prefix, takeLevel_prefix, C.limitNodeMap_prefix]

/-- Copy the limit strategy down the bijective opening of stage i and use a
legal default afterwards. These are finite approximations, not the final stage strategies. -/
def stageApproximation {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ) : (C.tree i).Strategy p :=
  fun t hp => if ht : t.val.length < k+i then
    let tl : (C.tree i).Level t.val.length := ⟨t,rfl⟩
    let e := Equiv.ofBijective (C.limitNodeMap i t.val.length)
      (C.limitNodeMap_bijective i t.val.length ht.le)
    let sl := e.symm tl
    let hps : (t.val.length % 2 == 0) = p := hp
    (C.tree i).moveOfNext tl (C.limitNodeMap i (t.val.length+1) (C.limitTree.nextLevel σ sl hps)) (by
      rw [C.limitNodeMap_take,takeLevel_nextLevel]
      exact e.apply_symm_apply tl)
  else (C.tree i).defaultStrategy p t hp

/-- At a position in the controlled opening, the approximation is the image of
exactly the limit strategy's next position. -/
theorem stageApproximation_next {p : Bool} (σ : C.limitTree.Strategy p) (i n : ℕ)
    (hn : n < k+i) (s : C.limitTree.Level n) (hp : (n % 2 == 0) = p) :
    (C.tree i).nextLevel (C.stageApproximation σ i) (C.limitNodeMap i n s) hp =
      C.limitNodeMap i (n+1) (C.limitTree.nextLevel σ s hp) := by
  generalize he : C.limitNodeMap i n s = t
  rcases t with ⟨t,ht⟩
  subst n
  have hinv : (Equiv.ofBijective (C.limitNodeMap i t.val.length)
      (C.limitNodeMap_bijective i t.val.length hn.le)).symm ⟨t,rfl⟩ = s := by
    rw [← he]
    exact Equiv.symm_apply_apply _ s
  let sl := (Equiv.ofBijective (C.limitNodeMap i t.val.length)
    (C.limitNodeMap_bijective i t.val.length hn.le)).symm ⟨t,rfl⟩
  let v := C.limitNodeMap i (t.val.length+1) (C.limitTree.nextLevel σ sl hp)
  have hparent : (C.tree i).takeLevel v t.val.length (Nat.le_succ _) = ⟨t,rfl⟩ := by
    rw [C.limitNodeMap_take,takeLevel_nextLevel]
    exact (Equiv.ofBijective (C.limitNodeMap i t.val.length)
      (C.limitNodeMap_bijective i t.val.length hn.le)).apply_symm_apply ⟨t,rfl⟩
  have hdecision : (C.stageApproximation σ i) t hp = (C.tree i).moveOfNext ⟨t,rfl⟩ v hparent := by
    simp only [stageApproximation,dite_eq_left hn]
    rfl
  have houter : (C.tree i).nextLevel (C.stageApproximation σ i) ⟨t,rfl⟩ hp =
      (⟨(C.tree i).child t ((C.tree i).moveOfNext ⟨t,rfl⟩ v hparent),
        by simp [child]⟩ : (C.tree i).Level (t.val.length+1)) := by
    apply Subtype.ext
    exact congrArg ((C.tree i).child t) hdecision
  exact houter.trans (((C.tree i).nextNode_moveOfNext ⟨t,rfl⟩ v hparent).trans
    (congrArg (fun q => C.limitNodeMap i (t.val.length+1) (C.limitTree.nextLevel σ q hp)) hinv))


/-- Coherent node families commute with the given bonding prefix maps. -/
theorem limitNodeMap_commutes (i n : ℕ) (s : C.limitTree.Level n) :
    (C.covering i).nodeMap n (C.limitNodeMap (i+1) n s) = C.limitNodeMap i n s :=
  (C.nodeEquiv n s).property i

/-- Adjacent finite approximations agree after the actual covering strategy map,
through any opening already controlled by the earlier stage. -/
theorem stageApproximation_compatible {p : Bool} (σ : C.limitTree.Strategy p)
    (i n : ℕ) (hn : n ≤ k+i) :
    (C.tree i).StrategyAgree n ((C.covering i).strategy p (C.stageApproximation σ (i+1)))
      (C.stageApproximation σ i) := by
  intro t hpt hlen
  have hbound : t.val.length < k+i := hlen.trans_le hn
  obtain ⟨s,hs⟩ := (C.limitNodeMap_bijective i t.val.length hbound.le).surjective ⟨t,rfl⟩
  have hp : (t.val.length % 2 == 0) = p := hpt
  have he := (C.covering i).initial_strategy p t.val.length hbound
    (C.stageApproximation σ (i+1)) (C.limitNodeMap (i+1) t.val.length s) hp
  rw [C.stageApproximation_next σ (i+1) _ (by omega) s hp,
    C.limitNodeMap_commutes,C.limitNodeMap_commutes] at he
  have heq := he.symm.trans (C.stageApproximation_next σ i _ hbound s hp).symm
  rw [hs] at heq
  have hw := congrArg (fun z => z.val.val) heq
  simpa only [nextLevel,child,List.append_cancel_left_eq,List.cons.injEq,and_true] using hw


/-- A stable approximation uses only the matching finite restriction of the limit strategy. -/
theorem stageApproximation_agrees {p : Bool} {σ τ : C.limitTree.Strategy p} {n : ℕ}
    (h : C.limitTree.StrategyAgree n σ τ) (i : ℕ) (hn : n ≤ k+i) :
    (C.tree i).StrategyAgree n (C.stageApproximation σ i) (C.stageApproximation τ i) := by
  intro t hpt hlen
  have hbound : t.val.length < k+i := hlen.trans_le hn
  obtain ⟨s,hs⟩ := (C.limitNodeMap_bijective i t.val.length hbound.le).surjective ⟨t,rfl⟩
  have hp : (t.val.length % 2 == 0) = p := hpt
  have hps : turn s.val.val = p := by simpa only [turn,s.property] using hp
  have hmove := h s.val hps (by simpa only [s.property] using hlen)
  have hnext : C.limitTree.nextLevel σ s hp = C.limitTree.nextLevel τ s hp := by
    apply Subtype.ext
    apply Subtype.ext
    change s.val.val ++ [(σ s.val hps).val] = s.val.val ++ [(τ s.val hps).val]
    rw [hmove]
  have he := (C.stageApproximation_next σ i _ hbound s hp).trans
    ((congrArg (C.limitNodeMap i (t.val.length+1)) hnext).trans
      (C.stageApproximation_next τ i _ hbound s hp).symm)
  rw [hs] at he
  have hw := congrArg (fun z => z.val.val) he
  simpa only [nextLevel,child,List.append_cancel_left_eq,List.cons.injEq,and_true] using hw

/-- The inverse system of depth-n restrictions for one fixed player. -/
@[reducible] def strategyLevels (p : Bool) (n : ℕ) : NatInverseSystem where
  Obj i := (C.tree i).FiniteStrategy p n
  step i := (C.covering i).finiteStrategyMap p n

/-- After a sufficiently late stage every finite strategy map is bijective. -/
theorem strategyLevels_eventually_bijective (p : Bool) (n j : ℕ) (hj : n ≤ k+j) :
    ∀ i ≥ j, Function.Bijective ((C.strategyLevels p n).step i) := by
  intro i hi
  exact (C.covering i).finiteStrategyMap_bijective p (by omega)

/-- A stable restriction determines one compatible family of finite strategies. -/
theorem strategy_evaluation_bijective (p : Bool) (n j : ℕ) (hj : n ≤ k+j) :
    Function.Bijective (fun σ : (C.strategyLevels p n).Limit => σ.val j) :=
  NatInverseSystem.evaluation_bijective (C.strategyLevels_eventually_bijective p n j hj)

/-- Restricting the depth of an entire compatible family preserves its bonding equations. -/
def restrictStrategies (p : Bool) {n m : ℕ} (hm : m ≤ n)
    (σ : (C.strategyLevels p n).Limit) : (C.strategyLevels p m).Limit := by
  refine ⟨fun i => (C.tree i).finiteRestrict hm (σ.val i), ?_⟩
  intro i
  change (C.covering i).finiteStrategyMap p m ((C.tree (i+1)).finiteRestrict hm (σ.val (i+1))) =
    (C.tree i).finiteRestrict hm (σ.val i)
  rw [← ControlledCovering.finiteStrategyMap_restrict]
  exact congrArg ((C.tree i).finiteRestrict hm) (σ.property i)

/-- Stabilize a depth-n approximation from stage n in both directions along the tower. -/
def finiteLimit {p : Bool} (σ : C.limitTree.Strategy p) (n : ℕ) : (C.strategyLevels p n).Limit :=
  NatInverseSystem.lift (C.strategyLevels_eventually_bijective p n n (by omega))
    ((C.tree n).finiteStrategy (C.stageApproximation σ n) n)

/-- Every later stable coordinate is the corresponding concrete finite approximation. -/
theorem finiteLimit_at_late {p : Bool} (σ : C.limitTree.Strategy p) (n j : ℕ) (hj : n ≤ j) :
    (C.finiteLimit σ n).val j = (C.tree j).finiteStrategy (C.stageApproximation σ j) n := by
  induction j, hj using Nat.le_induction with
  | base => exact NatInverseSystem.lift_at _ _
  | succ j hj ih =>
    apply ((C.covering j).finiteStrategyMap_bijective p (show n ≤ k+j by omega)).injective
    have hbond : (C.covering j).finiteStrategyMap p n ((C.finiteLimit σ n).val (j+1)) =
        (C.finiteLimit σ n).val j := (C.finiteLimit σ n).property j
    rw [hbond,ih]
    exact (Quotient.sound (C.stageApproximation_compatible σ j n (by omega))).symm

/-- Stabilization is compatible with shortening the opening. -/
theorem finiteLimit_restrict {p : Bool} (σ : C.limitTree.Strategy p) {n m : ℕ} (hm : m ≤ n) :
    C.restrictStrategies p hm (C.finiteLimit σ n) = C.finiteLimit σ m := by
  apply NatInverseSystem.limit_ext (C.strategyLevels_eventually_bijective p m n (by omega))
  change (C.tree n).finiteRestrict hm ((C.finiteLimit σ n).val n) = (C.finiteLimit σ m).val n
  rw [C.finiteLimit_at_late σ n n le_rfl,C.finiteLimit_at_late σ m n hm]
  rfl

/-- Realize at stage i all of the stabilized finite restrictions of one limit strategy. -/
def strategy {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ) : (C.tree i).Strategy p :=
  (C.tree i).realizeFinite (fun n => (C.finiteLimit σ n).val i)

theorem strategy_finite {p : Bool} (σ : C.limitTree.Strategy p) (i n : ℕ) :
    (C.tree i).finiteStrategy (C.strategy σ i) n = (C.finiteLimit σ n).val i := by
  apply (C.tree i).finiteStrategy_realize
  intro m n hm
  exact congrArg (fun t => t.val i) (C.finiteLimit_restrict σ hm)

/-- A stage strategy's finite restriction is the finite composite of any
sufficiently late approximation, exactly as in the book's construction. -/
theorem strategy_finite_from_late {p : Bool} (σ : C.limitTree.Strategy p) (i n j : ℕ)
    (hn : n ≤ j) (hi : i ≤ j) :
    (C.tree i).finiteStrategy (C.strategy σ i) n =
      (C.strategyLevels p n).down j ((C.tree j).finiteStrategy (C.stageApproximation σ j) n) i hi := by
  rw [C.strategy_finite, ← C.finiteLimit_at_late σ n j hn]
  exact ((C.strategyLevels p n).down_eq (C.finiteLimit σ n) j i hi).symm

/-@ booklink:
  source: polish-space-book/determinacy.md
  target: prose
  excerpt: |
    For a strategy $\sigma$ on $T_\infty$, define $\psi_i(\sigma)$ on positions of length $<k+j$ by applying the finite
    composite of the strategy maps from level $j$ down to level $i$. To supply a full strategy at stage $j$, extend the
    transported finite restriction by arbitrary legal moves beyond its opening. Causality makes the finite result
    independent of this extension. The locality condition for $(k+j)$-coverings makes it independent of all larger $j$.
    These compatible finite restrictions determine a full strategy $\psi_i(\sigma)$ for the same player as $\sigma$;
    the strategy maps commute with the given coverings, and agreement on any finite opening is preserved.
-/
/-- The full stage strategy maps commute, because their finite restrictions do. -/
theorem strategy_commutes {p : Bool} (σ : C.limitTree.Strategy p) (i : ℕ) :
    (C.covering i).strategy p (C.strategy σ (i+1)) = C.strategy σ i := by
  apply (C.tree i).strategy_ext_finite
  intro n
  change (C.covering i).finiteStrategyMap p n
    ((C.tree (i+1)).finiteStrategy (C.strategy σ (i+1)) n) = _
  rw [C.strategy_finite,C.strategy_finite]
  exact (C.finiteLimit σ n).property i


/-- The stabilized strategy map remains causal at every finite depth. -/
theorem strategy_causal {p : Bool} {σ τ : C.limitTree.Strategy p} (n : ℕ)
    (h : C.limitTree.StrategyAgree n σ τ) (i : ℕ) :
    (C.tree i).StrategyAgree n (C.strategy σ i) (C.strategy τ i) := by
  have he : C.finiteLimit σ n = C.finiteLimit τ n := by
    apply NatInverseSystem.limit_ext (C.strategyLevels_eventually_bijective p n n (by omega))
    rw [C.finiteLimit_at_late σ n n le_rfl,C.finiteLimit_at_late τ n n le_rfl]
    exact Quotient.sound (C.stageApproximation_agrees h n (by omega))
  have hi := congrArg (fun q => q.val i) he
  rw [← C.strategy_finite σ i n, ← C.strategy_finite τ i n] at hi
  exact Quotient.exact hi


end PolishSpaceBook.TreeGames.GameTree.ControlledTower
