module

public import PolishSpaceBook.GameTreeInverseLevels

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Finite strategy decisions under controlled coverings

A next-position choice is the same as a legal move once its parent is fixed.
At controlled levels the node bijections therefore lift every legal decision.
This is the local inverse needed to stabilize restrictions of strategies.
-/
noncomputable section
namespace PolishSpaceBook.TreeGames.GameTree
open Set Function
universe u v
variable {M : Type u} {N : Type v}

/-- A length-n+1 extension of a position determines its last legal move. -/
theorem append_last_of_take (T : GameTree M) {n : ℕ} (s : T.Level n) (t : T.Level (n+1))
    (ht : T.takeLevel t n (Nat.le_succ n) = s) :
    s.val.val ++ [t.val.val[n]'(by rw [t.property]; omega)] = t.val.val := by
  have he := congrArg (fun z => z.val.val) ht
  change t.val.val.take n = s.val.val at he
  rw [← he, ← List.take_succ_eq_append_getElem (by rw [t.property]; omega)]
  exact List.take_of_length_le (by rw [t.property])

/-- Turn an extension node into the move that reaches it. -/
def moveOfNext (T : GameTree M) {n : ℕ} (s : T.Level n) (t : T.Level (n+1))
    (ht : T.takeLevel t n (Nat.le_succ n) = s) : T.LegalMove s.val :=
  ⟨t.val.val[n]'(by rw [t.property]; omega), by
    rw [T.append_last_of_take s t ht]
    exact t.val.property⟩

theorem child_moveOfNext (T : GameTree M) {n : ℕ} (s : T.Level n) (t : T.Level (n+1))
    (ht : T.takeLevel t n (Nat.le_succ n) = s) :
    T.child s.val (T.moveOfNext s t ht) = t.val := by
  apply Subtype.ext
  exact T.append_last_of_take s t ht

theorem nextNode_moveOfNext (T : GameTree M) {n : ℕ} (s : T.Level n) (t : T.Level (n+1))
    (ht : T.takeLevel t n (Nat.le_succ n) = s) :
    (⟨T.child s.val (T.moveOfNext s t ht),by simp [child,s.property]⟩ : T.Level (n+1)) = t :=
  Subtype.ext (T.child_moveOfNext s t ht)

/-- The next position of any legal move has its prescribed parent. -/
@[simp] theorem takeLevel_child (T : GameTree M) {n : ℕ} (s : T.Level n) (a : T.LegalMove s.val) :
    T.takeLevel ⟨T.child s.val a,by simp [child,s.property]⟩ n (Nat.le_succ n) = s := by
  apply Subtype.ext
  apply Subtype.ext
  change (s.val.val ++ [a.val]).take n = s.val.val
  conv_lhs => arg 1; rw [← s.property]
  simp

@[simp] theorem takeLevel_nextLevel (T : GameTree M) {p : Bool} (σ : T.Strategy p)
    {n : ℕ} (s : T.Level n) (hp : (n % 2 == 0) = p) :
    T.takeLevel (T.nextLevel σ s hp) n (Nat.le_succ n) = s :=
  T.takeLevel_child s _

/-- Strategies are identified exactly when their decisions before n agree. -/
def strategySetoid (T : GameTree M) (p : Bool) (n : ℕ) : Setoid (T.Strategy p) where
  r := T.StrategyAgree n
  iseqv := ⟨fun _ _ _ _ => rfl,
    fun h s hp hs => (h s hp hs).symm,
    fun h₁ h₂ s hp hs => (h₁ s hp hs).trans (h₂ s hp hs)⟩

/-- A finite strategy restriction, retaining its player and depth. -/
abbrev FiniteStrategy (T : GameTree M) (p : Bool) (n : ℕ) := Quotient (T.strategySetoid p n)

def finiteStrategy (T : GameTree M) {p : Bool} (σ : T.Strategy p) (n : ℕ) : T.FiniteStrategy p n :=
  Quotient.mk _ σ

/-- Forget decisions outside a shorter opening. -/
def finiteRestrict (T : GameTree M) {p : Bool} {n m : ℕ} (hm : m ≤ n) :
    T.FiniteStrategy p n → T.FiniteStrategy p m :=
  Quotient.map id (fun _ _ h s hp hs => h s hp (hs.trans_le hm))


/-- Realize coherent finite restrictions by consulting the restriction that
includes the current decision. -/
def realizeFinite (T : GameTree M) {p : Bool} (a : ∀ n, T.FiniteStrategy p n) : T.Strategy p :=
  fun s hp => (Quotient.out (a (s.val.length+1))) s hp

/-- Compatible restrictions determine an actual strategy with exactly those restrictions. -/
theorem finiteStrategy_realize (T : GameTree M) {p : Bool} (a : ∀ n, T.FiniteStrategy p n)
    (ha : ∀ m n (hm : m ≤ n), T.finiteRestrict hm (a n) = a m) (n : ℕ) :
    T.finiteStrategy (T.realizeFinite a) n = a n := by
  have hout : T.finiteStrategy (Quotient.out (a n)) n = a n := Quotient.out_eq _
  rw [← hout]
  apply Quotient.sound
  intro s hp hs
  let m := s.val.length+1
  have hm : m ≤ n := by dsimp [m]; omega
  have he : T.finiteStrategy (Quotient.out (a n)) m = T.finiteStrategy (Quotient.out (a m)) m := by
    calc
      _ = T.finiteRestrict hm (a n) := by
        conv_rhs => rw [← hout]
        rfl
      _ = a m := ha m n hm
      _ = _ := (Quotient.out_eq _).symm
  exact ((Quotient.exact he) s hp (by dsimp [m]; omega)).symm

/-- Agreement at every finite depth is equality of full legal strategies. -/
theorem strategy_ext_finite (T : GameTree M) {p : Bool} {σ τ : T.Strategy p}
    (h : ∀ n, T.finiteStrategy σ n = T.finiteStrategy τ n) : σ = τ := by
  funext s hp
  apply Subtype.ext
  exact (Quotient.exact (h (s.val.length+1))) s hp (Nat.lt_succ_self _)


section Topological
variable [TopologicalSpace M] [TopologicalSpace N]
variable {S : GameTree N} {T : GameTree M} {k n : ℕ}
namespace ControlledCovering

/-- The unique inverse image of a next position at a controlled level. -/
def inverseNext (C : ControlledCovering S T k) (hn : n < k) (s : S.Level n)
    (t : T.Level (n+1)) (_ht : T.takeLevel t n (Nat.le_succ n) = C.nodeMap n s) : S.Level (n+1) :=
  (Equiv.ofBijective (C.nodeMap (n+1)) (C.initial_bijective (n+1) (by omega))).symm t

@[simp] theorem map_inverseNext (C : ControlledCovering S T k) (hn : n < k) (s : S.Level n)
    (t : T.Level (n+1)) (ht : T.takeLevel t n (Nat.le_succ n) = C.nodeMap n s) :
    C.nodeMap (n+1) (C.inverseNext hn s t ht) = t :=
  (Equiv.ofBijective (C.nodeMap (n+1)) (C.initial_bijective (n+1) (by omega))).apply_symm_apply t

/-- Prefix compatibility forces the inverse next position to have the right parent. -/
theorem take_inverseNext (C : ControlledCovering S T k) (hn : n < k) (s : S.Level n)
    (t : T.Level (n+1)) (ht : T.takeLevel t n (Nat.le_succ n) = C.nodeMap n s) :
    S.takeLevel (C.inverseNext hn s t ht) n (Nat.le_succ n) = s := by
  apply (C.initial_bijective n (by omega)).injective
  rw [← C.nodeMap_take,C.map_inverseNext]
  exact ht

/-- Every legal move downstairs has a uniquely determined legal lift in the preserved opening. -/
def liftMove (C : ControlledCovering S T k) (hn : n < k) (s : S.Level n)
    (a : T.LegalMove (C.nodeMap n s).val) : S.LegalMove s.val := by
  let t : T.Level (n+1) := ⟨T.child (C.nodeMap n s).val a,by simp [child,(C.nodeMap n s).property]⟩
  have ht : T.takeLevel t n (Nat.le_succ n) = C.nodeMap n s := T.takeLevel_child _ _
  exact S.moveOfNext s (C.inverseNext hn s t ht) (C.take_inverseNext hn s t ht)

/-- The lifted decision projects back to the original next position. -/
theorem liftMove_projects (C : ControlledCovering S T k) (hn : n < k) (s : S.Level n)
    (a : T.LegalMove (C.nodeMap n s).val) :
    C.nodeMap (n+1) ⟨S.child s.val (C.liftMove hn s a),by simp [child,s.property]⟩ =
      ⟨T.child (C.nodeMap n s).val a,by simp [child,(C.nodeMap n s).property]⟩ := by
  unfold liftMove
  rw [S.nextNode_moveOfNext]
  exact C.map_inverseNext _ _ _ _

/-- Lift a target strategy through the preserved opening, using arbitrary legal
moves after that opening. No inverse to the covering's global strategy map is asserted. -/
def liftStrategy (C : ControlledCovering S T k) {p : Bool} (τ : T.Strategy p) : S.Strategy p :=
  fun s hp => if hn : s.val.length < k then
    let sl : S.Level s.val.length := ⟨s,rfl⟩
    let tl := C.nodeMap s.val.length sl
    C.liftMove hn sl (τ tl.val (by simpa only [turn,tl.property] using hp))
  else S.defaultStrategy p s hp

/-- Each lifted decision realizes the original target decision under the node map. -/
theorem liftStrategy_projects (C : ControlledCovering S T k) {p : Bool} (τ : T.Strategy p)
    (hn : n < k) (s : S.Level n) (hp : (n % 2 == 0) = p) :
    C.nodeMap (n+1) (S.nextLevel (C.liftStrategy τ) s hp) =
      T.nextLevel τ (C.nodeMap n s) hp := by
  rcases s with ⟨s,rfl⟩
  simpa only [nextLevel,liftStrategy,dite_eq_left hn] using
    C.liftMove_projects hn ⟨s,rfl⟩
      (τ (C.nodeMap s.val.length ⟨s,rfl⟩).val
        (by simpa only [turn,(C.nodeMap s.val.length ⟨s,rfl⟩).property] using hp))

/-- The covering strategy map recovers every target strategy on the preserved opening. -/
theorem strategy_lift_agrees (C : ControlledCovering S T k) {p : Bool} (τ : T.Strategy p) :
    T.StrategyAgree k (C.strategy p (C.liftStrategy τ)) τ := by
  intro t hpt hlen
  obtain ⟨s,hs⟩ := (C.initial_bijective t.val.length hlen.le).surjective ⟨t,rfl⟩
  have hp : (t.val.length % 2 == 0) = p := hpt
  have he := C.initial_strategy p t.val.length hlen (C.liftStrategy τ) s hp
  rw [C.liftStrategy_projects τ hlen s hp,hs] at he
  have hw := congrArg (fun z => z.val.val) he
  simpa only [nextLevel,child,List.append_cancel_left_eq,List.cons.injEq,and_true] using hw.symm

/-- On controlled finite restrictions, strategy transport is injective. -/
theorem strategy_agree_iff (C : ControlledCovering S T k) {p : Bool} (hn : n ≤ k)
    (σ τ : S.Strategy p) :
    T.StrategyAgree n (C.strategy p σ) (C.strategy p τ) ↔ S.StrategyAgree n σ τ := by
  refine ⟨?_,C.strategy_causal p n σ τ⟩
  intro h s hp hlen
  let sl : S.Level s.val.length := ⟨s,rfl⟩
  let tl := C.nodeMap s.val.length sl
  have hpt : turn tl.val.val = p := by simpa only [turn,tl.property] using hp
  have hmove := h tl.val hpt (by simpa only [tl.property] using hlen)
  have hnext : T.nextLevel (C.strategy p σ) tl hp = T.nextLevel (C.strategy p τ) tl hp := by
    apply Subtype.ext
    apply Subtype.ext
    change tl.val.val ++ [(C.strategy p σ tl.val hpt).val] =
      tl.val.val ++ [(C.strategy p τ tl.val hpt).val]
    rw [hmove]
  have he : C.nodeMap (s.val.length+1) (S.nextLevel σ sl hp) =
      C.nodeMap (s.val.length+1) (S.nextLevel τ sl hp) := by
    rw [C.initial_strategy p _ (hlen.trans_le hn),C.initial_strategy p _ (hlen.trans_le hn)]
    exact hnext
  have hs := (C.initial_bijective (s.val.length+1) (by omega)).injective he
  have hw := congrArg (fun z => z.val.val) hs
  simpa only [nextLevel,child,List.append_cancel_left_eq,List.cons.injEq,and_true] using hw

/-- Causality makes strategy transport well-defined on each finite restriction. -/
def finiteStrategyMap (C : ControlledCovering S T k) (p : Bool) (n : ℕ) :
    S.FiniteStrategy p n → T.FiniteStrategy p n :=
  Quotient.map (C.strategy p) (C.strategy_causal p n)

/-- At every controlled depth the induced map of finite strategies is bijective. -/
theorem finiteStrategyMap_bijective (C : ControlledCovering S T k) (p : Bool) (hn : n ≤ k) :
    Function.Bijective (C.finiteStrategyMap p n) := by
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y (fun σ τ h => ?_)
    exact Quotient.sound ((C.strategy_agree_iff hn σ τ).mp (Quotient.exact h))
  · intro y
    refine Quotient.inductionOn y (fun τ => ?_)
    refine ⟨S.finiteStrategy (C.liftStrategy τ) n, Quotient.sound ?_⟩
    intro t hp ht
    exact C.strategy_lift_agrees τ t hp (ht.trans_le hn)

/-- Restriction and the causal strategy map commute. -/
theorem finiteStrategyMap_restrict (C : ControlledCovering S T k) (p : Bool) {m : ℕ}
    (hm : m ≤ n) (σ : S.FiniteStrategy p n) :
    T.finiteRestrict hm (C.finiteStrategyMap p n σ) = C.finiteStrategyMap p m (S.finiteRestrict hm σ) := by
  refine Quotient.inductionOn σ (fun τ => ?_)
  rfl

end ControlledCovering
end Topological
end PolishSpaceBook.TreeGames.GameTree
