module

/-
Modified for the math-private book: ported Sven Manthe's formalization to Lean 4.35.0
and its mathlib. See README.md and UPSTREAM.json in the vendor root for provenance;
the original Apache-2.0 license is retained in LICENSE.
-/

public import BorelDet.Proof.Zero.tree_lift

@[expose] public section

namespace GaleStewartGame.BorelDet.Zero
open Stream'.Discrete Descriptive Tree Game PreStrategy Covering
open Classical CategoryTheory

variable {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} {m n : ℕ}

noncomputable section

variable {R : Strategy (gameAsTrees hyp).2 Player.zero} (y : body (stratMap' R).pre.subtree)
@[simps] def bodyTake (n : ℕ) : TreeLift hyp where
  R := R
  x := body.take (2 * k + 2 + n) y
  hlvl := by simp; omega
@[simp] lemma bodyTake_take (h : 2 * k + 2 ≤ m) :
  (bodyTake y n).take m (by omega) = bodyTake y (min (m - (2 * k + 2)) n) := by
  ext1 <;> simp; congr; omega
@[simps!] def takeLift (n : ℕ) := (bodyTake y n).lift (by simp)
attribute [simp_lengths] bodyTake_x takeLift_x_coe
@[simp] lemma takeLift_mono : takeLift y m ≤ takeLift y n ↔ m ≤ n := by
  constructor <;> intro h
  · simpa using PreLift.length_mono h
  · ext1
    · ext1; simp [h]
    · rfl
@[simp] lemma takeLift_game : (takeLift y n).game = (takeLift y 0).game := by
  have h := Lift.eq_take_of_le <| (takeLift_mono y).mpr (Nat.zero_le n)
  rw [← h, Lift.take_toPreLift, PreLift.game_take]
lemma losable_of_losable_not_lost n (hL : (takeLift y n).Losable)
  (h' : ∀ m, ¬ (takeLift y m).Lost) m (hm : hL.2.num ≤ m + 1) : (takeLift y m).Losable := by
  have hc m : (takeLift y m).ConLong := by
    have := (bodyTake y m).conLong_or_lost; tauto
  use hc m; by_cases hW : WinningPrefix (takeLift y m).game Player.one
    ((body.take (2 * k + 2 + m) y).val.drop (2 * k + 1))
  · exact hW
  · have : hL.2.num ≤ n + 1 := by
      have := hL.2.num_le_length; simp at this
      rw [hL.2.prefix_num List.prefix_rfl (by simp) rfl] at this; omega
    have hW : (takeLift y m).Winnable := hW
    replace hW := hW.take (2 * k + 1 + max 1 hL.2.num) (by omega)
    replace hL := hL.take (n := 1 - hL.2.num) (by omega)
    simp_rw [takeLift] at hW hL
    rw [← TreeLift.lift_take _ (by omega) (by simp; omega)] at hW hL
    simp (disch := omega) only [bodyTake_take, min_eq_left] at hW hL
    cases hW (by convert hL.2 using 6; omega; congr! 1; omega)
set_option maxHeartbeats 800000 in
lemma body_lost_of_losable n (h : (takeLift y n).Losable) (h' : ∀ m, ¬ (takeLift y m).Lost) :
  ⟨y.val, body_mono (subtree_sub _) y.prop⟩ ∉ G.payoff := by
  have hL := losable_of_losable_not_lost y n h h'
  have hb : (body.drop (2 * k + 1 + h.2.num) y).val ∈ body h.2.strat.pre.subtree := by
    apply mem_body_of_take (n + 1); intro m hm
    let M := h.2.num + m - 1
    have hLM := hL M (by dsimp [M]; omega)
    have hpref : (takeLift y n).x.val.drop (2 * k + 1) <+:
        (takeLift y M).x.val.drop (2 * k + 1) := by
      apply List.IsPrefix.drop
      change y.val.take (2 * k + 2 + n) <+: y.val.take (2 * k + 2 + M)
      apply (Stream'.take_prefix _ _ _).mpr
      dsimp [M]; omega
    have hg : (takeLift y n).game = (takeLift y M).game := (takeLift_game (n := n) y).trans (takeLift_game (n := M) y).symm
    have hn : hLM.2.num = h.2.num := h.2.prefix_num hpref hg rfl
    have hs : hLM.2.strat.pre.subtree = h.2.strat.pre.subtree :=
      h.2.prefix_strat_subtree hpref hg rfl
    have ht := (bodyTake y M).losable_subtree (h := by simp) hLM (by
      simp only [TreeLift.dropLast, bodyTake_x,
        body.take_coe, Stream'.length_take, Nat.succ_add_sub_one, TreeLift.take_x,
        take_coe, Stream'.take_take, not_exists]
      intro hlen; simp at hlen; simp_rw [bodyTake_take y hlen]; apply h')
    change (y.val.take (2 * k + 2 + M)).drop (2 * k + 1 + hLM.2.num) ∈
      hLM.2.strat.pre.subtree at ht
    rw [hs] at ht
    rw [hn] at ht
    have hlen : 2 * k + 2 + M = 2 * k + 1 + h.2.num + m := by dsimp [M]; omega
    simpa only [hlen, body.drop_coe, Stream'.take_drop] using ht
  have hw := h.2.strat_winning hb
  generalize_proofs at hw
  simp only [takeLift_game, takeLift_x_coe, Player.payoff_residual,
    Player.residual_residual, List.length_append, List.length_take, List.length_drop, Stream'.length_take,
    div_add_self, Player.residual_even, Player.payoff_one, Set.preimage_compl] at hw
  simp only [Set.image_val_compl] at hw --simp only slow from here
  simp only [takeLift_game,
    body.drop_coe, Set.mem_sdiff, Set.mem_preimage, Set.mem_image,
    Subtype.exists, exists_and_right, exists_eq_right, not_exists] at hw
  replace hw := hw.2; simp [PreLift.game_payoff, Nat.add_mod] at hw
  generalize_proofs pf at hw
  have : ((y.val.take (2 * k + 2 + n)).drop (2 * k + 1)).take pf.num
    ++ₛ y.val.drop (2 * k + 1 + pf.num) = y.val.drop (2 * k + 1) := by
    have hnat : 2 * k + 2 + n = (2 * k + 1) + (1 + n) := by omega
    rw [← Stream'.drop_drop]
    conv => lhs; lhs; rhs; rw [hnat, ← Stream'.take_drop]
    rw [Stream'.take_take]
    have : pf.num ≤ 1 + n := by
      have := h.2.num_le_length; simp_rw [takeLift_game] at this; synth_isPosition
    simp [this, - Stream'.drop_drop]
  have htail : y.val.drop (2 * k + 1) ∈ body (takeLift y 0).game.tree := by
    apply mem_body_of_take (h.2.num + 1); intro j hj
    have hc := (hL (j - 1) (by omega)).1
    change (takeLift y (j - 1)).x.val.drop (2 * k + 1) ∈ (takeLift y (j - 1)).game.tree at hc
    rw [takeLift_game] at hc
    have hj' : 2 * k + 2 + (j - 1) = 2 * k + 1 + j := by omega
    simpa only [takeLift_x_coe, hj', Stream'.take_drop] using hc
  have hnot := hw (by rw [this]; exact htail)
    (by rw [this, Stream'.append_take_drop]; exact body_mono (subtree_sub _) y.prop)
  intro hy
  apply hnot
  convert hy using 1
  apply Subtype.ext
  change (takeLift y 0).x.val.take (2 * k + 1) ++ₛ _ = y.val
  dsimp only
  rw [this]
  simp [takeLift_x_coe]

lemma lost_of_body_lost (hy : ⟨y.val, body_mono (subtree_sub _) y.prop⟩ ∉ G.payoff) :
  ∃ m, (takeLift y m).Lost := by
  rw [← Subtype.val_injective.mem_set_image,
    ← (isClosed_image_payoff.mp hyp.closed).closure_eq,
    mem_closure_iff_nhds_basis (hasBasis_principalOpen y.val)] at hy
  simp at hy; obtain ⟨x, hx1, hx2⟩ := hy; use x.length
  apply TreeLift.lost_of_lost'; unfold Lift.Lost'
  rw [wonPosition_iff_disjoint, ← Set.subset_empty_iff]
  intro z ⟨h1, h2⟩; simp at h1 h2; apply hx2 z
  · exact h2.2
  · apply principalOpen_mono _ h1
    rw [principalOpen_iff_restrict] at hx1; rw [hx1]; simp
  · exact h2.1
lemma lost_of_losable n (h : (takeLift y n).Losable) : ∃ m, (takeLift y m).Lost := by
  by_cases h' : ∃ m, (takeLift y m).Lost; exact h'
  exact lost_of_body_lost y (body_lost_of_losable y n h (by push Not at h'; exact h'))

def wonLift (h : ∀ n, (takeLift y n).Winnable) : body R.pre.subtree :=
  bodyEquivSystem.inv.app ⟨_, R.pre.subtree⟩ ⟨fun k ↦
  ⟨(h k).toWLift'.liftVal.take k, ⟨take_mem ⟨_, (bodyTake y k).wLift_mem_tree _ _⟩, by
    simp⟩⟩, fun k ↦
    ((Lift.wLift_liftVal_mono ((takeLift_mono y).mpr (Nat.le_succ _))).take k).trans (by simp)⟩
lemma wonLift_map h :
  (bodyFunctor.map π ⟨(wonLift y h).val, body_mono R.pre.subtree_sub (wonLift y h).prop⟩).val
  = y.val := by ext; simp [wonLift, bodyEquivSystem, bodyEquivSystem_app, Stream'.get, Stream'.map]
def lostLift (h : (takeLift y n).Lost) : body R.pre.subtree :=
  have h' k : (takeLift y (n + k)).Lost := h.lost_of_le ((takeLift_mono y).mpr (by omega))
  bodyEquivSystem.inv.app ⟨_, R.pre.subtree⟩ ⟨fun k ↦
  ⟨(h' k).toLLift'.liftVal.take k, ⟨take_mem ⟨_, (bodyTake y (n + k)).lLift_mem_tree _ _⟩, by
    simp; omega⟩⟩, fun k ↦
    ((Lift.lLift_liftVal_mono (h' k).1 ((takeLift_mono y).mpr (Nat.le_succ _))).take k).trans (by simp)⟩
lemma lostLift_map (h : (takeLift y n).Lost) :
  (bodyFunctor.map π ⟨(lostLift y h).val, body_mono R.pre.subtree_sub (lostLift y h).prop⟩).val
  = y.val := by ext; simp [lostLift, bodyEquivSystem, bodyEquivSystem_app, Stream'.get, Stream'.map]

lemma body_stratMap :
  ∃ x : body R.pre.subtree, (bodyFunctor.map π
    ⟨x.val, body_mono R.pre.subtree_sub x.prop⟩).val = y.val :=
  if h : ∀ n, (takeLift y n).Winnable then ⟨wonLift y h, wonLift_map y h⟩
  else by
    obtain ⟨n, h⟩ := by simpa using h
    let ⟨n, h⟩ : ∃ n, (takeLift y n).Lost :=
      if h' : (takeLift y n).Lost then ⟨n, h'⟩
      else lost_of_losable y n ⟨by have := (bodyTake y n).conLong_or_lost; tauto, of_not_not h⟩
    exact ⟨lostLift y h, lostLift_map y h⟩

end
end GaleStewartGame.BorelDet.Zero
