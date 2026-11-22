module

public import PolishSpaceBook.SetTheoryUniverseConventions

@[expose] public section

/-! # The closure properties and contrasting cardinal examples in the universe discussion -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open Cardinal Ordinal Order
universe u

/-- Strong-limit closure bounds the actual power set of every smaller set. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The terminology is justified by closure under standard ZFC operations. If $\lambda < \kappa$ then $|\PowerSet{\lambda}|
    = 2^\lambda < \kappa$ by the strong-limit property, and any union of fewer than $\kappa$ sets each of cardinality less
    than $\kappa$ stays of cardinality less than $\kappa$ by regularity. The successor cardinals $\alephCard{\alpha+1}$ are
    regular under AC but never strong limits, since $2^{\alephCard{\alpha}} \ge \alephCard{\alpha+1}$. The cardinal
    $\bethCard{\omega} := \sup_n \bethCard{n}$ is a strong limit but $\cf(\bethCard{\omega}) = \omega < \bethCard{\omega}$,
    hence singular. These two closure properties explain the terminology: starting below an inaccessible cardinal,
    power sets and unions indexed by smaller sets do not reach it from below.
-/
theorem strong_limit_powerset_bound {κ : Cardinal.{u}} (hκ : κ.IsStrongLimit)
    {x : ZFSet.{u}} (hx : x.card < κ) : (ZFSet.powerset x).card < κ := by
  rw [ZFSet.card_powerset]
  exact hκ.isStrongPrelimit hx

/-- Regularity bounds unions indexed by a smaller set, with every member smaller too. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The terminology is justified by closure under standard ZFC operations. If $\lambda < \kappa$ then $|\PowerSet{\lambda}|
    = 2^\lambda < \kappa$ by the strong-limit property, and any union of fewer than $\kappa$ sets each of cardinality less
    than $\kappa$ stays of cardinality less than $\kappa$ by regularity. The successor cardinals $\alephCard{\alpha+1}$ are
    regular under AC but never strong limits, since $2^{\alephCard{\alpha}} \ge \alephCard{\alpha+1}$. The cardinal
    $\bethCard{\omega} := \sup_n \bethCard{n}$ is a strong limit but $\cf(\bethCard{\omega}) = \omega < \bethCard{\omega}$,
    hence singular. These two closure properties explain the terminology: starting below an inaccessible cardinal,
    power sets and unions indexed by smaller sets do not reach it from below.
-/
theorem regular_indexed_union_bound {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (I : ZFSet.{u}) (hI : I.card < κ) (f : I → ZFSet.{u})
    (hf : ∀ i, (f i).card < κ) : (ZFSet.iUnion f).card < κ := by
  let e := equivShrink I
  let g : Shrink.{u} I → ZFSet.{u} := fun i => f (e.symm i)
  have hsum : Cardinal.sum (fun i => (g i).card) < κ :=
    Cardinal.sum_lt_of_isRegular hκ (f := fun i => (g i).card) hI (fun i => hf (e.symm i))
  have hle : (ZFSet.iUnion g).card ≤ Cardinal.sum (fun i => (g i).card) := by
    simpa only [Cardinal.lift_id] using (ZFSet.lift_card_iUnion_le_sum_card (f := g))
  have he : ZFSet.iUnion g = ZFSet.iUnion f := by
    ext z
    simp only [ZFSet.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨e i, by simpa only [g, Equiv.symm_apply_apply] using hi⟩
  rw [← he]
  exact hle.trans_lt hsum

/-- Cantor's inequality prevents any successor cardinal from being a strong limit. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The terminology is justified by closure under standard ZFC operations. If $\lambda < \kappa$ then $|\PowerSet{\lambda}|
    = 2^\lambda < \kappa$ by the strong-limit property, and any union of fewer than $\kappa$ sets each of cardinality less
    than $\kappa$ stays of cardinality less than $\kappa$ by regularity. The successor cardinals $\alephCard{\alpha+1}$ are
    regular under AC but never strong limits, since $2^{\alephCard{\alpha}} \ge \alephCard{\alpha+1}$. The cardinal
    $\bethCard{\omega} := \sup_n \bethCard{n}$ is a strong limit but $\cf(\bethCard{\omega}) = \omega < \bethCard{\omega}$,
    hence singular. These two closure properties explain the terminology: starting below an inaccessible cardinal,
    power sets and unions indexed by smaller sets do not reach it from below.
-/
theorem successor_cardinal_not_strong_limit (κ : Cardinal.{u}) :
    Order.succ κ ≤ 2 ^ κ ∧ ¬(Order.succ κ).IsStrongLimit := by
  have h : Order.succ κ ≤ 2 ^ κ := Order.succ_le_of_lt (Cardinal.cantor κ)
  exact ⟨h, fun hs => (not_lt_of_ge h) (hs.isStrongPrelimit (Order.lt_succ κ))⟩

/-- Successor alephs are regular but fail the strong-limit condition. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The terminology is justified by closure under standard ZFC operations. If $\lambda < \kappa$ then $|\PowerSet{\lambda}|
    = 2^\lambda < \kappa$ by the strong-limit property, and any union of fewer than $\kappa$ sets each of cardinality less
    than $\kappa$ stays of cardinality less than $\kappa$ by regularity. The successor cardinals $\alephCard{\alpha+1}$ are
    regular under AC but never strong limits, since $2^{\alephCard{\alpha}} \ge \alephCard{\alpha+1}$. The cardinal
    $\bethCard{\omega} := \sup_n \bethCard{n}$ is a strong limit but $\cf(\bethCard{\omega}) = \omega < \bethCard{\omega}$,
    hence singular. These two closure properties explain the terminology: starting below an inaccessible cardinal,
    power sets and unions indexed by smaller sets do not reach it from below.
-/
theorem successor_aleph_regular_not_strong_limit (a : Ordinal.{u}) :
    (Cardinal.aleph (a + 1)).IsRegular ∧
      ¬(Cardinal.aleph (a + 1)).IsStrongLimit ∧
      Cardinal.aleph (a + 1) ≤ 2 ^ Cardinal.aleph a := by
  rw [← Cardinal.succ_aleph]
  exact ⟨Cardinal.isRegular_succ (Cardinal.aleph0_le_aleph a),
    (successor_cardinal_not_strong_limit _).2, (successor_cardinal_not_strong_limit _).1⟩

/-- Beth at omega is exactly the supremum of its finite beth stages. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The terminology is justified by closure under standard ZFC operations. If $\lambda < \kappa$ then $|\PowerSet{\lambda}|
    = 2^\lambda < \kappa$ by the strong-limit property, and any union of fewer than $\kappa$ sets each of cardinality less
    than $\kappa$ stays of cardinality less than $\kappa$ by regularity. The successor cardinals $\alephCard{\alpha+1}$ are
    regular under AC but never strong limits, since $2^{\alephCard{\alpha}} \ge \alephCard{\alpha+1}$. The cardinal
    $\bethCard{\omega} := \sup_n \bethCard{n}$ is a strong limit but $\cf(\bethCard{\omega}) = \omega < \bethCard{\omega}$,
    hence singular. These two closure properties explain the terminology: starting below an inaccessible cardinal,
    power sets and unions indexed by smaller sets do not reach it from below.
-/
theorem beth_omega_as_nat_sup :
    Cardinal.beth (Ordinal.omega0 : Ordinal.{u}) = ⨆ n : ℕ, Cardinal.beth (n : Ordinal.{u}) := by
  have h : Cardinal.beth (⨆ n : ℕ, (n : Ordinal.{u})) =
      ⨆ n : ℕ, Cardinal.beth (n : Ordinal.{u}) :=
    Cardinal.isNormal_beth.map_iSup bddAbove_of_small
  simpa only [Ordinal.iSup_natCast] using h

/-- Beth at omega is a strong limit of countable cofinality, strictly larger than aleph-zero. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The terminology is justified by closure under standard ZFC operations. If $\lambda < \kappa$ then $|\PowerSet{\lambda}|
    = 2^\lambda < \kappa$ by the strong-limit property, and any union of fewer than $\kappa$ sets each of cardinality less
    than $\kappa$ stays of cardinality less than $\kappa$ by regularity. The successor cardinals $\alephCard{\alpha+1}$ are
    regular under AC but never strong limits, since $2^{\alephCard{\alpha}} \ge \alephCard{\alpha+1}$. The cardinal
    $\bethCard{\omega} := \sup_n \bethCard{n}$ is a strong limit but $\cf(\bethCard{\omega}) = \omega < \bethCard{\omega}$,
    hence singular. These two closure properties explain the terminology: starting below an inaccessible cardinal,
    power sets and unions indexed by smaller sets do not reach it from below.
-/
theorem beth_omega_strong_limit_singular :
    (Cardinal.beth (Ordinal.omega0 : Ordinal.{u})).IsStrongLimit ∧
    (Cardinal.beth (Ordinal.omega0 : Ordinal.{u})).IsSingular ∧
    (Cardinal.beth (Ordinal.omega0 : Ordinal.{u})).ord.cof = ℵ₀ ∧
    ℵ₀ < Cardinal.beth (Ordinal.omega0 : Ordinal.{u}) := by
  have hstrong := (Cardinal.isStrongLimit_beth).mpr Ordinal.isSuccLimit_omega0.isSuccPrelimit
  have hcof : (Cardinal.beth (Ordinal.omega0 : Ordinal.{u})).ord.cof = ℵ₀ := by
    exact (Ordinal.cof_map_of_isNormal
      (Cardinal.isNormal_ord.comp Cardinal.isNormal_beth) Ordinal.isSuccLimit_omega0).trans
      Ordinal.cof_omega0
  have hlarge : ℵ₀ < Cardinal.beth (Ordinal.omega0 : Ordinal.{u}) := by
    simpa only [Cardinal.beth_zero] using
      (Cardinal.isNormal_beth.strictMono (Ordinal.omega0_pos : (0 : Ordinal.{u}) < _))
  exact ⟨hstrong, ⟨hlarge.le, by rw [hcof]; exact ne_of_lt hlarge⟩, hcof, hlarge⟩

/-- In the book's ordinal-valued convention, cf(beth_omega) is omega and is smaller. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The terminology is justified by closure under standard ZFC operations. If $\lambda < \kappa$ then $|\PowerSet{\lambda}|
    = 2^\lambda < \kappa$ by the strong-limit property, and any union of fewer than $\kappa$ sets each of cardinality less
    than $\kappa$ stays of cardinality less than $\kappa$ by regularity. The successor cardinals $\alephCard{\alpha+1}$ are
    regular under AC but never strong limits, since $2^{\alephCard{\alpha}} \ge \alephCard{\alpha+1}$. The cardinal
    $\bethCard{\omega} := \sup_n \bethCard{n}$ is a strong limit but $\cf(\bethCard{\omega}) = \omega < \bethCard{\omega}$,
    hence singular. These two closure properties explain the terminology: starting below an inaccessible cardinal,
    power sets and unions indexed by smaller sets do not reach it from below.
-/
theorem beth_omega_ordinal_cofinality :
    (Cardinal.beth (Ordinal.omega0 : Ordinal.{u})).ord.cof.ord = Ordinal.omega0 ∧
    (Ordinal.omega0 : Ordinal.{u}) < (Cardinal.beth Ordinal.omega0).ord := by
  have h := beth_omega_strong_limit_singular.{u}
  constructor
  · rw [h.2.2.1, Cardinal.ord_aleph0]
  · simpa only [Cardinal.ord_aleph0] using Cardinal.ord_strictMono h.2.2.2

end PolishSpaceBook.SetTheoryModels
