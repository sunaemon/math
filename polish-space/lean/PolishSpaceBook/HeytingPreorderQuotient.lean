module

public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Heyting.Basic

@[expose] public section

/-! # A shared quotient construction for Heyting preorders

Only the universal properties are supplied by a realizability model. Congruence
of operations and the canonical Heyting algebra on mutual-entailment classes are
proved here once.
-/
namespace PolishSpaceBook
universe u

class HeytingPreorderOps (P : Type u) [Preorder P] where
  meet : P → P → P
  join : P → P → P
  imp : P → P → P
  top : P
  bot : P
  le_meet : ∀ a b c, a ≤ meet b c ↔ a ≤ b ∧ a ≤ c
  join_le : ∀ a b c, join a b ≤ c ↔ a ≤ c ∧ b ≤ c
  imp_adj : ∀ a b c, meet a b ≤ c ↔ a ≤ imp b c
  le_top : ∀ a : P, a ≤ top
  bot_le : ∀ a : P, bot ≤ a

namespace HeytingPreorderOps
variable {P : Type u} [Preorder P] [h : HeytingPreorderOps P]

theorem meet_left (a b : P) : h.meet a b ≤ a := ((h.le_meet _ _ _).mp le_rfl).1
theorem meet_right (a b : P) : h.meet a b ≤ b := ((h.le_meet _ _ _).mp le_rfl).2
theorem join_left (a b : P) : a ≤ h.join a b := ((h.join_le _ _ _).mp le_rfl).1
theorem join_right (a b : P) : b ≤ h.join a b := ((h.join_le _ _ _).mp le_rfl).2

theorem meet_mono {a a' b b' : P} (ha : a ≤ a') (hb : b ≤ b') : h.meet a b ≤ h.meet a' b' :=
  (h.le_meet _ _ _).mpr ⟨(meet_left a b).trans ha,(meet_right a b).trans hb⟩

theorem join_mono {a a' b b' : P} (ha : a ≤ a') (hb : b ≤ b') : h.join a b ≤ h.join a' b' :=
  (h.join_le _ _ _).mpr ⟨ha.trans (join_left a' b'),hb.trans (join_right a' b')⟩

theorem imp_mono {a a' b b' : P} (ha : a' ≤ a) (hb : b ≤ b') : h.imp a b ≤ h.imp a' b' :=
  (h.imp_adj _ _ _).mp ((meet_mono le_rfl ha).trans
    (((h.imp_adj _ _ _).mpr le_rfl).trans hb))

def meetClass : Antisymmetrization P (· ≤ ·) → Antisymmetrization P (· ≤ ·) →
    Antisymmetrization P (· ≤ ·) :=
  Quotient.map₂ h.meet (fun _ _ ha _ _ hb =>
    ⟨meet_mono ha.1 hb.1,meet_mono ha.2 hb.2⟩)

def joinClass : Antisymmetrization P (· ≤ ·) → Antisymmetrization P (· ≤ ·) →
    Antisymmetrization P (· ≤ ·) :=
  Quotient.map₂ h.join (fun _ _ ha _ _ hb =>
    ⟨join_mono ha.1 hb.1,join_mono ha.2 hb.2⟩)

def impClass : Antisymmetrization P (· ≤ ·) → Antisymmetrization P (· ≤ ·) →
    Antisymmetrization P (· ≤ ·) :=
  Quotient.map₂ h.imp (fun _ _ ha _ _ hb =>
    ⟨imp_mono ha.2 hb.1,imp_mono ha.1 hb.2⟩)

instance quotientLattice : Lattice (Antisymmetrization P (· ≤ ·)) where
  toPartialOrder := inferInstance
  inf := meetClass
  sup := joinClass
  inf_le_left a b := Quotient.inductionOn₂ a b meet_left
  inf_le_right a b := Quotient.inductionOn₂ a b meet_right
  le_inf a b c := Quotient.inductionOn₃ a b c (fun _ _ _ ha hb => (h.le_meet _ _ _).mpr ⟨ha,hb⟩)
  le_sup_left a b := Quotient.inductionOn₂ a b join_left
  le_sup_right a b := Quotient.inductionOn₂ a b join_right
  sup_le a b c := Quotient.inductionOn₃ a b c (fun _ _ _ ha hb => (h.join_le _ _ _).mpr ⟨ha,hb⟩)

instance quotientTop : OrderTop (Antisymmetrization P (· ≤ ·)) where
  top := toAntisymmetrization (· ≤ ·) h.top
  le_top a := Quotient.inductionOn a h.le_top

instance quotientBot : OrderBot (Antisymmetrization P (· ≤ ·)) where
  bot := toAntisymmetrization (· ≤ ·) h.bot
  bot_le a := Quotient.inductionOn a h.bot_le

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    These universal properties imply monotonicity of meet and join. Implication is contravariant in its first
    argument and covariant in its second. Applying them in both directions shows that the operations descend to
    mutual-entailment classes. Their universal properties descend as well, giving the Heyting algebra. Reindexing
    keeps the same tracker and commutes pointwise with every displayed operation. It therefore induces a Heyting
    homomorphism; the identity and composition laws already hold on predicates.
-/
instance quotientHeyting : HeytingAlgebra (Antisymmetrization P (· ≤ ·)) where
  __ := quotientLattice
  __ := quotientTop
  __ := quotientBot
  himp := impClass
  compl a := impClass a ⊥
  le_himp_iff a b c := Quotient.inductionOn₃ a b c (fun a b c => (h.imp_adj a b c).symm)
  himp_bot _ := rfl

end HeytingPreorderOps
end PolishSpaceBook
