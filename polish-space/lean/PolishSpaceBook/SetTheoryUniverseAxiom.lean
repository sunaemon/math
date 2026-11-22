module

public import PolishSpaceBook.SetTheoryStrongLimitExamples

@[expose] public section

/-! # The universe axiom and the proper class of inaccessible cardinals -/

namespace PolishSpaceBook.SetTheoryModels
open Cardinal Ordinal
universe u

/-- The membership and subset versions of the universe axiom agree. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The standard **universe axiom** asserts that every set is contained in some Grothendieck universe, equivalently that the
    inaccessibles form a proper class.
-/
theorem universe_axiom_membership_iff_subset :
    (∀ x : ZFSet.{u}, ∃ U : ZFSet.{u}, IsGrothendieckUniverse U ∧ x ∈ U) ↔
    (∀ x : ZFSet.{u}, ∃ U : ZFSet.{u}, IsGrothendieckUniverse U ∧ x ⊆ U) := by
  constructor
  · intro h x
    obtain ⟨U, hU, hx⟩ := h x
    exact ⟨U, hU, hU.transitive.subset_of_mem hx⟩
  · intro h x
    obtain ⟨U, hU, hx⟩ := h ({x} : ZFSet.{u})
    exact ⟨U, hU, hx (ZFSet.mem_singleton.mpr rfl)⟩

/-- Having a universe for every set is equivalent to inaccessible heights being unbounded. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The standard **universe axiom** asserts that every set is contained in some Grothendieck universe, equivalently that the
    inaccessibles form a proper class.
-/
theorem universe_axiom_iff_unbounded_inaccessibles :
    (∀ x : ZFSet.{u}, ∃ U : ZFSet.{u}, IsGrothendieckUniverse U ∧ x ∈ U) ↔
    (∀ a : Ordinal.{u}, ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ a < κ.ord) := by
  constructor
  · intro h a
    obtain ⟨U, hU, ha⟩ := h a.toZFSet
    obtain ⟨κ, hκ, he⟩ := (grothendieck_universe_iff U).mp hU
    refine ⟨κ, hκ, ?_⟩
    rw [he, ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet] at ha
    exact ha
  · intro h x
    obtain ⟨κ, hκ, hx⟩ := h x.rank
    exact ⟨ZFSet.vonNeumann κ.ord, inaccessible_vonNeumann_isGrothendieckUniverse hκ,
      ZFSet.mem_vonNeumann.mpr hx⟩

/-- The actual class of inaccessible ordinal representatives is proper exactly when unbounded. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The standard **universe axiom** asserts that every set is contained in some Grothendieck universe, equivalently that the
    inaccessibles form a proper class.
-/
theorem inaccessible_class_proper_iff_unbounded :
    (¬ ∃ v : ZFSet.{u}, ∀ x : ZFSet.{u}, x ∈ v ↔
      ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ κ.ord.toZFSet = x) ↔
    (∀ a : Ordinal.{u}, ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ a < κ.ord) := by
  classical
  constructor
  · intro hp
    by_contra hn
    have hbound : ∃ a : Ordinal.{u}, ∀ κ : Cardinal.{u}, κ.IsInaccessible → κ.ord ≤ a := by
      simpa only [not_forall, not_exists, not_and, not_lt] using hn
    obtain ⟨a, ha⟩ := hbound
    apply hp
    refine ⟨(ZFSet.vonNeumann (a + 1)).sep
      (fun x => ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ κ.ord.toZFSet = x), ?_⟩
    intro x
    rw [ZFSet.mem_sep]
    constructor
    · exact And.right
    · intro hx
      refine ⟨?_, hx⟩
      obtain ⟨κ, hκ, rfl⟩ := hx
      apply ZFSet.mem_vonNeumann.mpr
      rw [Ordinal.rank_toZFSet]
      exact Order.lt_add_one_iff.mpr (ha κ hκ)
  · intro h ⟨v, hv⟩
    obtain ⟨κ, hκ, hlarge⟩ := h v.rank
    have hmem := (hv κ.ord.toZFSet).mpr ⟨κ, hκ, rfl⟩
    have hsmall := ZFSet.rank_lt_of_mem hmem
    rw [Ordinal.rank_toZFSet] at hsmall
    exact (not_lt_of_ge hlarge.le) hsmall

/-- The stated universe axiom is precisely the assertion that the inaccessibles form a proper class. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The standard **universe axiom** asserts that every set is contained in some Grothendieck universe, equivalently that the
    inaccessibles form a proper class.
-/
theorem universe_axiom_iff_proper_class_inaccessibles :
    (∀ x : ZFSet.{u}, ∃ U : ZFSet.{u}, IsGrothendieckUniverse U ∧ x ∈ U) ↔
    (¬ ∃ v : ZFSet.{u}, ∀ x : ZFSet.{u}, x ∈ v ↔
      ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ κ.ord.toZFSet = x) :=
  universe_axiom_iff_unbounded_inaccessibles.trans inaccessible_class_proper_iff_unbounded.symm

end PolishSpaceBook.SetTheoryModels
