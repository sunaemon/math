module

public import PolishSpaceBook.SetTheoryGrothendieckModels

@[expose] public section

/-! # The book's cardinal and set-size conventions for universes -/

namespace PolishSpaceBook.SetTheoryModels
open Cardinal
universe u

/-- Strong limits exclude zero; power-set closure alone would include zero vacuously. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A nonzero cardinal $\kappa$ is a \termdefine{strong limit} if $2^\lambda < \kappa$ for every cardinal $\lambda <
    \kappa$. An uncountable cardinal $\kappa$ is \termdefineas{inaccessible cardinal}{(strongly) inaccessible} if it is
    regular in the sense of §{sec:ordinals-cofinality} and a strong limit.
-/
theorem strong_limit_definition (κ : Cardinal.{u}) :
    κ.IsStrongLimit ↔ κ ≠ 0 ∧ ∀ c : Cardinal.{u}, c < κ → 2 ^ c < κ := by
  simpa only [Cardinal.IsStrongPrelimit] using (Cardinal.isStrongLimit_iff (c := κ))

/-- The inaccessible condition is exactly uncountability, regularity, and strong-limit closure. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A nonzero cardinal $\kappa$ is a \termdefine{strong limit} if $2^\lambda < \kappa$ for every cardinal $\lambda <
    \kappa$. An uncountable cardinal $\kappa$ is \termdefineas{inaccessible cardinal}{(strongly) inaccessible} if it is
    regular in the sense of §{sec:ordinals-cofinality} and a strong limit.
-/
theorem inaccessible_definition (κ : Cardinal.{u}) :
    κ.IsInaccessible ↔ ℵ₀ < κ ∧ κ.IsRegular ∧ κ.IsStrongLimit := by
  constructor
  · intro h
    exact ⟨h.aleph0_lt, h.isRegular, h.isStrongLimit⟩
  · rintro ⟨hu, hr, hs⟩
    exact ⟨hu, hr.le_cof_ord, hs.isStrongPrelimit⟩

/-- Smallness relative to a set-theoretic universe means membership, not merely having a small type. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A set is \termdefineas{U-small}{$U$-small} if it is an element of $U$. A set that is not $U$-small is
    \termdefineas{U-large}{$U$-large}.
-/
def IsUniverseSmall (U x : ZFSet.{u}) : Prop := x ∈ U

/-- The complementary size convention used by the categorical appendix. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A set is \termdefineas{U-small}{$U$-small} if it is an element of $U$. A set that is not $U$-small is
    \termdefineas{U-large}{$U$-large}.
-/
def IsUniverseLarge (U x : ZFSet.{u}) : Prop := ¬IsUniverseSmall U x

end PolishSpaceBook.SetTheoryModels
