module

public import PolishSpaceBook.SetTheoryCardinalBasics
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-! # The cofinal sequences and the omega-one bound used in the book -/

namespace PolishSpaceBook.SetTheoryModels
open Order Cardinal Ordinal
universe u

/-- The book treats cofinality as an ordinal, the initial ordinal of mathlib's cardinal cofinality. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\cf(\omega) = \omega$, so $\omega$ is regular.
    *   $\cf(\omega + \omega) = \omega$ via the sequence $\omega, \omega+1, \omega+2, \ldots$, so $\omega + \omega$ is
        singular.
    *   $\cf(\omega^\omega) = \omega$ via $\omega, \omega^2, \omega^3, \ldots$, so $\omega^\omega$ is singular despite being
        a much larger ordinal.
    *   Every successor cardinal $\alephCard{\alpha+1}$ is regular under the axiom of choice.
-/
theorem omega_regular_ordinal : (Ordinal.omega0 : Ordinal.{u}).cof.ord = Ordinal.omega0 := by
  rw [Ordinal.cof_omega0, Cardinal.ord_aleph0]

/-- The sequence omega, omega+1, ... is increasing with supremum omega+omega. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\cf(\omega) = \omega$, so $\omega$ is regular.
    *   $\cf(\omega + \omega) = \omega$ via the sequence $\omega, \omega+1, \omega+2, \ldots$, so $\omega + \omega$ is
        singular.
    *   $\cf(\omega^\omega) = \omega$ via $\omega, \omega^2, \omega^3, \ldots$, so $\omega^\omega$ is singular despite being
        a much larger ordinal.
    *   Every successor cardinal $\alephCard{\alpha+1}$ is regular under the axiom of choice.
-/
theorem omega_add_nat_sequence :
    StrictMono (fun n : ℕ => (Ordinal.omega0 : Ordinal.{u}) + n) ∧
      (⨆ n : ℕ, (Ordinal.omega0 : Ordinal.{u}) + n) = Ordinal.omega0 + Ordinal.omega0 := by
  refine ⟨?_, Ordinal.iSup_add_natCast _⟩
  intro m n h
  exact (Ordinal.isNormal_add_right Ordinal.omega0).strictMono (by exact_mod_cast h)

/-- Omega+omega is singular under the book's convention for arbitrary limit ordinals. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\cf(\omega) = \omega$, so $\omega$ is regular.
    *   $\cf(\omega + \omega) = \omega$ via the sequence $\omega, \omega+1, \omega+2, \ldots$, so $\omega + \omega$ is
        singular.
    *   $\cf(\omega^\omega) = \omega$ via $\omega, \omega^2, \omega^3, \ldots$, so $\omega^\omega$ is singular despite being
        a much larger ordinal.
    *   Every successor cardinal $\alephCard{\alpha+1}$ is regular under the axiom of choice.
-/
theorem omega_add_omega_singular :
    ((Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0).cof.ord = Ordinal.omega0 ∧
      ((Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0).cof.ord ≠ Ordinal.omega0 + Ordinal.omega0 := by
  have h : ((Ordinal.omega0 : Ordinal.{u}) + Ordinal.omega0).cof.ord = Ordinal.omega0 := by
    rw [Ordinal.cof_add _ Ordinal.omega0_ne_zero, Ordinal.cof_omega0, Cardinal.ord_aleph0]
  exact ⟨h, by rw [h]; exact ne_of_lt (lt_add_of_pos_right _ Ordinal.omega0_pos)⟩

/-- The powers omega, omega^2, ... increase to omega^omega. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\cf(\omega) = \omega$, so $\omega$ is regular.
    *   $\cf(\omega + \omega) = \omega$ via the sequence $\omega, \omega+1, \omega+2, \ldots$, so $\omega + \omega$ is
        singular.
    *   $\cf(\omega^\omega) = \omega$ via $\omega, \omega^2, \omega^3, \ldots$, so $\omega^\omega$ is singular despite being
        a much larger ordinal.
    *   Every successor cardinal $\alephCard{\alpha+1}$ is regular under the axiom of choice.
-/
theorem omega_power_nat_sequence :
    StrictMono (fun n : ℕ => (Ordinal.omega0 : Ordinal.{u}) ^ (n + 1 : Ordinal)) ∧
      (⨆ n : ℕ, (Ordinal.omega0 : Ordinal.{u}) ^ (n + 1 : Ordinal)) =
        Ordinal.omega0 ^ Ordinal.omega0 := by
  have hnormal := Ordinal.isNormal_opow (Ordinal.one_lt_omega0 : (1 : Ordinal.{u}) < _)
  constructor
  · intro m n h
    apply hnormal.strictMono
    exact_mod_cast (Nat.add_lt_add_right h 1)
  · apply le_antisymm
    · apply Ordinal.iSup_le
      intro n
      exact hnormal.strictMono.monotone (by simp)
    · apply (Ordinal.opow_le_of_isSuccLimit Ordinal.omega0_ne_zero Ordinal.isSuccLimit_omega0).mpr
      intro b hb
      obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hb
      exact (hnormal.strictMono.monotone (show (n : Ordinal.{u}) ≤ n + 1 from
        by exact_mod_cast (Nat.le_succ n))).trans (Ordinal.le_iSup (fun n : ℕ => (Ordinal.omega0 : Ordinal.{u}) ^ (n + 1 : Ordinal.{u})) n)

/-- Omega^omega has ordinal cofinality omega and is not regular. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\cf(\omega) = \omega$, so $\omega$ is regular.
    *   $\cf(\omega + \omega) = \omega$ via the sequence $\omega, \omega+1, \omega+2, \ldots$, so $\omega + \omega$ is
        singular.
    *   $\cf(\omega^\omega) = \omega$ via $\omega, \omega^2, \omega^3, \ldots$, so $\omega^\omega$ is singular despite being
        a much larger ordinal.
    *   Every successor cardinal $\alephCard{\alpha+1}$ is regular under the axiom of choice.
-/
theorem omega_power_omega_singular :
    ((Ordinal.omega0 : Ordinal.{u}) ^ Ordinal.omega0).cof.ord = Ordinal.omega0 ∧
      ((Ordinal.omega0 : Ordinal.{u}) ^ Ordinal.omega0).cof.ord ≠ Ordinal.omega0 ^ Ordinal.omega0 := by
  have h : ((Ordinal.omega0 : Ordinal.{u}) ^ Ordinal.omega0).cof.ord = Ordinal.omega0 := by
    rw [Ordinal.cof_map_of_isNormal (Ordinal.isNormal_opow Ordinal.one_lt_omega0)
      Ordinal.isSuccLimit_omega0, Ordinal.cof_omega0, Cardinal.ord_aleph0]
  refine ⟨h, ?_⟩
  rw [h]
  have hlt : (1 : Ordinal.{u}) < Ordinal.omega0 := Ordinal.one_lt_omega0
  simpa only [Ordinal.opow_one] using
    (ne_of_lt ((Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono hlt))

/-- Successor alephs are regular under the ambient axiom of choice. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   $\cf(\omega) = \omega$, so $\omega$ is regular.
    *   $\cf(\omega + \omega) = \omega$ via the sequence $\omega, \omega+1, \omega+2, \ldots$, so $\omega + \omega$ is
        singular.
    *   $\cf(\omega^\omega) = \omega$ via $\omega, \omega^2, \omega^3, \ldots$, so $\omega^\omega$ is singular despite being
        a much larger ordinal.
    *   Every successor cardinal $\alephCard{\alpha+1}$ is regular under the axiom of choice.
-/
theorem successor_aleph_regular (a : Ordinal.{u}) :
    Cardinal.IsRegular (Cardinal.aleph (a + 1)) := Cardinal.isRegular_aleph_add_one a

/-- Omega-one is regular in the ordinal convention. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular $\omegaOneOrd = \alephCard{1}$ is regular: any countable subset of $\omegaOneOrd$ is
    bounded
    below $\omegaOneOrd$, since the supremum of countably many countable ordinals is itself countable. This is the
    fact used in §{sec:borel-hierarchy} to show that the Borel hierarchy stabilizes at $\omegaOneOrd$.
-/
theorem omega_one_regular_ordinal :
    (Ordinal.omega (1 : Ordinal.{u})).cof.ord = Ordinal.omega 1 := by
  rw [Cardinal.cof_omega_one, Cardinal.ord_aleph]

/-- The supremum of any countable family of countable ordinals stays below omega-one. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular $\omegaOneOrd = \alephCard{1}$ is regular: any countable subset of $\omegaOneOrd$ is
    bounded
    below $\omegaOneOrd$, since the supremum of countably many countable ordinals is itself countable. This is the
    fact used in §{sec:borel-hierarchy} to show that the Borel hierarchy stabilizes at $\omegaOneOrd$.
-/
theorem countable_ordinal_sup_below_omega_one {ι : Type*} [Countable ι]
    (f : ι → Ordinal.{u}) (hf : ∀ i, Countable (f i).toZFSet) :
    (⨆ i, f i) < Ordinal.omega 1 := by
  apply Ordinal.iSup_lt_omega_one
  intro i
  exact (ordinal_set_countable_iff_lt_omega_one (f i)).mp (hf i)

/-- A countable subset of omega-one has a strict upper bound below omega-one. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In particular $\omegaOneOrd = \alephCard{1}$ is regular: any countable subset of $\omegaOneOrd$ is
    bounded
    below $\omegaOneOrd$, since the supremum of countably many countable ordinals is itself countable. This is the
    fact used in §{sec:borel-hierarchy} to show that the Borel hierarchy stabilizes at $\omegaOneOrd$.
-/
theorem countable_subset_omega_one_bounded (s : Set Ordinal.{u}) (hs : s.Countable)
    (hlt : ∀ a ∈ s, a < Ordinal.omega 1) :
    ∃ b < Ordinal.omega (1 : Ordinal.{u}), ∀ a ∈ s, a < b := by
  let : Countable s := hs.to_subtype
  refine ⟨⨆ a : s, a.val + 1, Ordinal.iSup_lt_omega_one (fun a => ?_), ?_⟩
  · exact (Cardinal.isSuccLimit_omega 1).add_one_lt (hlt a.val a.property)
  · intro a ha
    exact (lt_add_one a).trans_le (Ordinal.le_iSup (fun a : s => a.val + 1) ⟨a, ha⟩)

/-- The book extends regularity terminology from cardinals to arbitrary limit ordinals. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A limit ordinal is \termdefine{regular} if $\cf(\alpha) = \alpha$, otherwise \termdefine{singular}. Some authors reserve
    this terminology for cardinals; here it is used for arbitrary limit ordinals. Examples:
-/
def IsRegularLimitOrdinal (a : Ordinal.{u}) : Prop := IsSuccLimit a ∧ a.cof.ord = a

/-- Singularity in the same convention retains the limit-ordinal hypothesis. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A limit ordinal is \termdefine{regular} if $\cf(\alpha) = \alpha$, otherwise \termdefine{singular}. Some authors reserve
    this terminology for cardinals; here it is used for arbitrary limit ordinals. Examples:
-/
def IsSingularLimitOrdinal (a : Ordinal.{u}) : Prop := IsSuccLimit a ∧ a.cof.ord ≠ a

/-- On infinite cardinal representatives this is the canonical cardinal regularity condition. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A limit ordinal is \termdefine{regular} if $\cf(\alpha) = \alpha$, otherwise \termdefine{singular}. Some authors reserve
    this terminology for cardinals; here it is used for arbitrary limit ordinals. Examples:
-/
theorem cardinal_regular_iff_ordinal_cofinality (c : Cardinal.{u}) :
    Cardinal.IsRegular c ↔ ℵ₀ ≤ c ∧ c.ord.cof.ord = c.ord := by
  constructor
  · intro h
    exact ⟨h.aleph0_le, congrArg Cardinal.ord h.cof_ord⟩
  · rintro ⟨hc, h⟩
    exact ⟨hc, (Cardinal.ord_injective h).ge⟩

end PolishSpaceBook.SetTheoryModels
