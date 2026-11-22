module

public import PolishSpaceBook.SetTheoryOrdinalArithmetic
public import PolishSpaceBook.PolishSpaces
public import Mathlib.SetTheory.Ordinal.Veblen

@[expose] public section

/-! # Countable ordinal examples and the distinct Baire function space -/

namespace PolishSpaceBook.SetTheoryModels
open Cardinal Ordinal
universe u

/-- A countable ordinal cardinal gives a countable von Neumann set, in its actual sort universe. -/
theorem countable_ordinal_set {a : Ordinal.{u}} (ha : a.card ≤ ℵ₀) : Countable a.toZFSet := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [ZFSet.cardinalMk_coe_sort, Ordinal.card_toZFSet]
  simpa using (Cardinal.lift_le.{u + 1}.mpr ha)

/-- Sums and products preserve countable ordinal cardinality. -/
theorem countable_ordinal_arithmetic {a b : Ordinal.{u}}
    (ha : a.card ≤ ℵ₀) (hb : b.card ≤ ℵ₀) :
    (a + b).card ≤ ℵ₀ ∧ (a * b).card ≤ ℵ₀ ∧ (a ^ b).card ≤ ℵ₀ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Ordinal.card_add]
    exact (add_le_add ha hb).trans (by simp)
  · rw [Ordinal.card_mul]
    exact (mul_le_mul' ha hb).trans (by simp)
  · exact (Ordinal.card_opow_le a b).trans (max_le le_rfl (max_le ha hb))

/-- Epsilon zero is the least fixed point of ordinal omega-exponentiation. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A typical climb through the countable ordinals:
    $$0,\, 1,\, 2,\, \ldots,\, \omega,\, \omega+1,\, \omega+2,\, \ldots,\, \omega \cdot 2,\, \omega \cdot 2 + 1,\, \ldots,\,
    \omega^2,\, \ldots,\, \omega^\omega,\, \ldots,\, \varepsilon_0,\, \ldots$$
    where $\varepsilon_0$ is the least fixed point of $\alpha \mapsto \omega^\alpha$. Every ordinal in this list is
    countable as a set.
-/
theorem epsilon_zero_least_fixed_point :
    (Ordinal.omega0 : Ordinal.{u}) ^ Ordinal.epsilon 0 = Ordinal.epsilon 0 ∧
      ∀ a : Ordinal.{u}, Ordinal.omega0 ^ a = a → Ordinal.epsilon 0 ≤ a :=
  ⟨Ordinal.omega0_opow_epsilon 0, fun _ h =>
    Ordinal.epsilon_zero_le_of_omega0_opow_le h.le⟩

/-- The epsilon-zero ordinal is countable as a set. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A typical climb through the countable ordinals:
    $$0,\, 1,\, 2,\, \ldots,\, \omega,\, \omega+1,\, \omega+2,\, \ldots,\, \omega \cdot 2,\, \omega \cdot 2 + 1,\, \ldots,\,
    \omega^2,\, \ldots,\, \omega^\omega,\, \ldots,\, \varepsilon_0,\, \ldots$$
    where $\varepsilon_0$ is the least fixed point of $\alpha \mapsto \omega^\alpha$. Every ordinal in this list is
    countable as a set.
-/
theorem epsilon_zero_set_countable : Countable (Ordinal.epsilon (0 : Ordinal.{u})).toZFSet := by
  apply countable_ordinal_set
  simp [Ordinal.card_epsilon]

/-- The ordinal omega-to-the-omega is countable, unlike the space of all omega-sequences. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A typical climb through the countable ordinals:
    $$0,\, 1,\, 2,\, \ldots,\, \omega,\, \omega+1,\, \omega+2,\, \ldots,\, \omega \cdot 2,\, \omega \cdot 2 + 1,\, \ldots,\,
    \omega^2,\, \ldots,\, \omega^\omega,\, \ldots,\, \varepsilon_0,\, \ldots$$
    where $\varepsilon_0$ is the least fixed point of $\alpha \mapsto \omega^\alpha$. Every ordinal in this list is
    countable as a set.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A notational warning: the expression $\omega^\omega$ above is \termdefine{ordinal exponentiation} as defined here, a
    countable ordinal. The identical-looking expression $\BaireSpace$ used throughout the main text is the
    \termuse{Baire space} of functions $\omega \to \omega$, an uncountable Polish space. Context fixes which is meant; the
    rendered glyphs
    coincide.
-/
theorem omega_power_omega_set_countable :
    Countable (((Ordinal.omega0 : Ordinal.{u}) ^ Ordinal.omega0).toZFSet) := by
  apply countable_ordinal_set
  exact (countable_ordinal_arithmetic (a := Ordinal.omega0) (b := Ordinal.omega0)
    (by simp) (by simp)).2.2

/-- Binary sequences embed into Baire space coordinate by coordinate. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A notational warning: the expression $\omega^\omega$ above is \termdefine{ordinal exponentiation} as defined here, a
    countable ordinal. The identical-looking expression $\BaireSpace$ used throughout the main text is the
    \termuse{Baire space} of functions $\omega \to \omega$, an uncountable Polish space. Context fixes which is meant; the
    rendered glyphs
    coincide.
-/
theorem baire_function_space_not_countable : ¬ Countable PolishSpaceBook.baire_space := by
  intro h
  let : Countable PolishSpaceBook.baire_space := h
  let f : PolishSpaceBook.cantor_space → PolishSpaceBook.baire_space :=
    fun x n => if x n then 1 else 0
  have hf : Function.Injective f := by
    intro x y hxy
    funext n
    have hn := congrFun hxy n
    cases hx : x n <;> cases hy : y n <;> simp_all [f]
  exact PolishSpaceBook.cantor_space_not_countable hf.countable

/-- Natural ordinals and omega supply the countable generators in the displayed examples. -/
theorem countable_ordinal_generators :
    (∀ n : ℕ, (n : Ordinal.{u}).card ≤ ℵ₀) ∧
      (Ordinal.omega0 : Ordinal.{u}).card ≤ ℵ₀ := by
  constructor
  · intro n
    simp
  · simp

/-- Every finite-index family explicitly displayed in the countable climb is countable as a set. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A typical climb through the countable ordinals:
    $$0,\, 1,\, 2,\, \ldots,\, \omega,\, \omega+1,\, \omega+2,\, \ldots,\, \omega \cdot 2,\, \omega \cdot 2 + 1,\, \ldots,\,
    \omega^2,\, \ldots,\, \omega^\omega,\, \ldots,\, \varepsilon_0,\, \ldots$$
    where $\varepsilon_0$ is the least fixed point of $\alpha \mapsto \omega^\alpha$. Every ordinal in this list is
    countable as a set.
-/
theorem displayed_ordinal_families_countable (n : ℕ) :
    Countable (n : Ordinal.{u}).toZFSet ∧
    Countable ((Ordinal.omega0 + (n : Ordinal.{u})).toZFSet) ∧
    Countable ((Ordinal.omega0 * (n : Ordinal.{u})).toZFSet) ∧
    Countable ((Ordinal.omega0 * (n : Ordinal.{u}) + 1).toZFSet) ∧
    Countable ((Ordinal.omega0 ^ (n : Ordinal.{u})).toZFSet) := by
  have hn := countable_ordinal_generators.{u}.1 n
  have ho := countable_ordinal_generators.{u}.2
  have h := countable_ordinal_arithmetic ho hn
  have h1 : (1 : Ordinal.{u}).card ≤ ℵ₀ := by simp
  exact ⟨countable_ordinal_set hn, countable_ordinal_set h.1,
    countable_ordinal_set h.2.1,
    countable_ordinal_set (countable_ordinal_arithmetic h.2.1 h1).1,
    countable_ordinal_set h.2.2⟩

end PolishSpaceBook.SetTheoryModels
