module

public import PolishSpaceBook.RandomDensityException
public import PolishSpaceBook.ForcingBookNotions
public import PolishSpaceBook.SuslinBaireProperty

@[expose] public section

/-! # The measure-algebra presentation and local regularity consequences -/

namespace PolishSpaceBook
open Set MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let
    $$Q := \MeasureAlg{\CantorSpace}{\mu}$$
    be the \termuse{measure algebra} of §{sec:measure-algebras-maharam}, and let
    $Q_+ := \{[B] \in Q : \mu(B) > 0\}$ be the
    *positive-measure* elements. The forcing notion is $Q_+$ under inclusion mod null:
    $$[B'] \le [B] \quad\Longleftrightarrow\quad \mu(\SetDifference{B'}{B}) = 0.$$
    Two conditions are compatible iff $\mu(B \cap B') > 0$; they are incompatible iff $\mu(B \cap B') = 0$. The weakest
    condition is $1_Q := [\CantorSpace]$.
-/
theorem measureAlgebra_positive_iff_mass_pos (a : MeasureAlgebra μ) :
    a ≠ ⊥ ↔ 0 < MeasureAlgebra.mass a := by
  rw [pos_iff_ne_zero]
  exact not_congr (MeasureAlgebra.mass_eq_zero_iff a).symm

/-- A measurable positive set determines an actual nonzero quotient condition. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    approximates it by Borel conditions of positive measure: a condition is no longer "the generic
    real begins with $s$" but "the generic real lies in $B$, where $B$ is a Borel set of positive measure". Stronger
    conditions are smaller positive-measure subsets, with sets of measure zero ignored.
-/
def randomPositiveCondition (B : Set X) (hB : MeasurableSet B) (hp : 0 < μ B) :
    MeasureAlgebra.Positive μ :=
  ⟨MeasureAlgebra.mk B hB, fun h => (ne_of_gt hp) ((MeasureAlgebra.mk_eq_bot B hB).mp h)⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    approximates it by Borel conditions of positive measure: a condition is no longer "the generic
    real begins with $s$" but "the generic real lies in $B$, where $B$ is a Borel set of positive measure". Stronger
    conditions are smaller positive-measure subsets, with sets of measure zero ignored.
-/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let
    $$Q := \MeasureAlg{\CantorSpace}{\mu}$$
    be the \termuse{measure algebra} of §{sec:measure-algebras-maharam}, and let
    $Q_+ := \{[B] \in Q : \mu(B) > 0\}$ be the
    *positive-measure* elements. The forcing notion is $Q_+$ under inclusion mod null:
    $$[B'] \le [B] \quad\Longleftrightarrow\quad \mu(\SetDifference{B'}{B}) = 0.$$
    Two conditions are compatible iff $\mu(B \cap B') > 0$; they are incompatible iff $\mu(B \cap B') = 0$. The weakest
    condition is $1_Q := [\CantorSpace]$.
-/
theorem random_condition_order (B C : Set X) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hpB : 0 < μ B) (hpC : 0 < μ C) :
    randomPositiveCondition B hB hpB ≤ randomPositiveCondition C hC hpC ↔ μ (B \ C) = 0 :=
  MeasureAlgebra.mk_le_mk_iff_null_sdiff B C hB hC

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let
    $$Q := \MeasureAlg{\CantorSpace}{\mu}$$
    be the \termuse{measure algebra} of §{sec:measure-algebras-maharam}, and let
    $Q_+ := \{[B] \in Q : \mu(B) > 0\}$ be the
    *positive-measure* elements. The forcing notion is $Q_+$ under inclusion mod null:
    $$[B'] \le [B] \quad\Longleftrightarrow\quad \mu(\SetDifference{B'}{B}) = 0.$$
    Two conditions are compatible iff $\mu(B \cap B') > 0$; they are incompatible iff $\mu(B \cap B') = 0$. The weakest
    condition is $1_Q := [\CantorSpace]$.
-/
theorem random_condition_compatible (B C : Set X) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hpB : 0 < μ B) (hpC : 0 < μ C) :
    SetTheoryModels.ForcingCompatible (randomPositiveCondition B hB hpB)
      (randomPositiveCondition C hC hpC) ↔ 0 < μ (B ∩ C) := by
  change (∃ c : MeasureAlgebra.Positive μ, c ≤ _ ∧ c ≤ _) ↔ _
  rw [MeasureAlgebra.compatible_iff_inf_ne_bot]
  change (MeasureAlgebra.mk B hB ⊓ MeasureAlgebra.mk C hC ≠ ⊥) ↔ _
  rw [MeasureAlgebra.mk_inf, ne_eq, MeasureAlgebra.mk_eq_bot, pos_iff_ne_zero]

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let
    $$Q := \MeasureAlg{\CantorSpace}{\mu}$$
    be the \termuse{measure algebra} of §{sec:measure-algebras-maharam}, and let
    $Q_+ := \{[B] \in Q : \mu(B) > 0\}$ be the
    *positive-measure* elements. The forcing notion is $Q_+$ under inclusion mod null:
    $$[B'] \le [B] \quad\Longleftrightarrow\quad \mu(\SetDifference{B'}{B}) = 0.$$
    Two conditions are compatible iff $\mu(B \cap B') > 0$; they are incompatible iff $\mu(B \cap B') = 0$. The weakest
    condition is $1_Q := [\CantorSpace]$.
-/
def randomWeakestCondition [IsProbabilityMeasure μ] : MeasureAlgebra.Positive μ :=
  randomPositiveCondition univ MeasurableSet.univ (by simp)

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Let
    $$Q := \MeasureAlg{\CantorSpace}{\mu}$$
    be the \termuse{measure algebra} of §{sec:measure-algebras-maharam}, and let
    $Q_+ := \{[B] \in Q : \mu(B) > 0\}$ be the
    *positive-measure* elements. The forcing notion is $Q_+$ under inclusion mod null:
    $$[B'] \le [B] \quad\Longleftrightarrow\quad \mu(\SetDifference{B'}{B}) = 0.$$
    Two conditions are compatible iff $\mu(B \cap B') > 0$; they are incompatible iff $\mu(B \cap B') = 0$. The weakest
    condition is $1_Q := [\CantorSpace]$.
-/
theorem random_condition_le_weakest [IsProbabilityMeasure μ] (p : MeasureAlgebra.Positive μ) :
    p ≤ randomWeakestCondition :=
  show p.val ≤ (⊤ : MeasureAlgebra μ) from le_top

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Write $\mu_s$ for normalized measure inside the cylinder $\cyl{s}$:
    $$
    \mu_s(B):=\frac{\mu(B\cap\cyl{s})}{\mu(\cyl{s})}.
    $$
-/
theorem binary_cylinderDensity (A : Set (ℕ → Bool)) (s : List Bool) :
    BorelExpression.cylinderDensity A (s.map Bool.toNat) =
      fairCoinProduct.real (A ∩ cyl s) / fairCoinProduct.real (cyl s) := by
  rw [BorelExpression.cylinderDensity, BorelExpression.cantorInclusion_preimage_cyl]

variable {Y : Type*} [TopologicalSpace Y] [PolishSpace Y]

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Their boundaries differ: coanalytic sets still have Lebesgue measurability and the Baire property in ZFC,
    because both properties pass to complements,
-/
theorem coanalytic_baireMeasurableSet {A : Set Y} (hA : CoanalyticSet A) :
    BaireMeasurableSet A :=
  (analyticSet_baireMeasurableSet Aᶜ hA).of_compl

omit [PolishSpace Y] in
/-- The cited analytic measurability theorem is the input; the local step is
complementation in the completed measure, not Borel measurability. -/
/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Their boundaries differ: coanalytic sets still have Lebesgue measurability and the Baire property in ZFC,
    because both properties pass to complements,
-/
theorem coanalytic_nullMeasurable_of_analytic_regularity [MeasurableSpace Y]
    (ν : Measure Y) (hanalytic : ∀ B : Set Y, AnalyticSet B → NullMeasurableSet B ν)
    {A : Set Y} (hA : CoanalyticSet A) : NullMeasurableSet A ν := by
  simpa only [compl_compl] using (hanalytic Aᶜ hA).compl

end PolishSpaceBook
