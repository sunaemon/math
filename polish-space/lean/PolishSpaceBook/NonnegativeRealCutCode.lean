module

public import PolishSpaceBook.CantorInternalMeasureCutValue
public import PolishSpaceBook.SetTheoryNaturalPairSets

@[expose] public section

/-! # Nonnegative reals coded by all positive-denominator rational lower queries -/

noncomputable section
namespace PolishSpaceBook.CantorTreeMeasure
open FirstOrder Language ZFSet ForcingFormulas SetTheoryModels BorelExpression MeasureTheory
universe u

/-- Fractions need not be reduced; negative rational queries are implicit for a nonnegative real. -/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a nonnegative real $r$, encode its strict rational lower cut by
    $$\NonnegativeRealCut{r}:=\{\langle a,b\rangle\in\omega\times\omega:
    0<b,\ a/b<r\}.$$
    Here the coordinates are finite ordinals and the brackets denote set-theoretic ordered pairs.
    We retain every positive-denominator representation of a fraction; reducing fractions is unnecessary.
    Negative rational queries are implicit, since every negative rational is less than $r$.
    For example,
    $$\NonnegativeRealCut{0}=\emptyset,\qquad
    \NonnegativeRealCut{1}=\{\langle a,b\rangle\in\omega\times\omega:a<b\}.$$
-/
def nonnegativeRealCutCode (r : ℝ) : ZFSet.{u} :=
  naturalPairSet (fun a b => 0 < b ∧ (a : ℝ) / b < r)

lemma mem_nonnegativeRealCutCode (r : ℝ) (z : ZFSet.{u}) :
    z ∈ nonnegativeRealCutCode r ↔
      ∃ a b : ℕ, z = pair (natOrdinal a) (natOrdinal b) ∧ 0 < b ∧ (a : ℝ) / b < r :=
  mem_naturalPairSet _ _

lemma pair_mem_nonnegativeRealCutCode (r : ℝ) (a b : ℕ) :
    pair (natOrdinal a) (natOrdinal b) ∈ nonnegativeRealCutCode.{u} r ↔
      0 < b ∧ (a : ℝ) / b < r :=
  pair_mem_naturalPairSet _ _ _

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: statement
  kind: proposition
  title: Fraction cuts code nonnegative reals
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  target: prose
  excerpt: |
    Equality of the codes gives the same answer to every positive-denominator fraction query.
    The rational-density argument in §{sec:internal-borel-measure-cut} then gives equality of the two reals.
    The reverse implication follows immediately from the definition.
-/
theorem nonnegativeRealCutCode_injOn :
    Set.InjOn nonnegativeRealCutCode.{u} (Set.Ici (0 : ℝ)) := by
  intro x hx y hy he
  apply eq_of_nonneg_fraction_cuts x y hx hy
  intro a b hb
  have h := congrArg (fun C : ZFSet.{u} => pair (natOrdinal a) (natOrdinal b) ∈ C) he
  simpa only [pair_mem_nonnegativeRealCutCode, hb, true_and] using iff_of_eq h

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Finite additivity requires the sum of two coded nonnegative reals. Since the code of zero is empty,
    we must allow zero as a lower approximation even when it does not belong to the strict cut.
-/
/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a nonnegative real $r$, encode its strict rational lower cut by
    $$\NonnegativeRealCut{r}:=\{\langle a,b\rangle\in\omega\times\omega:
    0<b,\ a/b<r\}.$$
    Here the coordinates are finite ordinals and the brackets denote set-theoretic ordered pairs.
    We retain every positive-denominator representation of a fraction; reducing fractions is unnecessary.
    Negative rational queries are implicit, since every negative rational is less than $r$.
    For example,
    $$\NonnegativeRealCut{0}=\emptyset,\qquad
    \NonnegativeRealCut{1}=\{\langle a,b\rangle\in\omega\times\omega:a<b\}.$$
-/
lemma nonnegativeRealCutCode_zero : nonnegativeRealCutCode.{u} 0 = ∅ := by
  ext z
  simp only [mem_nonnegativeRealCutCode, ZFSet.notMem_empty, iff_false]
  rintro ⟨a, b, _, _, h⟩
  have hn : (0 : ℝ) ≤ (a : ℝ) / b := by positivity
  exact (not_lt_of_ge hn) h

/-@ booklink:
  source: polish-space-book/appendix-measure-absoluteness.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For a nonnegative real $r$, encode its strict rational lower cut by
    $$\NonnegativeRealCut{r}:=\{\langle a,b\rangle\in\omega\times\omega:
    0<b,\ a/b<r\}.$$
    Here the coordinates are finite ordinals and the brackets denote set-theoretic ordered pairs.
    We retain every positive-denominator representation of a fraction; reducing fractions is unnecessary.
    Negative rational queries are implicit, since every negative rational is less than $r$.
    For example,
    $$\NonnegativeRealCut{0}=\emptyset,\qquad
    \NonnegativeRealCut{1}=\{\langle a,b\rangle\in\omega\times\omega:a<b\}.$$
-/
lemma pair_mem_nonnegativeRealCutCode_one (a b : ℕ) :
    pair (natOrdinal a) (natOrdinal b) ∈ nonnegativeRealCutCode.{u} 1 ↔ a < b := by
  rw [pair_mem_nonnegativeRealCutCode]
  constructor
  · rintro ⟨hb, h⟩
    exact_mod_cast (div_lt_one (by exact_mod_cast hb : (0 : ℝ) < b)).mp h
  · intro h
    have hb := (Nat.zero_le a).trans_lt h
    exact ⟨hb, (div_lt_one (by exact_mod_cast hb)).mpr (by exact_mod_cast h)⟩

end PolishSpaceBook.CantorTreeMeasure
