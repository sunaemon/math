module

public import PolishSpaceBook.HKLDichotomy

@[expose] public section

namespace PolishSpaceBook
open Set MeasureTheory

/-- HKL leaves no nonsmooth Borel degree strictly below E0. The reverse
reduction is the actual HKL construction, not a supplied dichotomy hypothesis. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This is a strict dichotomy: nothing strictly $\BorelReducesTo$-between smooth and "$\EventualEqualityER$-above" exists.
-/
theorem e0_minimal_nonsmooth (X : Type) [MeasurableSpace X] [StandardBorelSpace X]
    (E : Setoid X) (hE : MeasurableSet {p : X × X | E.r p.1 p.2})
    (hbelow : BorelReducible E.r E0) : Smooth E.r ∨ BorelBiReducible E.r E0 := by
  classical
  by_cases hs : Smooth E.r
  · exact Or.inl hs
  · exact Or.inr ⟨hbelow, (hkl_reducible_iff_nonsmooth X E hE).mpr hs⟩

/-- The finite Borel approximations make their union Borel. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    every nonsmooth hyperfinite one contains the same first obstruction to smoothness by Glimm--Effros.
-/
theorem Hyperfinite.measurableSet {X : Type*} [MeasurableSpace X]
    {E : X → X → Prop} (hE : Hyperfinite E) :
    MeasurableSet {p : X × X | E p.1 p.2} := by
  obtain ⟨F, _, hF, _, _, hEq⟩ := hE
  have heq : {p : X × X | E p.1 p.2} = ⋃ n, {p : X × X | F n p.1 p.2} := by
    ext p
    simp only [mem_iUnion, mem_ofPred_eq, hEq]
  rw [heq]
  exact MeasurableSet.iUnion hF

/-- A hyperfinite class is the countable union of its finite approximations. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    every nonsmooth hyperfinite one contains the same first obstruction to smoothness by Glimm--Effros.
-/
theorem Hyperfinite.countable_class {X : Type*} [MeasurableSpace X]
    {E : X → X → Prop} (hE : Hyperfinite E) (x : X) : {y | E x y}.Countable := by
  obtain ⟨F, _, _, hfin, _, hEq⟩ := hE
  have heq : {y | E x y} = ⋃ n, {y | F n x y} := by ext y; simp [hEq]
  rw [heq]
  exact Set.countable_iUnion fun n => (hfin n x).countable

/-- The lower bound in the hyperfinite paragraph is a direct application of
proved HKL, after deriving Borelness from the actual approximating relations. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    every nonsmooth hyperfinite one contains the same first obstruction to smoothness by Glimm--Effros.
-/
theorem e0_reduces_nonsmooth_hyperfinite (X : Type) [MeasurableSpace X]
    [StandardBorelSpace X] (E : Setoid X) (hE : Hyperfinite E.r) (hns : ¬ Smooth E.r) :
    BorelReducible E0 E.r :=
  (hkl_reducible_iff_nonsmooth X E hE.measurableSet).mpr hns

/-- The upper reduction is the explicitly quoted DJK input. Combining it with
HKL yields bireducibility; this does not supply a proof of the DJK theorem. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    every nonsmooth hyperfinite one contains the same first obstruction to smoothness by Glimm--Effros.
-/
theorem nonsmooth_hyperfinite_bireducible (X : Type) [MeasurableSpace X]
    [StandardBorelSpace X] (E : Setoid X) (hE : Hyperfinite E.r) (hns : ¬ Smooth E.r)
    (hDJK : BorelReducible E.r E0) : BorelBiReducible E.r E0 :=
  ⟨hDJK, e0_reduces_nonsmooth_hyperfinite X E hE hns⟩

end PolishSpaceBook
