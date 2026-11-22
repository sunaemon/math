module

public import PolishSpaceBook.SetTheoryAbsoluteness

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # The bounded ordinal predicate on transitive domains -/

noncomputable section
namespace PolishSpaceBook.SetTheoryModels
open FirstOrder Language ZFSet ForcingFormulas
universe u

/-- Every member of a member of x belongs to x. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  target: prose
  excerpt: |
    The ordinal predicate from §{sec:ordinals-von-neumann} is
    $$
    \begin{aligned}
    \mathrm{Ord}(x)
    &:\equiv \mathrm{Trans}(x) \land (\forall y\in x)\,\mathrm{Trans}(y),\\
    \mathrm{Trans}(x)
    &:\equiv (\forall y\in x)(\forall z\in y)\,z\in x.
    \end{aligned}
    $$
    All quantifiers in these two formulas are bounded, so $\mathrm{Ord}(x)$ is $\Delta_0$.
    For a transitive set or class $N$ containing $x$, every member $y$ of $x$ belongs to $N$,
    and every member $z$ of $y$ also belongs to $N$.
    Thus the internal formula $\mathrm{Trans}(x)$ says exactly that $x$ is actually transitive.
    Applying the same argument to each $y\in x$ shows that the internal $\mathrm{Ord}(x)$ says exactly that $x$
    is a transitive set of transitive sets, the von Neumann ordinal condition.
    Consequently ordinalhood is absolute between transitive domains, without any ZFC assumption on those domains.
    This concerns a fixed parameter already in both domains; it does not by itself rule out new ordinal elements.
    The separate rank argument in §{sec:generic-extension}, with its ground-model closure hypotheses, gives
    $\mathrm{Ord}^{M[G]}=\mathrm{Ord}^M$.
-/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In symbols, the von Neumann definition is the ZFC formula
    $$\begin{aligned}
    \mathrm{Ord}(x) \;&:\equiv\; \mathrm{Trans}(x) \;\wedge\; (\forall y \in x)\,\mathrm{Trans}(y), \\
    \mathrm{Trans}(x) \;&:\equiv\; (\forall y \in x)(\forall z \in y)\; z \in x.
    \end{aligned}$$
    This formula is equivalent in ZF to the definition above. First, two ordinals are comparable by membership:
    their intersection is an initial segment of each, and a proper initial segment of an ordinal is the predecessor
    set of its least omitted element, hence that element itself. If the intersection were proper in both, it would
    belong to itself, contradicting Foundation. Now apply membership induction to a transitive set all of whose
    elements are transitive. Each of its elements has the same property and is therefore an ordinal by induction.
    Comparability of ordinals and Foundation then make membership a well-order on the original transitive set.
    The complexity classification and its forcing consequences appear in §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
def transitiveFormula {n : ℕ} (x : Fin n) : ForcingFormulas.Formula n :=
  boundedAll x (boundedAll (Fin.last n) (memberAt (Fin.last (n + 1)) x.castSucc.castSucc))

lemma transitiveFormula_deltaZero {n : ℕ} (x : Fin n) : IsDeltaZero (transitiveFormula x) :=
  .all x (.all (Fin.last n) (.member _))

/-- An ordinal is a transitive set of transitive sets. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    In symbols, the von Neumann definition is the ZFC formula
    $$\begin{aligned}
    \mathrm{Ord}(x) \;&:\equiv\; \mathrm{Trans}(x) \;\wedge\; (\forall y \in x)\,\mathrm{Trans}(y), \\
    \mathrm{Trans}(x) \;&:\equiv\; (\forall y \in x)(\forall z \in y)\; z \in x.
    \end{aligned}$$
    This formula is equivalent in ZF to the definition above. First, two ordinals are comparable by membership:
    their intersection is an initial segment of each, and a proper initial segment of an ordinal is the predecessor
    set of its least omitted element, hence that element itself. If the intersection were proper in both, it would
    belong to itself, contradicting Foundation. Now apply membership induction to a transitive set all of whose
    elements are transitive. Each of its elements has the same property and is therefore an ordinal by induction.
    Comparability of ordinals and Foundation then make membership a well-order on the original transitive set.
    The complexity classification and its forcing consequences appear in §{sec:zfc-absoluteness}.\termref{absoluteness}
-/
def ordinalFormula {n : ℕ} (x : Fin n) : ForcingFormulas.Formula n :=
  transitiveFormula x ⊓ boundedAll x (transitiveFormula (Fin.last n))

lemma ordinalFormula_deltaZero {n : ℕ} (x : Fin n) : IsDeltaZero (ordinalFormula x) :=
  (transitiveFormula_deltaZero x).and (.all x (transitiveFormula_deltaZero _))

lemma realize_transitiveFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (x : Fin n) (xs : Fin n → ClassDomain C) :
    (transitiveFormula x).Realize Empty.elim xs ↔ (xs x).val.IsTransitive := by
  simp only [transitiveFormula, realize_boundedAll, realize_memberAt_class,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h y hy z hz
    exact h ⟨y, hC _ (xs x).property _ hy⟩ hy ⟨z, hC _ (hC _ (xs x).property _ hy) _ hz⟩ hz
  · intro h y hy z hz
    exact h y.val hy hz

lemma realize_ordinalFormula (C : ZFClass.{u}) (hC : ∀ a, C a → ∀ b ∈ a, C b)
    {n : ℕ} (x : Fin n) (xs : Fin n → ClassDomain C) :
    (ordinalFormula x).Realize Empty.elim xs ↔ (xs x).val.IsOrdinal := by
  simp only [ordinalFormula, BoundedFormula.realize_inf, realize_boundedAll,
    realize_transitiveFormula C hC, Fin.snoc_last]
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  constructor
  · rintro ⟨ht, h⟩
    exact ⟨ht, fun y hy => h ⟨y, hC _ (xs x).property _ hy⟩ hy⟩
  · rintro ⟨ht, h⟩
    exact ⟨ht, fun y hy => h y.val hy⟩

/-- The internal ordinal predicate agrees with actual ordinalhood in any transitive domain. -/
theorem ordinal_absolute (M N : ZFClass.{u}) (hMN : M ⊆ N)
    (hM : ∀ a, M a → ∀ b ∈ a, M b) (hN : ∀ a, N a → ∀ b ∈ a, N b)
    (x : ClassDomain M) :
    (ordinalFormula (0 : Fin 1)).Realize Empty.elim ![x] ↔
      (ordinalFormula (0 : Fin 1)).Realize Empty.elim ![inclusion hMN x] := by
  rw [realize_ordinalFormula M hM, realize_ordinalFormula N hN]
  rfl

end PolishSpaceBook.SetTheoryModels
