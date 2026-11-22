module

public import PolishSpaceBook.ForcingPolishSpaces
public import PolishSpaceBook.RandomGenericReals
public import PolishSpaceBook.InternalCohenClosedSets

@[expose] public section

namespace PolishSpaceBook.ForcingProse
open Set MeasureTheory Filter
universe u

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    A binary sequence $x\in\CantorSpace$ is \termdefineas{disjunctive sequence}{disjunctive} if every finite binary word
    occurs somewhere as a consecutive block in $x$.
-/
/-- Disjunctiveness requires occurrence of every finite word, including the
empty word, with the actual consecutive-block predicate of the chapter. -/
def IsDisjunctive (x : ℕ → Bool) : Prop := ∀ u : CohenCondition, CohenOccursIn u x

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    All Boolean operations in $Q$ are operations on equivalence classes modulo null sets:
    $[B]\vee[C]=[B\cup C]$, $[B]\wedge[C]=[B\cap C]$, and $[B]\le[C]$ means $\SetDifference{B}{C}$ is null. With this
    convention, we have the following two facts.
-/
/-- Boolean operations are operations on measured equivalence classes,
not literal choices of representatives. -/
theorem boolean_operations_spec {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (B C : Set X) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    ((MeasureAlgebra.mk B hB : MeasureAlgebra μ) ⊔ MeasureAlgebra.mk C hC =
      MeasureAlgebra.mk (B ∪ C) (hB.union hC)) ∧
    ((MeasureAlgebra.mk B hB : MeasureAlgebra μ) ⊓ MeasureAlgebra.mk C hC =
      MeasureAlgebra.mk (B ∩ C) (hB.inter hC)) ∧
    ((MeasureAlgebra.mk B hB : MeasureAlgebra μ) ≤ MeasureAlgebra.mk C hC ↔ μ (B \ C) = 0) :=
  ⟨MeasureAlgebra.mk_sup B C hB hC, MeasureAlgebra.mk_inf B C hB hC,
    MeasureAlgebra.mk_le_mk_iff_null_sdiff B C hB hC⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    The converse for random forcing rests on a measure-theoretic reconstruction. We first make it explicit in the ambient
    measure algebra $Q$.
    A family of positive conditions is \termdefineas{predense family}{predense} if every positive condition is compatible
    with a member of the family.
-/
/-- Predensity is compatibility with some member, where compatibility is
existence of a common strengthening in the original forcing order. -/
def IsPredense {P : Type*} [Preorder P] (A : Set P) : Prop :=
  ∀ p, ∃ q ∈ A, ∃ r : P, r ≤ p ∧ r ≤ q

/-- In the positive Boolean algebra the common-strengthening formulation
is exactly the nonzero-intersection test used by the cover lemmas. -/
theorem predense_iff_positive_intersection {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : Set (MeasureAlgebra.Positive μ)) :
    IsPredense A ↔ ∀ p : MeasureAlgebra.Positive μ, ∃ q ∈ A, p.val ⊓ q.val ≠ ⊥ := by
  constructor
  · intro h p
    obtain ⟨q, hq, r, hrp, hrq⟩ := h p
    refine ⟨q, hq, ?_⟩
    intro hbot
    have hle : r.val ≤ p.val ⊓ q.val := le_inf hrp hrq
    rw [hbot] at hle
    exact r.property (le_bot_iff.mp hle)
  · intro h p
    obtain ⟨q, hq, hpq⟩ := h p
    exact ⟨q, hq, (MeasureAlgebra.compatible_iff_inf_ne_bot p q).mpr hpq⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    For the internal calculations, identify binary sequences and finite words with their function graphs.
    Put $Y:=\funcspace{\omega}{2}\cap M$ and $P:=\finseq{2}$. For an internal set $A\IncludedIn Y$, define
    $$D_A:=\{s\in P:\forall g\in A\ \neg(s\IncludedIn g)\}.$$
    The basis tests for closedness and nowhere density are
    $$
    \begin{aligned}
    C(A)\quad\Longleftrightarrow\quad& A\IncludedIn Y\ \land\\
    &\forall g\in\SetDifference{Y}{A}\ \exists s\in P\\
    &\bigl(s\IncludedIn g\ \land\ s\in D_A\bigr),\\
    N(A)\quad\Longleftrightarrow\quad&\forall s\in P\ \exists t\in P\\
    &\bigl(s\IncludedIn t\ \land\ t\in D_A\bigr).
    \end{aligned}
    $$
    Substituting the displayed definition of membership in $D_A$ makes both tests bounded formulas.
    The first says that every point outside the set has a cylinder neighborhood disjoint from it;
    the second says that every cylinder has a smaller cylinder disjoint from the set.
-/
/-- Both displayed tests are actual bounded predicates on the graph-coded
parameters, with their closedness and nowhere-density semantics exposed. -/
theorem cohen_basis_tests (M A : ZFSet.{u}) :
    (cohenClosedPredicate.eval ![cohenConditionSet Set.univ, BorelExpression.internalCantor M, A] ↔
      A ⊆ BorelExpression.internalCantor M ∧ ∀ x : ℕ → Bool,
        BorelExpression.cantorPointGraph x ∈ M → BorelExpression.cantorPointGraph x ∉ A →
          ∃ s ∈ cohenAvoidanceSet A, x ∈ cyl s) ∧
    (cohenNowhereDensePredicate.eval ![cohenConditionSet Set.univ, A] ↔
      CohenDense (cohenAvoidanceSet A)) :=
  ⟨eval_cohenClosedPredicate M A, eval_cohenNowhereDensePredicate_set A⟩

/-@ booklink:
  source: polish-space-book/forcing-polish-spaces.md
  target: prose
  excerpt: |
    Associate dense tests to $c$ recursively. A leaf adds no tests. A complement node retains its child's tests and adds
    $\ForcingDecision{\CodeForcingSet{d}}$, where $d$ is the child. A union node with children $d_n$ retains all their tests
    and adds
    $\ForcingDecision{\bigcup_n\CodeForcingSet{d_n}}$. There are only countably many tests: this follows by induction on the
    code, taking a countable union at each union node.
    Every test is dense and closed under strengthening.
-/
/-- The actual cylinder-code tests are countable, dense and lower. Atomic
lowerness is supplied by the positive-condition cones, not assumed as an
extra correctness specification for the code. -/
theorem random_code_tests_spec (μ : Measure (ℕ → Bool))
    (s : ℕ → List Bool) (c : BorelCode) :
    (randomCodeRequirements μ s c).Countable ∧
      ∀ D ∈ randomCodeRequirements μ s c, IsCoinitial D ∧ IsLowerSet D :=
  ⟨randomCodeRequirements_countable s c,
    c.forcingRequirements_dense_lower _ (fun _ => MeasureAlgebra.below_lower _)⟩

end PolishSpaceBook.ForcingProse
