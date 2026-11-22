module

public import PolishSpaceBook.SetTheoryCofinalityDefinitions
public import Mathlib.SetTheory.ZFC.VonNeumann
public import PolishSpaceBook.SetTheoryFiniteReflection
public import PolishSpaceBook.SetTheoryCountableCollapse

@[expose] public section

/-! # Cumulative layers and the least-stage characterization of rank -/

namespace PolishSpaceBook.SetTheoryModels
open Order
universe u

/-- The zero and successor stages of the cumulative hierarchy. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    ZFC's universe stratifies into the \termdefine{cumulative hierarchy} $V_\alpha$, defined by transfinite recursion on
    ordinals:
    $$V_0 := \emptyset, \qquad V_{\alpha+1} := \PowerSet{V_\alpha}, \qquad V_\lambda := \bigcup_{\alpha<\lambda} V_\alpha
    \text{ at limits } \lambda.$$
    Then $V = \bigcup_{\alpha \in \mathrm{Ord}} V_\alpha$ — by Foundation every set lies in some $V_\alpha$. The least
    $\alpha$ with $x \in V_{\alpha+1}$ is the \termdefine{rank} of $x$; ranks of ordinals satisfy $\mathrm{rank}(\alpha) =
    \alpha$. Each $V_\alpha$ is a transitive set, so the universe builds up in transitive layers.
-/
theorem cumulative_hierarchy_recursion (a : Ordinal.{u}) :
    ZFSet.vonNeumann (0 : Ordinal.{u}) = ∅ ∧
      ZFSet.vonNeumann (a + 1) = ZFSet.powerset (ZFSet.vonNeumann a) :=
  ⟨ZFSet.vonNeumann_zero, ZFSet.vonNeumann_add_one a⟩

/-- A limit layer is the union of all the preceding layers. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    ZFC's universe stratifies into the \termdefine{cumulative hierarchy} $V_\alpha$, defined by transfinite recursion on
    ordinals:
    $$V_0 := \emptyset, \qquad V_{\alpha+1} := \PowerSet{V_\alpha}, \qquad V_\lambda := \bigcup_{\alpha<\lambda} V_\alpha
    \text{ at limits } \lambda.$$
    Then $V = \bigcup_{\alpha \in \mathrm{Ord}} V_\alpha$ — by Foundation every set lies in some $V_\alpha$. The least
    $\alpha$ with $x \in V_{\alpha+1}$ is the \termdefine{rank} of $x$; ranks of ordinals satisfy $\mathrm{rank}(\alpha) =
    \alpha$. Each $V_\alpha$ is a transitive set, so the universe builds up in transitive layers.
-/
theorem cumulative_hierarchy_limit (a : Ordinal.{u}) (ha : IsSuccLimit a) :
    ZFSet.vonNeumann a = ZFSet.iUnion (fun b : Set.Iio a => ZFSet.vonNeumann b.val) :=
  ZFSet.vonNeumann_of_isSuccPrelimit ha.isSuccPrelimit

/-- Every set belongs to a layer of the hierarchy. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    ZFC's universe stratifies into the \termdefine{cumulative hierarchy} $V_\alpha$, defined by transfinite recursion on
    ordinals:
    $$V_0 := \emptyset, \qquad V_{\alpha+1} := \PowerSet{V_\alpha}, \qquad V_\lambda := \bigcup_{\alpha<\lambda} V_\alpha
    \text{ at limits } \lambda.$$
    Then $V = \bigcup_{\alpha \in \mathrm{Ord}} V_\alpha$ — by Foundation every set lies in some $V_\alpha$. The least
    $\alpha$ with $x \in V_{\alpha+1}$ is the \termdefine{rank} of $x$; ranks of ordinals satisfy $\mathrm{rank}(\alpha) =
    \alpha$. Each $V_\alpha$ is a transitive set, so the universe builds up in transitive layers.
-/
theorem cumulative_hierarchy_exhausts (x : ZFSet.{u}) :
    ∃ a : Ordinal.{u}, x ∈ ZFSet.vonNeumann a := ZFSet.exists_mem_vonNeumann x

/-- Rank is exactly the least a for which x belongs to the next layer. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    ZFC's universe stratifies into the \termdefine{cumulative hierarchy} $V_\alpha$, defined by transfinite recursion on
    ordinals:
    $$V_0 := \emptyset, \qquad V_{\alpha+1} := \PowerSet{V_\alpha}, \qquad V_\lambda := \bigcup_{\alpha<\lambda} V_\alpha
    \text{ at limits } \lambda.$$
    Then $V = \bigcup_{\alpha \in \mathrm{Ord}} V_\alpha$ — by Foundation every set lies in some $V_\alpha$. The least
    $\alpha$ with $x \in V_{\alpha+1}$ is the \termdefine{rank} of $x$; ranks of ordinals satisfy $\mathrm{rank}(\alpha) =
    \alpha$. Each $V_\alpha$ is a transitive set, so the universe builds up in transitive layers.
-/
theorem rank_least_next_layer (x : ZFSet.{u}) :
    IsLeast {a : Ordinal.{u} | x ∈ ZFSet.vonNeumann (a + 1)} x.rank := by
  constructor
  · exact ZFSet.mem_vonNeumann.mpr (lt_add_one x.rank)
  · intro a ha
    exact lt_add_one_iff.mp (ZFSet.mem_vonNeumann.mp ha)

/-- The set representative of an ordinal has that very ordinal as its rank. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    ZFC's universe stratifies into the \termdefine{cumulative hierarchy} $V_\alpha$, defined by transfinite recursion on
    ordinals:
    $$V_0 := \emptyset, \qquad V_{\alpha+1} := \PowerSet{V_\alpha}, \qquad V_\lambda := \bigcup_{\alpha<\lambda} V_\alpha
    \text{ at limits } \lambda.$$
    Then $V = \bigcup_{\alpha \in \mathrm{Ord}} V_\alpha$ — by Foundation every set lies in some $V_\alpha$. The least
    $\alpha$ with $x \in V_{\alpha+1}$ is the \termdefine{rank} of $x$; ranks of ordinals satisfy $\mathrm{rank}(\alpha) =
    \alpha$. Each $V_\alpha$ is a transitive set, so the universe builds up in transitive layers.
-/
theorem ordinal_rank_as_set (a : Ordinal.{u}) : a.toZFSet.rank = a := Ordinal.rank_toZFSet a

/-- The stages are transitive sets, rather than arbitrary sets of the correct rank. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    ZFC's universe stratifies into the \termdefine{cumulative hierarchy} $V_\alpha$, defined by transfinite recursion on
    ordinals:
    $$V_0 := \emptyset, \qquad V_{\alpha+1} := \PowerSet{V_\alpha}, \qquad V_\lambda := \bigcup_{\alpha<\lambda} V_\alpha
    \text{ at limits } \lambda.$$
    Then $V = \bigcup_{\alpha \in \mathrm{Ord}} V_\alpha$ — by Foundation every set lies in some $V_\alpha$. The least
    $\alpha$ with $x \in V_{\alpha+1}$ is the \termdefine{rank} of $x$; ranks of ordinals satisfy $\mathrm{rank}(\alpha) =
    \alpha$. Each $V_\alpha$ is a transitive set, so the universe builds up in transitive layers.
-/
theorem cumulative_hierarchy_transitive (a : Ordinal.{u}) :
    (ZFSet.vonNeumann a).IsTransitive := ZFSet.isTransitive_vonNeumann a

/-- Reflection followed by downward Lowenheim–Skolem and collapse gives a countable
transitive model for any specified finite list of ambient true sentences. -/
/-@ booklink:
  source: polish-space-book/appendix-set-theory.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This is the theorem behind the common forcing convention "work in a sufficiently large finite fragment of ZFC."
    Reflection supplies transitive sets $V_\alpha$ satisfying any prescribed finite fragment; compactness, downward
    Löwenheim--Skolem, and Mostowski collapse then explain the countable-transitive-model reduction used in
    §{sec:internal-model-closure}.
-/
theorem finite_fragment_countable_transitive_model
    (Φ : List ForcingFormulas.membershipLanguage.Sentence)
    (hΦ : ∀ φ ∈ Φ, ZFSet.{u} ⊨ φ) :
    ∃ M : ZFSet.{u}, M.IsTransitive ∧ Countable M ∧ ∀ φ ∈ Φ, M ⊨ φ := by
  obtain ⟨a, ha, hs⟩ := finite_true_sentences_reflect Φ hΦ 0
  have hempty : (∅ : ZFSet.{u}) ∈ ZFSet.vonNeumann a := by
    simpa only [ZFSet.mem_vonNeumann, ZFSet.rank_empty] using ha
  let : Nonempty (ZFSet.vonNeumann a) := ⟨⟨∅, hempty⟩⟩
  let : IsEmpty (∅ : ZFSet.{u}) := ⟨fun x => ZFSet.notMem_empty x.val x.property⟩
  obtain ⟨M, hM, hcount, _, hsentences⟩ := exists_countable_transitive_model
    (V := ZFSet.vonNeumann a) (T := ∅) (ZFSet.isTransitive_vonNeumann a)
    ZFSet.isTransitive_empty (by intro x hx; exact False.elim (ZFSet.notMem_empty x hx))
  exact ⟨M, hM, hcount, fun φ hφ => (hsentences φ).mpr (hs φ hφ)⟩

end PolishSpaceBook.SetTheoryModels
