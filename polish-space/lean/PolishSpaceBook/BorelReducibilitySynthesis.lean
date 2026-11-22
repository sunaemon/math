module

public import Mathlib.Order.Antisymmetrization
public import PolishSpaceBook.PolishGroups
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Instances.CantorSet

@[expose] public section

/-!
# Borel reducibility

Formalization targets for
`polish-space/src/polish-space-book/borel-reducibility-synthesis.md`.

Formalized here are Borel reduction and bireducibility, their reflexive and
transitive laws, the mutually reducible but nonisomorphic doubled-class
example, complete real-valued invariants and smoothness transfer, eventual
agreement `E₀`, its Borelness and equivalence-relation laws, and its explicit
finite Borel approximations proving hyperfiniteness.

`CompactSpectralInvariant.lean` proves the spectral classification of compact
self-adjoint operators using the signed min–max lists and the kernel's Hilbert
dimension as a Borel complete invariant. `BorelReductionProse.lean` supplies smoothness from
countably many Borel classes and the continued-fraction realization of smooth
equality on Baire space. `BorelTransversal.lean` supplies the Lusin--Suslin proof
that a Borel transversal gives a Borel selector. The finite-block Hewitt--Savage proof of nonsmoothness of `E₀`
is supplied by `HewittSavage.lean` and `E0Nonsmooth.lean`. Silver's
dichotomy, including coanalytic local truth, Cantor fusion, general-space
transport and mutual exclusivity, is proved in `SilverDichotomy.lean`.
The general HKL embedding is now proved in
`HKLPolishTransport.lean`, which depends on the definitions here.
`HKLDichotomy.lean` combines this with `e0_not_smooth` to prove the
mutually exclusive alternatives for every standard Borel space. The generic
smoothness-transfer lemma below is instantiated there without an additional
assumption. Survey material and cited external classification theorems are
explicitly skipped in the source.
-/

namespace PolishSpaceBook

noncomputable section

universe u v w

open Function Set

section Reductions

variable {X : Type u} {Y : Type v} {Z : Type w}

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Let $E$ and $F$ be equivalence relations on standard Borel spaces $X$ and $Y$. Say $E$ is
    \termdefine{Borel reducible} to $F$, written $E \BorelReducesTo F$, if there exists a Borel function $f : X \to Y$ with
    $$x \mathrel{E} x' \;\Longleftrightarrow\; f(x) \mathrel{F} f(x') \qquad (x, x' \in X).$$
-/
/-- A particular measurable map reduces `E` to `F`. -/
def BorelReduces [MeasurableSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop) (f : X → Y) : Prop :=
  Measurable f ∧ ∀ x x', E x x' ↔ F (f x) (f x')

/-- Existence of a Borel reduction. -/
def BorelReducible [MeasurableSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  ∃ f : X → Y, BorelReduces E F f

/-- Mutual Borel reducibility. -/
def BorelBiReducible [MeasurableSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (F : Y → Y → Prop) : Prop :=
  BorelReducible E F ∧ BorelReducible F E

theorem BorelReduces.id [MeasurableSpace X] (E : X → X → Prop) :
    BorelReduces E E id :=
  ⟨measurable_id, fun _ _ ↦ Iff.rfl⟩

theorem BorelReduces.comp
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {E : X → X → Prop} {F : Y → Y → Prop} {G : Z → Z → Prop}
    {f : X → Y} {g : Y → Z} (hg : BorelReduces F G g)
    (hf : BorelReduces E F f) : BorelReduces E G (g ∘ f) := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  intro x x'
  exact (hf.2 x x').trans (hg.2 (f x) (f x'))

theorem BorelReducible.refl [MeasurableSpace X] (E : X → X → Prop) :
    BorelReducible E E :=
  ⟨id, BorelReduces.id E⟩

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    The relation $\BorelReducesTo$ is transitive. If $f:X\to Y$ reduces $E$ to $F$ and $g:Y\to Z$ reduces $F$ to $H$, then
    $g\circ f$
    is Borel and
    $$
    x\mathrel E x'
    \Longleftrightarrow
    f(x)\mathrel F f(x')
    \Longleftrightarrow
    g(f(x))\mathrel H g(f(x')).
    $$
    It is reflexive by the identity map.
-/
theorem BorelReducible.trans
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {E : X → X → Prop} {F : Y → Y → Prop} {G : Z → Z → Prop}
    (hEF : BorelReducible E F) (hFG : BorelReducible F G) :
    BorelReducible E G := by
  rcases hEF with ⟨f, hf⟩
  rcases hFG with ⟨g, hg⟩
  exact ⟨g ∘ f, hg.comp hf⟩

/-- The quotient injection carried by a reduction, with its Borel lift retained. -/
def BorelReduces.quotientEmbedding [MeasurableSpace X] [MeasurableSpace Y]
    {E : Setoid X} {F : Setoid Y} {f : X → Y}
    (hf : BorelReduces E.r F.r f) : Quotient E ↪ Quotient F where
  toFun := Quotient.map f (fun _ _ h ↦ (hf.2 _ _).mp h)
  inj' := by
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        intro h
        exact Quotient.sound ((hf.2 a b).mpr (Quotient.exact h))

/-- Borel-definability here means having a Borel map on representatives;
no standard Borel structure on the quotient is assumed. -/
def HasBorelRepresentativeLift [MeasurableSpace X] [MeasurableSpace Y]
    (E : Setoid X) (F : Setoid Y) (j : Quotient E → Quotient F) : Prop :=
  ∃ f : X → Y, Measurable f ∧ ∀ x, j (Quotient.mk E x) = Quotient.mk F (f x)

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Such $f$ sends each $E$-class into a single $F$-class, sends distinct $E$-classes to distinct $F$-classes, and does so
    by a Borel map on representatives. Equivalently, it gives a \termdefine{Borel-definable} injection from the quotient
    $X/E$ into $Y/F$.
-/
theorem borelReducible_iff_quotient_embedding [MeasurableSpace X] [MeasurableSpace Y]
    (E : Setoid X) (F : Setoid Y) :
    BorelReducible E.r F.r ↔
      ∃ j : Quotient E ↪ Quotient F, HasBorelRepresentativeLift E F j := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨hf.quotientEmbedding, f, hf.1, fun _ ↦ rfl⟩
  · rintro ⟨j, f, hf, hj⟩
    refine ⟨f, hf, fun x x' ↦ ?_⟩
    constructor
    · intro h
      apply Quotient.exact
      rw [← hj x, ← hj x']
      exact congrArg j (Quotient.sound h)
    · intro h
      apply Quotient.exact
      apply j.injective
      rw [hj x, hj x']
      exact Quotient.sound h

/-- Bundled classification problems, allowing the underlying spaces to vary. -/
structure BorelClassificationProblem where
  carrier : Type u
  measurableSpace : MeasurableSpace carrier
  relation : Setoid carrier

attribute [instance] BorelClassificationProblem.measurableSpace

instance : Preorder BorelClassificationProblem where
  le E F := BorelReducible E.relation.r F.relation.r
  le_refl E := BorelReducible.refl E.relation.r
  le_trans _ _ _ := BorelReducible.trans

/-- Borel cardinalities identify precisely mutually reducible problems. -/
abbrev BorelCardinality := Antisymmetrization BorelClassificationProblem (· ≤ ·)

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Bidirectional reducibility $E \BorelEquivalentTo F$ means that the two quotients have the same size on
    the
    \termdefine{Borel cardinality} scale: after identifying mutually reducible problems, $\BorelReducesTo$ becomes a partial
    order on
    $\BorelEquivalentTo$-classes.
-/
/-- The quotient really carries the partial order induced by Borel reducibility. -/
abbrev borelCardinalityPartialOrder : PartialOrder BorelCardinality := inferInstance

/-- The projection to Borel cardinalities. -/
def BorelClassificationProblem.cardinality (E : BorelClassificationProblem) : BorelCardinality :=
  toAntisymmetrization (· ≤ ·) E

theorem BorelClassificationProblem.cardinality_le_iff (E F : BorelClassificationProblem) :
    E.cardinality ≤ F.cardinality ↔ BorelReducible E.relation.r F.relation.r := Iff.rfl

theorem BorelClassificationProblem.cardinality_eq_iff (E F : BorelClassificationProblem) :
    E.cardinality = F.cardinality ↔ BorelBiReducible E.relation.r F.relation.r :=
  toAntisymmetrization_eq (· ≤ ·) E F

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Hence $\BorelEquivalentTo$ is an equivalence relation on classification problems,
    and $\BorelReducesTo$
    descends to a genuine partial order on $\BorelEquivalentTo$-classes.
-/
theorem borelBiReducible_equivalence :
    Equivalence (fun E F : BorelClassificationProblem ↦ BorelBiReducible E.relation.r F.relation.r) := by
  simpa only [← BorelClassificationProblem.cardinality_eq_iff] using
    (show Equivalence (fun E F : BorelClassificationProblem ↦ E.cardinality = F.cardinality) from
      ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩)

/-- The relation on a doubled space that remembers only the first coordinate. -/
def SameFirst (p q : X × Bool) : Prop :=
  p.1 = q.1

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    This is weaker than isomorphism of equivalence relations on the underlying spaces. Let $E=\RealEqualityER$ be equality
    on
    $\R$, and let $F$ be the equivalence relation on $\R\times\{0,1\}$ defined by
    $$
    (r,i)\mathrel F(s,j)\quad\Longleftrightarrow\quad r=s.
    $$
    Then $E\BorelReducesTo F$ by $r\mapsto(r,0)$, while $F\BorelReducesTo E$ by $(r,i)\mapsto r$. Hence $E\BorelEquivalentTo F$.
-/
theorem equality_bireducible_sameFirst [MeasurableSpace X] :
    BorelBiReducible (Eq : X → X → Prop)
      (SameFirst : X × Bool → X × Bool → Prop) := by
  constructor
  · refine ⟨fun x ↦ (x, false), ?_⟩
    exact ⟨measurable_id.prodMk measurable_const, by simp [SameFirst]⟩
  · refine ⟨Prod.fst, ?_⟩
    exact ⟨measurable_fst, by simp [SameFirst]⟩

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    But there is no Borel
    isomorphism $h:\R\to\R\times\{0,1\}$ whose pullback of $F$ is equality and whose image is all of
    $\R\times\{0,1\}$. If such an $h$ existed, the two points $(r,0)$ and $(r,1)$ would have distinct preimages by
    injectivity and surjectivity,
    but they are $F$-equivalent, so the pullback condition would force those preimages to be equal.
-/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Thus Borel cardinal
    equivalence records mutual embeddability of quotient problems, not literal Borel isomorphism of their class structures.
-/
theorem no_bijective_reduction_equality_sameFirst [Nonempty X] :
    ¬ ∃ h : X → X × Bool, Bijective h ∧
      ∀ x x', x = x' ↔ SameFirst (h x) (h x') := by
  rintro ⟨h, hh, hpull⟩
  let r : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨x₀, hx₀⟩ := hh.2 (r, false)
  obtain ⟨x₁, hx₁⟩ := hh.2 (r, true)
  have hx : x₀ = x₁ := (hpull x₀ x₁).2 (by simp [SameFirst, hx₀, hx₁])
  have hcontra := congrArg h hx
  rw [hx₀, hx₁] at hcontra
  simp at hcontra

end Reductions

section Smoothness

variable {X : Type u} {Y : Type v}

/-- A complete invariant identifies exactly the equivalence classes. -/
def CompleteInvariant (E : X → X → Prop) (c : X → Y) : Prop :=
  ∀ x x', E x x' ↔ c x = c x'

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    $E$ is \termdefine{smooth} (or *concretely classifiable*) if $E \BorelReducesTo \RealEqualityER$, where $\RealEqualityER$ is equality
    on $\R$. By Kuratowski's isomorphism theorem in §{sec:kuratowski-isomorphism}, the choice of uncountable standard
    Borel codomain is immaterial. Concretely, $E$ is smooth iff there is a Borel map $f : X \to \R$ separating
    $E$-classes — a
    Borel \termdefine{complete invariant}.
-/
/-- Smoothness via a real-valued complete Borel invariant. -/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: statement
  excerpt: |
    \begin{corollary*}[Complete-invariant characterization] The relation $E$ is smooth iff it has a Borel complete invariant
-/
def Smooth [MeasurableSpace X] (E : X → X → Prop) : Prop :=
  ∃ c : X → ℝ, Measurable c ∧ CompleteInvariant E c

theorem smooth_iff_borelReducible_eq [MeasurableSpace X]
    (E : X → X → Prop) :
    Smooth E ↔ BorelReducible E (Eq : ℝ → ℝ → Prop) :=
  Iff.rfl

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: statement
  kind: proposition
  title: Standard-Borel invariant criterion
-/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: statement
  excerpt: |
    \begin{corollary*}[Complete-invariant characterization] The relation $E$ is smooth iff it has a Borel complete invariant
-/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    By the classification of standard Borel spaces in §{sec:standard-borel-classification}, there is a
    Borel injection $j:Y\to\R$. Then $j\circ c$ is a real-valued Borel complete invariant, proving the proposition. The
    forward implication of the first corollary uses $Y=\R$, and the reverse implication is the proposition.
-/
theorem smooth_of_standardBorel_completeInvariant
    [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    {E : X → X → Prop} {c : X → Y}
    (hc : Measurable c) (hcE : CompleteInvariant E c) : Smooth E := by
  obtain ⟨g, hg, hg_inj⟩ :=
    MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Y
  let e : (ℕ → Bool) → ℝ := fun p ↦
    (cantorSetHomeomorphNatToBool.symm p : ℝ)
  have he : Measurable e :=
    (continuous_subtype_val.comp
      cantorSetHomeomorphNatToBool.symm.continuous).measurable
  have he_inj : Injective e :=
    Subtype.coe_injective.comp cantorSetHomeomorphNatToBool.symm.injective
  refine ⟨e ∘ g ∘ c, (he.comp hg).comp hc, ?_⟩
  intro x x'
  constructor
  · intro h
    exact congrArg (e ∘ g) ((hcE x x').1 h)
  · intro h
    exact (hcE x x').2 (hg_inj (he_inj h))

/-- Smoothness pulls back along a Borel reduction. -/
theorem Smooth.of_reducible
    [MeasurableSpace X] [MeasurableSpace Y]
    {E : X → X → Prop} {F : Y → Y → Prop}
    (hF : Smooth F) (hEF : BorelReducible E F) : Smooth E := by
  rcases hF with ⟨c, hc, hcF⟩
  rcases hEF with ⟨f, hf, hfE⟩
  exact ⟨c ∘ f, hc.comp hf, fun x x' ↦ (hfE x x').trans (hcF (f x) (f x'))⟩

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Transversals give a useful sufficient criterion. A \termdefine{Borel transversal} for $E$ is a Borel set
    $T\IncludedIn X$ meeting every $E$-class in exactly one point.
-/
/-- A Borel set containing exactly one representative of every class. -/
def BorelTransversal [MeasurableSpace X] (E : X → X → Prop) (T : Set X) : Prop :=
  MeasurableSet T ∧ ∀ x, ∃! t, t ∈ T ∧ E x t

end Smoothness

section EventualAgreement

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    A representative example of a nonsmooth Borel equivalence relation is **$\EventualEqualityER$**, *eventual agreement* on
    $\CantorSpace$. Think of a
    point of $\CantorSpace$ as an infinite binary record. Equality asks that two records agree at every coordinate;
    $\EventualEqualityER$
    asks only that they agree from some finite stage onward:
    $$x \mathrel{\EventualEqualityER} y \;\Longleftrightarrow\; \exists N \in \omega,\, \forall n \ge N,\; x_n = y_n.$$
-/
/-- Agreement from coordinate `N` onward. -/
def E0At (N : ℕ) (x y : ℕ → Bool) : Prop :=
  ∀ n, N ≤ n → x n = y n

/-- Eventual agreement on binary sequences. -/
def E0 (x y : ℕ → Bool) : Prop :=
  ∃ N, E0At N x y

theorem e0At_equivalence (N : ℕ) : Equivalence (E0At N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x n _hn
    rfl
  · intro x y h n hn
    exact (h n hn).symm
  · intro x y z hxy hyz n hn
    exact (hxy n hn).trans (hyz n hn)

theorem e0_equivalence : Equivalence E0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨0, (e0At_equivalence 0).1 x⟩
  · rintro x y ⟨N, h⟩
    exact ⟨N, (e0At_equivalence N).2 h⟩
  · rintro x y z ⟨N, hxy⟩ ⟨M, hyz⟩
    refine ⟨max N M, ?_⟩
    intro n hn
    exact (hxy n ((le_max_left N M).trans hn)).trans
      (hyz n ((le_max_right N M).trans hn))

theorem measurableSet_e0At (N : ℕ) :
    MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | E0At N p.1 p.2} := by
  rw [show {p : (ℕ → Bool) × (ℕ → Bool) | E0At N p.1 p.2} =
      ⋂ n : ℕ, ⋂ (_h : N ≤ n), {p | p.1 n = p.2 n} by
    ext p
    simp [E0At]]
  refine MeasurableSet.iInter fun n ↦ MeasurableSet.iInter fun _hn ↦ ?_
  exact measurableSet_eq_fun
    (measurable_pi_iff.1 measurable_fst n)
    (measurable_pi_iff.1 measurable_snd n)

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    $\EventualEqualityER$ is Borel because it is the countable union, over $N$, of the closed relations requiring agreement at every
    coordinate $n\ge N$.
-/
theorem measurableSet_e0 :
    MeasurableSet {p : (ℕ → Bool) × (ℕ → Bool) | E0 p.1 p.2} := by
  rw [show {p : (ℕ → Bool) × (ℕ → Bool) | E0 p.1 p.2} =
      ⋃ N : ℕ, {p | E0At N p.1 p.2} by
    ext p
    simp [E0]]
  exact MeasurableSet.iUnion measurableSet_e0At

theorem e0At_class_finite (N : ℕ) (x : ℕ → Bool) :
    {y | E0At N x y}.Finite := by
  let f : {y // E0At N x y} → (Fin N → Bool) := fun y i ↦ y.1 i
  have hf : Injective f := by
    intro y z hyz
    apply Subtype.ext
    funext n
    by_cases hn : n < N
    · exact congrFun hyz ⟨n, hn⟩
    · have hN : N ≤ n := Nat.le_of_not_gt hn
      exact (y.2 n hN).symm.trans (z.2 n hN)
  let : Finite {y // E0At N x y} := Finite.of_injective f hf
  rw [Set.finite_def]
  exact ⟨Fintype.ofFinite {y // E0At N x y}⟩

theorem e0At_mono (N : ℕ) {x y : ℕ → Bool} (h : E0At N x y) :
    E0At (N + 1) x y := by
  intro n hn
  exact h n (Nat.le_trans (Nat.le_succ N) hn)

end EventualAgreement

section Hyperfinite

variable {X : Type u} [MeasurableSpace X]

/-- A relation is hyperfinite when it is the increasing union of Borel
equivalence relations with finite classes. -/
def Hyperfinite (E : X → X → Prop) : Prop :=
  ∃ Eₙ : ℕ → X → X → Prop,
    (∀ n, Equivalence (Eₙ n)) ∧
    (∀ n, MeasurableSet {p : X × X | Eₙ n p.1 p.2}) ∧
    (∀ n x, {y | Eₙ n x y}.Finite) ∧
    (∀ n x y, Eₙ n x y → Eₙ (n + 1) x y) ∧
    ∀ x y, E x y ↔ ∃ n, Eₙ n x y

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    The most important tame subclass is the class of \termdefineas{hyperfiniteness}{hyperfinite} equivalence relations.
    A
    countable Borel equivalence relation $E$ is hyperfinite if
    $$
    E=\bigcup_n E_n
    $$
    for an increasing sequence of finite Borel equivalence relations $E_n$.
-/
/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    Hyperfiniteness says that the infinite classes
    can be exhausted by finite approximations in a Borel-uniform way.
-/
theorem hyperfinite_def (E : X → X → Prop) :
    Hyperfinite E ↔
      ∃ Eₙ : ℕ → X → X → Prop,
        (∀ n, Equivalence (Eₙ n)) ∧
        (∀ n, MeasurableSet {p : X × X | Eₙ n p.1 p.2}) ∧
        (∀ n x, {y | Eₙ n x y}.Finite) ∧
        (∀ n x y, Eₙ n x y → Eₙ (n + 1) x y) ∧
        ∀ x y, E x y ↔ ∃ n, Eₙ n x y :=
  Iff.rfl

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: prose
  excerpt: |
    The relation $\EventualEqualityER$ is hyperfinite: let $E_n$ identify
    two binary sequences when they agree from coordinate $n$ onward
-/
theorem e0_hyperfinite : Hyperfinite E0 := by
  refine ⟨E0At, e0At_equivalence, measurableSet_e0At,
    e0At_class_finite, e0At_mono, ?_⟩
  intro x y
  exact Iff.rfl

end Hyperfinite

section Consequences

/-@ booklink:
  source: polish-space-book/borel-reducibility-synthesis.md
  target: proof
  excerpt: |
    The alternatives are mutually exclusive. If $E$ is smooth and $\EventualEqualityER \BorelReducesTo E$, then composing a
    reduction $\EventualEqualityER \BorelReducesTo E$ with a complete Borel invariant for $E$ gives a complete Borel invariant for $\EventualEqualityER$,
    contradicting the nonsmoothness of $\EventualEqualityER$ proved above.
-/
theorem smooth_excludes_e0_reduction
    {X : Type u} [MeasurableSpace X] {E : X → X → Prop}
    (hE0 : ¬ Smooth E0) (hE : Smooth E) : ¬ BorelReducible E0 E := by
  intro hred
  exact hE0 (hE.of_reducible hred)

/-- Pulling an equivalence relation back along a map. -/
def Pullback {P : Type u} {X : Type v} (E : X → X → Prop)
    (ρ : P → X) (p q : P) : Prop :=
  E (ρ p) (ρ q)

theorem injOn_of_pairwise_not_pullback
    {P : Type u} {X : Type v} {E : X → X → Prop} {ρ : P → X} {Q : Set P}
    (hE : ∀ x, E x x)
    (hQ : Q.Pairwise fun p q ↦ ¬ Pullback E ρ p q) : InjOn ρ Q := by
  intro p hp q hq hpq
  by_contra hp_ne_q
  apply hQ hp hq hp_ne_q
  rw [Pullback, hpq]
  exact hE _

end Consequences

end
end PolishSpaceBook
