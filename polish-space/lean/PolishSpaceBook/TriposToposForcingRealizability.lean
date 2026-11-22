module

public import PolishSpaceBook.DomainTheoryQuasiPolishSpaces
public import PolishSpaceBook.LambdaIndexPCA

@[expose] public section

/-!
# Tripos-to-topos: forcing and realizability

Formalization targets for `polish-space/src/polish-space-book/tripos-topos-forcing-realizability.md`.

`LambdaIndexPCA` constructs the concrete partial combinatory algebra from lambda
indices. The concrete quantifier transformations are supplied by `LambdaRealizerAbstraction`.
`LambdaRealizerLogic` supplies the propositional calculations;
`LambdaRealizabilityFibers` and `LambdaRealizabilityTripos` construct the quotient
Heyting algebras and the full Set-based realizability tripos.
`LambdaRealizabilityPER` constructs the realizer-valued PER category with
uniform functional relations. `LambdaRealizabilityProducts` and
`LambdaRealizabilityEqualizers` give terminal objects, binary products, predicate
restrictions, and equalizers with their universal properties, hence finite limits.
`LambdaRealizabilitySubobjects` presents every monomorphism as a predicate restriction.
`LambdaRealizabilityTruthValues` constructs the truth-value PER and identifies its
arrows with strict extensional predicates modulo uniform equivalence.
`LambdaRealizabilityClassifier` constructs the truth relation, proves the classifying
pullback and uniqueness for all monomorphisms, and packages the canonical subobject
classifier. `LambdaRealizabilityFunctionData` constructs the candidate function PER
with numerical witnesses of the four functional-relation conditions.
`LambdaRealizabilityEvaluation` constructs its evaluation arrow.
`LambdaRealizabilityCurrying` and `LambdaRealizabilityUncurrying` construct uniform
currying and prove the exponential universal property.
`LambdaRealizabilityExponentials` packages the canonical cartesian monoidal and
monoidal closed structures.
This file isolates the corrected
realizability-quantifier calculation.  `RealizerAbstraction` records exactly
the two abstraction operations used in the book proof: evaluation of a
returned code at `0`, and dummy abstraction that returns a code before
evaluating its body.  The resulting theorem checks both quantifier
adjunctions; the concrete categorical packaging is supplied by those later modules.
-/

namespace PolishSpaceBook

open Set

universe u v w

section RealizabilityQuantifiers

/-- Abstract partial application together with the two code transformations
used in the guarded universal-quantifier adjunction. -/
structure RealizerAbstraction (R : Type u) where
  app : R → R → R → Prop
  zero : R
  lower : R → R
  raise : R → R
  body : R → R → R
  lower_app : ∀ {u a e b}, app u a e → app e zero b → app (lower u) a b
  raise_outer : ∀ v a, app (raise v) a (body v a)
  raise_inner : ∀ {v a b}, app v a b → ∀ n, app (body v a) n b

/-- A realizability predicate on `I` with realizers in `R`. -/
abbrev RealizabilityPredicate (R : Type u) (I : Type v) :=
  I → Set R

/-- Uniform reducibility, expressed using a single partial-application code. -/
def RealizabilityReducible {R : Type u} {I : Type v}
    (K : RealizerAbstraction R)
    (φ ψ : RealizabilityPredicate R I) : Prop :=
  ∃ e : R, ∀ i a, a ∈ φ i → ∃ b, K.app e a b ∧ b ∈ ψ i

/-- Reindexing of predicates along a function. -/
def realizabilityReindex {R : Type u} {I : Type v} {J : Type w}
    (f : I → J) (ψ : RealizabilityPredicate R J) :
    RealizabilityPredicate R I :=
  fun i ↦ ψ (f i)

/-- The unguarded union over a fiber gives the existential quantifier. -/
def realizabilityExists {R : Type u} {I : Type v} {J : Type w}
    (f : I → J) (φ : RealizabilityPredicate R I) :
    RealizabilityPredicate R J :=
  fun j ↦ {a | ∃ i, f i = j ∧ a ∈ φ i}

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    Quantifiers along $f:I\to J$ are
    $$
    (\exists_f\varphi)(j)=\bigcup_{f(i)=j}\varphi(i),
    $$
    and
    $$
    \begin{aligned}
    (\forall_f\varphi)(j)
    &=\left\{e\in\NN:
      \begin{array}{l}
        \forall i\in I,\ f(i)=j\Longrightarrow{}\\
        \qquad\forall n\in\NN,\ e\cdot n\downarrow\in\varphi(i)
      \end{array}
    \right\}\\
    &=\bigcap_{f(i)=j}\bigl(\top\to\varphi(i)\bigr).
    \end{aligned}
    $$
-/
/-- The right adjoint uses a guarded intersection: a member is itself a code
defined on every realizer whenever the fiber is nonempty. -/
def realizabilityForall {R : Type u} {I : Type v} {J : Type w}
    (K : RealizerAbstraction R) (f : I → J)
    (φ : RealizabilityPredicate R I) : RealizabilityPredicate R J :=
  fun j ↦ {e | ∀ i, f i = j → ∀ n, ∃ b, K.app e n b ∧ b ∈ φ i}

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The empty union is $\emptyset$. On an empty fiber the condition defining $\forall_f\varphi$ is vacuous, so its value is
    $\NN$. The guard $\top\to-$ is essential: it records that the output realizer must itself be defined on every natural
    number whenever the fiber is nonempty.
-/
theorem realizabilityForall_eq_univ_of_empty_fiber
    {R : Type u} {I : Type v} {J : Type w}
    (K : RealizerAbstraction R) (f : I → J)
    (φ : RealizabilityPredicate R I) (j : J)
    (h : ∀ i, f i ≠ j) :
    realizabilityForall K f φ j = (Set.univ : Set R) := by
  ext e
  simp only [realizabilityForall, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro i hfi
  exact (h i hfi).elim

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  kind: lemma
  title: Realizability quantifier adjunctions
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For the existential adjunction, the same tracker works in both directions: an element of
    $(\exists_f\varphi)(j)$ is already an element of some $\varphi(i)$ with $f(i)=j$.

    For the universal adjunction, use the maps $\ell,r,d$ from the preceding lemma. Suppose $u$ tracks
    $\psi\le\forall_f\varphi$. If $f(i)=j$ and $a\in\psi(j)$, then $u\cdot a$ is an index that sends every
    $n\in\NN$ to an element of $\varphi(i)$. Evaluating it at $0$ shows that $\ell(u)$ tracks
    $f^\ast\psi\le\varphi$. Conversely, if $v$ tracks $f^\ast\psi\le\varphi$, then $r(v)\cdot a=d(v,a)$
    is defined for every $a$. Whenever $f(i)=j$ and $a\in\psi(j)$, the value $v\cdot a$ belongs to $\varphi(i)$,
    so $d(v,a)$ sends every $n$ to that value. Hence $r(v)$ tracks $\psi\le\forall_f\varphi$.
    On an empty fiber, the outer application still returns $d(v,a)$, while the defining condition for the universal
    quantifier imposes no requirement on its outputs.
    \end{proof}
-/
theorem realizability_quantifier_adjunctions
    {R : Type u} {I : Type v} {J : Type w}
    (K : RealizerAbstraction R) (f : I → J)
    (φ : RealizabilityPredicate R I) (ψ : RealizabilityPredicate R J) :
    (RealizabilityReducible K (realizabilityExists f φ) ψ ↔
      RealizabilityReducible K φ (realizabilityReindex f ψ)) ∧
    (RealizabilityReducible K (realizabilityReindex f ψ) φ ↔
      RealizabilityReducible K ψ (realizabilityForall K f φ)) := by
  constructor
  · constructor
    · rintro ⟨e, he⟩
      refine ⟨e, ?_⟩
      intro i a ha
      exact he (f i) a ⟨i, rfl, ha⟩
    · rintro ⟨e, he⟩
      refine ⟨e, ?_⟩
      intro j a ha
      obtain ⟨i, hfi, hai⟩ := ha
      obtain ⟨b, hab, hb⟩ := he i a hai
      exact ⟨b, hab, by simpa [realizabilityReindex, hfi] using hb⟩
  · constructor
    · rintro ⟨v, hv⟩
      refine ⟨K.raise v, ?_⟩
      intro j a ha
      refine ⟨K.body v a, K.raise_outer v a, ?_⟩
      intro i hfi n
      have hai : a ∈ realizabilityReindex f ψ i := by
        simpa [realizabilityReindex, hfi] using ha
      obtain ⟨b, hvab, hb⟩ := hv i a hai
      exact ⟨b, K.raise_inner hvab n, hb⟩
    · rintro ⟨u, hu⟩
      refine ⟨K.lower u, ?_⟩
      intro i a ha
      have ha' : a ∈ ψ (f i) := by
        simpa [realizabilityReindex] using ha
      obtain ⟨e, hua, he⟩ := hu (f i) a ha'
      obtain ⟨b, heb, hb⟩ := he i rfl K.zero
      exact ⟨b, K.lower_app hua heb, hb⟩

end RealizabilityQuantifiers

end PolishSpaceBook
