module

public import PolishSpaceBook.LambdaRealizabilityFibers
public import PolishSpaceBook.SetTriposCore

@[expose] public section

/-! # The concrete realizability tripos: quantifiers, base change, and generic predicate -/
namespace PolishSpaceBook.LambdaIndexPCA

open CategoryTheory Limits Opposite
universe u

/-- The guard uses the very same lambda-index application as Heyting implication. -/
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
theorem realizabilityForall_guard_iff {I J : Type*} (f : I → J)
    (φ : RealizabilityPredicate ℕ I) (j : J) (e : ℕ) :
    e ∈ realizabilityForall realizerAbstraction f φ j ↔
      ∀ i, f i = j → e ∈ realizabilityImp (realizabilityTop I) φ i := by
  simp only [realizabilityForall, realizabilityImp, realizabilityTop, Set.mem_ofPred_eq,
    Set.mem_univ, forall_const, realizerAbstraction_app]

theorem exists_reduces_mono {I J : Type*} (f : I → J)
    {φ ψ : RealizabilityPredicate ℕ I} (h : Reduces φ ψ) :
    Reduces (realizabilityExists f φ) (realizabilityExists f ψ) := by
  apply (lambda_realizability_quantifier_adjunctions f φ (realizabilityExists f ψ)).1.mpr
  exact reduces_trans h
    ((lambda_realizability_quantifier_adjunctions f ψ (realizabilityExists f ψ)).1.mp (reduces_refl _))

theorem forall_reduces_mono {I J : Type*} (f : I → J)
    {φ ψ : RealizabilityPredicate ℕ I} (h : Reduces φ ψ) :
    Reduces (realizabilityForall realizerAbstraction f φ) (realizabilityForall realizerAbstraction f ψ) := by
  apply (lambda_realizability_quantifier_adjunctions f ψ
    (realizabilityForall realizerAbstraction f φ)).2.mp
  exact reduces_trans
    ((lambda_realizability_quantifier_adjunctions f φ
      (realizabilityForall realizerAbstraction f φ)).2.mpr (reduces_refl _)) h

def fiberExists {I J : Type*} (f : I → J) : RealizabilityFiber I →o RealizabilityFiber J where
  toFun := Quotient.map (fun φ => ⟨realizabilityExists f φ.val⟩)
    (fun _ _ h => ⟨exists_reduces_mono f h.1, exists_reduces_mono f h.2⟩)
  monotone' a b := Quotient.inductionOn₂ a b fun _ _ h => exists_reduces_mono f h

def fiberForall {I J : Type*} (f : I → J) : RealizabilityFiber I →o RealizabilityFiber J where
  toFun := Quotient.map (fun φ => ⟨realizabilityForall realizerAbstraction f φ.val⟩)
    (fun _ _ h => ⟨forall_reduces_mono f h.1, forall_reduces_mono f h.2⟩)
  monotone' a b := Quotient.inductionOn₂ a b fun _ _ h => forall_reduces_mono f h

@[simp] theorem fiberExists_class {I J : Type*} (f : I → J) (φ : RealizabilityPredicate ℕ I) :
    fiberExists f (predicateClass φ) = predicateClass (realizabilityExists f φ) := rfl

@[simp] theorem fiberForall_class {I J : Type*} (f : I → J) (φ : RealizabilityPredicate ℕ I) :
    fiberForall f (predicateClass φ) = predicateClass (realizabilityForall realizerAbstraction f φ) := rfl

theorem fiber_exists_adjunction {I J : Type*} (f : I → J) :
    GaloisConnection (fiberExists f) (fiberReindex f) := by
  intro a b
  exact Quotient.inductionOn₂ a b fun φ ψ =>
    (lambda_realizability_quantifier_adjunctions f φ.val ψ.val).1

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    The quantifier adjunctions also pass to the quotient. To check independence of representatives, suppose
    $\varphi\le\psi$. The unit and counit of the already proved adjunctions give
    $$\varphi\le\psi\le f^{\ast}\exists_f\psi,\qquad
    f^{\ast}\forall_f\varphi\le\varphi\le\psi.$$
    Applying those adjunctions yields
    $$\exists_f\varphi\le\exists_f\psi,\qquad\forall_f\varphi\le\forall_f\psi.$$
    Thus both quantifiers preserve mutual reducibility and define monotone maps on the quotient fibers. Their
    adjunction equivalences are unchanged on representatives, so
    $$\exists_f\dashv f^{\ast}\dashv\forall_f$$
    holds on the Heyting algebras themselves.
-/
theorem fiber_forall_adjunction {I J : Type*} (f : I → J) :
    GaloisConnection (fiberReindex f) (fiberForall f) := by
  intro a b
  exact Quotient.inductionOn₂ a b fun ψ φ =>
    (lambda_realizability_quantifier_adjunctions f φ.val ψ.val).2

/-- The pullback property identifies the fibers by an actual bijection. -/
def pullbackFiberMap {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I}
    (h : IsPullback g' f' f g) (j : J') :
    {i' // f' i' = j} → {i // f i = g j} := fun i' =>
  ⟨g' i'.val, (ConcreteCategory.congr_hom h.w i'.val).trans (congrArg g i'.property)⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For Beck--Chevalley, take any pullback square
    $$\begin{array}{ccc}
    I'\! & \xrightarrow{g'} & I\\
    {\scriptstyle f'}\downarrow & & \downarrow{\scriptstyle f}\\
    J'\! & \xrightarrow{g} & J .
    \end{array}$$
    For each $j'\in J'$, the map $i'\mapsto g'(i')$ gives a bijection
    $$\{i'\in I':f'(i')=j'\}\longrightarrow\{i\in I:f(i)=g(j')\}.$$
    Commutativity makes this map well defined. For each $i$ in the right-hand fiber, the pullback property gives a unique
    $i'$ with $g'(i')=i$ and $f'(i')=j'$, proving bijectivity. Consequently, for every realizer $a$,
    $$
    \begin{aligned}
    a\in(g^{\ast}\exists_f\varphi)(j')
    &\Longleftrightarrow\exists i'\in I',\\
    &\qquad f'(i')=j'\ \text{and}\ a\in\varphi(g'(i')),\\
    a\in(g^{\ast}\forall_f\varphi)(j')
    &\Longleftrightarrow\forall i'\in I',\ f'(i')=j'\Longrightarrow{}\\
    &\qquad\forall n\in\NN,\ a\cdot n\downarrow\in\varphi(g'(i')).
    \end{aligned}
    $$
    These are exactly the membership conditions for $\exists_{f'}g'^{\ast}\varphi$ and
    $\forall_{f'}g'^{\ast}\varphi$. The guard quantifies over the same natural numbers on both sides; the argument also
    covers empty fibers. Thus both Beck--Chevalley equalities hold already as equalities of predicates, and therefore
    on their classes.
-/
theorem pullback_fiber_bijective {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I}
    (h : IsPullback g' f' f g) (j : J') : Function.Bijective (pullbackFiberMap h j) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact Types.ext_of_isPullback h (congrArg Subtype.val hab) (a.property.trans b.property.symm)
  · intro i
    obtain ⟨i', hg', hf'⟩ := Types.exists_of_isPullback h i.val j i.property
    exact ⟨⟨i', hf'⟩, Subtype.ext hg'⟩

/-- In a pullback, the existential formulas agree already before quotienting. -/
theorem exists_beckChevalley_raw {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I}
    (h : IsPullback g' f' f g) (φ : RealizabilityPredicate ℕ I) :
    realizabilityReindex g (realizabilityExists f φ) =
      realizabilityExists f' (realizabilityReindex g' φ) :=
  realizabilityExists_baseChange h φ

/-- The guard is preserved under the same fiber correspondence, including empty fibers. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For Beck--Chevalley, take any pullback square
    $$\begin{array}{ccc}
    I'\! & \xrightarrow{g'} & I\\
    {\scriptstyle f'}\downarrow & & \downarrow{\scriptstyle f}\\
    J'\! & \xrightarrow{g} & J .
    \end{array}$$
    For each $j'\in J'$, the map $i'\mapsto g'(i')$ gives a bijection
    $$\{i'\in I':f'(i')=j'\}\longrightarrow\{i\in I:f(i)=g(j')\}.$$
    Commutativity makes this map well defined. For each $i$ in the right-hand fiber, the pullback property gives a unique
    $i'$ with $g'(i')=i$ and $f'(i')=j'$, proving bijectivity. Consequently, for every realizer $a$,
    $$
    \begin{aligned}
    a\in(g^{\ast}\exists_f\varphi)(j')
    &\Longleftrightarrow\exists i'\in I',\\
    &\qquad f'(i')=j'\ \text{and}\ a\in\varphi(g'(i')),\\
    a\in(g^{\ast}\forall_f\varphi)(j')
    &\Longleftrightarrow\forall i'\in I',\ f'(i')=j'\Longrightarrow{}\\
    &\qquad\forall n\in\NN,\ a\cdot n\downarrow\in\varphi(g'(i')).
    \end{aligned}
    $$
    These are exactly the membership conditions for $\exists_{f'}g'^{\ast}\varphi$ and
    $\forall_{f'}g'^{\ast}\varphi$. The guard quantifies over the same natural numbers on both sides; the argument also
    covers empty fibers. Thus both Beck--Chevalley equalities hold already as equalities of predicates, and therefore
    on their classes.
-/
theorem forall_beckChevalley_raw {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I}
    (h : IsPullback g' f' f g) (φ : RealizabilityPredicate ℕ I) :
    realizabilityReindex g (realizabilityForall realizerAbstraction f φ) =
      realizabilityForall realizerAbstraction f' (realizabilityReindex g' φ) :=
  realizabilityForall_baseChange realizerAbstraction h φ

theorem fiber_exists_beckChevalley {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I}
    (h : IsPullback g' f' f g) (a : RealizabilityFiber I) :
    fiberReindex g (fiberExists f a) = fiberExists f' (fiberReindex g' a) := by
  refine Quotient.inductionOn a fun φ => ?_
  exact congrArg predicateClass (exists_beckChevalley_raw h φ.val)

theorem fiber_forall_beckChevalley {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I}
    (h : IsPullback g' f' f g) (a : RealizabilityFiber I) :
    fiberReindex g (fiberForall f a) = fiberForall f' (fiberReindex g' a) := by
  refine Quotient.inductionOn a fun φ => ?_
  exact congrArg predicateClass (forall_beckChevalley_raw h φ.val)

/-- The universe lift only places the power set of natural numbers in the chosen base universe. -/
def genericRealizabilityPredicate : RealizabilityPredicate ℕ (ULift.{u} (Set ℕ)) := fun S => S.down

theorem generic_realizability_raw {I : Type u} (φ : RealizabilityPredicate ℕ I) :
    realizabilityReindex (fun i => (⟨φ i⟩ : ULift.{u} (Set ℕ))) genericRealizabilityPredicate = φ := rfl

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Finally, put $\Sigma=\PowerSet{\NN}$ and define the predicate
    $$\sigma(S)=S\qquad(S\IncludedIn\NN).$$
    For any representative $\varphi:I\to\PowerSet{\NN}$, its classifying map is $i\mapsto\varphi(i)$, and reindexing
    $\sigma$ along this map gives $\varphi$ exactly. Given an element of the quotient fiber, choose a representative and
    use this classifier. Thus the class of $\sigma$ is a generic predicate. Together with the functor, adjunctions, and
    base-change equalities above, this proves all the tripos axioms.
    \end{proof}
-/
theorem generic_realizability_fiber {I : Type u} (a : RealizabilityFiber I) :
    ∃ f : I → ULift.{u} (Set ℕ),
      fiberReindex f (predicateClass genericRealizabilityPredicate) = a := by
  refine Quotient.inductionOn a fun φ => ?_
  exact ⟨fun i => ⟨φ.val i⟩, rfl⟩

/-- A Set-based tripos, using canonical functors, Heyting algebras, adjunctions,
and categorical pullback squares. -/
abbrev SetTripos := PolishSpaceBook.SetTripos.{u}

/-- All tripos data and laws are supplied by the concrete lambda-index application. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  kind: proposition
  title: Realizability tripos
-/
def lambdaRealizabilityTripos : SetTripos.{u} where
  predicates := realizabilityIndexedHeyting
  existsAlong := fiberExists
  forallAlong := fiberForall
  exists_adjunction := fiber_exists_adjunction
  forall_adjunction := fiber_forall_adjunction
  exists_beckChevalley := fiber_exists_beckChevalley
  forall_beckChevalley := fiber_forall_beckChevalley
  genericObject := ULift.{u} (Set ℕ)
  genericPredicate := predicateClass genericRealizabilityPredicate
  generic := generic_realizability_fiber

end PolishSpaceBook.LambdaIndexPCA
