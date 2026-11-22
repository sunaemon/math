module

public import PolishSpaceBook.PCARealizabilityFibers
public import PolishSpaceBook.SetTriposCore

@[expose] public section

/-! # The realizability tripos over an arbitrary PCA

The quotient quantifiers use antisymmetrization of the adjoint monotone maps.
Base change is the shared set-theoretic fiber argument, with the same guard.
-/
namespace PolishSpaceBook.PartialCombinatoryAlgebra
open CategoryTheory Limits Opposite
universe u
variable {A : Type u} (K : PartialCombinatoryAlgebra A)

def indexedExists {I J : Type u} (f : I → J) (φ : IndexedPredicate K I) : IndexedPredicate K J :=
  ⟨realizabilityExists f φ.val⟩

def indexedForall {I J : Type u} (f : I → J) (φ : IndexedPredicate K I) : IndexedPredicate K J :=
  ⟨realizabilityForall K.quantifierAbstraction f φ.val⟩

def indexedReindex {I J : Type u} (f : I → J) (φ : IndexedPredicate K J) : IndexedPredicate K I :=
  ⟨realizabilityReindex f φ.val⟩

theorem indexed_exists_adjunction {I J : Type u} (f : I → J) :
    GaloisConnection (K.indexedExists f) (K.indexedReindex f) :=
  fun φ ψ => (K.quantifier_adjunctions f φ.val ψ.val).1

theorem indexed_forall_adjunction {I J : Type u} (f : I → J) :
    GaloisConnection (K.indexedReindex f) (K.indexedForall f) :=
  fun ψ φ => (K.quantifier_adjunctions f φ.val ψ.val).2

def fiberExists {I J : Type u} (f : I → J) : K.Fiber I →o K.Fiber J :=
  (⟨K.indexedExists f,(K.indexed_exists_adjunction f).monotone_l⟩ :
    IndexedPredicate K I →o IndexedPredicate K J).antisymmetrization

def fiberForall {I J : Type u} (f : I → J) : K.Fiber I →o K.Fiber J :=
  (⟨K.indexedForall f,(K.indexed_forall_adjunction f).monotone_u⟩ :
    IndexedPredicate K I →o IndexedPredicate K J).antisymmetrization

theorem fiber_exists_adjunction {I J : Type u} (f : I → J) :
    GaloisConnection (K.fiberExists f) (K.fiberReindex f) := by
  intro a b
  exact Quotient.inductionOn₂ a b (fun φ ψ => (K.quantifier_adjunctions f φ.val ψ.val).1)

theorem fiber_forall_adjunction {I J : Type u} (f : I → J) :
    GaloisConnection (K.fiberReindex f) (K.fiberForall f) := by
  intro a b
  exact Quotient.inductionOn₂ a b (fun ψ φ => (K.quantifier_adjunctions f φ.val ψ.val).2)

theorem fiber_exists_beckChevalley {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I}
    (h : IsPullback g' f' f g) (a : K.Fiber I) :
    K.fiberReindex g (K.fiberExists f a) = K.fiberExists f' (K.fiberReindex g' a) := by
  refine Quotient.inductionOn a (fun φ => ?_)
  exact congrArg K.predicateClass (realizabilityExists_baseChange h φ.val)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For a pullback square with $f:I\to J$, $g:J'\to J$, $f':I'\to J'$, and $g':I'\to I$, the map
    $i'\mapsto g'(i')$ identifies the fiber of $f'$ over $j'$ with the fiber of $f$ over $g(j')$.
    Replacing one fiber by the other leaves the union clause unchanged. It also leaves the guarded universal
    clause unchanged, since the guard ranges over the same $A$ on both sides. Hence
    $$g^\ast\exists_f\varphi=\exists_{f'}g'^\ast\varphi,\qquad
     g^\ast\forall_f\varphi=\forall_{f'}g'^\ast\varphi.$$
    These equalities hold already on predicates, including empty fibers, and therefore on their classes.
-/
theorem fiber_forall_beckChevalley {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I}
    (h : IsPullback g' f' f g) (a : K.Fiber I) :
    K.fiberReindex g (K.fiberForall f a) = K.fiberForall f' (K.fiberReindex g' a) := by
  refine Quotient.inductionOn a (fun φ => ?_)
  exact congrArg K.predicateClass (realizabilityForall_baseChange K.quantifierAbstraction h φ.val)

def genericPredicate : RealizabilityPredicate A (Set A) := fun S => S

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Finally, put $\sigma(S):=S$ for $S\in\PowerSet{A}$. For any predicate $\varphi$, the map
    $i\mapsto\varphi(i)$ pulls $\sigma$ back to $\varphi$ exactly. Every quotient class has a representative,
    so the class of $\sigma$ is generic. This proves the tripos axioms.
-/
theorem generic_fiber {I : Type u} (a : K.Fiber I) :
    ∃ f : I → Set A, K.fiberReindex f (K.predicateClass genericPredicate) = a := by
  refine Quotient.inductionOn a (fun φ => ?_)
  exact ⟨φ.val,rfl⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Realizability tripos over a PCA
-/
def realizabilityTripos : SetTripos.{u} where
  predicates := K.indexedHeyting
  existsAlong := K.fiberExists
  forallAlong := K.fiberForall
  exists_adjunction := K.fiber_exists_adjunction
  forall_adjunction := K.fiber_forall_adjunction
  exists_beckChevalley := K.fiber_exists_beckChevalley
  forall_beckChevalley := K.fiber_forall_beckChevalley
  genericObject := Set A
  genericPredicate := K.predicateClass genericPredicate
  generic := K.generic_fiber

end PolishSpaceBook.PartialCombinatoryAlgebra
