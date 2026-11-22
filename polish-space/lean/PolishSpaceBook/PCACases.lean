module

public import PolishSpaceBook.PCACombinators

@[expose] public section

/-! # Case analysis on tagged PCA pairs

The tag selects a tracker before the payload is passed to it. The unused branch
is not evaluated, so exact partial-value equalities hold for arbitrary trackers.
-/
namespace PolishSpaceBook.PartialCombinatoryAlgebra
open Expression
universe u
variable {A : Type u} (K : PartialCombinatoryAlgebra A)

def casesTracker (r s : A) : A := K.abstractElement
  (.app
    (.app (.app (.app (.const K.firstProjection) (.var (none : Option Empty))) (.const r)) (.const s))
    (.app (.const K.secondProjection) (.var none))) Empty.elim

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Given morphisms out of the two summands with trackers $r,s$, track their combined function by
    $$\PCAAbstract{w}{\bigl((\mathsf l w)r s\bigr)(\mathsf r w)}.$$
    The first projection recovers the tag. Applied to the two tracker elements, this tag returns the tracker for the
    required summand; only then is that tracker applied to the payload obtained by the second projection.
    Thus the result on the left summand is $ra$, and the result on the right summand is $sb$, with exactly the
    corresponding domain of definition. The unused branch need not be defined on that payload.
    The two injection equations and uniqueness are those of the disjoint union of sets, proving the coproduct property.
-/
theorem application_casesTracker (r s tag b : A) :
    K.application (K.casesTracker r s) (K.pair tag b) =
      ((K.application tag r).bind (fun h => K.application h s)).bind (fun f => K.application f b) := by
  rw [casesTracker,application_abstractElement]
  simp only [Expression.eval,Option.elim_none,Part.bind_some,
    application_firstProjection,application_secondProjection]

@[simp] theorem application_casesTracker_left (r s b : A) :
    K.application (K.casesTracker r s) (K.pair K.k b) = K.application r b := by
  rw [application_casesTracker,K.k_law,Part.bind_some]

@[simp] theorem application_casesTracker_right (r s b : A) :
    K.application (K.casesTracker r s) (K.pair K.secondSelector b) = K.application s b := by
  rw [application_casesTracker,application_secondSelector,Part.bind_some]

end PolishSpaceBook.PartialCombinatoryAlgebra
