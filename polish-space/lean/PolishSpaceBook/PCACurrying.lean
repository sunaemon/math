module

public import PolishSpaceBook.PCACombinators

@[expose] public section

/-! # Evaluation and uniform parameter insertion in a PCA -/
namespace PolishSpaceBook.PartialCombinatoryAlgebra
open Expression
universe u
variable {A : Type u} (K : PartialCombinatoryAlgebra A)

def evaluation : A := K.abstractElement
  (.app (.app (.const K.firstProjection) (.var (none : Option Empty)))
    (.app (.const K.secondProjection) (.var none))) Empty.elim

theorem application_evaluation (r a : A) :
    K.application K.evaluation (K.pair r a) = K.application r a := by
  rw [evaluation,application_abstractElement]
  simp only [Expression.eval,Part.bind_some,Option.elim_none,
    application_firstProjection,application_secondProjection]

def curryEnvironment (a : A) : Option Empty → A := fun x => x.elim a Empty.elim

def curryBody (r : A) : Expression A (Option (Option Empty)) :=
  .app (.const r) (.app (.app (.const K.pairProgram) (.var (some none))) (.var none))

def specialized (r a : A) : A := K.abstractElement (K.curryBody r) (curryEnvironment a)
def currying (r : A) : A := K.abstractElement ((K.curryBody r).abstract K) Empty.elim

/-- Producing a tracker with one parameter fixed is total, even when its later computation is not. -/
theorem application_currying (r a : A) :
    K.application (K.currying r) a = Part.some (K.specialized r a) := by
  rw [currying,application_abstractElement,eval_abstract]
  rfl

theorem application_specialized (r a b : A) :
    K.application (K.specialized r a) b = K.application r (K.pair a b) := by
  rw [specialized,application_abstractElement]
  simp only [curryBody,Expression.eval,Part.bind_some,Option.elim_none,Option.elim_some,curryEnvironment,
    application_pairProgram,application_pairLeft]

end PolishSpaceBook.PartialCombinatoryAlgebra
