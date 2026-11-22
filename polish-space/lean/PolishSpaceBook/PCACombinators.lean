module

public import PolishSpaceBook.PCAAbstraction

@[expose] public section

/-! # Identity, composition and pairing from PCA abstraction -/
namespace PolishSpaceBook.PartialCombinatoryAlgebra
open Expression
universe u v
variable {A : Type u} (K : PartialCombinatoryAlgebra A)

def abstractElement {α : Type v} (t : Expression A (Option α)) (ρ : α → A) : A :=
  ((t.abstract K).eval K ρ).get (Expression.abstract_defined K t ρ)

theorem application_abstractElement {α : Type v} (t : Expression A (Option α)) (ρ : α → A) (a : A) :
    K.application (K.abstractElement t ρ) a = t.eval K (fun x => x.elim a ρ) := by
  have h := Expression.abstract_apply K t ρ a
  rw [← Part.some_get (Expression.abstract_defined K t ρ),Part.bind_some] at h
  exact h

theorem eval_abstract {α : Type v} (t : Expression A (Option α)) (ρ : α → A) :
    ((t.abstract K).eval K ρ) = Part.some (K.abstractElement t ρ) :=
  (Part.some_get (Expression.abstract_defined K t ρ)).symm

def identity : A := K.abstractElement (.var (none : Option Empty)) Empty.elim

@[simp] theorem application_identity (a : A) : K.application K.identity a = Part.some a := by
  rw [identity,application_abstractElement]
  rfl

def composition (r s : A) : A :=
  K.abstractElement (.app (.const s) (.app (.const r) (.var (none : Option Empty)))) Empty.elim

theorem application_composition (r s a : A) :
    K.application (K.composition r s) a = (K.application r a).bind (K.application s) := by
  rw [composition,application_abstractElement]
  simp only [Expression.eval,Part.bind_some,Option.elim_none]

def pairOne (a : A) : Option Empty → A := fun x => x.elim a Empty.elim
def pairTwo (a b : A) : Option (Option Empty) → A := fun x => x.elim b (pairOne a)

/-- The three variables are the two components and the final selector. -/
def pairBody : Expression A (Option (Option (Option Empty))) :=
  .app (.app (.var none) (.var (some (some none)))) (.var (some none))

def pair (a b : A) : A := K.abstractElement pairBody (pairTwo a b)
def pairLeft (a : A) : A := K.abstractElement (pairBody.abstract K) (pairOne a)
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Use abstraction to set
    $$\mathsf p:=\PCAAbstract{a,b,c}{cab},\qquad
    \PCAPair{a}{b}:=\mathsf p a b.$$
    The proper-prefix clause of the abstraction theorem makes every pair defined, and its computation rule gives
    $$\PCAPair{a}{b}\,c\simeq cab.$$
    Thus the same element constructs pairs for every pair of inputs.
-/
def pairProgram : A := K.abstractElement ((pairBody.abstract K).abstract K) Empty.elim

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: lemma
  title: PCA pairing
-/
@[simp] theorem application_pairProgram (a : A) :
    K.application K.pairProgram a = Part.some (K.pairLeft a) := by
  rw [pairProgram,application_abstractElement,eval_abstract]
  rfl

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: lemma
  title: PCA pairing
-/
@[simp] theorem application_pairLeft (a b : A) :
    K.application (K.pairLeft a) b = Part.some (K.pair a b) := by
  rw [pairLeft,application_abstractElement,eval_abstract]
  rfl


/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: lemma
  title: PCA pairing
-/
theorem application_pair (a b c : A) :
    K.application (K.pair a b) c = (K.application c a).bind (fun d => K.application d b) := by
  rw [pair,application_abstractElement]
  simp only [pairBody,Expression.eval,Part.bind_some,Option.elim_none,Option.elim_some,pairTwo,pairOne]

/-- The selector returning its second argument, defined before either argument is supplied. -/
def secondSelector : A := (K.application K.k K.identity).get (K.k_defined K.identity)

theorem application_secondSelector (a b : A) :
    (K.application K.secondSelector a).bind (fun c => K.application c b) = Part.some b := by
  have h := K.k_law K.identity a
  rw [← Part.some_get (K.k_defined K.identity),Part.bind_some] at h
  change K.application K.secondSelector a = Part.some K.identity at h
  rw [h,Part.bind_some,application_identity]

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Set $\mathsf q:=\mathsf k\mathsf i$. The constant-function and identity laws imply
    $\mathsf k a b=a$ and $\mathsf q a b=b$. Hence
    $$\mathsf l:=\PCAAbstract{w}{w\mathsf k},\qquad
    \mathsf r:=\PCAAbstract{w}{w\mathsf q}$$
    have the required projection laws. The selector is applied to the two components only after the encoded pair
    receives it; no value of an unrelated application is required to construct the pair.
-/
def firstProjection : A :=
  K.abstractElement (.app (.var (none : Option Empty)) (.const K.k)) Empty.elim

def secondProjection : A :=
  K.abstractElement (.app (.var (none : Option Empty)) (.const K.secondSelector)) Empty.elim

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: lemma
  title: PCA pairing
-/
@[simp] theorem application_firstProjection (a b : A) :
    K.application K.firstProjection (K.pair a b) = Part.some a := by
  rw [firstProjection,application_abstractElement]
  simp only [Expression.eval,Part.bind_some,Option.elim_none]
  rw [application_pair,K.k_law]

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: lemma
  title: PCA pairing
-/
@[simp] theorem application_secondProjection (a b : A) :
    K.application K.secondProjection (K.pair a b) = Part.some b := by
  rw [secondProjection,application_abstractElement]
  simp only [Expression.eval,Part.bind_some,Option.elim_none]
  rw [application_pair,application_secondSelector]

/-- Pair two tracked outputs on the same input. -/
def paired (r s : A) : A := K.abstractElement
  (.app (.app (.const K.pairProgram) (.app (.const r) (.var (none : Option Empty))))
    (.app (.const s) (.var none))) Empty.elim

theorem application_paired {r s a b c : A}
    (hr : K.application r a = Part.some b) (hs : K.application s a = Part.some c) :
    K.application (K.paired r s) a = Part.some (K.pair b c) := by
  rw [paired,application_abstractElement]
  simp only [Expression.eval,Part.bind_some,Option.elim_none,hr,hs,
    application_pairProgram,application_pairLeft]

end PolishSpaceBook.PartialCombinatoryAlgebra
