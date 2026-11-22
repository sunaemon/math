module

public import PolishSpaceBook.PCARealizabilityLogic

@[expose] public section

/-! # Guarded quantifier abstraction constructed in the PCA

The outer abstraction returns a code without evaluating the protected application.
The existing model-independent quantifier proof can therefore be instantiated.
-/
namespace PolishSpaceBook.PartialCombinatoryAlgebra
open Expression
universe u
variable {A : Type u} (K : PartialCombinatoryAlgebra A)

def lowerGuard (r : A) : A := K.abstractElement
  (.app (.app (.const r) (.var (none : Option Empty))) (.const K.k)) Empty.elim

theorem application_lowerGuard {r a e b : A}
    (hr : K.application r a = Part.some e) (he : K.application e K.k = Part.some b) :
    K.application (K.lowerGuard r) a = Part.some b := by
  rw [lowerGuard,application_abstractElement]
  simp only [Expression.eval,Option.elim_none,Part.bind_some,hr,he]

def guardBody (r : A) : Expression A (Option (Option Empty)) :=
  .app (.const r) (.var (some none))

def guardEnvironment (a : A) : Option Empty → A := fun x => x.elim a Empty.elim

def guarded (r a : A) : A := K.abstractElement (guardBody r) (guardEnvironment a)
def raiseGuard (r : A) : A := K.abstractElement ((guardBody r).abstract K) Empty.elim

theorem application_raiseGuard (r a : A) :
    K.application (K.raiseGuard r) a = Part.some (K.guarded r a) := by
  rw [raiseGuard,application_abstractElement,eval_abstract]
  rfl

theorem application_guarded (r a n : A) :
    K.application (K.guarded r a) n = K.application r a := by
  rw [guarded,application_abstractElement]
  simp only [guardBody,Expression.eval,Part.bind_some,Option.elim_some,Option.elim_none,guardEnvironment]

def quantifierAbstraction : RealizerAbstraction A where
  app r a b := K.application r a = Part.some b
  zero := K.k
  lower := K.lowerGuard
  raise := K.raiseGuard
  body := K.guarded
  lower_app := K.application_lowerGuard
  raise_outer := K.application_raiseGuard
  raise_inner := fun h n => (K.application_guarded _ _ n).trans h

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    Quantifiers along $f:I\to J$ are defined on representatives by
    $$\begin{aligned}
    (\exists_f\varphi)(j)&:=\bigcup_{f(i)=j}\varphi(i),\\
    (\forall_f\varphi)(j)&:=\{e\in A:\forall i,\ f(i)=j\Longrightarrow{}\\
    &\hspace{28mm}\forall a\in A,\ e\cdot a\downarrow\in\varphi(i)\}.
    \end{aligned}$$
    An empty union is $\emptyset$, while on an empty fiber the universal clause gives all of $A$.
    The universal clause is the guarded intersection $\bigcap_{f(i)=j}(\top\to\varphi(i))$.
-/
theorem forall_guard_iff {I J : Type*} (f : I → J)
    (φ : RealizabilityPredicate A I) (j : J) (e : A) :
    e ∈ realizabilityForall K.quantifierAbstraction f φ j ↔
      ∀ i, f i = j → e ∈ K.predImp (fun _ => Set.univ) φ i := by
  simp only [realizabilityForall,predImp,quantifierAbstraction,Set.mem_ofPred_eq,
    Set.mem_univ,forall_const]

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For the existential adjunction, the same tracker works in both directions, since membership in the union
    means membership in some fiber component. For the universal adjunction, fix $a_0:=\mathsf k$.
    If $u$ tracks $\psi\le\forall_f\varphi$, the element
    $$\PCAAbstract{a}{(ua)a_0}$$
    tracks $f^\ast\psi\le\varphi$. Conversely, if $v$ tracks the latter, use
    $$\PCAAbstract{a,b}{va}$$
    to track the former. Its first application always returns a code, and applying that code to any argument
    has exactly the same partial value as $va$. Thus the outer computation does not require $va$ to be defined;
    this is essential on empty fibers. The adjunctions imply monotonicity of both quantifiers, so they preserve
    mutual entailment and descend, with the same adjunctions, to the quotient algebras.
-/
theorem quantifier_adjunctions {I J : Type*} (f : I → J)
    (φ : RealizabilityPredicate A I) (ψ : RealizabilityPredicate A J) :
    (K.Entails (realizabilityExists f φ) ψ ↔ K.Entails φ (realizabilityReindex f ψ)) ∧
    (K.Entails (realizabilityReindex f ψ) φ ↔
      K.Entails ψ (realizabilityForall K.quantifierAbstraction f φ)) :=
  realizability_quantifier_adjunctions K.quantifierAbstraction f φ ψ

end PolishSpaceBook.PartialCombinatoryAlgebra
