module

public import PolishSpaceBook.AssemblyProducts
public import PolishSpaceBook.PCACurrying

@[expose] public section

/-! # Exponentials, evaluation, and currying of assemblies

The underlying elements are tracked functions, not selected trackers. Each
function is realized by all of its trackers. Currying is uniformly tracked by
inserting the actual input realizer as a parameter.
-/
namespace PolishSpaceBook.Assembly
open CategoryTheory CategoryTheory.Limits
universe u v
variable {A : Type u} {K : PartialCombinatoryAlgebra A}

abbrev exponential (X Y : Assembly.{u,v} K) : Assembly.{u,v} K where
  Carrier := X ⟶ Y
  realizes r f := Tracks X Y r f
  inhabited f := f.tracked

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Each function in this underlying set has a tracker by definition, so the prescribed realizer sets give an
    assembly. Evaluation and its tracker are
    $$\evalMap:\catExp{X}{Y}\times X\to Y,\qquad
    \evalMap(f,x)=f(x),\qquad
    \mathsf e:=\PCAAbstract{w}{(\mathsf l w)(\mathsf r w)}.$$
    Indeed, if $r$ tracks $f$ and $b\Vdash_X x$, then
    $\mathsf e\PCAPair{r}{b}\simeq rb$ is defined and realizes $f(x)$.
-/
def evaluation (X Y : Assembly.{u,v} K) : product (exponential X Y) X ⟶ Y where
  toFun fx := fx.1 fx.2
  tracked := by
    refine ⟨K.evaluation,?_⟩
    rintro ⟨f,x⟩ a ⟨r,b,rfl,hr,hb⟩
    obtain ⟨c,hc,hy⟩ := hr x b hb
    exact ⟨c,(K.application_evaluation r b).trans hc,hy⟩

lemma specialized_tracks {X Y Z : Assembly.{u,v} K} (h : product Z X ⟶ Y)
    {r : A} (hr : Tracks (product Z X) Y r h) (z : Z.Carrier) {a : A} (ha : Z.realizes a z) :
    Tracks X Y (K.specialized r a) (fun x => h (z,x)) := by
  intro x b hb
  obtain ⟨c,hc,hy⟩ := hr (z,x) (K.pair a b) ⟨a,b,rfl,ha,hb⟩
  exact ⟨c,(K.application_specialized r a b).trans hc,hy⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Let $h:Z\times X\to Y$ be tracked by $r$. Define its transpose and the corresponding tracker by
    $$\overline h(z)(x):=h(z,x),\qquad
    \mathsf c_r:=\PCAAbstract{a,b}{r(\PCAPair{a}{b})}.$$
    The abstraction theorem ensures that $\mathsf c_r a$ is defined for every $a\in A$, and that
    $$(\mathsf c_r a)b\simeq r(\PCAPair{a}{b}).$$
    If $a\Vdash_Z z$ and $b\Vdash_X x$, the right side is defined and realizes $h(z,x)$.
    Thus $\mathsf c_r a$ tracks the section $x\mapsto h(z,x)$. Every $z$ has a realizer, so every such section
    belongs to $\catExp{X}{Y}$. Moreover, the same element $\mathsf c_r$ takes every realizer of $z$ to a tracker
    of that section, and hence tracks $\overline h:Z\to\catExp{X}{Y}$. This construction uses the supplied
    realizer; it does not require a computable choice of a realizer for each underlying element.
-/
def curry {X Y Z : Assembly.{u,v} K} (h : product Z X ⟶ Y) : Z ⟶ exponential X Y where
  toFun z := {
    toFun := fun x => h (z,x)
    tracked := by
      obtain ⟨r,hr⟩ := h.tracked
      obtain ⟨a,ha⟩ := Z.inhabited z
      exact ⟨K.specialized r a,specialized_tracks h hr z ha⟩ }
  tracked := by
    obtain ⟨r,hr⟩ := h.tracked
    exact ⟨K.currying r,fun z a ha =>
      ⟨K.specialized r a,K.application_currying r a,specialized_tracks h hr z ha⟩⟩

def uncurry {X Y Z : Assembly.{u,v} K} (f : Z ⟶ exponential X Y) : product Z X ⟶ Y :=
  productLift (first Z X ≫ f) (second Z X) ≫ evaluation X Y

@[simp] theorem curry_apply {X Y Z : Assembly.{u,v} K} (h : product Z X ⟶ Y)
    (z : Z.Carrier) (x : X.Carrier) : curry h z x = h (z,x) := rfl

@[simp] theorem uncurry_apply {X Y Z : Assembly.{u,v} K} (f : Z ⟶ exponential X Y)
    (z : Z.Carrier) (x : X.Carrier) : uncurry f (z,x) = f z x := rfl

@[simp] theorem uncurry_curry {X Y Z : Assembly.{u,v} K} (h : product Z X ⟶ Y) :
    uncurry (curry h) = h := by ext ⟨z,x⟩; rfl

@[simp] theorem curry_uncurry {X Y Z : Assembly.{u,v} K} (f : Z ⟶ exponential X Y) :
    curry (uncurry f) = f := by
  apply Hom.ext
  intro z
  apply Hom.ext
  intro x
  rfl

def curryEquiv (X Y Z : Assembly.{u,v} K) : (product Z X ⟶ Y) ≃ (Z ⟶ exponential X Y) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    The equation
    $$\evalMap\circ(\overline h\times\mathrm{id}_X)=h$$
    holds on underlying elements. Conversely, if a morphism $f:Z\to\catExp{X}{Y}$ satisfies
    $\evalMap\circ(f\times\mathrm{id}_X)=h$, then $f(z)(x)=h(z,x)$ for all $z,x$, so $f=\overline h$.
    Morphisms are equal when their underlying functions are equal, irrespective of their trackers.
    This proves the universal property of the exponential.
-/
/-- The evaluation equation determines the transpose as an assembly morphism. -/
theorem curry_unique {X Y Z : Assembly.{u,v} K} (h : product Z X ⟶ Y)
    (f : Z ⟶ exponential X Y) (hf : uncurry f = h) : f = curry h := by
  rw [← hf,curry_uncurry]

/-- Postcomposition on the exponential reuses evaluation and currying. -/
def exponentialMap (X : Assembly.{u,v} K) {Y Z : Assembly.{u,v} K} (g : Y ⟶ Z) :
    exponential X Y ⟶ exponential X Z := curry (evaluation X Y ≫ g)

@[simp] theorem exponentialMap_apply (X : Assembly.{u,v} K) {Y Z : Assembly.{u,v} K}
    (g : Y ⟶ Z) (f : X ⟶ Y) (x : X.Carrier) : exponentialMap X g f x = g (f x) := rfl

def exponentialFunctor (X : Assembly.{u,v} K) : Assembly.{u,v} K ⥤ Assembly.{u,v} K where
  obj := exponential X
  map := exponentialMap X
  map_id _ := by apply Hom.ext; intro f; apply Hom.ext; intro x; rfl
  map_comp _ _ := by apply Hom.ext; intro f; apply Hom.ext; intro x; rfl

end PolishSpaceBook.Assembly
