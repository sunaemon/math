module

public import PolishSpaceBook.AssemblyClosed
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

/-! # Modest assemblies and closure under products, exponentials, and subobjects

The defining condition is uniqueness of the element realized by a given name.
Subobject closure uses categorical monomorphisms; their underlying functions are
injective because every element defines a tracked map from the terminal assembly.
-/
namespace PolishSpaceBook.Assembly
open CategoryTheory CategoryTheory.Limits
universe u v
variable {A : Type u} {K : PartialCombinatoryAlgebra A}

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Modest sets.** A \termdefine{modest set} is an assembly $X$ in which distinct elements have disjoint realizer sets:
    $$x \ne x' \;\Longrightarrow\; \Vdash_X x \cap \Vdash_X x' = \emptyset.$$
    Equivalently, each realizer realizes at most one element. This implies that the map
    $|X| \to \SetDifference{\PowerSet{A}}{\{\emptyset\}}$ is injective, but injectivity alone does not imply disjointness.
    \begin{mathmeta}
      \define{ModCat}
    \end{mathmeta}
    Write $\ModCat{A} \IncludedIn \AsmCat{A}$ for the full subcategory on modest sets.
-/
def Modest (X : Assembly.{u,v} K) : Prop :=
  ∀ (a : A) {x y : X.Carrier}, X.realizes a x → X.realizes a y → x = y

theorem modest_terminal : Modest (terminal.{u,v} K) := by
  intro a x y _ _
  cases x
  cases y
  rfl

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    The terminal assembly is modest because it has only one element. Suppose a realizer names two elements
    of a product of modest sets. Applying the first projection gives a common realizer of their first
    components, so those components are equal; the second projection gives equality of the second components.
    Thus the product is modest.
-/
theorem modest_product {X Y : Assembly.{u,v} K} (hx : Modest X) (hy : Modest Y) :
    Modest (product X Y) := by
  rintro a ⟨x,y⟩ ⟨x',y'⟩ ⟨b,c,rfl,hb,hc⟩ ⟨b',c',he,hb',hc'⟩
  have eb : b = b' := Part.some_injective (by
    rw [← K.application_firstProjection b c,he,K.application_firstProjection])
  have ec : c = c' := Part.some_injective (by
    rw [← K.application_secondProjection b c,he,K.application_secondProjection])
  subst b'
  subst c'
  exact Prod.ext (hx b hb hb') (hy c hc hc')

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Now let $r$ track two functions $f,g:X\to Y$, where $Y$ is modest. For each $x\in|X|$, choose any
    $a\Vdash_X x$. The single value $ra$ is defined and realizes both $f(x)$ and $g(x)$, so $f(x)=g(x)$.
    Hence $f=g$, proving that $\catExp{X}{Y}$ is modest. The product projections, evaluation, and transposes
    already constructed for assemblies are morphisms in the full subcategory. Their universal properties
    therefore restrict to that subcategory, proving that it is cartesian closed.
-/
/-- Only the codomain needs to be modest for its exponential to be modest. -/
theorem modest_exponential (X : Assembly.{u,v} K) {Y : Assembly.{u,v} K} (hy : Modest Y) :
    Modest (exponential X Y) := by
  intro r f g hf hg
  apply Hom.ext
  intro x
  obtain ⟨a,ha⟩ := X.inhabited x
  obtain ⟨b,hb,hyf⟩ := hf x a ha
  obtain ⟨c,hc,hyg⟩ := hg x a ha
  have e : b = c := Part.some_injective (hb.symm.trans hc)
  subst c
  exact hy b hyf hyg

/-- A point is tracked by a constant abstraction using any one of its realizers. -/
def point {X : Assembly.{u,v} K} (x : X.Carrier) : terminal K ⟶ X where
  toFun _ := x
  tracked := by
    obtain ⟨a,ha⟩ := X.inhabited x
    refine ⟨K.abstractElement (.const a : PartialCombinatoryAlgebra.Expression A (Option Empty))
      Empty.elim,fun _ b _ => ⟨a,?_,ha⟩⟩
    rw [K.application_abstractElement]
    rfl

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: lemma
  title: Monomorphisms of assemblies
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    An injective underlying function cancels on the left of a composition, so its morphism is a monomorphism.
    Conversely, let $m:X\to Y$ be a monomorphism and suppose $m(x)=m(x')$. Each element of $X$ gives a morphism
    from the terminal assembly: if $a$ realizes that element, the constant abstraction
    $\PCAAbstract{b}{a}$ tracks the constant function. The two morphisms corresponding to $x,x'$ become equal
    after composition with $m$, so cancellation makes them equal. Evaluating at the unique element of the
    terminal assembly gives $x=x'$.
-/
theorem mono_iff_injective {X Y : Assembly.{u,v} K} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective f := by
  constructor
  · intro hf
    let := hf
    intro x y hxy
    have h : point x ≫ f = point y ≫ f := Hom.ext (fun _ => hxy)
    have e : point x = point y := (cancel_mono f).mp h
    exact congrArg (fun g : terminal K ⟶ X => g PUnit.unit) e
  · exact ConcreteCategory.mono_of_injective f

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Finally, let $m:X\to Y$ be a monomorphism with $Y$ modest, and let $r$ track it. If $a$ realizes both
    $x$ and $x'$ in $X$, then $ra$ realizes both $m(x)$ and $m(x')$. Modesty of $Y$ gives
    $m(x)=m(x')$, and injectivity of the underlying function gives $x=x'$. Thus $X$ is modest.
-/
theorem modest_of_mono {X Y : Assembly.{u,v} K} (f : X ⟶ Y) [Mono f]
    (hy : Modest Y) : Modest X := by
  obtain ⟨r,hr⟩ := f.tracked
  intro a x y hx hy'
  obtain ⟨b,hb,hfx⟩ := hr x a hx
  obtain ⟨c,hc,hfy⟩ := hr y a hy'
  have e : b = c := Part.some_injective (hb.symm.trans hc)
  subst c
  exact (mono_iff_injective f).mp inferInstance (hy b hfx hfy)

end Assembly

universe u v

/-- The full subcategory, with the same tracked functions as morphisms. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Modest sets.** A \termdefine{modest set} is an assembly $X$ in which distinct elements have disjoint realizer sets:
    $$x \ne x' \;\Longrightarrow\; \Vdash_X x \cap \Vdash_X x' = \emptyset.$$
    Equivalently, each realizer realizes at most one element. This implies that the map
    $|X| \to \SetDifference{\PowerSet{A}}{\{\emptyset\}}$ is injective, but injectivity alone does not imply disjointness.
    \begin{mathmeta}
      \define{ModCat}
    \end{mathmeta}
    Write $\ModCat{A} \IncludedIn \AsmCat{A}$ for the full subcategory on modest sets.
-/
abbrev ModestAssembly {A : Type u} (K : PartialCombinatoryAlgebra A) :=
  CategoryTheory.ObjectProperty.FullSubcategory
    (Assembly.Modest (K := K) : CategoryTheory.ObjectProperty (Assembly.{u,v} K))

end PolishSpaceBook
