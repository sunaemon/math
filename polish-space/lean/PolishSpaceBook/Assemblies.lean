module

public import PolishSpaceBook.PCACombinators
public import Mathlib.CategoryTheory.ConcreteCategory.Basic

@[expose] public section

/-! # Assemblies and tracked functions

Trackers occur only in a proposition. Equality of morphisms is equality of
underlying functions; identity and composition use explicit PCA abstractions.
-/
namespace PolishSpaceBook
open CategoryTheory
universe u v
variable {A : Type u}

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{AsmCat,PCAPair}
    \end{mathmeta}
    Fix a PCA $A$. The category of \termuseas{assembly}{assemblies} $\AsmCat{A}$ is the first realizability category built
    over $A$ and is where the external concept of "set with realizers" lives intrinsically.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Assemblies.** An \termdefine{assembly} $X = (|X|, \Vdash_X)$ is a set $|X|$ — its \termdefine{underlying set} —
    together with a function
    $$\Vdash_X \;:\; |X| \to \SetDifference{\PowerSet{A}}{\{\emptyset\}}$$
    assigning to each element $x \in |X|$ a non-empty set $\Vdash_X x \IncludedIn A$ of
    \termdefineas{assembly realizer}{realizers} of $x$. We read $a \Vdash_X x$ as "$a$ realizes $x$" or "$a$ is a name for
    $x$." The non-emptiness
    condition is essential: every element must be realizable.
-/
structure Assembly (K : PartialCombinatoryAlgebra A) where
  Carrier : Type v
  realizes : A → Carrier → Prop
  inhabited : ∀ x, ∃ a, realizes a x

namespace Assembly
variable {K : PartialCombinatoryAlgebra A}

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{morphism of assemblies} $f : X \to Y$ is a function $f : |X| \to |Y|$ on underlying sets that is
    \termdefineas{tracked morphism}{tracked} by some $r \in A$, meaning: for every $x \in |X|$ and every $a \Vdash_X x$, the
    application $r \cdot a$ is defined and $r \cdot a \Vdash_Y f(x)$. The realizer $r$ is part of the data only
    existentially; two morphisms with the same underlying function but distinct trackers are identified.
-/
def Tracks (X Y : Assembly.{u,v} K) (r : A) (f : X.Carrier → Y.Carrier) : Prop :=
  ∀ x a, X.realizes a x → ∃ b, K.application r a = Part.some b ∧ Y.realizes b (f x)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    assembly
    morphisms in §{sec:realizability-assemblies} are also underlying functions, with trackers
    required to exist.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{morphism of assemblies} $f : X \to Y$ is a function $f : |X| \to |Y|$ on underlying sets that is
    \termdefineas{tracked morphism}{tracked} by some $r \in A$, meaning: for every $x \in |X|$ and every $a \Vdash_X x$, the
    application $r \cdot a$ is defined and $r \cdot a \Vdash_Y f(x)$. The realizer $r$ is part of the data only
    existentially; two morphisms with the same underlying function but distinct trackers are identified.
-/
structure Hom (X Y : Assembly.{u,v} K) where
  toFun : X.Carrier → Y.Carrier
  tracked : ∃ r, Tracks X Y r toFun

instance homFunLike (X Y : Assembly.{u,v} K) : FunLike (Hom X Y) X.Carrier Y.Carrier where
  coe := Hom.toFun
  coe_injective := by intro f g h; cases f; cases g; cases h; rfl

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{morphism of assemblies} $f : X \to Y$ is a function $f : |X| \to |Y|$ on underlying sets that is
    \termdefineas{tracked morphism}{tracked} by some $r \in A$, meaning: for every $x \in |X|$ and every $a \Vdash_X x$, the
    application $r \cdot a$ is defined and $r \cdot a \Vdash_Y f(x)$. The realizer $r$ is part of the data only
    existentially; two morphisms with the same underlying function but distinct trackers are identified.
-/
@[ext] theorem Hom.ext {X Y : Assembly.{u,v} K} {f g : Hom X Y}
    (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

def Hom.id (X : Assembly.{u,v} K) : Hom X X where
  toFun := fun x => x
  tracked := ⟨K.identity,fun _x a ha => ⟨a,K.application_identity a,ha⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Put $\mathsf i:=\mathsf s\mathsf k\mathsf k$. The abstraction theorem gives
    $\mathsf i a\simeq a$, so this element tracks every identity function.
    If $r$ tracks $f:X\to Y$ and $s$ tracks $g:Y\to Z$, the element
    $$\PCAAbstract{a}{s(ra)}$$
    tracks their composite. Indeed, an input realizer first yields a realizer of the intermediate element, and the
    second tracker then yields a realizer of the final element. Both applications are defined on the required inputs.
    The identity and associativity laws are the corresponding laws for functions. They do not require equality of
    chosen trackers, since a tracker is only required to exist.
-/
def Hom.comp {X Y Z : Assembly.{u,v} K} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toFun := g ∘ f
  tracked := by
    obtain ⟨r,hr⟩ := f.tracked
    obtain ⟨s,hs⟩ := g.tracked
    refine ⟨K.composition r s,fun x a ha => ?_⟩
    obtain ⟨b,hb,hy⟩ := hr x a ha
    obtain ⟨c,hc,hz⟩ := hs (f x) b hy
    refine ⟨c,?_,hz⟩
    rw [K.application_composition,hb,Part.bind_some,hc]

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Category of assemblies
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{AsmCat,PCAPair}
    \end{mathmeta}
    Fix a PCA $A$. The category of \termuseas{assembly}{assemblies} $\AsmCat{A}$ is the first realizability category built
    over $A$ and is where the external concept of "set with realizers" lives intrinsically.
-/
instance assemblyCategory : Category (Assembly.{u,v} K) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext x; rfl
  comp_id f := by ext x; rfl
  assoc f g h := by ext x; rfl

instance assemblyConcreteCategory : ConcreteCategory (Assembly.{u,v} K) Hom where
  hom := fun f => f
  ofHom := fun f => f
  id_apply _ := rfl
  comp_apply _ _ _ := rfl

@[simp] theorem id_apply (X : Assembly.{u,v} K) (x : X.Carrier) : (𝟙 X : X ⟶ X) x = x := rfl
@[simp] theorem comp_apply {X Y Z : Assembly.{u,v} K} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.Carrier) :
    (f ≫ g) x = g (f x) := rfl

end Assembly
end PolishSpaceBook
