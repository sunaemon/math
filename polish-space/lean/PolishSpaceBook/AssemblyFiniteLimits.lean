module

public import PolishSpaceBook.AssemblyProducts
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

@[expose] public section

/-! # Equalizers and finite limits of assemblies -/
namespace PolishSpaceBook.Assembly
open CategoryTheory CategoryTheory.Limits
universe u v
variable {A : Type u} {K : PartialCombinatoryAlgebra A}
variable {X Y : Assembly.{u,v} K}

def equalizerObject (f g : X ⟶ Y) : Assembly.{u,v} K where
  Carrier := {x : X.Carrier // f x = g x}
  realizes a x := X.realizes a x.val
  inhabited x := X.inhabited x.val

def equalizerInclusion (f g : X ⟶ Y) : equalizerObject f g ⟶ X where
  toFun := Subtype.val
  tracked := ⟨K.identity,fun _x a ha => ⟨a,K.application_identity a,ha⟩⟩

def equalizerLift (f g : X ⟶ Y) (s : Fork f g) : s.pt ⟶ equalizerObject f g where
  toFun x := ⟨s.ι x,congrArg (fun h : s.pt ⟶ Y => h x) s.condition⟩
  tracked := s.ι.tracked

def equalizerFork (f g : X ⟶ Y) : Fork f g :=
  Fork.ofι (equalizerInclusion f g) (Hom.ext (fun x => x.property))

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For parallel morphisms $f,g:X\to Y$, take
    $$E:=\{x\in|X|:f(x)=g(x)\},\qquad
     a\Vdash_E x\quad\Longleftrightarrow\quad a\Vdash_X x.$$
    The identity combinator tracks the inclusion. Any morphism equalizing the two maps factors uniquely through this
    subset as a function. Its original tracker still works because restricting the underlying set does not change
    the realizer set of any retained element. This proves the equalizer property. Terminal objects, binary products,
    and equalizers give all finite limits by the standard finite-limit construction.
-/
def equalizerIsLimit (f g : X ⟶ Y) : IsLimit (equalizerFork f g) :=
  Fork.IsLimit.mk _ (equalizerLift f g) (fun _ => Hom.ext (fun _ => rfl)) (by
    intro s m h
    apply Hom.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun q : s.pt ⟶ X => q x) h)

instance assemblyHasLimitParallelPair (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  HasLimit.mk ⟨_,equalizerIsLimit f g⟩

instance assemblyHasEqualizers : HasEqualizers (Assembly.{u,v} K) :=
  hasEqualizers_of_hasLimit_parallelPair _

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Finite limits of assemblies
-/
instance assemblyHasFiniteLimits : HasFiniteLimits (Assembly.{u,v} K) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

end PolishSpaceBook.Assembly
