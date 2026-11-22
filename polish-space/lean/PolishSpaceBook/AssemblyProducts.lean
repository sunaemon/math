module

public import PolishSpaceBook.Assemblies
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

@[expose] public section

/-! # The initial assembly, terminal assembly, and finite products -/
namespace PolishSpaceBook.Assembly
open CategoryTheory CategoryTheory.Limits
universe u v
variable {A : Type u} (K : PartialCombinatoryAlgebra A)

def terminal : Assembly.{u,v} K where
  Carrier := PUnit
  realizes _ _ := True
  inhabited _ := ⟨K.k,trivial⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    The terminal assembly has a singleton as underlying set, realized by every element of the PCA.
    The identity combinator tracks the unique function into it, so it is terminal.
-/
def terminalMap (X : Assembly.{u,v} K) : X ⟶ terminal K where
  toFun _ := PUnit.unit
  tracked := ⟨K.identity,fun _x a _ => ⟨a,K.application_identity a,trivial⟩⟩

def terminalIsTerminal : IsTerminal (terminal.{u,v} K) :=
  IsTerminal.ofUniqueHom (terminalMap K) (fun _ m => Hom.ext (fun x => by cases m x; rfl))

instance assemblyHasTerminal : HasTerminal (Assembly.{u,v} K) := (terminalIsTerminal K).hasTerminal

def initial : Assembly.{u,v} K where
  Carrier := PEmpty
  realizes _ _ := False
  inhabited x := x.elim

def initialMap (X : Assembly.{u,v} K) : initial K ⟶ X where
  toFun x := x.elim
  tracked := ⟨K.identity,fun x => x.elim⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    The empty set with no realizers is initial: its unique map to any assembly is tracked
    vacuously by any element.
-/
def initialIsInitial : IsInitial (initial.{u,v} K) :=
  IsInitial.ofUniqueHom (initialMap K) (fun _ _ => Hom.ext (fun x => x.elim))

instance assemblyHasInitial : HasInitial (Assembly.{u,v} K) := (initialIsInitial K).hasInitial

variable {K}

def product (X Y : Assembly.{u,v} K) : Assembly.{u,v} K where
  Carrier := X.Carrier × Y.Carrier
  realizes a xy := ∃ b c, a = K.pair b c ∧ X.realizes b xy.1 ∧ Y.realizes c xy.2
  inhabited xy := by
    obtain ⟨b,hb⟩ := X.inhabited xy.1
    obtain ⟨c,hc⟩ := Y.inhabited xy.2
    exact ⟨K.pair b c,b,c,rfl,hb,hc⟩

def first (X Y : Assembly.{u,v} K) : product X Y ⟶ X where
  toFun := Prod.fst
  tracked := by
    refine ⟨K.firstProjection,?_⟩
    rintro _xy a ⟨b,c,rfl,hb,_⟩
    exact ⟨b,K.application_firstProjection b c,hb⟩

def second (X Y : Assembly.{u,v} K) : product X Y ⟶ Y where
  toFun := Prod.snd
  tracked := by
    refine ⟨K.secondProjection,?_⟩
    rintro _xy a ⟨b,c,rfl,_,hc⟩
    exact ⟨c,K.application_secondProjection b c,hc⟩

def productLift {X Y Z : Assembly.{u,v} K} (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ product X Y where
  toFun z := (f z,g z)
  tracked := by
    obtain ⟨r,hr⟩ := f.tracked
    obtain ⟨s,hs⟩ := g.tracked
    refine ⟨K.paired r s,fun z a ha => ?_⟩
    obtain ⟨b,hb,hx⟩ := hr z a ha
    obtain ⟨c,hc,hy⟩ := hs z a ha
    exact ⟨K.pair b c,K.application_paired hb hc,b,c,rfl,hx,hy⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For the product, take the usual set product and put
    $$\PCAPair{a}{b}\Vdash_{X\times Y}(x,y)
    \quad\text{when }a\Vdash_X x\text{ and }b\Vdash_Y y.$$
    These are exactly the realizers of the product. Every pair of elements has one because each component has a
    realizer. The two projection elements track the set projections. If two maps into the factors have trackers
    $r,s$, their pairing is tracked by
    $$\PCAAbstract{a}{\mathsf p(ra)(sa)}.$$
    For a valid input, both component computations are defined and realize the required components, so the
    constructed pair realizes the required element of the product. The projection equations and uniqueness of the
    mediating map follow from equality of the underlying functions. Thus this is a categorical product.
-/
def productIsLimit (X Y : Assembly.{u,v} K) :
    IsLimit (BinaryFan.mk (first X Y) (second X Y)) :=
  BinaryFan.isLimitMk (fun s => productLift s.fst s.snd)
    (fun _ => Hom.ext (fun _ => rfl)) (fun _ => Hom.ext (fun _ => rfl)) (by
      intro s m hl hr
      apply Hom.ext
      intro z
      apply Prod.ext
      · exact congrArg (fun f : s.pt ⟶ X => f z) hl
      · exact congrArg (fun f : s.pt ⟶ Y => f z) hr)

instance assemblyHasLimitPair (X Y : Assembly.{u,v} K) : HasLimit (pair X Y) :=
  HasLimit.mk ⟨_,productIsLimit X Y⟩

instance assemblyHasBinaryProducts : HasBinaryProducts (Assembly.{u,v} K) :=
  hasBinaryProducts_of_hasLimit_pair _

instance assemblyHasFiniteProducts : HasFiniteProducts (Assembly.{u,v} K) :=
  hasFiniteProducts_of_has_binary_and_terminal

end PolishSpaceBook.Assembly
