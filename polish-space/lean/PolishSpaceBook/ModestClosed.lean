module

public import PolishSpaceBook.ModestAssemblies

@[expose] public section

/-! # The cartesian closed category of modest assemblies

Products, evaluation, and transposition are the assembly constructions, restricted
to the full subcategory. No new trackers or choices of representatives are needed.
-/
namespace PolishSpaceBook.ModestAssembly
open CategoryTheory CategoryTheory.Limits
universe u v
variable {A : Type u} (K : PartialCombinatoryAlgebra A)

abbrev terminal : ModestAssembly.{u,v} K := ⟨Assembly.terminal K,Assembly.modest_terminal⟩

def terminalIsTerminal : IsTerminal (terminal.{u,v} K) :=
  IsTerminal.ofUniqueHom (fun X => ObjectProperty.homMk (Assembly.terminalMap K X.obj))
    (by
      intro X m
      apply ObjectProperty.hom_ext
      apply Assembly.Hom.ext
      intro x
      cases m.hom x
      rfl)

variable {K}

abbrev product (X Y : ModestAssembly.{u,v} K) : ModestAssembly.{u,v} K :=
  ⟨Assembly.product X.obj Y.obj,Assembly.modest_product X.property Y.property⟩

def first (X Y : ModestAssembly.{u,v} K) : product X Y ⟶ X :=
  ObjectProperty.homMk (Assembly.first X.obj Y.obj)

def second (X Y : ModestAssembly.{u,v} K) : product X Y ⟶ Y :=
  ObjectProperty.homMk (Assembly.second X.obj Y.obj)

def productIsLimit (X Y : ModestAssembly.{u,v} K) :
    IsLimit (BinaryFan.mk (first X Y) (second X Y)) :=
  BinaryFan.isLimitMk
    (fun s => ObjectProperty.homMk (Assembly.productLift s.fst.hom s.snd.hom))
    (fun _ => ObjectProperty.hom_ext _ (Assembly.Hom.ext (fun _ => rfl)))
    (fun _ => ObjectProperty.hom_ext _ (Assembly.Hom.ext (fun _ => rfl))) (by
      intro s m hl hr
      apply ObjectProperty.hom_ext
      apply Assembly.Hom.ext
      intro z
      apply Prod.ext
      · exact congrArg (fun f : s.pt ⟶ X => f.hom z) hl
      · exact congrArg (fun f : s.pt ⟶ Y => f.hom z) hr)

instance modestCartesianMonoidal : CartesianMonoidalCategory (ModestAssembly.{u,v} K) :=
  .ofChosenFiniteProducts ⟨_,terminalIsTerminal K⟩
    (fun X Y => ⟨_,productIsLimit X Y⟩)

instance modestBraided : BraidedCategory (ModestAssembly.{u,v} K) :=
  .ofCartesianMonoidalCategory

abbrev exponential (X Y : ModestAssembly.{u,v} K) : ModestAssembly.{u,v} K :=
  ⟨Assembly.exponential X.obj Y.obj,Assembly.modest_exponential X.obj Y.property⟩

def exponentialFunctor (X : ModestAssembly.{u,v} K) :
    ModestAssembly.{u,v} K ⥤ ModestAssembly.{u,v} K where
  obj := exponential X
  map f := ObjectProperty.homMk (Assembly.exponentialMap X.obj f.hom)
  map_id Y := ObjectProperty.hom_ext _ ((Assembly.exponentialFunctor X.obj).map_id Y.obj)
  map_comp f g := ObjectProperty.hom_ext _
    ((Assembly.exponentialFunctor X.obj).map_comp f.hom g.hom)

def curryEquiv (X Y Z : ModestAssembly.{u,v} K) :
    (product Z X ⟶ Y) ≃ (Z ⟶ exponential X Y) where
  toFun h := ObjectProperty.homMk (Assembly.curry h.hom)
  invFun f := ObjectProperty.homMk (Assembly.uncurry f.hom)
  left_inv h := ObjectProperty.hom_ext _ (Assembly.uncurry_curry h.hom)
  right_inv f := ObjectProperty.hom_ext _ (Assembly.curry_uncurry f.hom)

def exponentialAdjunction (X : ModestAssembly.{u,v} K) :
    MonoidalCategory.tensorRight X ⊣ exponentialFunctor X :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun Z Y => curryEquiv X Y Z
    homEquiv_naturality_left_symm := by
      intro Z' Z Y f g
      apply ObjectProperty.hom_ext
      apply Assembly.Hom.ext
      intro ⟨z,x⟩
      rfl
    homEquiv_naturality_right := by
      intro Z Y Y' f g
      apply ObjectProperty.hom_ext
      apply Assembly.Hom.ext
      intro z
      apply Assembly.Hom.ext
      intro x
      rfl }

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Closure properties of modest sets
-/
instance modestMonoidalClosed : MonoidalClosed (ModestAssembly.{u,v} K) where
  closed X := {
    rightAdj := exponentialFunctor X
    adj := (exponentialAdjunction X).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight X).symm }

end PolishSpaceBook.ModestAssembly
