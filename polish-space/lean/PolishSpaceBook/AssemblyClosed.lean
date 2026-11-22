module

public import PolishSpaceBook.AssemblyExponentials
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

@[expose] public section

/-! # Cartesian closed structure on assemblies

The chosen products are the tracked products constructed in the book. The book's
right-product adjunction is proved by its evaluation and currying maps. Braiding
then converts this to mathlib's left-tensor convention for `Closed`.
-/
namespace PolishSpaceBook.Assembly
open CategoryTheory CategoryTheory.Limits
universe u v
variable {A : Type u} (K : PartialCombinatoryAlgebra A)

instance assemblyCartesianMonoidal : CartesianMonoidalCategory (Assembly.{u,v} K) :=
  .ofChosenFiniteProducts ⟨_,terminalIsTerminal K⟩
    (fun X Y => ⟨_,productIsLimit X Y⟩)

instance assemblyBraided : BraidedCategory (Assembly.{u,v} K) :=
  .ofCartesianMonoidalCategory

variable {K}

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For fixed $X$, postcomposition by a morphism $g:Y\to Y'$ gives the morphism
    $\catExp{X}{Y}\to\catExp{X}{Y'}$ obtained by transposing $g\circ\evalMap$.
    It sends $f$ to $g\circ f$, so identities and composition are preserved.
    The bijection given by transposition,
    $$\HomSet{\AsmCat{A}}{Z\times X}{Y}\cong
    \HomSet{\AsmCat{A}}{Z}{\catExp{X}{Y}},$$
    is natural: precomposing in $Z$ or postcomposing in $Y$ commutes with the rule
    $\overline h(z)(x)=h(z,x)$. Thus the exponential functor is right adjoint to the product functor,
    which proves cartesian closedness.
-/
def exponentialAdjunction (X : Assembly.{u,v} K) :
    MonoidalCategory.tensorRight X ⊣ exponentialFunctor X :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun Z Y => curryEquiv X Y Z
    homEquiv_naturality_left_symm := by
      intro Z' Z Y f g
      apply Hom.ext
      intro ⟨z,x⟩
      rfl
    homEquiv_naturality_right := by
      intro Z Y Y' f g
      apply Hom.ext
      intro z
      apply Hom.ext
      intro x
      rfl }

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Exponentials of assemblies
-/
instance assemblyMonoidalClosed : MonoidalClosed (Assembly.{u,v} K) where
  closed X := {
    rightAdj := exponentialFunctor X
    adj := (exponentialAdjunction X).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight X).symm }

end PolishSpaceBook.Assembly
