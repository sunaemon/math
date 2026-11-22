module

public import PolishSpaceBook.LambdaRealizabilityUncurrying
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

@[expose] public section

/-! # The canonical cartesian closed structure on realizability PERs -/
namespace PolishSpaceBook.LambdaIndexPCA
open RealizerPER CategoryTheory Limits
universe u

/-- Use the terminal object and binary products already constructed from numerical realizers. -/
noncomputable abbrev realizabilityCartesianMonoidal : CartesianMonoidalCategory RealizerPER.{u} :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    ⟨asEmptyCone terminal, RealizerPER.terminalIsTerminal⟩
    (fun X Y => ⟨BinaryFan.mk (fstRelation X Y).toHom (sndRelation X Y).toHom, productIsLimit X Y⟩)

attribute [instance] realizabilityCartesianMonoidal

noncomputable instance realizabilityBraided : BraidedCategory RealizerPER.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory

private theorem comp_pairHom {W Z X Y : RealizerPER.{u}} (f : W ⟶ Z) (g : Z ⟶ X) (h : Z ⟶ Y) :
    f ≫ pairHom g h = pairHom (f ≫ g) (f ≫ h) := by
  conv_lhs => rw [pairHom_eta (f ≫ pairHom g h)]
  simp only [Category.assoc, pairHom_fst, pairHom_snd]

private theorem tensorRight_map {W Z X : RealizerPER.{u}} (f : W ⟶ Z) :
    (MonoidalCategory.tensorRight X).map f =
      pairHom ((fstRelation W X).toHom ≫ f) (sndRelation W X).toHom := by
  change pairHom ((fstRelation W X).toHom ≫ f) ((sndRelation W X).toHom ≫ 𝟙 X) = _
  rw [Category.comp_id]

/-- Application commutes with changing the parameter by an arbitrary arrow. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For completeness, this bijection is natural in the parameter: for $k:W\to Z$,
    $$\UncurriedRelation{f\circ k}=\UncurriedRelation{f}\circ(k\times\mathrm{id}_X).$$
    This follows from the expression for the inverse map in terms of evaluation, together with functoriality of products.
    Thus the bijection defines the right adjoint to $-\times X$; on a morphism $g:Y\to Y'$ it takes
    the transpose of $g\circ\evalMap$. Product symmetry gives the right adjoint to $X\times-$ as well.
    This supplies the cartesian closed structure on the category.
    \end{proof}
-/
theorem uncurryHom_natural_pair {W Z X Y : RealizerPER.{u}} (f : W ⟶ Z) (g : Z ⟶ functionSpace X Y) :
    uncurryHom (f ≫ g) =
      pairHom ((fstRelation W X).toHom ≫ f) (sndRelation W X).toHom ≫ uncurryHom g := by
  rw [uncurryHom_eq, uncurryHom_eq]
  symm
  rw [← Category.assoc, comp_pairHom]
  simp only [← Category.assoc, pairHom_fst, pairHom_snd]

theorem curryHom_natural (X : RealizerPER.{u})
    (W Z Y : RealizerPER.{u}) (f : W ⟶ Z) (h : product Z X ⟶ Y) :
    curryHom ((MonoidalCategory.tensorRight X).map f ≫ h) = f ≫ curryHom h := by
  change curryHom (pairHom ((fstRelation W X).toHom ≫ f) ((sndRelation W X).toHom ≫ 𝟙 X) ≫ h) = _
  rw [Category.comp_id]
  apply (realizabilityCurryEquiv W X Y).symm.injective
  change uncurryHom (curryHom (pairHom ((fstRelation W X).toHom ≫ f) (sndRelation W X).toHom ≫ h)) =
    uncurryHom (f ≫ curryHom h)
  have hi : uncurryHom (curryHom h) = h := (realizabilityCurryEquiv Z X Y).left_inv h
  exact ((realizabilityCurryEquiv W X Y).left_inv _).trans
    (by simpa only [hi] using (uncurryHom_natural_pair f (curryHom h)).symm)

/-- The exponential functor is determined by the explicit hom-set bijection. -/
noncomputable def realizabilityExponentialFunctor (X : RealizerPER.{u}) : RealizerPER.{u} ⥤ RealizerPER.{u} :=
  Adjunction.rightAdjointOfEquiv (F := MonoidalCategory.tensorRight X)
    (fun Z Y => realizabilityCurryEquiv Z X Y) (curryHom_natural X)

/-- The product on the right has the constructed exponential as a right adjoint. -/
noncomputable def realizabilityExponentialAdjunction (X : RealizerPER.{u}) :
    MonoidalCategory.tensorRight X ⊣ realizabilityExponentialFunctor X :=
  Adjunction.adjunctionOfEquivRight (F := MonoidalCategory.tensorRight X)
    (fun Z Y => realizabilityCurryEquiv Z X Y) (curryHom_natural X)

/-- Cartesian symmetry supplies the conventional left-tensor version of closedness. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Finite limits were constructed in §{sec:effective-topos-finite-limits}, the subobject classifier in
    §{sec:effective-topos-classifier}, and exponentials with their universal property in
    §{sec:effective-topos-exponentials}. These are precisely the defining structures of an elementary topos.
    \end{proof}
-/
noncomputable instance realizabilityMonoidalClosed : MonoidalClosed RealizerPER.{u} where
  closed X := {
    rightAdj := realizabilityExponentialFunctor X
    adj := (realizabilityExponentialAdjunction X).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight X).symm }

end PolishSpaceBook.LambdaIndexPCA
