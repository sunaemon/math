module

public import PolishSpaceBook.PCARealizabilityPER
public import Mathlib.CategoryTheory.Subobject.Basic

@[expose] public section

/-! # Predicate restrictions over a general PCA

Every strict extensional predicate defines a categorical monomorphism. The
factorization proof retains the original relation and all its realizer names.
-/
namespace PolishSpaceBook.PCARealizability
open CategoryTheory
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}
namespace RealizerPER

def product (X Y : (RealizerPER.{r,u} K)) : (RealizerPER.{r,u} K) where
  Carrier := X.Carrier × Y.Carrier
  rel p q := {a | ∃ b c, a = K.pair b c ∧ b ∈ X.rel p.1 q.1 ∧ c ∈ Y.rel p.2 q.2}
  symmetry := K.and_intro (X.symm_of (K.and_left _ _))
    (Y.symm_of (K.and_right _ _))
  transitivity := K.and_intro
    (X.trans_of (K.entails_trans (K.and_left _ _) (K.and_left _ _))
      (K.entails_trans (K.and_right _ _) (K.and_left _ _)))
    (Y.trans_of (K.entails_trans (K.and_left _ _) (K.and_right _ _))
      (K.entails_trans (K.and_right _ _) (K.and_right _ _)))

def fstMap (X Y : (RealizerPER.{r,u} K)) : Map (product X Y) X where
  toFun := Prod.fst
  preserves := K.and_left _ _

def sndMap (X Y : (RealizerPER.{r,u} K)) : Map (product X Y) Y where
  toFun := Prod.snd
  preserves := K.and_right _ _

abbrev fstRelation (X Y : (RealizerPER.{r,u} K)) := (fstMap X Y).graph
abbrev sndRelation (X Y : (RealizerPER.{r,u} K)) := (sndMap X Y).graph

structure StrictPredicate (X : (RealizerPER.{r,u} K)) where
  val : X.Carrier → Set R
  strict : K.Entails val X.extent
  extensional : K.Entails
    (K.predAnd (fun p : X.Carrier × X.Carrier => X.rel p.1 p.2) (fun p => val p.1))
    (fun p => val p.2)

def StrictPredicate.restriction {X : RealizerPER K} (P : StrictPredicate X) : RealizerPER K where
  Carrier := X.Carrier
  rel x y := {a | ∃ b c, a = K.pair b c ∧ b ∈ X.rel x y ∧ c ∈ P.val x}
  symmetry := K.and_intro (X.symm_of (K.and_left _ _)) P.extensional
  transitivity := K.and_intro
    (X.trans_of (K.entails_trans (K.and_left _ _) (K.and_left _ _))
      (K.entails_trans (K.and_right _ _) (K.and_left _ _)))
    (K.entails_trans (K.and_left _ _) (K.and_right _ _))

/-- The inclusion has exactly the same realizer sets as the restricted equality. -/
def StrictPredicate.inclusion {X : RealizerPER K} (P : StrictPredicate X) :
    FunctionalRelation P.restriction X where
  val := P.restriction.rel
  strict := K.and_intro
    (K.and_intro (X.extent_left_of (K.and_left _ _)) (K.and_right _ _))
    (X.extent_right_of (K.and_left _ _))
  extensional := K.and_intro
    (X.trans_of
      (X.trans_of
        (X.symm_of (K.entails_trans (K.entails_trans (K.and_left _ _) (K.and_left _ _))
          (K.and_left _ _)))
        (K.entails_trans (K.entails_trans (K.and_left _ _) (K.and_right _ _))
          (K.and_left _ _))) (K.and_right _ _))
    (K.entails_trans
      (P.restriction.extent_right_of (K.entails_trans (K.and_left _ _) (K.and_left _ _)))
      (K.and_right _ _))
  single := X.trans_of
    (X.symm_of (K.entails_trans (K.and_left _ _) (K.and_left _ _)))
    (K.entails_trans (K.and_right _ _) (K.and_left _ _))
  total := reduces_of_subset fun x _ h => ⟨x, h⟩

/-- A relation all of whose values satisfy the predicate lifts without changing its realizer sets. -/
def StrictPredicate.lift {X Z : RealizerPER K} (P : StrictPredicate X) (F : FunctionalRelation Z X)
    (h : K.Entails (fun p : Z.Carrier × X.Carrier => F.val p.1 p.2) (fun p => P.val p.2)) :
    FunctionalRelation Z P.restriction where
  val := F.val
  strict := K.and_intro (F.strict_left_of (K.entails_refl _))
    (K.and_intro (F.strict_right_of (K.entails_refl _)) h)
  extensional := F.ext_of (K.entails_trans (K.and_left _ _) (K.and_left _ _))
    (K.entails_trans (K.and_left _ _) (K.and_right _ _))
    (K.entails_trans (K.and_right _ _) (K.and_left _ _))
  single := K.and_intro F.single
    (K.entails_trans (K.and_left _ _)
      (K.reindex_entails (fun p : Z.Carrier × X.Carrier × X.Carrier => (p.1, p.2.1)) h))
  total := F.total

theorem StrictPredicate.lift_inclusion {X Z : RealizerPER K} (P : StrictPredicate X)
    (F : FunctionalRelation Z X)
    (h : K.Entails (fun p : Z.Carrier × X.Carrier => F.val p.1 p.2) (fun p => P.val p.2)) :
    FunctionalRelation.Equivalent (FunctionalRelation.comp (P.lift F h) P.inclusion) F :=
  FunctionalRelation.comp_identity (P.lift F h)

/-- Forgetting the restriction reflects equality of arrows. -/
theorem StrictPredicate.inclusion_cancel {X Z : RealizerPER K} (P : StrictPredicate X)
    (f g : Z ⟶ P.restriction) (h : f ≫ P.inclusion.toHom = g ≫ P.inclusion.toHom) : f = g := by
  revert h
  refine Quotient.inductionOn₂ f g fun F G h => ?_
  have he := (FunctionalRelation.toHom_eq_iff
    (FunctionalRelation.comp F P.inclusion) (FunctionalRelation.comp G P.inclusion)).mp h
  apply Quotient.sound
  exact ⟨K.entails_trans (FunctionalRelation.comp_identity F).2
      (K.entails_trans he.1 (FunctionalRelation.comp_identity G).1),
    K.entails_trans (FunctionalRelation.comp_identity G).2
      (K.entails_trans he.2 (FunctionalRelation.comp_identity F).1)⟩

instance StrictPredicate.inclusion_mono {X : RealizerPER K} (P : StrictPredicate X) :
    Mono (C := RealizerPER K) P.inclusion.toHom := ⟨fun f g h => P.inclusion_cancel f g h⟩

end RealizerPER
end PolishSpaceBook.PCARealizability
