module

public import PolishSpaceBook.PCARealizabilityRestrictions
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

@[expose] public section

/-! # The binary product universal property for general PCA relations -/
namespace PolishSpaceBook.PCARealizability
open CategoryTheory Limits RealizerPER
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}

private theorem and_reduces_mono {I : Type*} {φ φ' ψ ψ' : I → Set R}
    (h : K.Entails φ φ') (h' : K.Entails ψ ψ') :
    K.Entails (K.predAnd φ ψ) (K.predAnd φ' ψ') :=
  K.and_intro (K.entails_trans (K.and_left _ _) h) (K.entails_trans (K.and_right _ _) h')

namespace FunctionalRelation
def pairing {Z X Y : (RealizerPER.{r,u} K)} (F : FunctionalRelation Z X) (G : FunctionalRelation Z Y) :
    FunctionalRelation Z (product X Y) where
  val z p := {a | ∃ b c, a = K.pair b c ∧ b ∈ F.val z p.1 ∧ c ∈ G.val z p.2}
  strict := K.and_intro (F.strict_left_of (K.and_left _ _))
    (K.and_intro (F.strict_right_of (K.and_left _ _))
      (G.strict_right_of (K.and_right _ _)))
  extensional := K.and_intro
    (F.ext_of (K.entails_trans (K.and_left _ _) (K.and_left _ _))
      (K.entails_trans (K.entails_trans (K.and_left _ _) (K.and_right _ _))
        (K.and_left _ _)) (K.entails_trans (K.and_right _ _) (K.and_left _ _)))
    (G.ext_of (K.entails_trans (K.and_left _ _) (K.and_left _ _))
      (K.entails_trans (K.entails_trans (K.and_left _ _) (K.and_right _ _))
        (K.and_right _ _)) (K.entails_trans (K.and_right _ _) (K.and_right _ _)))
  single := K.and_intro
    (F.single_of (K.entails_trans (K.and_left _ _) (K.and_left _ _))
      (K.entails_trans (K.and_right _ _) (K.and_left _ _)))
    (G.single_of (K.entails_trans (K.and_left _ _) (K.and_right _ _))
      (K.entails_trans (K.and_right _ _) (K.and_right _ _)))
  total := by
    apply K.entails_trans (K.and_intro F.total G.total)
    apply reduces_of_subset
    rintro z _ ⟨a,b,rfl,⟨x,hx⟩,⟨y,hy⟩⟩
    exact ⟨(x,y),a,b,rfl,hx,hy⟩

theorem pairing_mono {Z X Y : (RealizerPER.{r,u} K)} {F F' : FunctionalRelation Z X}
    {G G' : FunctionalRelation Z Y} (hF : LE F F') (hG : LE G G') : LE (pairing F G) (pairing F' G') :=
  and_reduces_mono
    (K.reindex_entails (fun p : Z.Carrier × (X.Carrier × Y.Carrier) => (p.1, p.2.1)) hF)
    (K.reindex_entails (fun p : Z.Carrier × (X.Carrier × Y.Carrier) => (p.1, p.2.2)) hG)

theorem pairing_congr {Z X Y : (RealizerPER.{r,u} K)} {F F' : FunctionalRelation Z X}
    {G G' : FunctionalRelation Z Y} (hF : Equivalent F F') (hG : Equivalent G G') :
    Equivalent (pairing F G) (pairing F' G') :=
  ⟨pairing_mono hF.1 hG.1, pairing_mono hF.2 hG.2⟩


theorem pairing_fst {Z X Y : (RealizerPER.{r,u} K)} (F : FunctionalRelation Z X) (G : FunctionalRelation Z Y) :
    Equivalent (comp (pairing F G) (fstRelation X Y)) F := by
  constructor
  · let Γ : (Z.Carrier × X.Carrier) × (X.Carrier × Y.Carrier) → Set R :=
      K.predAnd (fun p => (pairing F G).val p.1.1 p.2)
        (fun p => (fstRelation X Y).val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    have hF : K.Entails Γ (fun p => F.val p.1.1 p.2.1) :=
      K.entails_trans (K.and_left _ _) (K.and_left _ _)
    exact F.ext_of (F.strict_left_of hF) hF
      (K.entails_trans (K.and_right _ _) (K.and_right _ _))
  · apply K.entails_trans (K.and_intro (K.entails_refl _)
      (K.entails_trans (F.strict_left_of (K.entails_refl _)) (K.reindex_entails Prod.fst G.total)))
    let Γ : (Z.Carrier × X.Carrier) × Y.Carrier → Set R :=
      K.predAnd (fun p => F.val p.1.1 p.1.2) (fun p => G.val p.1.1 p.2)
    apply reduces_cover (θ := Γ)
    · rintro p _ ⟨a,b,rfl,ha,⟨y,hy⟩⟩
      exact ⟨y,a,b,rfl,ha,hy⟩
    · exact relationComp_intro (y := fun p => (p.1.2, p.2)) (K.entails_refl _)
        (K.and_intro ((pairing F G).strict_right_of (K.entails_refl _))
          (F.strict_right_of (K.and_left _ _)))

theorem pairing_snd {Z X Y : (RealizerPER.{r,u} K)} (F : FunctionalRelation Z X) (G : FunctionalRelation Z Y) :
    Equivalent (comp (pairing F G) (sndRelation X Y)) G := by
  constructor
  · let Γ : (Z.Carrier × Y.Carrier) × (X.Carrier × Y.Carrier) → Set R :=
      K.predAnd (fun p => (pairing F G).val p.1.1 p.2)
        (fun p => (sndRelation X Y).val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    have hG : K.Entails Γ (fun p => G.val p.1.1 p.2.2) :=
      K.entails_trans (K.and_left _ _) (K.and_right _ _)
    exact G.ext_of (G.strict_left_of hG) hG
      (K.entails_trans (K.and_right _ _) (K.and_right _ _))
  · apply K.entails_trans (K.and_intro
      (K.entails_trans (G.strict_left_of (K.entails_refl _)) (K.reindex_entails Prod.fst F.total))
      (K.entails_refl _))
    let Γ : (Z.Carrier × Y.Carrier) × X.Carrier → Set R :=
      K.predAnd (fun p => F.val p.1.1 p.2) (fun p => G.val p.1.1 p.1.2)
    apply reduces_cover (θ := Γ)
    · rintro p _ ⟨a,b,rfl,⟨x,hx⟩,ha⟩
      exact ⟨x,a,b,rfl,hx,ha⟩
    · exact relationComp_intro (y := fun p => (p.2, p.1.2)) (K.entails_refl _)
        (K.and_intro ((pairing F G).strict_right_of (K.entails_refl _))
          (G.strict_right_of (K.and_right _ _)))

/-- Coordinate images determine the full functional relation, including its realizers. -/
theorem pairing_eta {Z X Y : (RealizerPER.{r,u} K)} (H : FunctionalRelation Z (product X Y)) :
    Equivalent H (pairing (comp H (fstRelation X Y)) (comp H (sndRelation X Y))) := by
  constructor
  · have hE : K.Entails (fun p : Z.Carrier × (X.Carrier × Y.Carrier) => H.val p.1 p.2)
        (fun p => (product X Y).extent p.2) := H.strict_right_of (K.entails_refl _)
    exact K.and_intro
      (relationComp_intro (K.entails_refl _)
        (K.and_intro hE (K.entails_trans hE (K.and_left _ _))))
      (relationComp_intro (K.entails_refl _)
        (K.and_intro hE (K.entails_trans hE (K.and_right _ _))))
  · let Γ : (Z.Carrier × (X.Carrier × Y.Carrier)) ×
        ((X.Carrier × Y.Carrier) × (X.Carrier × Y.Carrier)) → Set R :=
      K.predAnd
        (K.predAnd (fun p => H.val p.1.1 p.2.1)
          (fun p => (fstRelation X Y).val p.2.1 p.1.2.1))
        (K.predAnd (fun p => H.val p.1.1 p.2.2)
          (fun p => (sndRelation X Y).val p.2.2 p.1.2.2))
    apply reduces_cover (θ := Γ)
    · rintro p _ ⟨a,b,rfl,⟨q,hq⟩,⟨r,hr⟩⟩
      exact ⟨(q,r),a,b,rfl,hq,hr⟩
    · have hH : K.Entails Γ (fun p => H.val p.1.1 p.2.1) :=
        K.entails_trans (K.and_left _ _) (K.and_left _ _)
      have hH' : K.Entails Γ (fun p => H.val p.1.1 p.2.2) :=
        K.entails_trans (K.and_right _ _) (K.and_left _ _)
      exact H.ext_of (H.strict_left_of hH) hH
        (K.and_intro
          (K.entails_trans (K.entails_trans (K.and_left _ _) (K.and_right _ _))
            (K.and_right _ _))
          (Y.trans_of (K.entails_trans (H.single_of hH hH') (K.and_right _ _))
            (K.entails_trans (K.entails_trans (K.and_right _ _) (K.and_right _ _))
              (K.and_right _ _))))

end FunctionalRelation
namespace RealizerPER

def pairHom {Z X Y : (RealizerPER.{r,u} K)} : (Z ⟶ X) → (Z ⟶ Y) → (Z ⟶ product X Y) :=
  Quotient.map₂ FunctionalRelation.pairing (fun _ _ hF _ _ hG => FunctionalRelation.pairing_congr hF hG)

theorem pairHom_fst {Z X Y : (RealizerPER.{r,u} K)} (f : Z ⟶ X) (g : Z ⟶ Y) :
    pairHom f g ≫ (fstRelation X Y).toHom = f :=
  Quotient.inductionOn₂ f g fun F G => Quotient.sound (FunctionalRelation.pairing_fst F G)

theorem pairHom_snd {Z X Y : (RealizerPER.{r,u} K)} (f : Z ⟶ X) (g : Z ⟶ Y) :
    pairHom f g ≫ (sndRelation X Y).toHom = g :=
  Quotient.inductionOn₂ f g fun F G => Quotient.sound (FunctionalRelation.pairing_snd F G)

theorem pairHom_eta {Z X Y : (RealizerPER.{r,u} K)} (h : Z ⟶ product X Y) :
    h = pairHom (h ≫ (fstRelation X Y).toHom) (h ≫ (sndRelation X Y).toHom) :=
  Quotient.inductionOn h fun H => Quotient.sound (FunctionalRelation.pairing_eta H)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    The product has underlying pairs, equality given by componentwise conjunction, and extent
    $D(x,y):=E(x)\land E(y)$. Pairing functional relations proves its product universal property as in
    §{sec:effective-topos-finite-limits}. The equality predicate $\delta(x,y):=\rho(x,y)$ is strict and
    extensional on this product: symmetry and transitivity extract both extents and transport equality
    in the two coordinates. It therefore defines a monomorphism from
    $\PERRestriction{(X\times X)}{\delta}$ into the product.
-/
def productIsLimit (X Y : (RealizerPER.{r,u} K)) :
    IsLimit (BinaryFan.mk (C := (RealizerPER.{r,u} K)) (fstRelation X Y).toHom (sndRelation X Y).toHom) :=
  BinaryFan.isLimitMk (fun s => pairHom s.fst s.snd)
    (fun s => pairHom_fst s.fst s.snd) (fun s => pairHom_snd s.fst s.snd)
    (fun s m h₁ h₂ => (pairHom_eta m).trans (by rw [h₁, h₂]))

end RealizerPER
end PolishSpaceBook.PCARealizability
