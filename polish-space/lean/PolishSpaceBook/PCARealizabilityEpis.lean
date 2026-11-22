module

public import PolishSpaceBook.PCARealizabilityTruthValues

@[expose] public section

/-! # Epimorphisms and uniform image coverage

Cancellation is characterized by coverage of the codomain extent by the image
predicate. Coverage produces a relation realizer, never a selected preimage.
-/
namespace PolishSpaceBook.PCARealizability
open CategoryTheory RealizerPER
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}
namespace FunctionalRelation

def Covers {X Y : RealizerPER.{r,u} K} (F : FunctionalRelation X Y) : Prop :=
  K.Entails Y.extent F.imagePredicate.val

/-- Uniform coverage permits cancellation even though intermediate points are not computed. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    \begin{proof}
    Suppose first that the displayed entailment holds and that $G\circ F=H\circ F$.
    From $b\in G(y,z)$, strictness and the assumed entailment give $a\in F(x,y)$ for some $x$.
    The realizer $\PCAPair{a}{b}$ lies in $(G\circ F)(x,z)$, so the assumed equality transforms it into
    $\PCAPair{c}{e}\in(H\circ F)(x,z)$, with $c\in F(x,y')$ and $e\in H(y',z)$ for some $y'$.
    Single-valuedness of $F$ gives a realizer of $\rho_Y(y,y')$ from $a,c$.
    Symmetry and extensionality of $H$ then transform $e$ into an $H(y,z)$-realizer. Every operation is
    uniform in the original input $b$. Thus $G\le H$, and the one-inclusion criterion gives $G=H$.
    This proves the categorical cancellation property.
-/
theorem le_of_comp_le {X Y Z : RealizerPER.{r,u} K} (F : FunctionalRelation X Y)
    (hF : F.Covers) (G H : FunctionalRelation Y Z) (h : (F.comp G).LE (F.comp H)) : G.LE H := by
  have hc : K.Entails (fun p : Y.Carrier × Z.Carrier => G.val p.1 p.2)
      (fun p => F.imagePredicate.val p.1) :=
    K.entails_trans (G.strict_left_of (K.entails_refl _)) (K.reindex_entails Prod.fst hF)
  apply K.entails_trans (K.and_intro hc (K.entails_refl _))
  let Θ : (Y.Carrier × Z.Carrier) × X.Carrier → Set R :=
    K.predAnd (fun p => F.val p.2 p.1.1) (fun p => G.val p.1.1 p.1.2)
  apply reduces_cover (θ := Θ)
  · rintro p _ ⟨a,b,rfl,⟨x,hx⟩,hb⟩
    exact ⟨x,a,b,rfl,hx,hb⟩
  · have hFG : K.Entails Θ (fun p => (F.comp G).val p.2 p.1.2) :=
      relationComp_intro (K.and_left _ _) (K.and_right _ _)
    have hFH : K.Entails Θ (fun p => (F.comp H).val p.2 p.1.2) :=
      K.entails_trans hFG (K.reindex_entails (fun p : (Y.Carrier × Z.Carrier) × X.Carrier =>
        (p.2,p.1.2)) h)
    apply K.entails_trans (K.and_intro (K.and_left _ _) hFH)
    let Ξ : ((Y.Carrier × Z.Carrier) × X.Carrier) × Y.Carrier → Set R :=
      K.predAnd (fun p => F.val p.1.2 p.1.1.1)
        (K.predAnd (fun p => F.val p.1.2 p.2) (fun p => H.val p.2 p.1.1.2))
    apply reduces_cover (θ := Ξ)
    · rintro p _ ⟨a,bc,rfl,ha,⟨y,hbc⟩⟩
      exact ⟨y,a,bc,rfl,ha,hbc⟩
    · have hf₁ : K.Entails Ξ (fun p => F.val p.1.2 p.1.1.1) := K.and_left _ _
      have hf₂ : K.Entails Ξ (fun p => F.val p.1.2 p.2) :=
        K.entails_trans (K.and_right _ _) (K.and_left _ _)
      have hh : K.Entails Ξ (fun p => H.val p.2 p.1.1.2) :=
        K.entails_trans (K.and_right _ _) (K.and_right _ _)
      exact H.ext_of (Y.symm_of (F.single_of hf₁ hf₂)) hh (H.strict_right_of hh)

theorem epi_of_covers {X Y : RealizerPER.{r,u} K} (F : FunctionalRelation X Y) (hF : F.Covers) :
    Epi (C := RealizerPER K) F.toHom where
  left_cancellation g h := by
    refine Quotient.inductionOn₂ g h fun G H he => ?_
    apply Quotient.sound
    apply equivalent_of_le
    exact F.le_of_comp_le hF G H ((toHom_eq_iff _ _).mp he).1

end FunctionalRelation

/-- The extent predicate presents the whole object. -/
def RealizerPER.extentPredicate (X : RealizerPER.{r,u} K) : StrictPredicate X where
  val := X.extent
  strict := K.entails_refl _
  extensional := X.extent_right_of (K.and_left _ _)

namespace FunctionalRelation

/-- On an image realizer the image predicate and the extent predicate agree uniformly. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Now take $\varphi:=I_F$ and $\psi:=E_Y$. An $F(x,y)$-realizer belongs to $I_F(y)$ and supplies
    $E_Y(y)$. Combined with a realizer of $\chi_{I_F}(y,S)$, it therefore supplies an $S$-realizer.
    Parameter abstraction gives constant transformers $E_Y(y)\to S$ and $S\to E_Y(y)$ from these
    supplied names. Hence
    $$\chi_{I_F}\circ F\le\chi_{E_Y}\circ F,$$
    and the one-inclusion criterion gives equality. If $F$ is epic, cancel it to obtain
    $\chi_{I_F}=\chi_{E_Y}$. The preceding argument yields $E_Y\le I_F$, as required.
    \end{proof}
-/
theorem image_characteristic_comp {X Y : RealizerPER.{r,max r u} K} (F : FunctionalRelation X Y) :
    (F.comp (characteristic.{r,u} F.imagePredicate)).Equivalent
      (F.comp (characteristic.{r,u} Y.extentPredicate)) := by
  apply equivalent_of_le
  let Θ : (X.Carrier × (truthValues.{r,u} (K := K)).Carrier) × Y.Carrier → Set R :=
    K.predAnd (fun p => F.val p.1.1 p.2)
      (fun p => (characteristic.{r,u} F.imagePredicate).val p.2 p.1.2)
  apply reduces_cover (θ := Θ) (fun _ _ h => h)
  have hf : K.Entails Θ (fun p => F.val p.1.1 p.2) := K.and_left _ _
  have hp : K.Entails Θ (fun p => F.imagePredicate.val p.2) :=
    K.entails_trans hf (reduces_of_subset fun p _ h => ⟨p.1.1,h⟩)
  have hχ : K.Entails Θ (fun p => (characteristic.{r,u} F.imagePredicate).val p.2 p.1.2) :=
    K.and_right _ _
  have hS : K.Entails Θ (fun p => p.1.2.down) :=
    imp_apply_of (K.entails_trans (K.entails_trans hχ (K.and_right _ _)) (K.and_left _ _)) hp
  have hES : K.Entails Θ (K.predImp (fun p => Y.extent p.2) (fun p => p.1.2.down)) :=
    (K.imp_adjunction _ _ _).mp (K.entails_trans (K.and_left _ _) hS)
  have hSE : K.Entails Θ (K.predImp (fun p => p.1.2.down) (fun p => Y.extent p.2)) :=
    (K.imp_adjunction _ _ _).mp (K.entails_trans (K.and_left _ _) (F.strict_right_of hf))
  exact relationComp_intro hf (K.and_intro (F.strict_right_of hf) (K.and_intro hES hSE))

theorem covers_of_epi {X Y : RealizerPER.{r,max r u} K} (F : FunctionalRelation X Y)
    [Epi (C := RealizerPER K) F.toHom] : F.Covers := by
  have h : (characteristic.{r,u} F.imagePredicate).toHom = (characteristic.{r,u} Y.extentPredicate).toHom :=
    Epi.left_cancellation (C := RealizerPER K) (f := F.toHom) _ _
      (Quotient.sound F.image_characteristic_comp)
  exact (predicate_equivalent_of_characteristic_eq F.imagePredicate Y.extentPredicate h).2

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Uniform image criterion for epimorphisms
-/
theorem epi_iff_covers {X Y : RealizerPER.{r,max r u} K} (F : FunctionalRelation X Y) :
    Epi (C := RealizerPER K) F.toHom ↔ F.Covers :=
  ⟨fun h => @covers_of_epi _ _ _ _ _ h,fun h => F.epi_of_covers h⟩

end FunctionalRelation
end PolishSpaceBook.PCARealizability
