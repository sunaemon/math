module

public import PolishSpaceBook.PCARealizabilityRestrictions

@[expose] public section

/-! # All subobjects are predicate restrictions

Categorical cancellation at a kernel object supplies uniform injectivity. The
inverse image relation keeps realizer names and never computes a preimage point.
-/
namespace PolishSpaceBook.PCARealizability
open CategoryTheory RealizerPER
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}

namespace FunctionalRelation

/-- A common image of two representatives, retaining both PCA realizers. -/
def kernelPredicate {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y) : StrictPredicate (product X X) where
  val p := {a | ∃ y, ∃ b c, a = K.pair b c ∧ b ∈ M.val p.1 y ∧ c ∈ M.val p.2 y}
  strict := by
    apply reduces_cover (θ := K.predAnd
      (fun p : (X.Carrier × X.Carrier) × Y.Carrier => M.val p.1.1 p.2)
      (fun p => M.val p.1.2 p.2)) (fun _ _ h => h)
    exact K.and_intro (M.strict_left_of (K.and_left _ _))
      (M.strict_left_of (K.and_right _ _))
  extensional := by
    let Γ : ((X.Carrier × X.Carrier) × (X.Carrier × X.Carrier)) × Y.Carrier → Set R :=
      K.predAnd (fun p => (product X X).rel p.1.1 p.1.2)
        (K.predAnd (fun p => M.val p.1.1.1 p.2) (fun p => M.val p.1.1.2 p.2))
    apply reduces_cover (θ := Γ)
    · rintro p _ ⟨a,b,rfl,hr,⟨y,hy⟩⟩
      exact ⟨y,a,b,rfl,hr,hy⟩
    · have h₁ : K.Entails Γ (fun p => M.val p.1.1.1 p.2) :=
        K.entails_trans (K.and_right _ _) (K.and_left _ _)
      have h₂ : K.Entails Γ (fun p => M.val p.1.1.2 p.2) :=
        K.entails_trans (K.and_right _ _) (K.and_right _ _)
      apply K.entails_trans (K.and_intro
        (M.ext_of (K.entails_trans (K.and_left _ _) (K.and_left _ _)) h₁ (M.strict_right_of h₁))
        (M.ext_of (K.entails_trans (K.and_left _ _) (K.and_right _ _)) h₂ (M.strict_right_of h₂)))
      exact reduces_of_subset fun p _ h => ⟨p.2, h⟩

def kernelFirst {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y) :
    Map (kernelPredicate M).restriction X where
  toFun := Prod.fst
  preserves := K.entails_trans (K.and_left _ _) (K.and_left _ _)

def kernelSecond {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y) :
    Map (kernelPredicate M).restriction X where
  toFun := Prod.snd
  preserves := K.entails_trans (K.and_left _ _) (K.and_right _ _)

theorem kernel_swap {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y) :
    K.Entails (kernelPredicate M).val (fun p => (kernelPredicate M).val (p.2, p.1)) := by
  apply reduces_cover (θ := K.predAnd
    (fun p : (X.Carrier × X.Carrier) × Y.Carrier => M.val p.1.1 p.2)
    (fun p => M.val p.1.2 p.2)) (fun _ _ h => h)
  apply K.entails_trans (K.and_intro (K.and_right _ _) (K.and_left _ _))
  exact reduces_of_subset fun p _ h => ⟨p.2, h⟩

/-- If two inputs have a common image, every image of the first is an image of the second. -/
theorem kernel_transfer {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y) :
    K.Entails (K.predAnd
      (fun p : (X.Carrier × X.Carrier) × Y.Carrier => (kernelPredicate M).val p.1)
      (fun p => M.val p.1.1 p.2)) (fun p => M.val p.1.2 p.2) := by
  let Γ : ((X.Carrier × X.Carrier) × Y.Carrier) × Y.Carrier → Set R :=
    K.predAnd (K.predAnd (fun p => M.val p.1.1.1 p.2) (fun p => M.val p.1.1.2 p.2))
      (fun p => M.val p.1.1.1 p.1.2)
  apply reduces_cover (θ := Γ)
  · rintro p _ ⟨a,b,rfl,⟨y,hy⟩,ha⟩
    exact ⟨y,a,b,rfl,hy,ha⟩
  · have h₂ : K.Entails Γ (fun p => M.val p.1.1.2 p.2) :=
      K.entails_trans (K.and_left _ _) (K.and_right _ _)
    exact M.ext_of (M.strict_left_of h₂) h₂
      (M.single_of (K.entails_trans (K.and_left _ _) (K.and_left _ _)) (K.and_right _ _))

theorem kernel_transfer_of {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y)
    {I : Type*} {Γ : I → Set R} {x x' : I → X.Carrier} {y : I → Y.Carrier}
    (hK : K.Entails Γ (fun i => (kernelPredicate M).val (x i, x' i)))
    (hM : K.Entails Γ (fun i => M.val (x i) (y i))) : K.Entails Γ (fun i => M.val (x' i) (y i)) :=
  K.entails_trans (K.and_intro hK hM)
    (K.reindex_entails (fun i => ((x i, x' i), y i)) (kernel_transfer M))

theorem kernel_projections_condition {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y) :
    Equivalent (comp (kernelFirst M).graph M) (comp (kernelSecond M).graph M) := by
  constructor
  · let Γ : ((X.Carrier × X.Carrier) × Y.Carrier) × X.Carrier → Set R :=
      K.predAnd (fun p => (kernelFirst M).graph.val p.1.1 p.2) (fun p => M.val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    have hE : K.Entails Γ (fun p => (kernelPredicate M).restriction.extent p.1.1) :=
      K.entails_trans (K.and_left _ _) (K.and_left _ _)
    have hM : K.Entails Γ (fun p => M.val p.2 p.1.2) := K.and_right _ _
    have h₁ : K.Entails Γ (fun p => M.val p.1.1.1 p.1.2) :=
      M.ext_of (X.symm_of (K.entails_trans (K.and_left _ _) (K.and_right _ _)))
        hM (M.strict_right_of hM)
    have h₂ := kernel_transfer_of M (K.entails_trans hE (K.and_right _ _)) h₁
    exact relationComp_intro (I := ((X.Carrier × X.Carrier) × Y.Carrier) × X.Carrier) (F := (kernelSecond M).graph.val) (G := M.val)
      (x := fun p => p.1.1) (y := fun p => p.1.1.2) (z := fun p => p.1.2)
      (K.and_intro hE (M.strict_left_of h₂)) h₂
  · let Γ : ((X.Carrier × X.Carrier) × Y.Carrier) × X.Carrier → Set R :=
      K.predAnd (fun p => (kernelSecond M).graph.val p.1.1 p.2) (fun p => M.val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    have hE : K.Entails Γ (fun p => (kernelPredicate M).restriction.extent p.1.1) :=
      K.entails_trans (K.and_left _ _) (K.and_left _ _)
    have hM : K.Entails Γ (fun p => M.val p.2 p.1.2) := K.and_right _ _
    have h₂ : K.Entails Γ (fun p => M.val p.1.1.2 p.1.2) :=
      M.ext_of (X.symm_of (K.entails_trans (K.and_left _ _) (K.and_right _ _)))
        hM (M.strict_right_of hM)
    have hK : K.Entails Γ (fun p => (kernelPredicate M).val (p.1.1.2, p.1.1.1)) :=
      K.entails_trans (K.entails_trans hE (K.and_right _ _))
        (K.reindex_entails (fun p : ((X.Carrier × X.Carrier) × Y.Carrier) × X.Carrier => p.1.1)
          (kernel_swap M))
    have h₁ := kernel_transfer_of M hK h₂
    exact relationComp_intro (I := ((X.Carrier × X.Carrier) × Y.Carrier) × X.Carrier) (F := (kernelFirst M).graph.val) (G := M.val)
      (x := fun p => p.1.1) (y := fun p => p.1.1.1) (z := fun p => p.1.2)
      (K.and_intro hE (M.strict_left_of h₁)) h₁

/-- Categorical monicity entails one uniform realizer of injectivity. -/
theorem injective_of_mono {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y)
    [Mono (C := RealizerPER K) M.toHom] :
    K.Entails (K.predAnd (fun p : X.Carrier × X.Carrier × Y.Carrier => M.val p.1 p.2.2)
      (fun p => M.val p.2.1 p.2.2)) (fun p => X.rel p.1 p.2.1) := by
  have hh : ((kernelFirst M).graph.toHom : (kernelPredicate M).restriction ⟶ X) =
      (kernelSecond M).graph.toHom :=
    Mono.right_cancellation (C := (RealizerPER.{r,u} K)) (f := M.toHom)
      (kernelFirst M).graph.toHom (kernelSecond M).graph.toHom
      (Quotient.sound (kernel_projections_condition M))
  have h := (toHom_eq_iff _ _).mp hh
  let Γ : X.Carrier × X.Carrier × Y.Carrier → Set R :=
    K.predAnd (fun p => M.val p.1 p.2.2) (fun p => M.val p.2.1 p.2.2)
  have hE : K.Entails Γ (fun p => (kernelPredicate M).restriction.extent (p.1, p.2.1)) :=
    K.and_intro
      (K.and_intro (M.strict_left_of (K.and_left _ _))
        (M.strict_left_of (K.and_right _ _)))
      (reduces_of_subset fun p _ ha => ⟨p.2.2, ha⟩)
  have hout : K.Entails Γ (fun p => (kernelSecond M).graph.val (p.1, p.2.1) p.1) :=
    K.entails_trans
      (K.and_intro hE (M.strict_left_of (K.and_left _ _)))
      (K.reindex_entails (fun p : X.Carrier × X.Carrier × Y.Carrier => ((p.1, p.2.1), p.1)) h.1)
  exact X.symm_of (K.entails_trans hout (K.and_right _ _))

/-- The range predicate records an output realizer but does not encode its preimage. -/
def imagePredicate {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y) : StrictPredicate Y where
  val y := {a | ∃ x, a ∈ M.val x y}
  strict := by
    apply reduces_cover (θ := fun p : Y.Carrier × X.Carrier => M.val p.2 p.1) (fun _ _ h => h)
    exact M.strict_right_of (K.entails_refl _)
  extensional := by
    let Γ : (Y.Carrier × Y.Carrier) × X.Carrier → Set R :=
      K.predAnd (fun p => Y.rel p.1.1 p.1.2) (fun p => M.val p.2 p.1.1)
    apply reduces_cover (θ := Γ)
    · rintro p _ ⟨a,b,rfl,hr,⟨x,hx⟩⟩
      exact ⟨x,a,b,rfl,hr,hx⟩
    · apply K.entails_trans (M.ext_of (M.strict_left_of (K.and_right _ _))
        (K.and_right _ _) (K.and_left _ _))
      exact reduces_of_subset fun p _ h => ⟨p.2, h⟩

def imageLift {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y) :
    FunctionalRelation X (imagePredicate M).restriction :=
  (imagePredicate M).lift M (reduces_of_subset fun p _ h => ⟨p.1, h⟩)

/-- Injectivity makes the converse relation single-valued; its totality is the range predicate. -/
def imageInverse {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y)
    [Mono (C := RealizerPER K) M.toHom] : FunctionalRelation (imagePredicate M).restriction X where
  val y x := M.val x y
  strict := K.and_intro
    (K.and_intro (M.strict_right_of (K.entails_refl _)) (reduces_of_subset fun p _ h => ⟨p.2, h⟩))
    (M.strict_left_of (K.entails_refl _))
  extensional := M.ext_of (K.and_right _ _)
    (K.entails_trans (K.and_left _ _) (K.and_right _ _))
    (K.entails_trans (K.entails_trans (K.and_left _ _) (K.and_left _ _))
      (K.and_left _ _))
  single := K.reindex_entails (fun p : Y.Carrier × X.Carrier × X.Carrier => (p.2.1, p.2.2, p.1))
    (injective_of_mono M)
  total := K.and_right _ _

theorem imageLift_inverse {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y)
    [Mono (C := RealizerPER K) M.toHom] : Equivalent (comp M.imageLift M.imageInverse) (identity X) := by
  constructor
  · apply reduces_cover (θ := K.predAnd
      (fun p : (X.Carrier × X.Carrier) × Y.Carrier => M.val p.1.1 p.2)
      (fun p => M.val p.1.2 p.2)) (fun _ _ h => h)
    exact K.reindex_entails (fun p : (X.Carrier × X.Carrier) × Y.Carrier => (p.1.1, p.1.2, p.2)) (injective_of_mono M)
  · apply K.entails_trans (K.and_intro (K.entails_refl _)
      (K.entails_trans (X.extent_left_of (K.entails_refl _)) (K.reindex_entails Prod.fst M.total)))
    let Γ : (X.Carrier × X.Carrier) × Y.Carrier → Set R :=
      K.predAnd (fun p => X.rel p.1.1 p.1.2) (fun p => M.val p.1.1 p.2)
    apply reduces_cover (θ := Γ)
    · rintro p _ ⟨a,b,rfl,hr,⟨y,hy⟩⟩
      exact ⟨y,a,b,rfl,hr,hy⟩
    · exact relationComp_intro (K.and_right _ _)
        (M.ext_of (K.and_left _ _) (K.and_right _ _) (M.strict_right_of (K.and_right _ _)))

theorem imageInverse_lift {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y)
    [Mono (C := RealizerPER K) M.toHom] :
    Equivalent (comp M.imageInverse M.imageLift) (identity (imagePredicate M).restriction) := by
  constructor
  · let Γ : (Y.Carrier × Y.Carrier) × X.Carrier → Set R :=
      K.predAnd (fun p => M.val p.2 p.1.1) (fun p => M.val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    exact K.and_intro (M.single_of (K.and_left _ _) (K.and_right _ _))
      (K.entails_trans (K.and_left _ _) (reduces_of_subset fun p _ h => ⟨p.2, h⟩))
  · let Γ : (Y.Carrier × Y.Carrier) × X.Carrier → Set R :=
      K.predAnd (fun p => Y.rel p.1.1 p.1.2) (fun p => M.val p.2 p.1.1)
    apply reduces_cover (θ := Γ)
    · rintro p _ ⟨a,b,rfl,hr,⟨x,hx⟩⟩
      exact ⟨x,a,b,rfl,hr,hx⟩
    · exact relationComp_intro (K.and_right _ _)
        (M.ext_of (M.strict_left_of (K.and_right _ _)) (K.and_right _ _) (K.and_left _ _))

def imageIso {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y)
    [Mono (C := RealizerPER K) M.toHom] : X ≅ (imagePredicate M).restriction where
  hom := M.imageLift.toHom
  inv := M.imageInverse.toHom
  hom_inv_id := Quotient.sound (imageLift_inverse M)
  inv_hom_id := Quotient.sound (imageInverse_lift M)

theorem imageIso_inclusion {X Y : (RealizerPER.{r,u} K)} (M : FunctionalRelation X Y)
    [Mono (C := RealizerPER K) M.toHom] :
    M.imageIso.hom ≫ (imagePredicate M).inclusion.toHom = M.toHom :=
  Quotient.sound ((imagePredicate M).lift_inclusion M (reduces_of_subset fun p _ h => ⟨p.1, h⟩))


end FunctionalRelation

/-- Every categorical subobject admits a strict extensional predicate presentation. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    Fix a realizer-valued PER $X$ with equality $\rho$ and
    extent $E(x):=\rho(x,x)$. The restriction and subobject-presentation proofs in
    §{sec:effective-topos-finite-limits} and §{sec:effective-topos-subobjects-truth-values} use only the
    uniform operations already constructed over a PCA. Thus every subobject of $X$ has a presentation
    $\PERRestriction{X}{\varphi}\hookrightarrow X$, where
    $$\varphi\le E,\qquad \rho(x,y)\land\varphi(x)\le\varphi(y).$$
    Moreover, one such subobject lies below another exactly when their predicates admit a uniform entailment.
    Indeed, an entailment gives a factorization by the restriction lemma. Conversely, a factorization
    transforms a name in the first predicate into an inclusion realizer at some intermediate point;
    extensionality of the second predicate transports that name back to the original point.
-/
theorem RealizerPER.mono_is_predicate_restriction {X Y : (RealizerPER.{r,u} K)} (m : X ⟶ Y) (hm : Mono m) :
    ∃ P : StrictPredicate Y, ∃ e : X ≅ P.restriction, e.hom ≫ P.inclusion.toHom = m := by
  revert hm
  refine Quotient.inductionOn m fun M hm => ?_
  let : Mono (C := (RealizerPER.{r,u} K)) (X := X) (Y := Y) M.toHom := hm
  exact ⟨M.imagePredicate, M.imageIso, M.imageIso_inclusion⟩


/-- A factorization between predicate inclusions gives a uniform implication of predicates. -/
theorem RealizerPER.StrictPredicate.reduces_of_factor {X : (RealizerPER.{r,u} K)} (P Q : StrictPredicate X)
    (l : P.restriction ⟶ Q.restriction) (h : l ≫ Q.inclusion.toHom = P.inclusion.toHom) :
    K.Entails P.val Q.val := by
  revert h
  refine Quotient.inductionOn l fun L h => ?_
  have he := (FunctionalRelation.toHom_eq_iff (FunctionalRelation.comp L Q.inclusion) P.inclusion).mp h
  have hi : K.Entails P.val (fun x => P.inclusion.val x x) :=
    K.and_intro P.strict (K.entails_refl _)
  apply K.entails_trans (K.entails_trans hi (K.reindex_entails (fun x => (x, x)) he.2))
  let Γ : X.Carrier × X.Carrier → Set R :=
    K.predAnd (fun p => L.val p.1 p.2) (fun p => Q.inclusion.val p.2 p.1)
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  exact K.entails_trans (K.and_right _ _)
    (K.reindex_entails (fun p : X.Carrier × X.Carrier => (p.2, p.1)) Q.extensional)

theorem RealizerPER.StrictPredicate.equivalent_of_iso {X : (RealizerPER.{r,u} K)} (P Q : StrictPredicate X)
    (e : P.restriction ≅ Q.restriction) (he : e.hom ≫ Q.inclusion.toHom = P.inclusion.toHom) :
    K.Entails P.val Q.val ∧ K.Entails Q.val P.val := by
  refine ⟨P.reduces_of_factor Q e.hom he, Q.reduces_of_factor P e.inv ?_⟩
  rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]

end PolishSpaceBook.PCARealizability
