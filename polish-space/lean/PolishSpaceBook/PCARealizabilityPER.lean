module

public import PolishSpaceBook.PCARealizabilityTripos

@[expose] public section

/-! # Functional relations over a general PCA

The relation calculus uses the existing uniform entailment operations. All
existential witnesses are semantic points; no tracker receives those points.
-/
namespace PolishSpaceBook.PCARealizability
universe r u v w
variable {R : Type r} {K : PartialCombinatoryAlgebra R}


theorem reduces_of_subset {I : Type*} {φ ψ : I → Set R}
    (h : ∀ i, φ i ⊆ ψ i) : K.Entails φ ψ :=
  ⟨K.identity,fun i a ha => ⟨a,K.application_identity a,h i ha⟩⟩

theorem reduces_cover {I J : Type*} {φ ψ : I → Set R} {θ : I × J → Set R}
    (cover : ∀ i a, a ∈ φ i → ∃ j, a ∈ θ (i,j))
    (h : K.Entails θ (fun p => ψ p.1)) : K.Entails φ ψ := by
  obtain ⟨e,he⟩ := h
  refine ⟨e,fun i a ha => ?_⟩
  obtain ⟨j,hj⟩ := cover i a ha
  exact he (i,j) a hj

abbrev RealizerRelation (A : Type u) (B : Type v) := A → B → Set R

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    The functional-relation construction above works over every PCA. Composition is
    $$ (G\circ F)(x,z):=\bigcup_y\{\PCAPair{a}{b}:a\in F(x,y),\ b\in G(y,z)\}, $$
    and equality of arrows is mutual uniform entailment. Pairing and projections, together with the
    strictness, extensionality, and PER trackers, prove the identity and associativity laws exactly as in
    §{sec:effective-topos-objects-morphisms}. Intermediate points occur only as witnesses in these unions.
    The one-inclusion criterion from §{sec:effective-topos-subobjects-truth-values} also applies: for total
    functional relations, a uniform inclusion in one direction implies a uniform inclusion in the other.
    Its proof uses strictness, totality, single-valuedness, and extensionality, all available over any PCA.
-/
def relationComp {A B C : Type*} (F : RealizerRelation (R := R) A B)
    (G : RealizerRelation (R := R) B C) : RealizerRelation (R := R) A C :=
  fun x z => {a | ∃ y, ∃ b c, a = K.pair b c ∧ b ∈ F x y ∧ c ∈ G y z}

theorem relationComp_intro {I A B C : Type*} {Γ : I → Set R}
    {F : RealizerRelation (R := R) A B} {G : RealizerRelation (R := R) B C} {x : I → A} {y : I → B} {z : I → C}
    (hF : K.Entails Γ (fun i => F (x i) (y i)))
    (hG : K.Entails Γ (fun i => G (y i) (z i))) :
    K.Entails Γ (fun i => relationComp (K := K) F G (x i) (z i)) :=
  K.entails_trans (K.and_intro hF hG) (reduces_of_subset fun i _ ha => ⟨y i, ha⟩)

/-- A PER is allowed to have empty extent; symmetry and transitivity have uniform trackers. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Setting $\mathcal C = \SetCatU$ and $\mathcal P = \mathcal P_{K_1}$ in the realizability tripos
    gives
    $$\EffCat \;:=\; \SetCatU[\mathcal P_{K_1}].$$
    An object of $\EffCat$ is a $U$-small set $I$ together with a $\mathcal P_{K_1}$-PER $\sim$, which one can read as: $I$
    is a set of *would-be elements*, and $\sim(i, j)$ specifies the realizers witnessing that $i$ and $j$ name the same
    actual element. The extent $E_\sim(i) = \sim(i, i)$ is the set of realizers of $i$, recovering the assembly perspective
    when $\sim$ is the equality PER. Each object and morphism uses $U$-small data, although the collection of all
    objects is $U$-large, so $\EffCat$ is locally $U$-small in the sense
    of §{sec:cat-universe}.
-/
structure RealizerPER (K : PartialCombinatoryAlgebra R) where
  Carrier : Type u
  rel : RealizerRelation (R := R) Carrier Carrier
  symmetry : K.Entails (fun p : Carrier × Carrier => rel p.1 p.2)
    (fun p => rel p.2 p.1)
  transitivity : K.Entails
    (K.predAnd (fun p : Carrier × Carrier × Carrier => rel p.1 p.2.1)
      (fun p => rel p.2.1 p.2.2)) (fun p => rel p.1 p.2.2)

namespace RealizerPER

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Setting $\mathcal C = \SetCatU$ and $\mathcal P = \mathcal P_{K_1}$ in the realizability tripos
    gives
    $$\EffCat \;:=\; \SetCatU[\mathcal P_{K_1}].$$
    An object of $\EffCat$ is a $U$-small set $I$ together with a $\mathcal P_{K_1}$-PER $\sim$, which one can read as: $I$
    is a set of *would-be elements*, and $\sim(i, j)$ specifies the realizers witnessing that $i$ and $j$ name the same
    actual element. The extent $E_\sim(i) = \sim(i, i)$ is the set of realizers of $i$, recovering the assembly perspective
    when $\sim$ is the equality PER. Each object and morphism uses $U$-small data, although the collection of all
    objects is $U$-large, so $\EffCat$ is locally $U$-small in the sense
    of §{sec:cat-universe}.
-/
def extent (X : RealizerPER K) (x : X.Carrier) : Set R := X.rel x x

theorem symm_of (X : RealizerPER K) {I : Type*} {Γ : I → Set R} {x y : I → X.Carrier}
    (h : K.Entails Γ (fun i => X.rel (x i) (y i))) :
    K.Entails Γ (fun i => X.rel (y i) (x i)) :=
  K.entails_trans h (K.reindex_entails (fun i => (x i, y i)) X.symmetry)

theorem trans_of (X : RealizerPER K) {I : Type*} {Γ : I → Set R} {x y z : I → X.Carrier}
    (h₁ : K.Entails Γ (fun i => X.rel (x i) (y i)))
    (h₂ : K.Entails Γ (fun i => X.rel (y i) (z i))) :
    K.Entails Γ (fun i => X.rel (x i) (z i)) :=
  K.entails_trans (K.and_intro h₁ h₂)
    (K.reindex_entails (fun i => (x i, y i, z i)) X.transitivity)

/-- Extent evidence is derived uniformly, not assumed for every representative. -/
theorem extent_left_of (X : RealizerPER K) {I : Type*} {Γ : I → Set R} {x y : I → X.Carrier}
    (h : K.Entails Γ (fun i => X.rel (x i) (y i))) :
    K.Entails Γ (fun i => X.extent (x i)) := X.trans_of h (X.symm_of h)

theorem extent_right_of (X : RealizerPER K) {I : Type*} {Γ : I → Set R} {x y : I → X.Carrier}
    (h : K.Entails Γ (fun i => X.rel (x i) (y i))) :
    K.Entails Γ (fun i => X.extent (y i)) := X.trans_of (X.symm_of h) h

end RealizerPER

/-- The four conditions use one tracker per condition, uniform in all representatives. -/
structure FunctionalRelation (X Y : (RealizerPER.{r,u} K)) where
  val : RealizerRelation (R := R) X.Carrier Y.Carrier
  strict : K.Entails (fun p : X.Carrier × Y.Carrier => val p.1 p.2)
    (K.predAnd (fun p => X.extent p.1) (fun p => Y.extent p.2))
  extensional : K.Entails
    (K.predAnd
      (K.predAnd (fun p : X.Carrier × X.Carrier × Y.Carrier × Y.Carrier => X.rel p.1 p.2.1)
        (fun p => val p.1 p.2.2.1)) (fun p => Y.rel p.2.2.1 p.2.2.2))
    (fun p => val p.2.1 p.2.2.2)
  single : K.Entails
    (K.predAnd (fun p : X.Carrier × Y.Carrier × Y.Carrier => val p.1 p.2.1)
      (fun p => val p.1 p.2.2)) (fun p => Y.rel p.2.1 p.2.2)
  total : K.Entails X.extent (fun x => {a | ∃ y, a ∈ val x y})

namespace FunctionalRelation

theorem strict_left_of {X Y : RealizerPER K} (F : FunctionalRelation X Y)
    {I : Type*} {Γ : I → Set R} {x : I → X.Carrier} {y : I → Y.Carrier}
    (h : K.Entails Γ (fun i => F.val (x i) (y i))) : K.Entails Γ (fun i => X.extent (x i)) :=
  K.entails_trans h (K.entails_trans (K.reindex_entails (fun i => (x i, y i)) F.strict)
    (K.and_left _ _))

theorem strict_right_of {X Y : RealizerPER K} (F : FunctionalRelation X Y)
    {I : Type*} {Γ : I → Set R} {x : I → X.Carrier} {y : I → Y.Carrier}
    (h : K.Entails Γ (fun i => F.val (x i) (y i))) : K.Entails Γ (fun i => Y.extent (y i)) :=
  K.entails_trans h (K.entails_trans (K.reindex_entails (fun i => (x i, y i)) F.strict)
    (K.and_right _ _))

theorem ext_of {X Y : RealizerPER K} (F : FunctionalRelation X Y)
    {I : Type*} {Γ : I → Set R} {x x' : I → X.Carrier} {y y' : I → Y.Carrier}
    (hx : K.Entails Γ (fun i => X.rel (x i) (x' i)))
    (hF : K.Entails Γ (fun i => F.val (x i) (y i)))
    (hy : K.Entails Γ (fun i => Y.rel (y i) (y' i))) :
    K.Entails Γ (fun i => F.val (x' i) (y' i)) :=
  K.entails_trans (K.and_intro (K.and_intro hx hF) hy)
    (K.reindex_entails (fun i => (x i, x' i, y i, y' i)) F.extensional)

theorem single_of {X Y : RealizerPER K} (F : FunctionalRelation X Y)
    {I : Type*} {Γ : I → Set R} {x : I → X.Carrier} {y y' : I → Y.Carrier}
    (hF : K.Entails Γ (fun i => F.val (x i) (y i)))
    (hF' : K.Entails Γ (fun i => F.val (x i) (y' i))) :
    K.Entails Γ (fun i => Y.rel (y i) (y' i)) :=
  K.entails_trans (K.and_intro hF hF')
    (K.reindex_entails (fun i => (x i, y i, y' i)) F.single)

def identity (X : RealizerPER K) : FunctionalRelation X X where
  val := X.rel
  strict := K.and_intro (X.extent_left_of (K.entails_refl _))
    (X.extent_right_of (K.entails_refl _))
  extensional := X.trans_of
    (X.trans_of (X.symm_of (K.entails_trans (K.and_left _ _) (K.and_left _ _)))
      (K.entails_trans (K.and_left _ _) (K.and_right _ _))) (K.and_right _ _)
  single := X.trans_of (X.symm_of (K.and_left _ _)) (K.and_right _ _)
  total := reduces_of_subset fun x _ ha => ⟨x, ha⟩


/-- Composition carries paired realizers, with no encoded intermediate representative. -/
def comp {X Y Z : RealizerPER K} (F : FunctionalRelation X Y) (G : FunctionalRelation Y Z) :
    FunctionalRelation X Z where
  val := relationComp (K := K) F.val G.val
  strict := by
    let Γ : (X.Carrier × Z.Carrier) × Y.Carrier → Set R :=
      K.predAnd (fun p => F.val p.1.1 p.2) (fun p => G.val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    exact K.and_intro (F.strict_left_of (K.and_left _ _))
      (G.strict_right_of (K.and_right _ _))
  extensional := by
    let Γ : (X.Carrier × X.Carrier × Z.Carrier × Z.Carrier) × Y.Carrier → Set R :=
      K.predAnd
        (K.predAnd (fun p => X.rel p.1.1 p.1.2.1)
          (K.predAnd (fun p => F.val p.1.1 p.2) (fun p => G.val p.2 p.1.2.2.1)))
        (fun p => Z.rel p.1.2.2.1 p.1.2.2.2)
    apply reduces_cover (θ := Γ)
    · intro i a ha
      obtain ⟨ab,c,rfl,⟨a,b,rfl,ha,⟨y,hy⟩⟩,hc⟩ := ha
      exact ⟨y,_,_,rfl,⟨_,_,rfl,ha,hy⟩,hc⟩
    · have hF : K.Entails Γ (fun p => F.val p.1.1 p.2) :=
        K.entails_trans (K.entails_trans (K.and_left _ _) (K.and_right _ _))
          (K.and_left _ _)
      have hG : K.Entails Γ (fun p => G.val p.2 p.1.2.2.1) :=
        K.entails_trans (K.entails_trans (K.and_left _ _) (K.and_right _ _))
          (K.and_right _ _)
      exact relationComp_intro
        (F.ext_of (K.entails_trans (K.and_left _ _) (K.and_left _ _))
          hF (F.strict_right_of hF))
        (G.ext_of (G.strict_left_of hG) hG (K.and_right _ _))
  single := by
    let Γ : (X.Carrier × Z.Carrier × Z.Carrier) × (Y.Carrier × Y.Carrier) → Set R :=
      K.predAnd
        (K.predAnd (fun p => F.val p.1.1 p.2.1) (fun p => G.val p.2.1 p.1.2.1))
        (K.predAnd (fun p => F.val p.1.1 p.2.2) (fun p => G.val p.2.2 p.1.2.2))
    apply reduces_cover (θ := Γ)
    · intro i a ha
      obtain ⟨a,b,rfl,⟨y,hy⟩,⟨y',hy'⟩⟩ := ha
      exact ⟨(y,y'),a,b,rfl,hy,hy'⟩
    · have hF : K.Entails Γ (fun p => F.val p.1.1 p.2.1) :=
        K.entails_trans (K.and_left _ _) (K.and_left _ _)
      have hF' : K.Entails Γ (fun p => F.val p.1.1 p.2.2) :=
        K.entails_trans (K.and_right _ _) (K.and_left _ _)
      have hG : K.Entails Γ (fun p => G.val p.2.1 p.1.2.1) :=
        K.entails_trans (K.and_left _ _) (K.and_right _ _)
      have hG' : K.Entails Γ (fun p => G.val p.2.2 p.1.2.2) :=
        K.entails_trans (K.and_right _ _) (K.and_right _ _)
      exact G.single_of (G.ext_of (F.single_of hF hF') hG (G.strict_right_of hG)) hG'
  total := by
    apply K.entails_trans F.total
    apply reduces_cover (θ := fun p : X.Carrier × Y.Carrier => F.val p.1 p.2)
    · exact fun _ _ h => h
    · have hg : K.Entails (fun p : X.Carrier × Y.Carrier => F.val p.1 p.2)
          (fun p => {a | ∃ z, a ∈ G.val p.2 z}) :=
        K.entails_trans (F.strict_right_of (K.entails_refl _))
          (K.reindex_entails Prod.snd G.total)
      apply K.entails_trans (K.and_intro (K.entails_refl _) hg)
      apply reduces_of_subset
      intro p a ha
      obtain ⟨a,b,rfl,ha,⟨z,hz⟩⟩ := ha
      exact ⟨z,p.2,a,b,rfl,ha,hz⟩


/-- A single transformer works for every pair of representatives. -/
def LE {X Y : RealizerPER K} (F G : FunctionalRelation X Y) : Prop :=
  K.Entails (fun p : X.Carrier × Y.Carrier => F.val p.1 p.2) (fun p => G.val p.1 p.2)

def Equivalent {X Y : RealizerPER K} (F G : FunctionalRelation X Y) : Prop := LE F G ∧ LE G F

instance relationSetoid (X Y : RealizerPER K) : Setoid (FunctionalRelation X Y) where
  r := Equivalent
  iseqv := ⟨fun _ => ⟨K.entails_refl _, K.entails_refl _⟩,
    fun h => ⟨h.2, h.1⟩,
    fun h k => ⟨K.entails_trans h.1 k.1, K.entails_trans k.2 h.2⟩⟩

theorem comp_mono {X Y Z : RealizerPER K} {F F' : FunctionalRelation X Y}
    {G G' : FunctionalRelation Y Z} (hF : LE F F') (hG : LE G G') :
    LE (comp F G) (comp F' G') := by
  let Γ : (X.Carrier × Z.Carrier) × Y.Carrier → Set R :=
    K.predAnd (fun p => F.val p.1.1 p.2) (fun p => G.val p.2 p.1.2)
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  exact relationComp_intro
    (K.entails_trans (K.and_left _ _) (K.reindex_entails (fun p : (X.Carrier × Z.Carrier) × Y.Carrier => (p.1.1, p.2)) hF))
    (K.entails_trans (K.and_right _ _) (K.reindex_entails (fun p : (X.Carrier × Z.Carrier) × Y.Carrier => (p.2, p.1.2)) hG))

theorem comp_congr {X Y Z : RealizerPER K} {F F' : FunctionalRelation X Y}
    {G G' : FunctionalRelation Y Z} (hF : Equivalent F F') (hG : Equivalent G G') :
    Equivalent (comp F G) (comp F' G') :=
  ⟨comp_mono hF.1 hG.1, comp_mono hF.2 hG.2⟩

theorem identity_comp {X Y : RealizerPER K} (F : FunctionalRelation X Y) :
    Equivalent (comp (identity X) F) F := by
  constructor
  · let Γ : (X.Carrier × Y.Carrier) × X.Carrier → Set R :=
      K.predAnd (fun p => X.rel p.1.1 p.2) (fun p => F.val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    exact F.ext_of (X.symm_of (K.and_left _ _)) (K.and_right _ _)
      (F.strict_right_of (K.and_right _ _))
  · exact relationComp_intro (F.strict_left_of (K.entails_refl _)) (K.entails_refl _)

theorem comp_identity {X Y : RealizerPER K} (F : FunctionalRelation X Y) :
    Equivalent (comp F (identity Y)) F := by
  constructor
  · let Γ : (X.Carrier × Y.Carrier) × Y.Carrier → Set R :=
      K.predAnd (fun p => F.val p.1.1 p.2) (fun p => Y.rel p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    exact F.ext_of (F.strict_left_of (K.and_left _ _)) (K.and_left _ _)
      (K.and_right _ _)
  · exact relationComp_intro (K.entails_refl _) (F.strict_right_of (K.entails_refl _))

/-- Reassociate encoded pairs; no computation on the intermediate points is used. -/
theorem comp_assoc {W X Y Z : RealizerPER K} (F : FunctionalRelation W X)
    (G : FunctionalRelation X Y) (H : FunctionalRelation Y Z) :
    Equivalent (comp (comp F G) H) (comp F (comp G H)) := by
  constructor
  · let Γ : (W.Carrier × Z.Carrier) × (X.Carrier × Y.Carrier) → Set R :=
      K.predAnd
        (K.predAnd (fun p => F.val p.1.1 p.2.1) (fun p => G.val p.2.1 p.2.2))
        (fun p => H.val p.2.2 p.1.2)
    apply reduces_cover (θ := Γ)
    · intro i a ha
      obtain ⟨y,ab,c,rfl,⟨x,a,b,rfl,hF,hG⟩,hH⟩ := ha
      exact ⟨(x,y),_,c,rfl,⟨a,b,rfl,hF,hG⟩,hH⟩
    · exact relationComp_intro
        (K.entails_trans (K.and_left _ _) (K.and_left _ _))
        (relationComp_intro (K.entails_trans (K.and_left _ _) (K.and_right _ _))
          (K.and_right _ _))
  · let Γ : (W.Carrier × Z.Carrier) × (X.Carrier × Y.Carrier) → Set R :=
      K.predAnd (fun p => F.val p.1.1 p.2.1)
        (K.predAnd (fun p => G.val p.2.1 p.2.2) (fun p => H.val p.2.2 p.1.2))
    apply reduces_cover (θ := Γ)
    · intro i a ha
      obtain ⟨x,a,bc,rfl,hF,⟨y,b,c,rfl,hG,hH⟩⟩ := ha
      exact ⟨(x,y),a,_,rfl,hF,⟨b,c,rfl,hG,hH⟩⟩
    · exact relationComp_intro
        (relationComp_intro (K.and_left _ _)
          (K.entails_trans (K.and_right _ _) (K.and_left _ _)))
        (K.entails_trans (K.and_right _ _) (K.and_right _ _))

end FunctionalRelation

/-- Morphisms are uniform-equivalence classes, not pointwise inhabitedness classes. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The functional-relation presentation of the topos in §{sec:realizability-tripos} gives
    morphisms as equivalence classes of relations instead.
-/
abbrev RealizerPER.Hom (X Y : (RealizerPER.{r,u} K)) := Quotient (FunctionalRelation.relationSetoid X Y)

def FunctionalRelation.toHom {X Y : RealizerPER K} (F : FunctionalRelation X Y) : RealizerPER.Hom X Y :=
  Quotient.mk _ F

@[simp] theorem FunctionalRelation.toHom_eq_iff {X Y : RealizerPER K} (F G : FunctionalRelation X Y) :
    F.toHom = G.toHom ↔ FunctionalRelation.Equivalent F G := Quotient.eq

def RealizerPER.compose {X Y Z : RealizerPER K} : X.Hom Y → Y.Hom Z → X.Hom Z :=
  Quotient.map₂ FunctionalRelation.comp (fun _ _ hF _ _ hG => FunctionalRelation.comp_congr hF hG)

/-- The category laws hold literally after quotienting the relations. -/
instance realizabilityPERCategory : CategoryTheory.Category (RealizerPER.{r,u} K) where
  Hom := RealizerPER.Hom
  id X := (FunctionalRelation.identity X).toHom
  comp := RealizerPER.compose
  id_comp f := Quotient.inductionOn f fun F => Quotient.sound (FunctionalRelation.identity_comp F)
  comp_id f := Quotient.inductionOn f fun F => Quotient.sound (FunctionalRelation.comp_identity F)
  assoc f g h := Quotient.inductionOn₃ f g h fun F G H =>
    Quotient.sound (FunctionalRelation.comp_assoc F G H)

namespace RealizerPER
/-- A function on representatives whose action on equality has one uniform tracker. -/
structure Map (X Y : RealizerPER.{r,u} K) where
  toFun : X.Carrier → Y.Carrier
  preserves : K.Entails (fun p : X.Carrier × X.Carrier => X.rel p.1 p.2)
    (fun p => Y.rel (toFun p.1) (toFun p.2))

theorem Map.map_of {X Y : RealizerPER K} (f : Map X Y) {I : Type*} {Γ : I → Set R}
    {x x' : I → X.Carrier} (h : K.Entails Γ (fun i => X.rel (x i) (x' i))) :
    K.Entails Γ (fun i => Y.rel (f.toFun (x i)) (f.toFun (x' i))) :=
  K.entails_trans h (K.reindex_entails (fun i => (x i, x' i)) f.preserves)

/-- The extent factor ensures strictness even at absent representatives. -/
def Map.graph {X Y : RealizerPER K} (f : Map X Y) : FunctionalRelation X Y where
  val x y := {a | ∃ b c, a = K.pair b c ∧ b ∈ X.extent x ∧ c ∈ Y.rel (f.toFun x) y}
  strict := K.and_intro (K.and_left _ _)
    (Y.extent_right_of (K.and_right _ _))
  extensional := by
    apply K.and_intro
    · exact X.extent_right_of (K.entails_trans (K.and_left _ _) (K.and_left _ _))
    · exact Y.trans_of
        (Y.trans_of
          (Y.symm_of (f.map_of (K.entails_trans (K.and_left _ _) (K.and_left _ _))))
          (K.entails_trans (K.entails_trans (K.and_left _ _) (K.and_right _ _))
            (K.and_right _ _))) (K.and_right _ _)
  single := Y.trans_of (Y.symm_of (K.entails_trans (K.and_left _ _) (K.and_right _ _)))
    (K.entails_trans (K.and_right _ _) (K.and_right _ _))
  total := K.entails_trans (K.and_intro (K.entails_refl _) (f.map_of (K.entails_refl _)))
    (reduces_of_subset fun x _ h => ⟨f.toFun x, h⟩)

end RealizerPER

namespace FunctionalRelation
theorem equivalent_of_le {X Y : RealizerPER.{r,u} K} {F G : FunctionalRelation X Y}
    (h : LE F G) : Equivalent F G := by
  refine ⟨h, ?_⟩
  apply K.entails_trans (K.and_intro (K.entails_refl _)
    (K.entails_trans (G.strict_left_of (K.entails_refl _)) (K.reindex_entails Prod.fst F.total)))
  let Γ : (X.Carrier × Y.Carrier) × Y.Carrier → Set R :=
    K.predAnd (fun p => G.val p.1.1 p.1.2) (fun p => F.val p.1.1 p.2)
  apply reduces_cover (θ := Γ)
  · rintro p _ ⟨a,b,rfl,ha,⟨y,hy⟩⟩
    exact ⟨y,a,b,rfl,ha,hy⟩
  · have hF : K.Entails Γ (fun p => F.val p.1.1 p.2) := K.and_right _ _
    have hG : K.Entails Γ (fun p => G.val p.1.1 p.2) :=
      K.entails_trans hF (K.reindex_entails (fun p : (X.Carrier × Y.Carrier) × Y.Carrier => (p.1.1, p.2)) h)
    exact F.ext_of (F.strict_left_of hF) hF (G.single_of hG (K.and_left _ _))

end FunctionalRelation

end PolishSpaceBook.PCARealizability
