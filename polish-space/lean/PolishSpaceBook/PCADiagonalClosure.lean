module

public import PolishSpaceBook.PCADoubleNegationClosure
public import PolishSpaceBook.PCARealizerMaps
public import PolishSpaceBook.PCARealizabilityProducts

@[expose] public section

/-! # The categorical diagonal and double-negation separation

The equality-predicate restriction is isomorphic over the product to the
categorical diagonal. Thus the earlier predicate condition is exactly closedness
of this actual monomorphism, not a replacement definition on representatives.
-/
namespace PolishSpaceBook.PCARealizability.RealizerPER
open CategoryTheory
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}

def diagonalMap (X : RealizerPER.{r,u} K) : Map X (product X X) where
  toFun x := (x,x)
  preserves := K.and_intro (K.entails_refl _) (K.entails_refl _)

theorem diagonal_fst (X : RealizerPER.{r,u} K) :
    X.diagonalMap.graph.toHom ≫ (fstRelation X X).toHom = 𝟙 X :=
  (Quotient.sound (X.diagonalMap.graph_comp (fstMap X X))).trans
    (Quotient.sound (Map.graph_id X))

theorem diagonal_snd (X : RealizerPER.{r,u} K) :
    X.diagonalMap.graph.toHom ≫ (sndRelation X X).toHom = 𝟙 X :=
  (Quotient.sound (X.diagonalMap.graph_comp (sndMap X X))).trans
    (Quotient.sound (Map.graph_id X))

def diagonalLift (X : RealizerPER.{r,u} K) : Map X X.equalityPredicate.restriction where
  toFun x := (x,x)
  preserves := K.and_intro (K.and_intro (K.entails_refl _) (K.entails_refl _))
    (X.extent_left_of (K.entails_refl _))

def diagonalInverse (X : RealizerPER.{r,u} K) : Map X.equalityPredicate.restriction X where
  toFun := Prod.fst
  preserves := K.entails_trans (K.and_left _ _) (K.and_left _ _)

theorem diagonal_inverse_related (X : RealizerPER.{r,u} K) :
    K.Entails X.equalityPredicate.restriction.extent
      (fun p => X.equalityPredicate.restriction.rel (p.1,p.1) p) :=
  K.and_intro
    (K.and_intro (K.entails_trans (K.and_left _ _) (K.and_left _ _)) (K.and_right _ _))
    (K.entails_trans (K.and_left _ _) (K.and_left _ _))

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    The function $x\mapsto(x,x)$ preserves equality into this restriction, and first projection preserves
    equality back to $X$. Their composite on $X$ is the identity. For the other composite, an extent
    realizer in the restriction has the form $\PCAPair{\PCAPair{a}{b}}{c}$, where the three components
    realize $E(x),E(y),\rho(x,y)$. The transformation
    $$\PCAPair{\PCAPair{a}{b}}{c}\longmapsto\PCAPair{\PCAPair{a}{c}}{a}$$
    realizes equality between $(x,x)$ and $(x,y)$ in the restriction. Hence the graphs of the two functions
    are inverse arrows.
-/
def diagonalIso (X : RealizerPER.{r,u} K) : X ≅ X.equalityPredicate.restriction where
  hom := X.diagonalLift.graph.toHom
  inv := X.diagonalInverse.graph.toHom
  hom_inv_id := (Quotient.sound (X.diagonalLift.graph_comp X.diagonalInverse)).trans
    (Quotient.sound (Map.graph_id X))
  inv_hom_id := (Quotient.sound (X.diagonalInverse.graph_comp X.diagonalLift)).trans
    ((Quotient.sound (Map.graph_equivalent_of_related _ (Map.id _)
      X.diagonal_inverse_related)).trans (Quotient.sound (Map.graph_id _)))

def StrictPredicate.forget {X : RealizerPER.{r,u} K} (P : StrictPredicate X) : Map P.restriction X where
  toFun := id
  preserves := K.and_left _ _

theorem StrictPredicate.forget_graph {X : RealizerPER.{r,u} K} (P : StrictPredicate X) :
    P.forget.graph.Equivalent P.inclusion :=
  FunctionalRelation.equivalent_of_le
    (K.and_intro (K.and_right _ _) (K.entails_trans (K.and_left _ _) (K.and_right _ _)))

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    The resulting isomorphism commutes with the inclusion into the product, so this
    restriction represents the actual diagonal subobject.
-/
theorem diagonalIso_inclusion (X : RealizerPER.{r,u} K) :
    X.diagonalIso.hom ≫ X.equalityPredicate.inclusion.toHom = X.diagonalMap.graph.toHom := by
  rw [← show X.equalityPredicate.forget.graph.toHom = X.equalityPredicate.inclusion.toHom from
    Quotient.sound X.equalityPredicate.forget_graph]
  exact Quotient.sound (X.diagonalLift.graph_comp X.equalityPredicate.forget)

instance diagonal_mono (X : RealizerPER.{r,u} K) : Mono (C := RealizerPER K) X.diagonalMap.graph.toHom := by
  rw [← X.diagonalIso_inclusion]
  infer_instance

def diagonalSubobject (X : RealizerPER.{r,u} K) : Subobject (product X X) :=
  Subobject.mk X.diagonalMap.graph.toHom

theorem diagonal_subobject_eq_predicate (X : RealizerPER.{r,u} K) :
    X.diagonalSubobject = X.equalityPredicate.subobject :=
  Subobject.mk_eq_mk_of_comm _ _ X.diagonalIso X.diagonalIso_inclusion

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Closed diagonal criterion
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Applying the preceding proposition to
    $\delta$ with ambient extent $D$ proves the criterion.
-/
theorem diagonal_closed_iff_separated (X : RealizerPER.{r,u} K) :
    (doubleNegClosureOperator (product X X)).IsClosed X.diagonalSubobject ↔ X.Separated := by
  rw [X.diagonal_subobject_eq_predicate,X.equality_closed_iff_separated]

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    In particular, the assembly reconstruction
    applies to every object with closed diagonal,
-/
theorem closed_diagonal_in_essentialImage (X : RealizerPER.{r,u} K)
    (h : (doubleNegClosureOperator (product X X)).IsClosed X.diagonalSubobject) :
    (Assembly.realizerEmbedding (K := K)).essImage X :=
  X.separated_in_essentialImage ((X.diagonal_closed_iff_separated).mp h)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    and embedded assemblies have closed diagonals.
-/
theorem assembly_closed_diagonal (A : Assembly.{r,u} K) :
    (doubleNegClosureOperator (product A.toRealizerPER A.toRealizerPER)).IsClosed
      A.toRealizerPER.diagonalSubobject :=
  (A.toRealizerPER.diagonal_closed_iff_separated).mpr (assembly_separated A)

end PolishSpaceBook.PCARealizability.RealizerPER
