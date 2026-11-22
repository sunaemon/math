module

public import PolishSpaceBook.PCARealizabilitySubobjects
public import PolishSpaceBook.PCASeparatedAssemblies
public import Mathlib.Order.Closure

@[expose] public section

/-! # Double-negation closure on categorical subobjects

Strict extensional predicates present all subobjects, with uniform entailment
exactly matching factorization of their inclusions. Closure retains the ambient
extent, and its definition on Subobject is independent of the presentation.
-/
namespace PolishSpaceBook.PCARealizability.RealizerPER
open CategoryTheory
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R} {X : RealizerPER.{r,u} K}

namespace StrictPredicate

def subobject (P : StrictPredicate X) : Subobject X := Subobject.mk P.inclusion.toHom

theorem subobject_le_iff (P Q : StrictPredicate X) :
    P.subobject ≤ Q.subobject ↔ K.Entails P.val Q.val := by
  constructor
  · intro h
    exact P.reduces_of_factor Q (Subobject.ofMkLEMk _ _ h) (Subobject.ofMkLEMk_comp h)
  · intro h
    have hc : K.Entails (fun p : X.Carrier × X.Carrier => P.inclusion.val p.1 p.2)
        (fun p => Q.val p.2) :=
      K.entails_trans (K.and_intro (K.and_left _ _)
        (K.entails_trans (K.and_right _ _) (K.reindex_entails Prod.fst h))) Q.extensional
    exact Subobject.mk_le_mk_of_comm (Q.lift P.inclusion hc).toHom
      (Quotient.sound (Q.lift_inclusion P.inclusion hc))

theorem subobject_eq_iff (P Q : StrictPredicate X) :
    P.subobject = Q.subobject ↔ K.Entails P.val Q.val ∧ K.Entails Q.val P.val := by
  rw [le_antisymm_iff,P.subobject_le_iff Q,Q.subobject_le_iff P]

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Both displayed predicates are strict by first projection. To check extensionality of the closure,
    a name of $\rho(x,y)$ supplies a name of $E(y)$. If $\varphi(x)$ is inhabited, extensionality of
    $\varphi$ makes $\varphi(y)$ inhabited, so any supplied name realizes its double negation.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{RelativeNegation,DoubleNegationClosure}
    \end{mathmeta}
    On strict extensional predicates define
    $$\RelativeNegation{X}{\varphi}:=E\land\neg\varphi,\qquad
    \DoubleNegationClosure{X}{\varphi}:=E\land\neg\neg\varphi.$$
    The extent factors are necessary: a predicate on an object must carry evidence that its argument exists.
-/
def doubleNegClosure (P : StrictPredicate X) : StrictPredicate X where
  val := K.predAnd X.extent (K.predNeg (K.predNeg P.val))
  strict := K.and_left _ _
  extensional := by
    apply K.and_intro (X.extent_right_of (K.and_left _ _))
    apply reduces_of_subset
    rintro ⟨x,y⟩ w ⟨a,bc,hw,ha,⟨b,c,_,_,hc⟩⟩
    apply (K.mem_doubleNeg_iff P.val y w).mpr
    obtain ⟨d,hd⟩ := (K.mem_doubleNeg_iff P.val x c).mp hc
    obtain ⟨t,ht⟩ := P.extensional
    obtain ⟨e,_,he⟩ := ht (x,y) (K.pair a d) ⟨a,d,rfl,ha,hd⟩
    exact ⟨e,he⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Strictness and double-negation introduction give
    $\varphi\le\DoubleNegationClosure{X}{\varphi}$.
-/
theorem le_doubleNegClosure (P : StrictPredicate X) : K.Entails P.val P.doubleNegClosure.val :=
  K.and_intro P.strict (K.entails_doubleNeg P.val)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    If $\varphi\le\psi$, inhabitedness of $\varphi(x)$
    implies inhabitedness of $\psi(x)$, so the same pair of names realizes the corresponding closure
    inclusion. This proves monotonicity and independence of the presentation.
-/
theorem doubleNegClosure_mono (P Q : StrictPredicate X) (h : K.Entails P.val Q.val) :
    K.Entails P.doubleNegClosure.val Q.doubleNegClosure.val := by
  apply reduces_of_subset
  rintro x _ ⟨a,b,rfl,ha,hb⟩
  refine ⟨a,b,rfl,ha,(K.mem_doubleNeg_iff Q.val x b).mpr ?_⟩
  obtain ⟨c,hc⟩ := (K.mem_doubleNeg_iff P.val x b).mp hb
  obtain ⟨t,ht⟩ := h
  obtain ⟨d,_,hd⟩ := ht x c hc
  exact ⟨d,hd⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    A name of
    $\DoubleNegationClosure{X}{(\DoubleNegationClosure{X}{\varphi})}$ implies that $\varphi(x)$ is inhabited;
    retaining its extent component and its second name gives a name of $\DoubleNegationClosure{X}{\varphi}$.
    The reverse entailment is extensivity. Hence the induced operation is idempotent.
-/
theorem doubleNegClosure_idempotent (P : StrictPredicate X) :
    K.Entails P.doubleNegClosure.doubleNegClosure.val P.doubleNegClosure.val := by
  apply reduces_of_subset
  rintro x _ ⟨a,b,rfl,ha,hb⟩
  obtain ⟨_,c,d,_,_,hd⟩ := (K.mem_doubleNeg_iff P.doubleNegClosure.val x b).mp hb
  exact ⟨a,b,rfl,ha,(K.mem_doubleNeg_iff P.val x b).mpr ((K.mem_doubleNeg_iff P.val x d).mp hd)⟩

end StrictPredicate

theorem exists_predicate_subobject (S : Subobject X) :
    ∃ P : StrictPredicate X, P.subobject = S := by
  obtain ⟨P,e,he⟩ := mono_is_predicate_restriction S.arrow inferInstance
  refine ⟨P,?_⟩
  exact (Subobject.mk_eq_mk_of_comm S.arrow P.inclusion.toHom e he).symm.trans (Subobject.mk_arrow S)

noncomputable def predicatePresentation (S : Subobject X) : StrictPredicate X :=
  (exists_predicate_subobject S).choose

theorem predicatePresentation_spec (S : Subobject X) : (predicatePresentation S).subobject = S :=
  (exists_predicate_subobject S).choose_spec

noncomputable def subobjectDoubleNeg (S : Subobject X) : Subobject X :=
  (predicatePresentation S).doubleNegClosure.subobject

theorem subobjectDoubleNeg_predicate (P : StrictPredicate X) :
    subobjectDoubleNeg P.subobject = P.doubleNegClosure.subobject := by
  obtain ⟨h,h'⟩ := (StrictPredicate.subobject_eq_iff _ _).mp (predicatePresentation_spec P.subobject)
  exact (StrictPredicate.subobject_eq_iff _ _).mpr
    ⟨StrictPredicate.doubleNegClosure_mono _ _ h,StrictPredicate.doubleNegClosure_mono _ _ h'⟩

theorem subobjectDoubleNeg_monotone : Monotone (subobjectDoubleNeg (X := X)) := by
  intro S T h
  obtain ⟨P,rfl⟩ := exists_predicate_subobject S
  obtain ⟨Q,rfl⟩ := exists_predicate_subobject T
  rw [subobjectDoubleNeg_predicate,subobjectDoubleNeg_predicate,StrictPredicate.subobject_le_iff]
  exact P.doubleNegClosure_mono Q ((P.subobject_le_iff Q).mp h)

theorem le_subobjectDoubleNeg (S : Subobject X) : S ≤ subobjectDoubleNeg S := by
  obtain ⟨P,rfl⟩ := exists_predicate_subobject S
  rw [subobjectDoubleNeg_predicate,StrictPredicate.subobject_le_iff]
  exact P.le_doubleNegClosure

theorem subobjectDoubleNeg_idempotent (S : Subobject X) :
    subobjectDoubleNeg (subobjectDoubleNeg S) = subobjectDoubleNeg S := by
  obtain ⟨P,rfl⟩ := exists_predicate_subobject S
  rw [subobjectDoubleNeg_predicate,subobjectDoubleNeg_predicate]
  apply (StrictPredicate.subobject_eq_iff _ _).mpr
  exact ⟨P.doubleNegClosure_idempotent,P.doubleNegClosure.le_doubleNegClosure⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Double-negation closure of subobjects
-/
noncomputable def doubleNegClosureOperator (X : RealizerPER.{r,u} K) : ClosureOperator (Subobject X) where
  toFun := subobjectDoubleNeg
  monotone' := subobjectDoubleNeg_monotone
  le_closure' := le_subobjectDoubleNeg
  idempotent' := subobjectDoubleNeg_idempotent

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Double-negation closure of subobjects
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Finally, its fixed
    points are exactly those presentations admitting the stated reverse entailment.
-/
theorem doubleNeg_closed_iff (P : StrictPredicate X) :
    (doubleNegClosureOperator X).IsClosed P.subobject ↔ K.Entails P.doubleNegClosure.val P.val := by
  rw [ClosureOperator.isClosed_iff]
  change subobjectDoubleNeg P.subobject = P.subobject ↔ _
  rw [subobjectDoubleNeg_predicate,StrictPredicate.subobject_eq_iff]
  exact ⟨fun h => h.1,fun h => ⟨h,P.le_doubleNegClosure⟩⟩

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
def equalityPredicate (X : RealizerPER.{r,u} K) : StrictPredicate (product X X) where
  val p := X.rel p.1 p.2
  strict := K.and_intro (X.extent_left_of (K.entails_refl _)) (X.extent_right_of (K.entails_refl _))
  extensional := X.trans_of
    (X.trans_of (X.symm_of (K.entails_trans (K.and_left _ _) (K.and_left _ _))) (K.and_right _ _))
    (K.entails_trans (K.and_left _ _) (K.and_right _ _))

theorem equality_closed_iff_separated (X : RealizerPER.{r,u} K) :
    (doubleNegClosureOperator (product X X)).IsClosed X.equalityPredicate.subobject ↔ X.Separated := by
  rw [doubleNeg_closed_iff]
  rfl

end PolishSpaceBook.PCARealizability.RealizerPER
