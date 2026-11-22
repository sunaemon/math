module

public import PolishSpaceBook.PCADoubleNegationClosure

@[expose] public section

/-! # Pseudocomplements in the categorical subobject order

The universal property of relative negation identifies the previously
constructed closure with double pseudocomplementation on actual subobjects.
-/
namespace PolishSpaceBook.PCARealizability.RealizerPER
open CategoryTheory
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R} {X : RealizerPER.{r,u} K}
namespace StrictPredicate

def bottom (X : RealizerPER.{r,u} K) : StrictPredicate X where
  val _ := ∅
  strict := K.bot_entails _
  extensional := K.and_right _ _

def meet (P Q : StrictPredicate X) : StrictPredicate X where
  val := K.predAnd P.val Q.val
  strict := K.entails_trans (K.and_left _ _) P.strict
  extensional := K.and_intro
    (K.entails_trans (K.and_intro (K.and_left _ _)
      (K.entails_trans (K.and_right _ _) (K.and_left _ _))) P.extensional)
    (K.entails_trans (K.and_intro (K.and_left _ _)
      (K.entails_trans (K.and_right _ _) (K.and_right _ _))) Q.extensional)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For relative negation, if $\varphi(x)$ is empty but $\varphi(y)$ were inhabited, symmetry of $\rho$
    and extensionality of $\varphi$ would give a contradiction. Thus $\varphi(y)$ is empty, and again
    any supplied name realizes the required negation. Pairing with the computed extent gives uniform
    trackers in both cases.
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
def negation (P : StrictPredicate X) : StrictPredicate X where
  val := K.predAnd X.extent (K.predNeg P.val)
  strict := K.and_left _ _
  extensional := by
    apply K.and_intro (X.extent_right_of (K.and_left _ _))
    apply reduces_of_subset
    rintro ⟨x,y⟩ w ⟨a,bc,_,ha,⟨b,c,_,_,hc⟩⟩
    apply (K.mem_predNeg_iff P.val y w).mpr
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro d hd
    obtain ⟨s,hs⟩ := X.symmetry
    obtain ⟨e,_,he⟩ := hs (x,y) a ha
    obtain ⟨t,ht⟩ := P.extensional
    obtain ⟨f,_,hf⟩ := ht (y,x) (K.pair e d) ⟨e,d,rfl,he,hd⟩
    have hp := (K.mem_predNeg_iff P.val x c).mp hc
    simp [hp] at hf

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    The empty predicate represents the least subobject,
-/
theorem bottom_subobject_le (S : Subobject X) : (bottom X).subobject ≤ S := by
  obtain ⟨P,rfl⟩ := exists_predicate_subobject S
  exact ((bottom X).subobject_le_iff P).mpr (K.bot_entails _)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    and conjunction represents the meet: a predicate
    entails a conjunction exactly when it entails both components.
-/
theorem le_meet_subobject_iff (S : Subobject X) (P Q : StrictPredicate X) :
    S ≤ (P.meet Q).subobject ↔ S ≤ P.subobject ∧ S ≤ Q.subobject := by
  obtain ⟨T,rfl⟩ := exists_predicate_subobject S
  simp only [subobject_le_iff]
  exact ⟨fun h => ⟨K.entails_trans h (K.and_left _ _),K.entails_trans h (K.and_right _ _)⟩,
    fun h => K.and_intro h.1 h.2⟩

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
    The implication adjunction gives
    $$\psi\land\varphi\le\bot\quad\Longleftrightarrow\quad
    \psi\le\RelativeNegation{X}{\varphi}$$
    for every strict extensional $\psi$, since its strictness already supplies $E$. This proves the
    pseudocomplement universal property.
-/
theorem negation_universal (P Q : StrictPredicate X) :
    (Q.meet P).subobject ≤ (bottom X).subobject ↔ Q.subobject ≤ P.negation.subobject := by
  simp only [subobject_le_iff]
  constructor
  · intro h
    exact K.and_intro Q.strict ((K.imp_adjunction Q.val P.val (fun _ => ∅)).mp h)
  · intro h
    exact (K.imp_adjunction Q.val P.val (fun _ => ∅)).mpr (K.entails_trans h (K.and_right _ _))

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
    On an input carrying an $E(x)$-name, the set
    $(E\land\neg\varphi)(x)$ is empty exactly when $\varphi(x)$ is inhabited. Applying the negation clause
    once more therefore gives
    $$\RelativeNegation{X}{(\RelativeNegation{X}{\varphi})}\equiv
    \DoubleNegationClosure{X}{\varphi},$$
    with the identity tracker in both directions.
-/
theorem double_negation_subobject (P : StrictPredicate X) :
    P.negation.negation.subobject = P.doubleNegClosure.subobject := by
  classical
  apply (subobject_eq_iff _ _).mpr
  constructor
  · apply reduces_of_subset
    rintro x _ ⟨a,b,rfl,ha,hb⟩
    refine ⟨a,b,rfl,ha,(K.mem_doubleNeg_iff P.val x b).mpr ?_⟩
    by_contra hn
    have hp : P.val x = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hne : K.pair a b ∈ P.negation.val x :=
      ⟨a,b,rfl,ha,(K.mem_predNeg_iff P.val x b).mpr hp⟩
    have hempty := (K.mem_predNeg_iff P.negation.val x b).mp hb
    simp [hempty] at hne
  · apply reduces_of_subset
    rintro x _ ⟨a,b,rfl,ha,hb⟩
    refine ⟨a,b,rfl,ha,(K.mem_predNeg_iff P.negation.val x b).mpr ?_⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨c,d,_,_,hd⟩
    obtain ⟨e,he⟩ := (K.mem_doubleNeg_iff P.val x b).mp hb
    have hempty := (K.mem_predNeg_iff P.val x d).mp hd
    simp [hempty] at he

end StrictPredicate
end PolishSpaceBook.PCARealizability.RealizerPER
