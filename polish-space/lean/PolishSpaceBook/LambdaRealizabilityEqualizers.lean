module

public import PolishSpaceBook.LambdaRealizabilityProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

@[expose] public section

/-! # Predicate restrictions and equalizers of realizability PERs -/
namespace PolishSpaceBook.LambdaIndexPCA
open CategoryTheory Limits
universe u
namespace RealizerPER

structure StrictPredicate (X : RealizerPER.{u}) where
  val : X.Carrier → Set ℕ
  strict : Reduces val X.extent
  extensional : Reduces
    (realizabilityAnd (fun p : X.Carrier × X.Carrier => X.rel p.1 p.2) (fun p => val p.1))
    (fun p => val p.2)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{realizability predicate restriction}{Restriction by a realizability predicate}]
-/
def StrictPredicate.restriction {X : RealizerPER} (P : StrictPredicate X) : RealizerPER where
  Carrier := X.Carrier
  rel x y := {a | a.unpair.1 ∈ X.rel x y ∧ a.unpair.2 ∈ P.val x}
  symmetry := reduces_and_intro (X.symm_of (reduces_and_left _ _)) P.extensional
  transitivity := reduces_and_intro
    (X.trans_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
      (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)))
    (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))

/-- The inclusion has exactly the same realizer sets as the restricted equality. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    For symmetry, from realizers of $x\sim_X x'$ and $\varphi(x)$ compute a realizer of $x'\sim_X x$ by symmetry and
    one of $\varphi(x')$ by the second assumption. Transitivity combines the two $X$-equality realizers and retains
    the first $\varphi$ realizer. Thus the displayed relation is a PER, with
    $$E_{\PERRestriction{X}{\varphi}}(x)=E_X(x)\land\varphi(x).$$
    The equality realizer in $J_\varphi(x,x')$ supplies both $X$-extents, while its second component supplies
    $\varphi(x)$; this proves strictness. Symmetry, transitivity, and the second assumption give extensionality and
    single-valuedness. The identity transformer on $E_{\PERRestriction{X}{\varphi}}(x)$ proves totality, using $x'=x$.
-/
def StrictPredicate.inclusion {X : RealizerPER} (P : StrictPredicate X) :
    FunctionalRelation P.restriction X where
  val := P.restriction.rel
  strict := reduces_and_intro
    (reduces_and_intro (X.extent_left_of (reduces_and_left _ _)) (reduces_and_right _ _))
    (X.extent_right_of (reduces_and_left _ _))
  extensional := reduces_and_intro
    (X.trans_of
      (X.trans_of
        (X.symm_of (reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
          (reduces_and_left _ _)))
        (reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
          (reduces_and_left _ _))) (reduces_and_right _ _))
    (reduces_trans
      (P.restriction.extent_right_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)))
      (reduces_and_right _ _))
  single := X.trans_of
    (X.symm_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)))
    (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _))
  total := reduces_of_subset fun x _ h => ⟨x, h⟩

/-- A relation all of whose values satisfy the predicate lifts without changing its realizer sets. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For the factorization, retain $F(z,x)$ as its value in $\PERRestriction{X}{\varphi}$. The assumed conversion to
    $\varphi(x)$ supplies the extra extent component for strictness and the extra equality component for
    single-valuedness. Extensionality discards the extra component of the target equality; totality is unchanged.
    The relation $J_\varphi$ has exactly the same realizer sets as the identity on $\PERRestriction{X}{\varphi}$, so
    the identity-law conversions from §{sec:effective-topos-objects-morphisms} prove that the composite represents $F$.
    For any two arrows into $\PERRestriction{X}{\varphi}$, these same conversions turn an equivalence of their
    composites with $J_\varphi$ into an equivalence of the original relations. Thus $J_\varphi$ is monic and the
    factorization is unique.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{realizability predicate restriction}{Restriction by a realizability predicate}]
-/
def StrictPredicate.lift {X Z : RealizerPER} (P : StrictPredicate X) (F : FunctionalRelation Z X)
    (h : Reduces (fun p : Z.Carrier × X.Carrier => F.val p.1 p.2) (fun p => P.val p.2)) :
    FunctionalRelation Z P.restriction where
  val := F.val
  strict := reduces_and_intro (F.strict_left_of (reduces_refl _))
    (reduces_and_intro (F.strict_right_of (reduces_refl _)) h)
  extensional := F.ext_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
    (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
    (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _))
  single := reduces_and_intro F.single
    (reduces_trans (reduces_and_left _ _)
      (reindex_reduces (fun p : Z.Carrier × X.Carrier × X.Carrier => (p.1, p.2.1)) h))
  total := F.total

theorem StrictPredicate.lift_inclusion {X Z : RealizerPER} (P : StrictPredicate X)
    (F : FunctionalRelation Z X)
    (h : Reduces (fun p : Z.Carrier × X.Carrier => F.val p.1 p.2) (fun p => P.val p.2)) :
    FunctionalRelation.Equivalent (FunctionalRelation.comp (P.lift F h) P.inclusion) F :=
  FunctionalRelation.comp_identity (P.lift F h)

/-- Forgetting the restriction reflects equality of arrows. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For the factorization, retain $F(z,x)$ as its value in $\PERRestriction{X}{\varphi}$. The assumed conversion to
    $\varphi(x)$ supplies the extra extent component for strictness and the extra equality component for
    single-valuedness. Extensionality discards the extra component of the target equality; totality is unchanged.
    The relation $J_\varphi$ has exactly the same realizer sets as the identity on $\PERRestriction{X}{\varphi}$, so
    the identity-law conversions from §{sec:effective-topos-objects-morphisms} prove that the composite represents $F$.
    For any two arrows into $\PERRestriction{X}{\varphi}$, these same conversions turn an equivalence of their
    composites with $J_\varphi$ into an equivalence of the original relations. Thus $J_\varphi$ is monic and the
    factorization is unique.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{realizability predicate restriction}{Restriction by a realizability predicate}]
-/
theorem StrictPredicate.inclusion_cancel {X Z : RealizerPER} (P : StrictPredicate X)
    (f g : Z ⟶ P.restriction) (h : f ≫ P.inclusion.toHom = g ≫ P.inclusion.toHom) : f = g := by
  revert h
  refine Quotient.inductionOn₂ f g fun F G h => ?_
  have he := (FunctionalRelation.toHom_eq_iff
    (FunctionalRelation.comp F P.inclusion) (FunctionalRelation.comp G P.inclusion)).mp h
  apply Quotient.sound
  exact ⟨reduces_trans (FunctionalRelation.comp_identity F).2
      (reduces_trans he.1 (FunctionalRelation.comp_identity G).1),
    reduces_trans (FunctionalRelation.comp_identity G).2
      (reduces_trans he.2 (FunctionalRelation.comp_identity F).1)⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{realizability predicate restriction}{Restriction by a realizability predicate}]
-/
instance StrictPredicate.inclusion_mono {X : RealizerPER} (P : StrictPredicate X) :
    Mono (C := RealizerPER) P.inclusion.toHom := ⟨fun f g h => P.inclusion_cancel f g h⟩

end RealizerPER
namespace FunctionalRelation
open RealizerPER

/-- Existence of one common output, with a pair of its two realizers. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For equalizers, choose functional relations $F,G:X\to Y$ representing the two arrows and put
    $$D(x):=\bigcup_{y\in|Y|}\bigl(F(x,y)\land G(x,y)\bigr).$$
    Strictness of $F$ proves $D(x)\le E_X(x)$. Given realizers of $x\sim_X x'$ and $D(x)$, apply extensionality of
    $F$ and $G$ at the common output $y$, using their strictness outputs to realize $y\sim_Y y$.
    This proves $(x\sim_X x')\land D(x)\le D(x')$ uniformly. The restriction lemma therefore gives the PER
    $Q=\PERRestriction{X}{D}$ and its monomorphism $J_D:Q\to X$.
-/
def agreement {X Y : RealizerPER} (F G : FunctionalRelation X Y) : StrictPredicate X where
  val x := {a | ∃ y, a.unpair.1 ∈ F.val x y ∧ a.unpair.2 ∈ G.val x y}
  strict := by
    apply reduces_cover (θ := realizabilityAnd
      (fun p : X.Carrier × Y.Carrier => F.val p.1 p.2) (fun p => G.val p.1 p.2)) (fun _ _ h => h)
    exact F.strict_left_of (reduces_and_left _ _)
  extensional := by
    let Γ : (X.Carrier × X.Carrier) × Y.Carrier → Set ℕ :=
      realizabilityAnd (fun p => X.rel p.1.1 p.1.2)
        (realizabilityAnd (fun p => F.val p.1.1 p.2) (fun p => G.val p.1.1 p.2))
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨hr, ⟨y, hy⟩⟩
      exact ⟨y, hr, hy⟩
    · have hF : Reduces Γ (fun p => F.val p.1.1 p.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)
      have hG : Reduces Γ (fun p => G.val p.1.1 p.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)
      apply reduces_trans (reduces_and_intro
        (F.ext_of (reduces_and_left _ _) hF (F.strict_right_of hF))
        (G.ext_of (reduces_and_left _ _) hG (G.strict_right_of hG)))
      exact reduces_of_subset fun p _ h => ⟨p.2, h⟩

/-- Agreement converts any F-output into a G-output with the same representative. -/
theorem agreement_convert {X Y : RealizerPER} (F G : FunctionalRelation X Y) :
    Reduces (realizabilityAnd (fun p : X.Carrier × Y.Carrier => (agreement F G).val p.1)
      (fun p => F.val p.1 p.2)) (fun p => G.val p.1 p.2) := by
  let Γ : (X.Carrier × Y.Carrier) × Y.Carrier → Set ℕ :=
    realizabilityAnd (realizabilityAnd (fun p => F.val p.1.1 p.2) (fun p => G.val p.1.1 p.2))
      (fun p => F.val p.1.1 p.1.2)
  apply reduces_cover (θ := Γ)
  · rintro p a ⟨⟨y, hy⟩, ha⟩
    exact ⟨y, hy, ha⟩
  · have hG : Reduces Γ (fun p => G.val p.1.1 p.2) :=
      reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)
    exact G.ext_of (G.strict_left_of hG) hG
      (F.single_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
        (reduces_and_right _ _))

theorem agreement_swap {X Y : RealizerPER} (F G : FunctionalRelation X Y) :
    Reduces (agreement F G).val (agreement G F).val := by
  apply reduces_cover (θ := realizabilityAnd
    (fun p : X.Carrier × Y.Carrier => F.val p.1 p.2) (fun p => G.val p.1 p.2)) (fun _ _ h => h)
  apply reduces_trans (reduces_and_intro (reduces_and_right _ _) (reduces_and_left _ _))
  exact reduces_of_subset fun p _ h => ⟨p.2, h⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    To check the equalizing equation, suppose a realizer of $D(x)$ gives $u\in F(x,y_0)$ and $v\in G(x,y_0)$,
    and let $a\in F(x,y)$. Single-valuedness of $F$ computes $v_F(u,a)\in(y_0\sim_Y y)$, so
    $$q_G\bigl(\ell_G(v),v,v_F(u,a)\bigr)\in G(x,y).$$
    Thus $D(x)\land F(x,y)\le G(x,y)$; swapping the two components of the agreement realizer proves the reverse
    conversion with $F$ and $G$ interchanged. A realizer of $J_D(x,x')$ also supplies $D(x')$ by extensionality of $D$.
    Applying the conversions at that intermediate point gives
    $$F\circ J_D\equiv G\circ J_D.$$
    Neither conversion needs to compute $y_0$ or $x'$.
-/
theorem agreement_inclusion_condition {X Y : RealizerPER} (F G : FunctionalRelation X Y) :
    Equivalent (comp (agreement F G).inclusion F) (comp (agreement F G).inclusion G) := by
  let P := agreement F G
  have direction (A B : FunctionalRelation X Y)
      (h : Reduces (realizabilityAnd (fun p : X.Carrier × Y.Carrier => P.val p.1)
        (fun p => A.val p.1 p.2)) (fun p => B.val p.1 p.2)) :
      LE (comp P.inclusion A) (comp P.inclusion B) := by
    let Γ : (X.Carrier × Y.Carrier) × X.Carrier → Set ℕ :=
      realizabilityAnd (fun p => P.inclusion.val p.1.1 p.2) (fun p => A.val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    exact relationComp_intro (reduces_and_left _ _)
      (reduces_trans (reduces_and_intro
        (reduces_trans (P.restriction.extent_right_of (reduces_and_left _ _)) (reduces_and_right _ _))
        (reduces_and_right _ _))
        (reindex_reduces (fun p : (X.Carrier × Y.Carrier) × X.Carrier => (p.2, p.1.2)) h))
  exact ⟨direction F G (agreement_convert F G), direction G F
    (reduces_trans (and_reduces_mono (reindex_reduces Prod.fst (agreement_swap F G)) (reduces_refl _))
      (agreement_convert G F))⟩

/-- Equal composites provide agreement evidence at every value of H, uniformly. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For the universal property, let $H:Z\to X$ satisfy $F\circ H\equiv G\circ H$, and fix a tracker $c$ for the
    forward reduction. From $a\in H(z,x)$ compute
    $$\begin{aligned}
    u&=u_F(r_H(a)),\\
    \NatPair{a'}{b}&=c\cdot\NatPair{a}{u},\\
    b^\ast&=q_G\bigl(s_X(v_H(a,a')),b,r_G(b)\bigr).
    \end{aligned}$$
    For some $y$, the first output lies in $F(x,y)$. The second line is defined because $\NatPair{a}{u}$ realizes
    $(F\circ H)(z,y)$; for some $x'$, its projections satisfy $a'\in H(z,x')$ and $b\in G(x',y)$.
    Single-valuedness of $H$ gives $x\sim_X x'$, and symmetry and extensionality of $G$ give $b^\ast\in G(x,y)$.
    Hence $\NatPair{u}{b^\ast}\in D(x)$. We have proved $H(z,x)\le D(x)$ uniformly, so the restriction lemma gives
    a factorization through $J_D$. It is unique because $J_D$ is monic. These calculations establish the equalizer
    universal property for any chosen representatives $F,G$; consequently different representatives yield canonically
    isomorphic equalizers.
-/
theorem agreement_of_composites {Z X Y : RealizerPER} (F G : FunctionalRelation X Y)
    (H : FunctionalRelation Z X) (h : Equivalent (comp H F) (comp H G)) :
    Reduces (fun p : Z.Carrier × X.Carrier => H.val p.1 p.2)
      (fun p => (agreement F G).val p.2) := by
  apply reduces_trans (reduces_and_intro (reduces_refl _)
    (reduces_trans (H.strict_right_of (reduces_refl _)) (reindex_reduces Prod.snd F.total)))
  let Γ : (Z.Carrier × X.Carrier) × Y.Carrier → Set ℕ :=
    realizabilityAnd (fun p => H.val p.1.1 p.1.2) (fun p => F.val p.1.2 p.2)
  apply reduces_cover (θ := Γ)
  · rintro p a ⟨ha, ⟨y, hy⟩⟩
    exact ⟨y, ha, hy⟩
  · have hc : Reduces Γ (fun p => (comp H G).val p.1.1 p.2) :=
      reduces_trans (relationComp_intro (reduces_and_left _ _) (reduces_and_right _ _))
        (reindex_reduces (fun p : (Z.Carrier × X.Carrier) × Y.Carrier => (p.1.1, p.2)) h.1)
    apply reduces_trans (reduces_and_intro (reduces_refl _) hc)
    let Δ : ((Z.Carrier × X.Carrier) × Y.Carrier) × X.Carrier → Set ℕ :=
      realizabilityAnd (fun p => Γ p.1)
        (realizabilityAnd (fun p => H.val p.1.1.1 p.2) (fun p => G.val p.2 p.1.2))
    apply reduces_cover (θ := Δ)
    · rintro p a ⟨ha, ⟨x, hx⟩⟩
      exact ⟨x, ha, hx⟩
    · have hH : Reduces Δ (fun p => H.val p.1.1.1 p.1.1.2) :=
        reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)
      have hF : Reduces Δ (fun p => F.val p.1.1.2 p.1.2) :=
        reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)
      have hH' : Reduces Δ (fun p => H.val p.1.1.1 p.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)
      have hG : Reduces Δ (fun p => G.val p.2 p.1.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)
      apply reduces_trans (reduces_and_intro hF
        (G.ext_of (X.symm_of (H.single_of hH hH')) hG (G.strict_right_of hG)))
      exact reduces_of_subset fun p _ ha => ⟨p.1.2, ha⟩

end FunctionalRelation

namespace RealizerPER
open FunctionalRelation

def equalizerFork {X Y : RealizerPER.{u}} (F G : FunctionalRelation X Y) :
    Fork (C := RealizerPER.{u}) F.toHom G.toHom :=
  Fork.ofι (agreement F G).inclusion.toHom (Quotient.sound (agreement_inclusion_condition F G))

theorem equalizer_exists_lift {X Y Z : RealizerPER.{u}} (F G : FunctionalRelation X Y)
    (h : Z ⟶ X) (comm : h ≫ F.toHom = h ≫ G.toHom) :
    ∃ l : Z ⟶ (agreement F G).restriction, l ≫ (agreement F G).inclusion.toHom = h := by
  revert comm
  refine Quotient.inductionOn h fun H comm => ?_
  have hc : Equivalent (comp H F) (comp H G) := (toHom_eq_iff _ _).mp comm
  let hP := agreement_of_composites F G H hc
  exact ⟨((agreement F G).lift H hP).toHom,
    Quotient.sound ((agreement F G).lift_inclusion H hP)⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For the universal property, let $H:Z\to X$ satisfy $F\circ H\equiv G\circ H$, and fix a tracker $c$ for the
    forward reduction. From $a\in H(z,x)$ compute
    $$\begin{aligned}
    u&=u_F(r_H(a)),\\
    \NatPair{a'}{b}&=c\cdot\NatPair{a}{u},\\
    b^\ast&=q_G\bigl(s_X(v_H(a,a')),b,r_G(b)\bigr).
    \end{aligned}$$
    For some $y$, the first output lies in $F(x,y)$. The second line is defined because $\NatPair{a}{u}$ realizes
    $(F\circ H)(z,y)$; for some $x'$, its projections satisfy $a'\in H(z,x')$ and $b\in G(x',y)$.
    Single-valuedness of $H$ gives $x\sim_X x'$, and symmetry and extensionality of $G$ give $b^\ast\in G(x,y)$.
    Hence $\NatPair{u}{b^\ast}\in D(x)$. We have proved $H(z,x)\le D(x)$ uniformly, so the restriction lemma gives
    a factorization through $J_D$. It is unique because $J_D$ is monic. These calculations establish the equalizer
    universal property for any chosen representatives $F,G$; consequently different representatives yield canonically
    isomorphic equalizers.
-/
noncomputable def equalizerIsLimit {X Y : RealizerPER.{u}} (F G : FunctionalRelation X Y) :
    IsLimit (equalizerFork F G) := by
  apply Fork.IsLimit.ofExistsUnique
  intro s
  obtain ⟨l, hl⟩ := equalizer_exists_lift F G s.ι s.condition
  refine ⟨l, hl, ?_⟩
  intro m hm
  exact (agreement F G).inclusion_cancel m l (hm.trans hl.symm)

instance realizabilityHasTerminal : HasTerminal RealizerPER.{u} := terminalIsTerminal.hasTerminal

instance realizabilityHasBinaryProducts : HasBinaryProducts RealizerPER.{u} := by
  have h (X Y : RealizerPER.{u}) : HasLimit (pair X Y) :=
    HasLimit.mk ⟨_, productIsLimit X Y⟩
  let : ∀ {X Y : RealizerPER.{u}}, HasLimit (pair X Y) := fun {X Y} => h X Y
  exact hasBinaryProducts_of_hasLimit_pair RealizerPER.{u}

instance realizabilityHasFiniteProducts : HasFiniteProducts RealizerPER.{u} :=
  hasFiniteProducts_of_has_binary_and_terminal

instance realizabilityHasEqualizers : HasEqualizers RealizerPER.{u} := by
  have h {X Y : RealizerPER.{u}} (f g : X ⟶ Y) : HasLimit (parallelPair f g) := by
    refine Quotient.inductionOn₂ f g fun F G => ?_
    exact HasLimit.mk ⟨_, equalizerIsLimit F G⟩
  let : ∀ {X Y : RealizerPER.{u}} {f g : X ⟶ Y}, HasLimit (parallelPair f g) := fun {X Y} {f g} => h f g
  exact hasEqualizers_of_hasLimit_parallelPair RealizerPER.{u}

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{finite limits in realizability}{Finite limits in realizability}]
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{theorem*} $\EffCat$ is an elementary topos.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    Finally, the standard finite-limit criterion recalled in Appendix §{sec:cat-ccc} gives all finite limits from
    these terminal objects, binary products, and equalizers.
-/
instance realizabilityHasFiniteLimits : HasFiniteLimits RealizerPER.{u} :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

end RealizerPER
end PolishSpaceBook.LambdaIndexPCA
