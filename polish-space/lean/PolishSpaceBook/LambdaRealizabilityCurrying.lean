module

public import PolishSpaceBook.LambdaRealizabilityEvaluation

@[expose] public section

/-! # Currying by uniform abstraction of the parameter realizer -/
namespace PolishSpaceBook.LambdaIndexPCA
open RealizerPER
universe u

/-- A slice is a raw relation even when the parameter has empty extent. -/
def functionSlice {Z X Y : RealizerPER.{u}} (H : FunctionalRelation (product Z X) Y)
    (z : Z.Carrier) : RawFunction X Y := fun x y => H.val (z, x) y

/-- All four indices are computed from an extent realizer of the parameter. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Fix trackers for the four conditions on $H$, and use the notation $\ell_H,r_H,q_H,v_H,u_H$ from
    §{sec:effective-topos-objects-morphisms}. Write $\pi_0,\pi_1$ for the numerical pair projections.
    Given $a\in E_Z(z)$, the four required programs act as follows:
    $$\begin{aligned}
     b&\longmapsto\NatPair{\pi_1(\ell_H(b))}{r_H(b)},\\
     \NatPair{\NatPair{r}{b}}{c}&\longmapsto q_H(\NatPair{a}{r},b,c),\\
     \NatPair{b}{c}&\longmapsto v_H(b,c),\\
     r&\longmapsto u_H(\NatPair{a}{r}).
    \end{aligned}$$
    The first program discards the $Z$-extent from strictness of $H$. The second uses $a$ to keep $z$ fixed while
    transporting $x$ and $y$. The third is single-valuedness of $H$. The last supplies totality of $H$ with the
    paired extent of $(z,x)$. Uniform tracker abstraction computes all four indices from $a$ before any of these
    programs is run, and pairs them to obtain an element of $\FunctionalRealizers{R_z}$.
    The raw slice $R_z$ exists even when $E_Z(z)$ is empty; no functionality is asserted without an extent realizer.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{uniform realizability currying}{Uniform currying}]
-/
theorem functionSlice_data {Z X Y : RealizerPER.{u}} (H : FunctionalRelation (product Z X) Y) :
    Reduces Z.extent (fun z => functionData (functionSlice H z)) := by
  change Reduces Z.extent (realizabilityAnd (fun z => strictData (functionSlice H z))
    (realizabilityAnd (fun z => extensionalData (functionSlice H z))
      (realizabilityAnd (fun z => singleData (functionSlice H z))
        (fun z => totalData (functionSlice H z)))))
  apply reduces_and_intro
  · apply uniformImp_intro
    let Γ : Z.Carrier × (X.Carrier × Y.Carrier) → Set ℕ :=
      realizabilityAnd (fun p => Z.extent p.1) (fun p => H.val (p.1, p.2.1) p.2.2)
    have h : Reduces Γ (fun p => H.val (p.1, p.2.1) p.2.2) := reduces_and_right _ _
    exact reduces_and_intro (reduces_trans (H.strict_left_of h) (reduces_and_right _ _))
      (H.strict_right_of h)
  · apply reduces_and_intro
    · apply uniformImp_intro
      let Γ : Z.Carrier × (X.Carrier × X.Carrier × Y.Carrier × Y.Carrier) → Set ℕ :=
        realizabilityAnd (fun p => Z.extent p.1)
          (realizabilityAnd (realizabilityAnd (fun p => X.rel p.2.1 p.2.2.1)
            (fun p => H.val (p.1, p.2.1) p.2.2.2.1)) (fun p => Y.rel p.2.2.2.1 p.2.2.2.2))
      have hz : Reduces Γ (fun p => Z.extent p.1) := reduces_and_left _ _
      have hx : Reduces Γ (fun p => X.rel p.2.1 p.2.2.1) :=
        reduces_trans (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)) (reduces_and_left _ _)
      have ha : Reduces Γ (fun p => H.val (p.1, p.2.1) p.2.2.2.1) :=
        reduces_trans (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)) (reduces_and_right _ _)
      exact H.ext_of (Γ := Γ) (x := fun p => (p.1, p.2.1)) (x' := fun p => (p.1, p.2.2.1))
        (reduces_and_intro hz hx) ha
        (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
    · apply reduces_and_intro
      · apply uniformImp_intro
        exact H.single_of
          (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _))
          (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
      · apply uniformImp_intro
        exact H.total

/-- Transport of the parameter computes a single conversion for every argument and value. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Given $d\in(z\sim_Z z')$, the PER laws supply extents for $z,z'$, hence data for both slices.
    For $b\in R_z(x,y)$, the program
    $$b\longmapsto q_H(\NatPair{d}{\pi_1(\ell_H(b))},b,r_H(b))$$
    produces an element of $R_{z'}(x,y)$. Abstracting $d$ yields one conversion index for every $x,y$.
    Symmetry in $Z$ gives the reverse conversion. These two indices and the two data tuples realize $R_z\sim R_{z'}$.
    The graph construction in §{sec:effective-topos-finite-limits} now proves that $\CurriedRelation{H}$ is functional.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{uniform realizability currying}{Uniform currying}]
-/
theorem functionSlice_transport {Z X Y : RealizerPER.{u}} (H : FunctionalRelation (product Z X) Y) :
    Reduces (fun p : Z.Carrier × Z.Carrier => Z.rel p.1 p.2)
      (fun p => relationEntailment (functionSlice H p.1) (functionSlice H p.2)) := by
  apply uniformImp_intro
  let Γ : (Z.Carrier × Z.Carrier) × (X.Carrier × Y.Carrier) → Set ℕ :=
    realizabilityAnd (fun p => Z.rel p.1.1 p.1.2) (fun p => H.val (p.1.1, p.2.1) p.2.2)
  have ha : Reduces Γ (fun p => H.val (p.1.1, p.2.1) p.2.2) := reduces_and_right _ _
  exact H.ext_of
    (reduces_and_intro (reduces_and_left _ _)
      (reduces_trans (H.strict_left_of ha) (reduces_and_right _ _))) ha (H.strict_right_of ha)

/-- Currying does not choose tracking indices separately at each semantic parameter. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{uniform realizability currying}{Uniform currying}]
-/
def functionSliceMap {Z X Y : RealizerPER.{u}} (H : FunctionalRelation (product Z X) Y) :
    Map Z (functionSpace X Y) where
  toFun := functionSlice H
  preserves := reduces_and_intro
    (reduces_and_intro
      (reduces_trans (Z.extent_left_of (reduces_refl _)) (reindex_reduces Prod.fst (functionSlice_data H)))
      (reduces_trans (Z.extent_right_of (reduces_refl _)) (reindex_reduces Prod.snd (functionSlice_data H))))
    (reduces_and_intro (functionSlice_transport H)
      (reduces_trans Z.symmetry (reindex_reduces (fun p : Z.Carrier × Z.Carrier => (p.2,p.1)) (functionSlice_transport H))))

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{lemma*}[\termdefineas{uniform realizability currying}{Uniform currying}]
-/
def curryRelation {Z X Y : RealizerPER.{u}} (H : FunctionalRelation (product Z X) Y) :
    FunctionalRelation Z (functionSpace X Y) := (functionSliceMap H).graph

end PolishSpaceBook.LambdaIndexPCA
