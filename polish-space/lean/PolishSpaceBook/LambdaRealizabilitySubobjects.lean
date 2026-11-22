module

public import PolishSpaceBook.LambdaRealizabilityEqualizers

@[expose] public section

/-! # Monomorphisms as restrictions by strict extensional predicates

Monicity is converted into a uniform realizer for injectivity using the two
projections of a concrete kernel object. No inverse on representatives is chosen.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open CategoryTheory Limits RealizerPER
universe u
namespace FunctionalRelation

/-- A common image of two representatives, retaining both numerical realizers. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Use the tracker notation from §{sec:effective-topos-objects-morphisms}. We first extract uniform injectivity from
    categorical monicity. On $X\times X$ put
    $$\kappa(x,x'):=\bigcup_{y\in|Y|}\bigl(M(x,y)\land M(x',y)\bigr).$$
    Strictness of $M$ gives both coordinate extents. Applying extensionality of $M$ in each coordinate, while retaining
    the same output, proves extensionality of $\kappa$. Thus the restriction
    $$K:=\PERRestriction{(X\times X)}{\kappa}$$
    is defined, and the two coordinate functions induce arrows $p,q:K\to X$ by the graph construction in
    §{sec:effective-topos-finite-limits}.
-/
def kernelPredicate {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y) : StrictPredicate (product X X) where
  val p := {a | ∃ y, a.unpair.1 ∈ M.val p.1 y ∧ a.unpair.2 ∈ M.val p.2 y}
  strict := by
    apply reduces_cover (θ := realizabilityAnd
      (fun p : (X.Carrier × X.Carrier) × Y.Carrier => M.val p.1.1 p.2)
      (fun p => M.val p.1.2 p.2)) (fun _ _ h => h)
    exact reduces_and_intro (M.strict_left_of (reduces_and_left _ _))
      (M.strict_left_of (reduces_and_right _ _))
  extensional := by
    let Γ : ((X.Carrier × X.Carrier) × (X.Carrier × X.Carrier)) × Y.Carrier → Set ℕ :=
      realizabilityAnd (fun p => (product X X).rel p.1.1 p.1.2)
        (realizabilityAnd (fun p => M.val p.1.1.1 p.2) (fun p => M.val p.1.1.2 p.2))
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨hr, ⟨y, hy⟩⟩
      exact ⟨y, hr, hy⟩
    · have h₁ : Reduces Γ (fun p => M.val p.1.1.1 p.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)
      have h₂ : Reduces Γ (fun p => M.val p.1.1.2 p.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)
      apply reduces_trans (reduces_and_intro
        (M.ext_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)) h₁ (M.strict_right_of h₁))
        (M.ext_of (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)) h₂ (M.strict_right_of h₂)))
      exact reduces_of_subset fun p _ h => ⟨p.2, h⟩

def kernelFirst {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y) :
    Map (kernelPredicate M).restriction X where
  toFun := Prod.fst
  preserves := reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)

def kernelSecond {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y) :
    Map (kernelPredicate M).restriction X where
  toFun := Prod.snd
  preserves := reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)

theorem kernel_swap {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y) :
    Reduces (kernelPredicate M).val (fun p => (kernelPredicate M).val (p.2, p.1)) := by
  apply reduces_cover (θ := realizabilityAnd
    (fun p : (X.Carrier × X.Carrier) × Y.Carrier => M.val p.1.1 p.2)
    (fun p => M.val p.1.2 p.2)) (fun _ _ h => h)
  apply reduces_trans (reduces_and_intro (reduces_and_right _ _) (reduces_and_left _ _))
  exact reduces_of_subset fun p _ h => ⟨p.2, h⟩

/-- If two inputs have a common image, every image of the first is an image of the second. -/
theorem kernel_transfer {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y) :
    Reduces (realizabilityAnd
      (fun p : (X.Carrier × X.Carrier) × Y.Carrier => (kernelPredicate M).val p.1)
      (fun p => M.val p.1.1 p.2)) (fun p => M.val p.1.2 p.2) := by
  let Γ : ((X.Carrier × X.Carrier) × Y.Carrier) × Y.Carrier → Set ℕ :=
    realizabilityAnd (realizabilityAnd (fun p => M.val p.1.1.1 p.2) (fun p => M.val p.1.1.2 p.2))
      (fun p => M.val p.1.1.1 p.1.2)
  apply reduces_cover (θ := Γ)
  · rintro p a ⟨⟨y, hy⟩, ha⟩
    exact ⟨y, hy, ha⟩
  · have h₂ : Reduces Γ (fun p => M.val p.1.1.2 p.2) :=
      reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)
    exact M.ext_of (M.strict_left_of h₂) h₂
      (M.single_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)) (reduces_and_right _ _))

theorem kernel_transfer_of {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y)
    {I : Type*} {Γ : I → Set ℕ} {x x' : I → X.Carrier} {y : I → Y.Carrier}
    (hK : Reduces Γ (fun i => (kernelPredicate M).val (x i, x' i)))
    (hM : Reduces Γ (fun i => M.val (x i) (y i))) : Reduces Γ (fun i => M.val (x' i) (y i)) :=
  reduces_trans (reduces_and_intro hK hM)
    (reindex_reduces (fun i => ((x i, x' i), y i)) (kernel_transfer M))

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    The composites $M\circ p$ and $M\circ q$ are equivalent. Indeed, let $a\in M(x,y_0)$ and $b\in M(x',y_0)$
    be a common-image realizer. Given $c\in M(x,y)$, the expression
    $$q_M\bigl(\ell_M(b),b,v_M(a,c)\bigr)\in M(x',y)$$
    transfers that output to the second coordinate. Swapping $a,b$ gives the converse; the equality components in the
    projection graphs are handled first by extensionality of $M$. Monicity now gives $p=q$. Fix the uniform conversion
    between these two projection relations supplied by that equality. From $a\in M(x,y)$ and $b\in M(x',y)$ we can
    construct an extent realizer of $(x,x')\in K$, using their strictness outputs and $\NatPair{a}{b}$.
    This gives a realizer of $p((x,x'),x)$. The fixed conversion returns one of $q((x,x'),x)$, whose equality component
    realizes $x'\sim_X x$. Symmetry therefore gives a single uniform transformer $i_M$ with
    $$i_M(a,b)\in(x\sim_X x').$$
    This is a transformer of realizer numbers; no preimage representative is computed.
-/
theorem kernel_projections_condition {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y) :
    Equivalent (comp (kernelFirst M).graph M) (comp (kernelSecond M).graph M) := by
  constructor
  · let Γ : ((X.Carrier × X.Carrier) × Y.Carrier) × X.Carrier → Set ℕ :=
      realizabilityAnd (fun p => (kernelFirst M).graph.val p.1.1 p.2) (fun p => M.val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    have hE : Reduces Γ (fun p => (kernelPredicate M).restriction.extent p.1.1) :=
      reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)
    have hM : Reduces Γ (fun p => M.val p.2 p.1.2) := reduces_and_right _ _
    have h₁ : Reduces Γ (fun p => M.val p.1.1.1 p.1.2) :=
      M.ext_of (X.symm_of (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)))
        hM (M.strict_right_of hM)
    have h₂ := kernel_transfer_of M (reduces_trans hE (reduces_and_right _ _)) h₁
    exact relationComp_intro (I := ((X.Carrier × X.Carrier) × Y.Carrier) × X.Carrier) (F := (kernelSecond M).graph.val) (G := M.val)
      (x := fun p => p.1.1) (y := fun p => p.1.1.2) (z := fun p => p.1.2)
      (reduces_and_intro hE (M.strict_left_of h₂)) h₂
  · let Γ : ((X.Carrier × X.Carrier) × Y.Carrier) × X.Carrier → Set ℕ :=
      realizabilityAnd (fun p => (kernelSecond M).graph.val p.1.1 p.2) (fun p => M.val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    have hE : Reduces Γ (fun p => (kernelPredicate M).restriction.extent p.1.1) :=
      reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)
    have hM : Reduces Γ (fun p => M.val p.2 p.1.2) := reduces_and_right _ _
    have h₂ : Reduces Γ (fun p => M.val p.1.1.2 p.1.2) :=
      M.ext_of (X.symm_of (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)))
        hM (M.strict_right_of hM)
    have hK : Reduces Γ (fun p => (kernelPredicate M).val (p.1.1.2, p.1.1.1)) :=
      reduces_trans (reduces_trans hE (reduces_and_right _ _))
        (reindex_reduces (fun p : ((X.Carrier × X.Carrier) × Y.Carrier) × X.Carrier => p.1.1)
          (kernel_swap M))
    have h₁ := kernel_transfer_of M hK h₂
    exact relationComp_intro (I := ((X.Carrier × X.Carrier) × Y.Carrier) × X.Carrier) (F := (kernelFirst M).graph.val) (G := M.val)
      (x := fun p => p.1.1) (y := fun p => p.1.1.1) (z := fun p => p.1.2)
      (reduces_and_intro hE (M.strict_left_of h₁)) h₁

/-- Categorical monicity entails one uniform realizer of injectivity. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    The composites $M\circ p$ and $M\circ q$ are equivalent. Indeed, let $a\in M(x,y_0)$ and $b\in M(x',y_0)$
    be a common-image realizer. Given $c\in M(x,y)$, the expression
    $$q_M\bigl(\ell_M(b),b,v_M(a,c)\bigr)\in M(x',y)$$
    transfers that output to the second coordinate. Swapping $a,b$ gives the converse; the equality components in the
    projection graphs are handled first by extensionality of $M$. Monicity now gives $p=q$. Fix the uniform conversion
    between these two projection relations supplied by that equality. From $a\in M(x,y)$ and $b\in M(x',y)$ we can
    construct an extent realizer of $(x,x')\in K$, using their strictness outputs and $\NatPair{a}{b}$.
    This gives a realizer of $p((x,x'),x)$. The fixed conversion returns one of $q((x,x'),x)$, whose equality component
    realizes $x'\sim_X x$. Symmetry therefore gives a single uniform transformer $i_M$ with
    $$i_M(a,b)\in(x\sim_X x').$$
    This is a transformer of realizer numbers; no preimage representative is computed.
-/
theorem injective_of_mono {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y)
    [Mono (C := RealizerPER) M.toHom] :
    Reduces (realizabilityAnd (fun p : X.Carrier × X.Carrier × Y.Carrier => M.val p.1 p.2.2)
      (fun p => M.val p.2.1 p.2.2)) (fun p => X.rel p.1 p.2.1) := by
  have hh : ((kernelFirst M).graph.toHom : (kernelPredicate M).restriction ⟶ X) =
      (kernelSecond M).graph.toHom :=
    Mono.right_cancellation (C := RealizerPER.{u}) (f := M.toHom)
      (kernelFirst M).graph.toHom (kernelSecond M).graph.toHom
      (Quotient.sound (kernel_projections_condition M))
  have h := (toHom_eq_iff _ _).mp hh
  let Γ : X.Carrier × X.Carrier × Y.Carrier → Set ℕ :=
    realizabilityAnd (fun p => M.val p.1 p.2.2) (fun p => M.val p.2.1 p.2.2)
  have hE : Reduces Γ (fun p => (kernelPredicate M).restriction.extent (p.1, p.2.1)) :=
    reduces_and_intro
      (reduces_and_intro (M.strict_left_of (reduces_and_left _ _))
        (M.strict_left_of (reduces_and_right _ _)))
      (reduces_of_subset fun p _ ha => ⟨p.2.2, ha⟩)
  have hout : Reduces Γ (fun p => (kernelSecond M).graph.val (p.1, p.2.1) p.1) :=
    reduces_trans
      (reduces_and_intro hE (M.strict_left_of (reduces_and_left _ _)))
      (reindex_reduces (fun p : X.Carrier × X.Carrier × Y.Carrier => ((p.1, p.2.1), p.1)) h.1)
  exact X.symm_of (reduces_trans hout (reduces_and_right _ _))

/-- The range predicate records an output realizer but does not encode its preimage. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    The range predicate $\varphi_M$ is strict by strictness of $M$, and extensional by extensionality of $M$ on the
    output coordinate. Every $M(x,y)$ reduces to $\varphi_M(y)$ by the identity transformer, so the restriction lemma
    lifts $M$ to $\PERRestriction{Y}{\varphi_M}$. For the converse relation $R$, strictness uses the two strictness
    outputs of $M$ and its input realizer as evidence of $\varphi_M(y)$. Extensionality uses extensionality of $M$
    with the two coordinates exchanged. Single-valuedness is precisely the transformer $i_M$ just constructed, and
    totality follows from the defining union in $\varphi_M(y)$. Thus $R$ is functional.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{realizability subobject presentation}{Predicate presentation of subobjects}]
-/
def imagePredicate {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y) : StrictPredicate Y where
  val y := {a | ∃ x, a ∈ M.val x y}
  strict := by
    apply reduces_cover (θ := fun p : Y.Carrier × X.Carrier => M.val p.2 p.1) (fun _ _ h => h)
    exact M.strict_right_of (reduces_refl _)
  extensional := by
    let Γ : (Y.Carrier × Y.Carrier) × X.Carrier → Set ℕ :=
      realizabilityAnd (fun p => Y.rel p.1.1 p.1.2) (fun p => M.val p.2 p.1.1)
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨hr, ⟨x, hx⟩⟩
      exact ⟨x, hr, hx⟩
    · apply reduces_trans (M.ext_of (M.strict_left_of (reduces_and_right _ _))
        (reduces_and_right _ _) (reduces_and_left _ _))
      exact reduces_of_subset fun p _ h => ⟨p.2, h⟩

def imageLift {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y) :
    FunctionalRelation X (imagePredicate M).restriction :=
  (imagePredicate M).lift M (reduces_of_subset fun p _ h => ⟨p.1, h⟩)

/-- Injectivity makes the converse relation single-valued; its totality is the range predicate. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    The range predicate $\varphi_M$ is strict by strictness of $M$, and extensional by extensionality of $M$ on the
    output coordinate. Every $M(x,y)$ reduces to $\varphi_M(y)$ by the identity transformer, so the restriction lemma
    lifts $M$ to $\PERRestriction{Y}{\varphi_M}$. For the converse relation $R$, strictness uses the two strictness
    outputs of $M$ and its input realizer as evidence of $\varphi_M(y)$. Extensionality uses extensionality of $M$
    with the two coordinates exchanged. Single-valuedness is precisely the transformer $i_M$ just constructed, and
    totality follows from the defining union in $\varphi_M(y)$. Thus $R$ is functional.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{realizability subobject presentation}{Predicate presentation of subobjects}]
-/
def imageInverse {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y)
    [Mono (C := RealizerPER) M.toHom] : FunctionalRelation (imagePredicate M).restriction X where
  val y x := M.val x y
  strict := reduces_and_intro
    (reduces_and_intro (M.strict_right_of (reduces_refl _)) (reduces_of_subset fun p _ h => ⟨p.2, h⟩))
    (M.strict_left_of (reduces_refl _))
  extensional := M.ext_of (reduces_and_right _ _)
    (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
    (reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
      (reduces_and_left _ _))
  single := reindex_reduces (fun p : Y.Carrier × X.Carrier × X.Carrier => (p.2.1, p.2.2, p.1))
    (injective_of_mono M)
  total := reduces_and_right _ _

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    In $R\circ M$, the transformer $i_M$ converts a pair of common-image realizers into $X$-equality.
    Conversely, from an $X$-equality realizer, totality of $M$ gives an output at the first input and extensionality
    transfers it to the second input, producing a composite realizer. In $M\circ R$, single-valuedness of $M$ gives
    $Y$-equality, and the first component also realizes $\varphi_M$ at the source. Conversely, a restricted equality
    realizer supplies a preimage through its $\varphi_M$ component; extensionality transports the associated $M$ realizer
    to the other output. These are uniform conversions in both directions, proving both inverse laws.
    The factorization through $J_{\varphi_M}$ is the one in the restriction lemma.
-/
theorem imageLift_inverse {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y)
    [Mono (C := RealizerPER) M.toHom] : Equivalent (comp M.imageLift M.imageInverse) (identity X) := by
  constructor
  · apply reduces_cover (θ := realizabilityAnd
      (fun p : (X.Carrier × X.Carrier) × Y.Carrier => M.val p.1.1 p.2)
      (fun p => M.val p.1.2 p.2)) (fun _ _ h => h)
    exact reindex_reduces (fun p : (X.Carrier × X.Carrier) × Y.Carrier => (p.1.1, p.1.2, p.2)) (injective_of_mono M)
  · apply reduces_trans (reduces_and_intro (reduces_refl _)
      (reduces_trans (X.extent_left_of (reduces_refl _)) (reindex_reduces Prod.fst M.total)))
    let Γ : (X.Carrier × X.Carrier) × Y.Carrier → Set ℕ :=
      realizabilityAnd (fun p => X.rel p.1.1 p.1.2) (fun p => M.val p.1.1 p.2)
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨hr, ⟨y, hy⟩⟩
      exact ⟨y, hr, hy⟩
    · exact relationComp_intro (reduces_and_right _ _)
        (M.ext_of (reduces_and_left _ _) (reduces_and_right _ _) (M.strict_right_of (reduces_and_right _ _)))

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    In $R\circ M$, the transformer $i_M$ converts a pair of common-image realizers into $X$-equality.
    Conversely, from an $X$-equality realizer, totality of $M$ gives an output at the first input and extensionality
    transfers it to the second input, producing a composite realizer. In $M\circ R$, single-valuedness of $M$ gives
    $Y$-equality, and the first component also realizes $\varphi_M$ at the source. Conversely, a restricted equality
    realizer supplies a preimage through its $\varphi_M$ component; extensionality transports the associated $M$ realizer
    to the other output. These are uniform conversions in both directions, proving both inverse laws.
    The factorization through $J_{\varphi_M}$ is the one in the restriction lemma.
-/
theorem imageInverse_lift {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y)
    [Mono (C := RealizerPER) M.toHom] :
    Equivalent (comp M.imageInverse M.imageLift) (identity (imagePredicate M).restriction) := by
  constructor
  · let Γ : (Y.Carrier × Y.Carrier) × X.Carrier → Set ℕ :=
      realizabilityAnd (fun p => M.val p.2 p.1.1) (fun p => M.val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    exact reduces_and_intro (M.single_of (reduces_and_left _ _) (reduces_and_right _ _))
      (reduces_trans (reduces_and_left _ _) (reduces_of_subset fun p _ h => ⟨p.2, h⟩))
  · let Γ : (Y.Carrier × Y.Carrier) × X.Carrier → Set ℕ :=
      realizabilityAnd (fun p => Y.rel p.1.1 p.1.2) (fun p => M.val p.2 p.1.1)
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨hr, ⟨x, hx⟩⟩
      exact ⟨x, hr, hx⟩
    · exact relationComp_intro (reduces_and_right _ _)
        (M.ext_of (M.strict_left_of (reduces_and_right _ _)) (reduces_and_right _ _) (reduces_and_left _ _))

def imageIso {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y)
    [Mono (C := RealizerPER) M.toHom] : X ≅ (imagePredicate M).restriction where
  hom := M.imageLift.toHom
  inv := M.imageInverse.toHom
  hom_inv_id := Quotient.sound (imageLift_inverse M)
  inv_hom_id := Quotient.sound (imageInverse_lift M)

theorem imageIso_inclusion {X Y : RealizerPER.{u}} (M : FunctionalRelation X Y)
    [Mono (C := RealizerPER) M.toHom] :
    M.imageIso.hom ≫ (imagePredicate M).inclusion.toHom = M.toHom :=
  Quotient.sound ((imagePredicate M).lift_inclusion M (reduces_of_subset fun p _ h => ⟨p.1, h⟩))

/-- Uniform inclusion between total functional relations is already uniform equivalence. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    We will use the following consequence of totality and single-valuedness: if $A\le B$ uniformly for two functional
    relations with the same source and target, then $B\le A$ as well. Given a $B(x,y)$ realizer, strictness and totality
    of $A$ produce an $A(x,y')$ realizer for some $y'$. The assumed reduction turns it into a $B(x,y')$ realizer.
    Single-valuedness of $B$ gives $y'\sim y$, and extensionality of $A$ returns an $A(x,y)$ realizer.
    All operations use the fixed trackers, so this is a uniform reverse reduction.
-/
theorem equivalent_of_le {X Y : RealizerPER.{u}} {F G : FunctionalRelation X Y}
    (h : LE F G) : Equivalent F G := by
  refine ⟨h, ?_⟩
  apply reduces_trans (reduces_and_intro (reduces_refl _)
    (reduces_trans (G.strict_left_of (reduces_refl _)) (reindex_reduces Prod.fst F.total)))
  let Γ : (X.Carrier × Y.Carrier) × Y.Carrier → Set ℕ :=
    realizabilityAnd (fun p => G.val p.1.1 p.1.2) (fun p => F.val p.1.1 p.2)
  apply reduces_cover (θ := Γ)
  · rintro p a ⟨ha, ⟨y, hy⟩⟩
    exact ⟨y, ha, hy⟩
  · have hF : Reduces Γ (fun p => F.val p.1.1 p.2) := reduces_and_right _ _
    have hG : Reduces Γ (fun p => G.val p.1.1 p.2) :=
      reduces_trans hF (reindex_reduces (fun p : (X.Carrier × Y.Carrier) × Y.Carrier => (p.1.1, p.2)) h)
    exact F.ext_of (F.strict_left_of hF) hF (G.single_of hG (reduces_and_left _ _))

end FunctionalRelation

/-- Every categorical subobject admits a strict extensional predicate presentation. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{realizability subobject presentation}{Predicate presentation of subobjects}]
-/
theorem RealizerPER.mono_is_predicate_restriction {X Y : RealizerPER.{u}} (m : X ⟶ Y) (hm : Mono m) :
    ∃ P : StrictPredicate Y, ∃ e : X ≅ P.restriction, e.hom ≫ P.inclusion.toHom = m := by
  revert hm
  refine Quotient.inductionOn m fun M hm => ?_
  let : Mono (C := RealizerPER.{u}) (X := X) (Y := Y) M.toHom := hm
  exact ⟨M.imagePredicate, M.imageIso, M.imageIso_inclusion⟩


/-- A factorization between predicate inclusions gives a uniform implication of predicates. -/
theorem RealizerPER.StrictPredicate.reduces_of_factor {X : RealizerPER.{u}} (P Q : StrictPredicate X)
    (l : P.restriction ⟶ Q.restriction) (h : l ≫ Q.inclusion.toHom = P.inclusion.toHom) :
    Reduces P.val Q.val := by
  revert h
  refine Quotient.inductionOn l fun L h => ?_
  have he := (FunctionalRelation.toHom_eq_iff (FunctionalRelation.comp L Q.inclusion) P.inclusion).mp h
  have hi : Reduces P.val (fun x => P.inclusion.val x x) :=
    reduces_and_intro P.strict (reduces_refl _)
  apply reduces_trans (reduces_trans hi (reindex_reduces (fun x => (x, x)) he.2))
  let Γ : X.Carrier × X.Carrier → Set ℕ :=
    realizabilityAnd (fun p => L.val p.1 p.2) (fun p => Q.inclusion.val p.2 p.1)
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  exact reduces_trans (reduces_and_right _ _)
    (reindex_reduces (fun p : X.Carrier × X.Carrier => (p.2, p.1)) Q.extensional)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For uniqueness of the predicate presentation, suppose an arrow $L$ satisfies $J_\psi\circ L=J_\varphi$.
    A realizer of $\varphi(y)$ supplies $J_\varphi(y,y)$ by strictness. The equality of arrows converts it into a
    composite realizer with some intermediate point $y'$. Its inclusion component contains $y'\sim_Y y$ and $\psi(y')$,
    so extensionality of $\psi$ returns $\psi(y)$. This proves $\varphi\le\psi$ uniformly. Applying the same argument
    to an inverse isomorphism proves $\psi\le\varphi$.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{realizability subobject presentation}{Predicate presentation of subobjects}]
-/
theorem RealizerPER.StrictPredicate.equivalent_of_iso {X : RealizerPER.{u}} (P Q : StrictPredicate X)
    (e : P.restriction ≅ Q.restriction) (he : e.hom ≫ Q.inclusion.toHom = P.inclusion.toHom) :
    Reduces P.val Q.val ∧ Reduces Q.val P.val := by
  refine ⟨P.reduces_of_factor Q e.hom he, Q.reduces_of_factor P e.inv ?_⟩
  rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]

end PolishSpaceBook.LambdaIndexPCA
