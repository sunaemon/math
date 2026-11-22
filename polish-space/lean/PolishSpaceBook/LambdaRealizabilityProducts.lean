module

public import PolishSpaceBook.LambdaRealizabilityPER
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

@[expose] public section

/-! # Terminal object and binary products of realizability PERs -/
namespace PolishSpaceBook.LambdaIndexPCA
open CategoryTheory Limits
universe u

namespace RealizerPER

/-- A function on representatives whose action on equality has one uniform tracker. -/
structure Map (X Y : RealizerPER.{u}) where
  toFun : X.Carrier → Y.Carrier
  preserves : Reduces (fun p : X.Carrier × X.Carrier => X.rel p.1 p.2)
    (fun p => Y.rel (toFun p.1) (toFun p.2))

theorem Map.map_of {X Y : RealizerPER} (f : Map X Y) {I : Type*} {Γ : I → Set ℕ}
    {x x' : I → X.Carrier} (h : Reduces Γ (fun i => X.rel (x i) (x' i))) :
    Reduces Γ (fun i => Y.rel (f.toFun (x i)) (f.toFun (x' i))) :=
  reduces_trans h (reindex_reduces (fun i => (x i, x' i)) f.preserves)

/-- The extent factor ensures strictness even at absent representatives. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For products, use representatives $(x,y)\in|X|\times|Y|$ and equality
    $$(x,y)\sim_{X\times Y}(x',y')=(x\sim_X x')\land(y\sim_Y y').$$
    Symmetry and transitivity act on each component. The projection relations are
    $$\begin{aligned}
    P_X((x,y),x')&=E_{X\times Y}(x,y)\land(x\sim_X x'),\\
    P_Y((x,y),y')&=E_{X\times Y}(x,y)\land(y\sim_Y y').
    \end{aligned}$$
    The extent factors ensure strictness even when a coordinate has empty extent. More generally, if a function $f$ on
    representatives uniformly preserves equality, its relation
    $$E_A(a)\land(f(a)\sim_B b)$$
    is functional. Symmetry and transitivity give extensionality and single-valuedness. A realizer of $E_A(a)$, together
    with its image under the equality-preserving tracker, proves totality at $b=f(a)$. Applying this observation to the two
    coordinate functions gives the displayed projections.
-/
def Map.graph {X Y : RealizerPER} (f : Map X Y) : FunctionalRelation X Y where
  val x y := {a | a.unpair.1 ∈ X.extent x ∧ a.unpair.2 ∈ Y.rel (f.toFun x) y}
  strict := reduces_and_intro (reduces_and_left _ _)
    (Y.extent_right_of (reduces_and_right _ _))
  extensional := by
    apply reduces_and_intro
    · exact X.extent_right_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
    · exact Y.trans_of
        (Y.trans_of
          (Y.symm_of (f.map_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))))
          (reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
            (reduces_and_right _ _))) (reduces_and_right _ _)
  single := Y.trans_of (Y.symm_of (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)))
    (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
  total := reduces_trans (reduces_and_intro (reduces_refl _) (f.map_of (reduces_refl _)))
    (reduces_of_subset fun x _ h => ⟨f.toFun x, h⟩)

def terminal : RealizerPER.{u} where
  Carrier := PUnit
  rel _ _ := Set.univ
  symmetry := reduces_refl _
  transitivity := reduces_top _

def toTerminal (X : RealizerPER.{u}) : FunctionalRelation X terminal where
  val x _ := X.extent x
  strict := reduces_and_intro (reduces_refl _) (reduces_top _)
  extensional := X.extent_right_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
  single := reduces_top _
  total := reduces_of_subset fun _ _ h => ⟨PUnit.unit, h⟩

theorem toTerminal_unique {X : RealizerPER.{u}} (F : FunctionalRelation X terminal) :
    F.Equivalent (toTerminal X) := by
  constructor
  · exact F.strict_left_of (reduces_refl _)
  · apply reduces_trans (reindex_reduces Prod.fst F.total)
    apply reduces_of_subset
    rintro p a ⟨y, hy⟩
    have h : y = p.2 := @Subsingleton.elim PUnit inferInstance y p.2
    exact h ▸ hy

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    We use the tracker notation from the proof in §{sec:effective-topos-objects-morphisms}.
    For the terminal object, take $1=\{\ast\}$ with $(\ast\sim_1\ast)=\NN$. The relation
    $$T_X(x,\ast)=E_X(x)$$
    is functional: strictness pairs the input with any natural number, extensionality follows from equality in $X$,
    single-valuedness has value $\NN$, and totality uses the same input. Any functional relation $F:X\to1$ reduces to
    $T_X$ by strictness. Conversely, totality sends $E_X(x)$ into $F(x,\ast)$ because there is only one representative
    in $1$. This proves uniqueness of the arrow to $1$.
-/
def terminalIsTerminal : IsTerminal terminal.{u} :=
  IsTerminal.ofUniqueHom (fun X => (toTerminal X).toHom)
    (fun _ f => Quotient.inductionOn f fun F => Quotient.sound (toTerminal_unique F))

/-- Equality in the product is a numerical pair of coordinate equality realizers. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For products, use representatives $(x,y)\in|X|\times|Y|$ and equality
    $$(x,y)\sim_{X\times Y}(x',y')=(x\sim_X x')\land(y\sim_Y y').$$
    Symmetry and transitivity act on each component. The projection relations are
    $$\begin{aligned}
    P_X((x,y),x')&=E_{X\times Y}(x,y)\land(x\sim_X x'),\\
    P_Y((x,y),y')&=E_{X\times Y}(x,y)\land(y\sim_Y y').
    \end{aligned}$$
    The extent factors ensure strictness even when a coordinate has empty extent. More generally, if a function $f$ on
    representatives uniformly preserves equality, its relation
    $$E_A(a)\land(f(a)\sim_B b)$$
    is functional. Symmetry and transitivity give extensionality and single-valuedness. A realizer of $E_A(a)$, together
    with its image under the equality-preserving tracker, proves totality at $b=f(a)$. Applying this observation to the two
    coordinate functions gives the displayed projections.
-/
def product (X Y : RealizerPER.{u}) : RealizerPER.{u} where
  Carrier := X.Carrier × Y.Carrier
  rel p q := {a | a.unpair.1 ∈ X.rel p.1 q.1 ∧ a.unpair.2 ∈ Y.rel p.2 q.2}
  symmetry := reduces_and_intro (X.symm_of (reduces_and_left _ _))
    (Y.symm_of (reduces_and_right _ _))
  transitivity := reduces_and_intro
    (X.trans_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
      (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)))
    (Y.trans_of (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
      (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)))

def fstMap (X Y : RealizerPER.{u}) : Map (product X Y) X where
  toFun := Prod.fst
  preserves := reduces_and_left _ _

def sndMap (X Y : RealizerPER.{u}) : Map (product X Y) Y where
  toFun := Prod.snd
  preserves := reduces_and_right _ _

abbrev fstRelation (X Y : RealizerPER.{u}) := (fstMap X Y).graph
abbrev sndRelation (X Y : RealizerPER.{u}) := (sndMap X Y).graph

end RealizerPER
namespace FunctionalRelation
open RealizerPER

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Given $F:Z\to X$ and $G:Z\to Y$, define
    $$H(z,(x,y)):=F(z,x)\land G(z,y).$$
    Strictness, extensionality, and single-valuedness follow componentwise; for totality, apply the two totality trackers
    to the same extent realizer and pair their outputs. Projection of a composite realizer, followed by extensionality of
    $F$, proves $P_X\circ H\le F$. Conversely, from $a\in F(z,x)$ compute $u_G(\ell_F(a))$; it belongs to $G(z,y)$
    for some $y$. These two outputs and their strictness outputs supply a realizer of $(P_X\circ H)(z,x)$.
    Thus $P_X\circ H\equiv F$, and the same argument gives $P_Y\circ H\equiv G$.
-/
def pairing {Z X Y : RealizerPER.{u}} (F : FunctionalRelation Z X) (G : FunctionalRelation Z Y) :
    FunctionalRelation Z (product X Y) where
  val z p := {a | a.unpair.1 ∈ F.val z p.1 ∧ a.unpair.2 ∈ G.val z p.2}
  strict := reduces_and_intro (F.strict_left_of (reduces_and_left _ _))
    (reduces_and_intro (F.strict_right_of (reduces_and_left _ _))
      (G.strict_right_of (reduces_and_right _ _)))
  extensional := reduces_and_intro
    (F.ext_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
      (reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
        (reduces_and_left _ _)) (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)))
    (G.ext_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
      (reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
        (reduces_and_right _ _)) (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)))
  single := reduces_and_intro
    (F.single_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
      (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)))
    (G.single_of (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
      (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)))
  total := by
    apply reduces_trans (reduces_and_intro F.total G.total)
    apply reduces_of_subset
    rintro z a ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨(x, y), hx, hy⟩

theorem pairing_mono {Z X Y : RealizerPER.{u}} {F F' : FunctionalRelation Z X}
    {G G' : FunctionalRelation Z Y} (hF : LE F F') (hG : LE G G') : LE (pairing F G) (pairing F' G') :=
  and_reduces_mono
    (reindex_reduces (fun p : Z.Carrier × (X.Carrier × Y.Carrier) => (p.1, p.2.1)) hF)
    (reindex_reduces (fun p : Z.Carrier × (X.Carrier × Y.Carrier) => (p.1, p.2.2)) hG)

theorem pairing_congr {Z X Y : RealizerPER.{u}} {F F' : FunctionalRelation Z X}
    {G G' : FunctionalRelation Z Y} (hF : Equivalent F F') (hG : Equivalent G G') :
    Equivalent (pairing F G) (pairing F' G') :=
  ⟨pairing_mono hF.1 hG.1, pairing_mono hF.2 hG.2⟩


/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Given $F:Z\to X$ and $G:Z\to Y$, define
    $$H(z,(x,y)):=F(z,x)\land G(z,y).$$
    Strictness, extensionality, and single-valuedness follow componentwise; for totality, apply the two totality trackers
    to the same extent realizer and pair their outputs. Projection of a composite realizer, followed by extensionality of
    $F$, proves $P_X\circ H\le F$. Conversely, from $a\in F(z,x)$ compute $u_G(\ell_F(a))$; it belongs to $G(z,y)$
    for some $y$. These two outputs and their strictness outputs supply a realizer of $(P_X\circ H)(z,x)$.
    Thus $P_X\circ H\equiv F$, and the same argument gives $P_Y\circ H\equiv G$.
-/
theorem pairing_fst {Z X Y : RealizerPER.{u}} (F : FunctionalRelation Z X) (G : FunctionalRelation Z Y) :
    Equivalent (comp (pairing F G) (fstRelation X Y)) F := by
  constructor
  · let Γ : (Z.Carrier × X.Carrier) × (X.Carrier × Y.Carrier) → Set ℕ :=
      realizabilityAnd (fun p => (pairing F G).val p.1.1 p.2)
        (fun p => (fstRelation X Y).val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    have hF : Reduces Γ (fun p => F.val p.1.1 p.2.1) :=
      reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)
    exact F.ext_of (F.strict_left_of hF) hF
      (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
  · apply reduces_trans (reduces_and_intro (reduces_refl _)
      (reduces_trans (F.strict_left_of (reduces_refl _)) (reindex_reduces Prod.fst G.total)))
    let Γ : (Z.Carrier × X.Carrier) × Y.Carrier → Set ℕ :=
      realizabilityAnd (fun p => F.val p.1.1 p.1.2) (fun p => G.val p.1.1 p.2)
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨ha, ⟨y, hy⟩⟩
      exact ⟨y, ha, hy⟩
    · exact relationComp_intro (y := fun p => (p.1.2, p.2)) (reduces_refl _)
        (reduces_and_intro ((pairing F G).strict_right_of (reduces_refl _))
          (F.strict_right_of (reduces_and_left _ _)))

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Given $F:Z\to X$ and $G:Z\to Y$, define
    $$H(z,(x,y)):=F(z,x)\land G(z,y).$$
    Strictness, extensionality, and single-valuedness follow componentwise; for totality, apply the two totality trackers
    to the same extent realizer and pair their outputs. Projection of a composite realizer, followed by extensionality of
    $F$, proves $P_X\circ H\le F$. Conversely, from $a\in F(z,x)$ compute $u_G(\ell_F(a))$; it belongs to $G(z,y)$
    for some $y$. These two outputs and their strictness outputs supply a realizer of $(P_X\circ H)(z,x)$.
    Thus $P_X\circ H\equiv F$, and the same argument gives $P_Y\circ H\equiv G$.
-/
theorem pairing_snd {Z X Y : RealizerPER.{u}} (F : FunctionalRelation Z X) (G : FunctionalRelation Z Y) :
    Equivalent (comp (pairing F G) (sndRelation X Y)) G := by
  constructor
  · let Γ : (Z.Carrier × Y.Carrier) × (X.Carrier × Y.Carrier) → Set ℕ :=
      realizabilityAnd (fun p => (pairing F G).val p.1.1 p.2)
        (fun p => (sndRelation X Y).val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    have hG : Reduces Γ (fun p => G.val p.1.1 p.2.2) :=
      reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)
    exact G.ext_of (G.strict_left_of hG) hG
      (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
  · apply reduces_trans (reduces_and_intro
      (reduces_trans (G.strict_left_of (reduces_refl _)) (reindex_reduces Prod.fst F.total))
      (reduces_refl _))
    let Γ : (Z.Carrier × Y.Carrier) × X.Carrier → Set ℕ :=
      realizabilityAnd (fun p => F.val p.1.1 p.2) (fun p => G.val p.1.1 p.1.2)
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨⟨x, hx⟩, ha⟩
      exact ⟨x, hx, ha⟩
    · exact relationComp_intro (y := fun p => (p.2, p.1.2)) (reduces_refl _)
        (reduces_and_intro ((pairing F G).strict_right_of (reduces_refl _))
          (G.strict_right_of (reduces_and_right _ _)))

/-- Coordinate images determine the full functional relation, including its realizers. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For uniqueness, let $K:Z\to X\times Y$ be any functional relation. Its strictness outputs give
    $$K(z,(x,y))\le(P_X\circ K)(z,x)\land(P_Y\circ K)(z,y).$$
    For the reverse inequality, the two composite realizers supply intermediate points $p,p'$ with realizers of
    $K(z,p)$ and $K(z,p')$, together with $p_1\sim_X x$ and $p'_2\sim_Y y$. Single-valuedness of $K$ gives
    $p\sim_{X\times Y}p'$, hence $p_2\sim_Y p'_2$. Transitivity yields $p_2\sim_Y y$, and pairing it with
    $p_1\sim_X x$ gives $p\sim_{X\times Y}(x,y)$. Extensionality of $K$ now supplies $K(z,(x,y))$.
    Each step uses a fixed tracker on the given numerical realizers. Consequently $K$ is uniformly equivalent to the
    pairing of its two projections, proving uniqueness.
-/
theorem pairing_eta {Z X Y : RealizerPER.{u}} (H : FunctionalRelation Z (product X Y)) :
    Equivalent H (pairing (comp H (fstRelation X Y)) (comp H (sndRelation X Y))) := by
  constructor
  · have hE : Reduces (fun p : Z.Carrier × (X.Carrier × Y.Carrier) => H.val p.1 p.2)
        (fun p => (product X Y).extent p.2) := H.strict_right_of (reduces_refl _)
    exact reduces_and_intro
      (relationComp_intro (reduces_refl _)
        (reduces_and_intro hE (reduces_trans hE (reduces_and_left _ _))))
      (relationComp_intro (reduces_refl _)
        (reduces_and_intro hE (reduces_trans hE (reduces_and_right _ _))))
  · let Γ : (Z.Carrier × (X.Carrier × Y.Carrier)) ×
        ((X.Carrier × Y.Carrier) × (X.Carrier × Y.Carrier)) → Set ℕ :=
      realizabilityAnd
        (realizabilityAnd (fun p => H.val p.1.1 p.2.1)
          (fun p => (fstRelation X Y).val p.2.1 p.1.2.1))
        (realizabilityAnd (fun p => H.val p.1.1 p.2.2)
          (fun p => (sndRelation X Y).val p.2.2 p.1.2.2))
    apply reduces_cover (θ := Γ)
    · rintro p a ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
      exact ⟨(q, r), hq, hr⟩
    · have hH : Reduces Γ (fun p => H.val p.1.1 p.2.1) :=
        reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)
      have hH' : Reduces Γ (fun p => H.val p.1.1 p.2.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)
      exact H.ext_of (H.strict_left_of hH) hH
        (reduces_and_intro
          (reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
            (reduces_and_right _ _))
          (Y.trans_of (reduces_trans (H.single_of hH hH') (reduces_and_right _ _))
            (reduces_trans (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))
              (reduces_and_right _ _))))

end FunctionalRelation
namespace RealizerPER

def pairHom {Z X Y : RealizerPER.{u}} : (Z ⟶ X) → (Z ⟶ Y) → (Z ⟶ product X Y) :=
  Quotient.map₂ FunctionalRelation.pairing (fun _ _ hF _ _ hG => FunctionalRelation.pairing_congr hF hG)

theorem pairHom_fst {Z X Y : RealizerPER.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    pairHom f g ≫ (fstRelation X Y).toHom = f :=
  Quotient.inductionOn₂ f g fun F G => Quotient.sound (FunctionalRelation.pairing_fst F G)

theorem pairHom_snd {Z X Y : RealizerPER.{u}} (f : Z ⟶ X) (g : Z ⟶ Y) :
    pairHom f g ≫ (sndRelation X Y).toHom = g :=
  Quotient.inductionOn₂ f g fun F G => Quotient.sound (FunctionalRelation.pairing_snd F G)

theorem pairHom_eta {Z X Y : RealizerPER.{u}} (h : Z ⟶ product X Y) :
    h = pairHom (h ≫ (fstRelation X Y).toHom) (h ≫ (sndRelation X Y).toHom) :=
  Quotient.inductionOn h fun H => Quotient.sound (FunctionalRelation.pairing_eta H)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For uniqueness, let $K:Z\to X\times Y$ be any functional relation. Its strictness outputs give
    $$K(z,(x,y))\le(P_X\circ K)(z,x)\land(P_Y\circ K)(z,y).$$
    For the reverse inequality, the two composite realizers supply intermediate points $p,p'$ with realizers of
    $K(z,p)$ and $K(z,p')$, together with $p_1\sim_X x$ and $p'_2\sim_Y y$. Single-valuedness of $K$ gives
    $p\sim_{X\times Y}p'$, hence $p_2\sim_Y p'_2$. Transitivity yields $p_2\sim_Y y$, and pairing it with
    $p_1\sim_X x$ gives $p\sim_{X\times Y}(x,y)$. Extensionality of $K$ now supplies $K(z,(x,y))$.
    Each step uses a fixed tracker on the given numerical realizers. Consequently $K$ is uniformly equivalent to the
    pairing of its two projections, proving uniqueness.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{finite limits in realizability}{Finite limits in realizability}]
-/
def productIsLimit (X Y : RealizerPER.{u}) :
    IsLimit (BinaryFan.mk (C := RealizerPER.{u}) (fstRelation X Y).toHom (sndRelation X Y).toHom) :=
  BinaryFan.isLimitMk (fun s => pairHom s.fst s.snd)
    (fun s => pairHom_fst s.fst s.snd) (fun s => pairHom_snd s.fst s.snd)
    (fun s m h₁ h₂ => (pairHom_eta m).trans (by rw [h₁, h₂]))

end RealizerPER
end PolishSpaceBook.LambdaIndexPCA
