module

public import PolishSpaceBook.LambdaRealizabilityTripos

@[expose] public section

/-! # Realizer-valued partial equivalence relations and functional relations

All entailments below use the concrete lambda-index application graph. Logical
composition reuses the closed lambda programs constructed in `LambdaRealizerLogic`.
Existential witnesses are semantic base points, never inputs to those programs.
-/
namespace PolishSpaceBook.LambdaIndexPCA

universe u v w

/-- Pointwise inclusion is tracked by the identity lambda term. -/
theorem reduces_of_subset {I : Type*} {φ ψ : I → Set ℕ}
    (h : ∀ i, φ i ⊆ ψ i) : Reduces φ ψ := by
  obtain ⟨e, he⟩ := (reduces_iff ψ ψ).mp (reduces_refl ψ)
  exact (reduces_iff φ ψ).mpr ⟨e, fun i a ha => he i a (h i ha)⟩

/-- Forget a semantic witness using a tracker independent of that witness. -/
theorem reduces_cover {I J : Type*} {φ ψ : I → Set ℕ} {θ : I × J → Set ℕ}
    (cover : ∀ i a, a ∈ φ i → ∃ j, a ∈ θ (i, j))
    (h : Reduces θ (fun p => ψ p.1)) : Reduces φ ψ := by
  obtain ⟨e, he⟩ := (reduces_iff _ _).mp h
  apply (reduces_iff _ _).mpr
  refine ⟨e, fun i a ha => ?_⟩
  obtain ⟨j, hj⟩ := cover i a ha
  exact he (i, j) a hj

abbrev RealizerRelation (A : Type u) (B : Type v) := A → B → Set ℕ

def relationComp {A B C : Type*} (F : RealizerRelation A B) (G : RealizerRelation B C) :
    RealizerRelation A C := fun x z => {a | ∃ y, a.unpair.1 ∈ F x y ∧ a.unpair.2 ∈ G y z}

/-- The concrete union of sets of paired realizers in the book. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    Composition is relational:
    $$
    (G\circ F)(x,z)
    =
    \bigcup_{y\in |Y|}
    \{\NatPair{a}{b}:a\in F(x,y),\ b\in G(y,z)\}.
    $$
-/
theorem relationComp_mem_iff {A B C : Type*} (F : RealizerRelation A B)
    (G : RealizerRelation B C) (x : A) (z : C) (n : ℕ) :
    n ∈ relationComp F G x z ↔ ∃ y a, a ∈ F x y ∧ ∃ b, b ∈ G y z ∧ n = Nat.pair a b := by
  constructor
  · rintro ⟨y, ha, hb⟩
    exact ⟨y, n.unpair.1, ha, n.unpair.2, hb, (Nat.pair_unpair n).symm⟩
  · rintro ⟨y, a, ha, b, hb, rfl⟩
    exact ⟨y, by simpa using ha, by simpa using hb⟩

theorem relationComp_intro {I A B C : Type*} {Γ : I → Set ℕ}
    {F : RealizerRelation A B} {G : RealizerRelation B C} {x : I → A} {y : I → B} {z : I → C}
    (hF : Reduces Γ (fun i => F (x i) (y i)))
    (hG : Reduces Γ (fun i => G (y i) (z i))) :
    Reduces Γ (fun i => relationComp F G (x i) (z i)) :=
  reduces_trans (reduces_and_intro hF hG) (reduces_of_subset fun i _ ha => ⟨y i, ha⟩)

/-- A PER is allowed to have empty extent; symmetry and transitivity have uniform trackers. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    An \termdefineas{effective topos object}{object} is a pair
    $$X=(|X|,\sim_X)$$
    where $|X|$ is a set and
    $$\sim_X:|X|\times |X|\to\PowerSet{\NN}$$
    is a realizability predicate satisfying symmetry and transitivity:
    
    *   there is an index sending every realizer of $x\sim_X y$ to a realizer of $y\sim_X x$;
    *   there is an index sending a pair of realizers of $x\sim_X y$ and $y\sim_X z$ to a realizer of $x\sim_X z$.
-/
structure RealizerPER where
  Carrier : Type u
  rel : RealizerRelation Carrier Carrier
  symmetry : Reduces (fun p : Carrier × Carrier => rel p.1 p.2)
    (fun p => rel p.2 p.1)
  transitivity : Reduces
    (realizabilityAnd (fun p : Carrier × Carrier × Carrier => rel p.1 p.2.1)
      (fun p => rel p.2.1 p.2.2)) (fun p => rel p.1 p.2.2)

namespace RealizerPER

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The \termdefineas{effective topos extent}{extent} of $x$ is
    $$E_X(x):=(x\sim_X x).$$
    Only elements with inhabited extent are internally present; an element whose extent is empty is a formal representative
    with no evidence of existence.
-/
def extent (X : RealizerPER) (x : X.Carrier) : Set ℕ := X.rel x x

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    Fix trackers for the PER and functional-relation conditions. Write $s_X(a)$ for the symmetry transformer and
    $t_X(a,b)$ for the transitivity transformer applied to $\NatPair{a}{b}$. For $F$, let
    $\ell_F(a),r_F(a)$ be the two projections of its strictness output. Write $q_F(r,a,s)$ for its extensionality
    transformer applied to $\NatPair{\NatPair{r}{a}}{s}$, $v_F(a,b)$ for its single-valuedness transformer applied to
    $\NatPair{a}{b}$, and $u_F(e)$ for its totality transformer. These are partial numerical functions evaluated by
    lambda indices, with definedness guaranteed on the indicated realizers. Every expression below expands into a closed
    lambda term by using $U=\LambdaOutputSearch$, numerical pairing, projections, and composition, as in
    §{sec:effective-topos-construction}. In particular, no transformation is allowed to depend on an unprovided
    representative of an underlying set.
-/
theorem symm_of (X : RealizerPER) {I : Type*} {Γ : I → Set ℕ} {x y : I → X.Carrier}
    (h : Reduces Γ (fun i => X.rel (x i) (y i))) :
    Reduces Γ (fun i => X.rel (y i) (x i)) :=
  reduces_trans h (reindex_reduces (fun i => (x i, y i)) X.symmetry)

theorem trans_of (X : RealizerPER) {I : Type*} {Γ : I → Set ℕ} {x y z : I → X.Carrier}
    (h₁ : Reduces Γ (fun i => X.rel (x i) (y i)))
    (h₂ : Reduces Γ (fun i => X.rel (y i) (z i))) :
    Reduces Γ (fun i => X.rel (x i) (z i)) :=
  reduces_trans (reduces_and_intro h₁ h₂)
    (reindex_reduces (fun i => (x i, y i, z i)) X.transitivity)

/-- Extent evidence is derived uniformly, not assumed for every representative. -/
theorem extent_left_of (X : RealizerPER) {I : Type*} {Γ : I → Set ℕ} {x y : I → X.Carrier}
    (h : Reduces Γ (fun i => X.rel (x i) (y i))) :
    Reduces Γ (fun i => X.extent (x i)) := X.trans_of h (X.symm_of h)

theorem extent_right_of (X : RealizerPER) {I : Type*} {Γ : I → Set ℕ} {x y : I → X.Carrier}
    (h : Reduces Γ (fun i => X.rel (x i) (y i))) :
    Reduces Γ (fun i => X.extent (y i)) := X.trans_of (X.symm_of h) h

end RealizerPER

/-- The four conditions use one index per condition, uniform in all representatives. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    A \termdefineas{effective topos morphism}{morphism} $F:X\to Y$ is represented by a realizability relation
    $$F:|X|\times |Y|\to\PowerSet{\NN}$$
    satisfying the following four conditions, each uniformly realized by some natural-number index:
    
    1.  \termdefineas{strictness of effective topos morphism}{strictness}: $F(x,y)$ implies $E_X(x)$ and $E_Y(y)$.
    2.  \termdefineas{extensionality of effective topos morphism}{extensionality}: $x\sim_X x'$, $F(x,y)$, and $y\sim_Y y'$
        imply $F(x',y')$.
    3.  \termdefineas{single-valuedness of effective topos morphism}{single-valuedness}: $F(x,y)$ and $F(x,y')$ imply
        $y\sim_Y y'$.
    4.  \termdefineas{totality on effective topos extent}{totality on the extent}: $E_X(x)$ implies $\exists y\,F(x,y)$.
-/
structure FunctionalRelation (X Y : RealizerPER.{u}) where
  val : RealizerRelation X.Carrier Y.Carrier
  strict : Reduces (fun p : X.Carrier × Y.Carrier => val p.1 p.2)
    (realizabilityAnd (fun p => X.extent p.1) (fun p => Y.extent p.2))
  extensional : Reduces
    (realizabilityAnd
      (realizabilityAnd (fun p : X.Carrier × X.Carrier × Y.Carrier × Y.Carrier => X.rel p.1 p.2.1)
        (fun p => val p.1 p.2.2.1)) (fun p => Y.rel p.2.2.1 p.2.2.2))
    (fun p => val p.2.1 p.2.2.2)
  single : Reduces
    (realizabilityAnd (fun p : X.Carrier × Y.Carrier × Y.Carrier => val p.1 p.2.1)
      (fun p => val p.1 p.2.2)) (fun p => Y.rel p.2.1 p.2.2)
  total : Reduces X.extent (fun x => {a | ∃ y, a ∈ val x y})

namespace FunctionalRelation

theorem strict_left_of {X Y : RealizerPER} (F : FunctionalRelation X Y)
    {I : Type*} {Γ : I → Set ℕ} {x : I → X.Carrier} {y : I → Y.Carrier}
    (h : Reduces Γ (fun i => F.val (x i) (y i))) : Reduces Γ (fun i => X.extent (x i)) :=
  reduces_trans h (reduces_trans (reindex_reduces (fun i => (x i, y i)) F.strict)
    (reduces_and_left _ _))

theorem strict_right_of {X Y : RealizerPER} (F : FunctionalRelation X Y)
    {I : Type*} {Γ : I → Set ℕ} {x : I → X.Carrier} {y : I → Y.Carrier}
    (h : Reduces Γ (fun i => F.val (x i) (y i))) : Reduces Γ (fun i => Y.extent (y i)) :=
  reduces_trans h (reduces_trans (reindex_reduces (fun i => (x i, y i)) F.strict)
    (reduces_and_right _ _))

theorem ext_of {X Y : RealizerPER} (F : FunctionalRelation X Y)
    {I : Type*} {Γ : I → Set ℕ} {x x' : I → X.Carrier} {y y' : I → Y.Carrier}
    (hx : Reduces Γ (fun i => X.rel (x i) (x' i)))
    (hF : Reduces Γ (fun i => F.val (x i) (y i)))
    (hy : Reduces Γ (fun i => Y.rel (y i) (y' i))) :
    Reduces Γ (fun i => F.val (x' i) (y' i)) :=
  reduces_trans (reduces_and_intro (reduces_and_intro hx hF) hy)
    (reindex_reduces (fun i => (x i, x' i, y i, y' i)) F.extensional)

theorem single_of {X Y : RealizerPER} (F : FunctionalRelation X Y)
    {I : Type*} {Γ : I → Set ℕ} {x : I → X.Carrier} {y y' : I → Y.Carrier}
    (hF : Reduces Γ (fun i => F.val (x i) (y i)))
    (hF' : Reduces Γ (fun i => F.val (x i) (y' i))) :
    Reduces Γ (fun i => Y.rel (y i) (y' i)) :=
  reduces_trans (reduces_and_intro hF hF')
    (reindex_reduces (fun i => (x i, y i, y' i)) F.single)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    First consider the identity relation. From $a\in(x\sim_X y)$, symmetry and transitivity compute extent realizers
    $$t_X(a,s_X(a))\in E_X(x),\qquad t_X(s_X(a),a)\in E_X(y).$$
    Pairing these proves strictness. Given $r\in(x\sim_X x')$, $a\in(x\sim_X y)$, and $s\in(y\sim_X y')$, the expression
    $$t_X\bigl(t_X(s_X(r),a),s\bigr)\in(x'\sim_X y')$$
    proves extensionality. From $a\in(x\sim_X y)$ and $b\in(x\sim_X y')$, the expression $t_X(s_X(a),b)$ proves
    single-valuedness. An extent realizer already belongs to the identity relation at $(x,x)$, so the identity lambda term
    proves totality.
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    The identity on $X$ is $\sim_X$ itself.
-/
def identity (X : RealizerPER) : FunctionalRelation X X where
  val := X.rel
  strict := reduces_and_intro (X.extent_left_of (reduces_refl _))
    (X.extent_right_of (reduces_refl _))
  extensional := X.trans_of
    (X.trans_of (X.symm_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)))
      (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))) (reduces_and_right _ _)
  single := X.trans_of (X.symm_of (reduces_and_left _ _)) (reduces_and_right _ _)
  total := reduces_of_subset fun x _ ha => ⟨x, ha⟩


/-- Composition carries paired realizers, with no encoded intermediate representative. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Now take $F:X\to Y$ and $G:Y\to Z$. A composite realizer is a pair $\NatPair{a}{b}$ with
    $a\in F(x,y)$ and $b\in G(y,z)$ for some $y$. The pair $\NatPair{\ell_F(a)}{r_G(b)}$ realizes strictness.
    For extensionality, also suppose $r\in(x\sim_X x')$ and $s\in(z\sim_Z z')$. Then
    $$\NatPair{q_F(r,a,r_F(a))}{q_G(\ell_G(b),b,s)}$$
    belongs to $(G\circ F)(x',z')$, using the same intermediate point $y$. The terms $r_F(a)$ and $\ell_G(b)$ both
    supply evidence of $y\sim_Y y$, so each use of extensionality has all its required inputs.
    
    For single-valuedness, let $\NatPair{a}{b}$ and $\NatPair{a'}{b'}$ realize the composite at $(x,z)$ and
    $(x,z')$, with intermediate points $y,y'$. Put
    $$d=v_F(a,a'),\qquad c=q_G(d,b,r_G(b)).$$
    Here $d\in(y\sim_Y y')$ and $c\in G(y',z)$. Thus $v_G(c,b')\in(z\sim_Z z')$ proves single-valuedness.
    For totality, from $e\in E_X(x)$ compute
    $$a=u_F(e),\qquad b=u_G(r_F(a)),\qquad \NatPair{a}{b}.$$
    The first output belongs to $F(x,y)$ for some $y$; its strictness output $r_F(a)$ realizes $E_Y(y)$.
    The second output therefore belongs to $G(y,z)$ for some $z$, proving totality of the composite. The program never
    extracts or chooses $y$ or $z$: they occur only in the proof of membership of its numerical outputs.
-/
def comp {X Y Z : RealizerPER} (F : FunctionalRelation X Y) (G : FunctionalRelation Y Z) :
    FunctionalRelation X Z where
  val := relationComp F.val G.val
  strict := by
    let Γ : (X.Carrier × Z.Carrier) × Y.Carrier → Set ℕ :=
      realizabilityAnd (fun p => F.val p.1.1 p.2) (fun p => G.val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    exact reduces_and_intro (F.strict_left_of (reduces_and_left _ _))
      (G.strict_right_of (reduces_and_right _ _))
  extensional := by
    let Γ : (X.Carrier × X.Carrier × Z.Carrier × Z.Carrier) × Y.Carrier → Set ℕ :=
      realizabilityAnd
        (realizabilityAnd (fun p => X.rel p.1.1 p.1.2.1)
          (realizabilityAnd (fun p => F.val p.1.1 p.2) (fun p => G.val p.2 p.1.2.2.1)))
        (fun p => Z.rel p.1.2.2.1 p.1.2.2.2)
    apply reduces_cover (θ := Γ)
    · intro i a ha
      obtain ⟨y, hy⟩ := ha.1.2
      exact ⟨y, ⟨ha.1.1, hy⟩, ha.2⟩
    · have hF : Reduces Γ (fun p => F.val p.1.1 p.2) :=
        reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
          (reduces_and_left _ _)
      have hG : Reduces Γ (fun p => G.val p.2 p.1.2.2.1) :=
        reduces_trans (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
          (reduces_and_right _ _)
      exact relationComp_intro
        (F.ext_of (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
          hF (F.strict_right_of hF))
        (G.ext_of (G.strict_left_of hG) hG (reduces_and_right _ _))
  single := by
    let Γ : (X.Carrier × Z.Carrier × Z.Carrier) × (Y.Carrier × Y.Carrier) → Set ℕ :=
      realizabilityAnd
        (realizabilityAnd (fun p => F.val p.1.1 p.2.1) (fun p => G.val p.2.1 p.1.2.1))
        (realizabilityAnd (fun p => F.val p.1.1 p.2.2) (fun p => G.val p.2.2 p.1.2.2))
    apply reduces_cover (θ := Γ)
    · intro i a ha
      obtain ⟨y, hy⟩ := ha.1
      obtain ⟨y', hy'⟩ := ha.2
      exact ⟨(y, y'), hy, hy'⟩
    · have hF : Reduces Γ (fun p => F.val p.1.1 p.2.1) :=
        reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)
      have hF' : Reduces Γ (fun p => F.val p.1.1 p.2.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)
      have hG : Reduces Γ (fun p => G.val p.2.1 p.1.2.1) :=
        reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)
      have hG' : Reduces Γ (fun p => G.val p.2.2 p.1.2.2) :=
        reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)
      exact G.single_of (G.ext_of (F.single_of hF hF') hG (G.strict_right_of hG)) hG'
  total := by
    apply reduces_trans F.total
    apply reduces_cover (θ := fun p : X.Carrier × Y.Carrier => F.val p.1 p.2)
    · exact fun _ _ h => h
    · have hg : Reduces (fun p : X.Carrier × Y.Carrier => F.val p.1 p.2)
          (fun p => {a | ∃ z, a ∈ G.val p.2 z}) :=
        reduces_trans (F.strict_right_of (reduces_refl _))
          (reindex_reduces Prod.snd G.total)
      apply reduces_trans (reduces_and_intro (reduces_refl _) hg)
      apply reduces_of_subset
      intro p a ha
      obtain ⟨z, hz⟩ := ha.2
      exact ⟨z, p.2, ha.1, hz⟩


/-- A single transformer works for every pair of representatives. -/
def LE {X Y : RealizerPER} (F G : FunctionalRelation X Y) : Prop :=
  Reduces (fun p : X.Carrier × Y.Carrier => F.val p.1 p.2) (fun p => G.val p.1 p.2)

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    Two such relations represent the same morphism if they are internally equivalent:
    $$
    F\equiv G
    \quad\Longleftrightarrow\quad
    F(x,y)\le G(x,y)\ \text{and}\ G(x,y)\le F(x,y)
    \text{ uniformly in }x,y.
    $$
-/
def Equivalent {X Y : RealizerPER} (F G : FunctionalRelation X Y) : Prop := LE F G ∧ LE G F

instance relationSetoid (X Y : RealizerPER) : Setoid (FunctionalRelation X Y) where
  r := Equivalent
  iseqv := ⟨fun _ => ⟨reduces_refl _, reduces_refl _⟩,
    fun h => ⟨h.2, h.1⟩,
    fun h k => ⟨reduces_trans h.1 k.1, reduces_trans k.2 h.2⟩⟩

theorem comp_mono {X Y Z : RealizerPER} {F F' : FunctionalRelation X Y}
    {G G' : FunctionalRelation Y Z} (hF : LE F F') (hG : LE G G') :
    LE (comp F G) (comp F' G') := by
  let Γ : (X.Carrier × Z.Carrier) × Y.Carrier → Set ℕ :=
    realizabilityAnd (fun p => F.val p.1.1 p.2) (fun p => G.val p.2 p.1.2)
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  exact relationComp_intro
    (reduces_trans (reduces_and_left _ _) (reindex_reduces (fun p : (X.Carrier × Z.Carrier) × Y.Carrier => (p.1.1, p.2)) hF))
    (reduces_trans (reduces_and_right _ _) (reindex_reduces (fun p : (X.Carrier × Z.Carrier) × Y.Carrier => (p.2, p.1.2)) hG))

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Composition respects uniform equivalence. Indeed, if $e$ and $f$ track $F\le F'$ and $G\le G'$, respectively,
    then
    $$\NatPair{a}{b}\longmapsto\NatPair{e\cdot a}{f\cdot b}$$
    tracks $G\circ F\le G'\circ F'$. The same intermediate point witnesses membership on both sides.
    Applying this in both directions makes composition well defined on equivalence classes.
-/
theorem comp_congr {X Y Z : RealizerPER} {F F' : FunctionalRelation X Y}
    {G G' : FunctionalRelation Y Z} (hF : Equivalent F F') (hG : Equivalent G G') :
    Equivalent (comp F G) (comp F' G') :=
  ⟨comp_mono hF.1 hG.1, comp_mono hF.2 hG.2⟩

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    Finally, for $F\circ 1_X\equiv F$ the forward and reverse transformations are
    $$\NatPair{r}{a}\longmapsto q_F(s_X(r),a,r_F(a)),\qquad
     a\longmapsto\NatPair{\ell_F(a)}{a}.$$
    The forward map transports $F(x',y)$ along $r\in(x\sim_X x')$, while the reverse map uses $x$ as the intermediate
    point. For $1_Y\circ F\equiv F$, use
    $$\NatPair{a}{s}\longmapsto q_F(\ell_F(a),a,s),\qquad
     a\longmapsto\NatPair{a}{r_F(a)}.$$
    These formulas require only strictness and extensionality of $F$ and symmetry of the source PER.
    Thus associativity and both identity laws hold as literal equalities of equivalence classes.
    \end{proof}
-/
theorem identity_comp {X Y : RealizerPER} (F : FunctionalRelation X Y) :
    Equivalent (comp (identity X) F) F := by
  constructor
  · let Γ : (X.Carrier × Y.Carrier) × X.Carrier → Set ℕ :=
      realizabilityAnd (fun p => X.rel p.1.1 p.2) (fun p => F.val p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    exact F.ext_of (X.symm_of (reduces_and_left _ _)) (reduces_and_right _ _)
      (F.strict_right_of (reduces_and_right _ _))
  · exact relationComp_intro (F.strict_left_of (reduces_refl _)) (reduces_refl _)

theorem comp_identity {X Y : RealizerPER} (F : FunctionalRelation X Y) :
    Equivalent (comp F (identity Y)) F := by
  constructor
  · let Γ : (X.Carrier × Y.Carrier) × Y.Carrier → Set ℕ :=
      realizabilityAnd (fun p => F.val p.1.1 p.2) (fun p => Y.rel p.2 p.1.2)
    apply reduces_cover (θ := Γ) (fun _ _ h => h)
    exact F.ext_of (F.strict_left_of (reduces_and_left _ _)) (reduces_and_left _ _)
      (reduces_and_right _ _)
  · exact relationComp_intro (reduces_refl _) (F.strict_right_of (reduces_refl _))

/-- Reassociate numerical pairs; no computation on the intermediate points is used. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: proof
  excerpt: |
    For associativity, the two bracketings have the same intermediate points and differ only in their numerical pairing.
    The transformations
    $$\NatPair{\NatPair{a}{b}}{c}\longmapsto\NatPair{a}{\NatPair{b}{c}},\qquad
    \NatPair{a}{\NatPair{b}{c}}\longmapsto\NatPair{\NatPair{a}{b}}{c}$$
    use only numerical projections and pairing and realize the two inequalities uniformly.
-/
theorem comp_assoc {W X Y Z : RealizerPER} (F : FunctionalRelation W X)
    (G : FunctionalRelation X Y) (H : FunctionalRelation Y Z) :
    Equivalent (comp (comp F G) H) (comp F (comp G H)) := by
  constructor
  · let Γ : (W.Carrier × Z.Carrier) × (X.Carrier × Y.Carrier) → Set ℕ :=
      realizabilityAnd
        (realizabilityAnd (fun p => F.val p.1.1 p.2.1) (fun p => G.val p.2.1 p.2.2))
        (fun p => H.val p.2.2 p.1.2)
    apply reduces_cover (θ := Γ)
    · intro i a ha
      obtain ⟨y, ⟨x, hF, hG⟩, hH⟩ := ha
      exact ⟨(x, y), ⟨hF, hG⟩, hH⟩
    · exact relationComp_intro
        (reduces_trans (reduces_and_left _ _) (reduces_and_left _ _))
        (relationComp_intro (reduces_trans (reduces_and_left _ _) (reduces_and_right _ _))
          (reduces_and_right _ _))
  · let Γ : (W.Carrier × Z.Carrier) × (X.Carrier × Y.Carrier) → Set ℕ :=
      realizabilityAnd (fun p => F.val p.1.1 p.2.1)
        (realizabilityAnd (fun p => G.val p.2.1 p.2.2) (fun p => H.val p.2.2 p.1.2))
    apply reduces_cover (θ := Γ)
    · intro i a ha
      obtain ⟨x, hF, ⟨y, hG, hH⟩⟩ := ha
      exact ⟨(x, y), hF, hG, hH⟩
    · exact relationComp_intro
        (relationComp_intro (reduces_and_left _ _)
          (reduces_trans (reduces_and_right _ _) (reduces_and_left _ _)))
        (reduces_trans (reduces_and_right _ _) (reduces_and_right _ _))

end FunctionalRelation

/-- Morphisms are uniform-equivalence classes, not pointwise inhabitedness classes. -/
abbrev RealizerPER.Hom (X Y : RealizerPER.{u}) := Quotient (FunctionalRelation.relationSetoid X Y)

def FunctionalRelation.toHom {X Y : RealizerPER} (F : FunctionalRelation X Y) : RealizerPER.Hom X Y :=
  Quotient.mk _ F

/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    Two such relations represent the same morphism if they are internally equivalent:
    $$
    F\equiv G
    \quad\Longleftrightarrow\quad
    F(x,y)\le G(x,y)\ \text{and}\ G(x,y)\le F(x,y)
    \text{ uniformly in }x,y.
    $$
-/
@[simp] theorem FunctionalRelation.toHom_eq_iff {X Y : RealizerPER} (F G : FunctionalRelation X Y) :
    F.toHom = G.toHom ↔ FunctionalRelation.Equivalent F G := Quotient.eq

def RealizerPER.compose {X Y Z : RealizerPER} : X.Hom Y → Y.Hom Z → X.Hom Z :=
  Quotient.map₂ FunctionalRelation.comp (fun _ _ hF _ _ hG => FunctionalRelation.comp_congr hF hG)

/-- The category laws hold literally after quotienting the relations. -/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: statement
  excerpt: |
    \begin{proposition*}[\termdefineas{realizability PER category}{Category of realizability PERs}]
-/
/-@ booklink:
  source: polish-space-book/tripos-topos-forcing-realizability.md
  target: prose
  excerpt: |
    Concretely, it is the category of realizability
    \termdefineas{partial equivalence relation}{partial equivalence relations} and functional relations.
-/
instance realizabilityPERCategory : CategoryTheory.Category RealizerPER.{u} where
  Hom := RealizerPER.Hom
  id X := (FunctionalRelation.identity X).toHom
  comp := RealizerPER.compose
  id_comp f := Quotient.inductionOn f fun F => Quotient.sound (FunctionalRelation.identity_comp F)
  comp_id f := Quotient.inductionOn f fun F => Quotient.sound (FunctionalRelation.comp_identity F)
  assoc f g h := Quotient.inductionOn₃ f g h fun F G H =>
    Quotient.sound (FunctionalRelation.comp_assoc F G H)

end PolishSpaceBook.LambdaIndexPCA
