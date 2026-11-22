module

public import PolishSpaceBook.PCAAssemblyEmbedding

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! # Reconstructing separated realizability PERs as assemblies

Only supported representatives enter the external quotient. Every class keeps
all names of its representatives; no tracker selects a representative.
-/
namespace PolishSpaceBook.PCARealizability.RealizerPER
open CategoryTheory
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Assembly equality and double negation.** Write $\neg\varphi:=\varphi\to\bot$.
    For an assembly $X$ over $A$, put
    $$\begin{aligned}
    E(x)&:=\{a\in A:a\Vdash_X x\},\\
    \delta(x,y)&:=\begin{cases}E(x),&x=y,\\\emptyset,&x\ne y,\end{cases}\\
    D(x,y)&:=E(x)\land E(y).
    \end{aligned}$$
    In the PER presentation, $\neg\neg$-separation says that equality is stable under double negation
    when the existence evidence for both arguments is retained:
    $$D\land\neg\neg\delta\le\delta.$$
    A monomorphism is $\neg\neg$-dense when double negation of its image predicate is the top predicate
    on its codomain.
-/
def Separated (X : RealizerPER.{r,u} K) : Prop :=
  K.Entails
    (K.predAnd (K.predAnd (fun p : X.Carrier × X.Carrier => X.extent p.1)
      (fun p => X.extent p.2)) (K.predNeg (K.predNeg (fun p => X.rel p.1 p.2))))
    (fun p => X.rel p.1 p.2)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Let $s$ track the assumed stability condition. If $a\in E(x)$ and $b\in E(y)$ with
    $\rho(x,y)\ne\emptyset$, put $w:=\PCAPair{a}{b}$. Then $w$ realizes the two extents and also belongs
    to $(\neg\neg\rho)(x,y)$, so
    $$s\PCAPair{w}{w}\downarrow\in\rho(x,y).$$
    This is a fixed operation on the supplied names. For single-valuedness of $G$, two names coming from
    the same class give the required nonempty equality set by the quotient definition. The displayed
    operation therefore supplies a realizer of equality, proving that $G$ is functional.
-/
theorem separated_of {X : RealizerPER.{r,u} K} (hX : X.Separated)
    {I : Type*} {Γ : I → Set R} {x y : I → X.Carrier}
    (hx : K.Entails Γ (fun i => X.extent (x i)))
    (hy : K.Entails Γ (fun i => X.extent (y i)))
    (h : ∀ i a, a ∈ Γ i → (X.rel (x i) (y i)).Nonempty) :
    K.Entails Γ (fun i => X.rel (x i) (y i)) := by
  apply K.entails_trans (K.and_intro (K.and_intro hx hy) (reduces_of_subset ?_))
    (K.reindex_entails (fun i => (x i,y i)) hX)
  intro i a ha
  exact (K.mem_doubleNeg_iff _ _ a).mpr (h i a ha)

def Supported (X : RealizerPER.{r,u} K) := {x : X.Carrier // (X.extent x).Nonempty}

theorem nonempty_symm (X : RealizerPER.{r,u} K) {x y : X.Carrier}
    (h : (X.rel x y).Nonempty) : (X.rel y x).Nonempty := by
  obtain ⟨a,ha⟩ := h
  obtain ⟨s,hs⟩ := X.symmetry
  obtain ⟨b,_,hb⟩ := hs (x,y) a ha
  exact ⟨b,hb⟩

theorem nonempty_trans (X : RealizerPER.{r,u} K) {x y z : X.Carrier}
    (h : (X.rel x y).Nonempty) (h' : (X.rel y z).Nonempty) : (X.rel x z).Nonempty := by
  obtain ⟨a,ha⟩ := h
  obtain ⟨b,hb⟩ := h'
  obtain ⟨t,ht⟩ := X.transitivity
  obtain ⟨c,_,hc⟩ := ht (x,y,z) (K.pair a b) ⟨a,b,rfl,ha,hb⟩
  exact ⟨c,hc⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For the converse, let $\rho$ be the equality PER of an object with underlying set $I$, and put
    $E(x):=\rho(x,x)$. Restrict first to the supported representatives and then form their external quotient:
    $$\begin{aligned}
    S&:=\{x\in I:E(x)\ne\emptyset\},\\
    x\approx y&\quad\Longleftrightarrow\quad\rho(x,y)\ne\emptyset\quad(x,y\in S),\\
    Q&:=\SetQuotient{S}{\approx}.
    \end{aligned}$$
    This is an equivalence relation: reflexivity uses the definition of the support, and the symmetry and
    transitivity trackers send inhabited realizer sets to inhabited realizer sets. Representatives with
    empty extent are excluded even when the underlying set contains them.
-/
def supportSetoid (X : RealizerPER.{r,u} K) : Setoid X.Supported where
  r x y := (X.rel x.val y.val).Nonempty
  iseqv := ⟨fun x => x.property,fun h => X.nonempty_symm h,fun h h' => X.nonempty_trans h h'⟩

def components (X : RealizerPER.{r,u} K) := Quotient X.supportSetoid

def component (X : RealizerPER.{r,u} K) (x : X.Supported) : X.components := Quotient.mk _ x

theorem component_eq_iff (X : RealizerPER.{r,u} K) (x y : X.Supported) :
    X.component x = X.component y ↔ (X.rel x.val y.val).Nonempty := Quotient.eq

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Give each class every name of each of its representatives:
    $$a\Vdash_Q q\quad\Longleftrightarrow\quad
    \exists x\in S\,\bigl(\EquivalenceClass{\approx}{x}=q\land a\in E(x)\bigr).$$
    Every class has such a name, so this defines an assembly. Define relations in the two directions by
    $$F(x,q)=G(q,x):=
    \begin{cases}
    E(x),&x\in S\text{ and }\EquivalenceClass{\approx}{x}=q,\\
    \emptyset,&\text{otherwise}.
    \end{cases}$$
    No value of a tracker depends on choosing a representative of a class.
-/
def componentAssembly (X : RealizerPER.{r,u} K) : Assembly.{r,u} K where
  Carrier := X.components
  realizes a q := ∃ x : X.Supported, X.component x = q ∧ a ∈ X.extent x.val
  inhabited q := by
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨a,ha⟩ := x.property
      exact ⟨a,x,rfl,ha⟩

/-- The forward and reverse relations keep an existing name of the representative. -/
def componentRelation (X : RealizerPER.{r,u} K) (x : X.Carrier) (q : X.components) : Set R :=
  {a | ∃ hx : (X.extent x).Nonempty, X.component ⟨x,hx⟩ = q ∧ a ∈ X.extent x}

theorem componentRelation_name (X : RealizerPER.{r,u} K) {x : X.Carrier} {q : X.components}
    {a : R} (h : a ∈ X.componentRelation x q) : X.componentAssembly.realizes a q := by
  obtain ⟨hx,hq,ha⟩ := h
  exact ⟨⟨x,hx⟩,hq,ha⟩

theorem componentRelation_nonempty (X : RealizerPER.{r,u} K) {x y : X.Carrier} {q : X.components}
    {a b : R} (h : a ∈ X.componentRelation x q) (h' : b ∈ X.componentRelation y q) :
    (X.rel x y).Nonempty := by
  obtain ⟨hx,hq,_⟩ := h
  obtain ⟨hy,hq',_⟩ := h'
  exact (X.component_eq_iff ⟨x,hx⟩ ⟨y,hy⟩).mp (hq.trans hq'.symm)

/-- Transport names to an equal representative using the PER's extent tracker. -/
theorem componentRelation_transport (X : RealizerPER.{r,u} K)
    {I : Type*} {Γ : I → Set R} {x y : I → X.Carrier} {q : I → X.components}
    (he : K.Entails Γ (fun i => X.rel (x i) (y i)))
    (h : ∀ i a, a ∈ Γ i → ∃ b, b ∈ X.componentRelation (x i) (q i)) :
    K.Entails Γ (fun i => X.componentRelation (y i) (q i)) := by
  obtain ⟨t,ht⟩ := X.extent_right_of he
  obtain ⟨e,he⟩ := he
  refine ⟨t,fun i a ha => ?_⟩
  obtain ⟨b,hb,hby⟩ := ht i a ha
  obtain ⟨c,_,hc⟩ := he i a ha
  obtain ⟨d,hx,hq,_⟩ := h i a ha
  refine ⟨b,hb,⟨b,hby⟩,?_,hby⟩
  exact ((X.component_eq_iff ⟨x i,hx⟩ ⟨y i,⟨b,hby⟩⟩).mpr ⟨c,hc⟩).symm.trans hq

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Both relations are strict: duplicate the input name to obtain the two extent realizers.
    They are total using the identity tracker. In the forward direction an extent name realizes the forward relation at
    the class of its representative; in the reverse direction a name of a class already
    realizes some representative. These representatives witness membership, but are not computed outputs.
    For extensionality, a realizer of $\rho(x,x')$ gives an extent realizer of $x'$ and implies that their
    classes agree. This transports the displayed relations; assembly equality identifies the two class
    arguments. For single-valuedness of $F$, the two classes are equal to the class of the same
    representative, and first projection supplies a name of that class.
-/
def toComponents (X : RealizerPER.{r,u} K) :
    FunctionalRelation X X.componentAssembly.toRealizerPER where
  val := X.componentRelation
  strict := K.and_intro
    (reduces_of_subset fun _ _ h => h.choose_spec.2)
    (reduces_of_subset fun _ _ h => ⟨rfl,X.componentRelation_name h⟩)
  extensional := by
    let Γ := K.predAnd
      (K.predAnd (fun p : X.Carrier × X.Carrier × X.components × X.components => X.rel p.1 p.2.1)
        (fun p => X.componentRelation p.1 p.2.2.1))
      (fun p => X.componentAssembly.toRealizerPER.rel p.2.2.1 p.2.2.2)
    apply X.componentRelation_transport (Γ := Γ)
      (x := fun p => p.1) (q := fun p => p.2.2.2)
      (K.entails_trans (K.and_left _ _) (K.and_left _ _))
    rintro p _ ⟨ab,c,rfl,⟨a,b,rfl,_,hb⟩,hc⟩
    exact ⟨b,hc.1 ▸ hb⟩
  single := by
    refine ⟨K.firstProjection,?_⟩
    rintro ⟨x,q,q'⟩ _ ⟨a,b,rfl,⟨hx,hq,ha⟩,⟨_,hq',_⟩⟩
    exact ⟨a,K.application_firstProjection a b,hq.symm.trans hq',⟨⟨x,hx⟩,hq,ha⟩⟩
  total := reduces_of_subset fun x a ha => ⟨X.component ⟨x,⟨a,ha⟩⟩,⟨a,ha⟩,rfl,ha⟩

def fromComponents (X : RealizerPER.{r,u} K) (hX : X.Separated) :
    FunctionalRelation X.componentAssembly.toRealizerPER X where
  val q x := X.componentRelation x q
  strict := K.and_intro
    (reduces_of_subset fun _ _ h => ⟨rfl,X.componentRelation_name h⟩)
    (reduces_of_subset fun _ _ h => h.choose_spec.2)
  extensional := by
    apply X.componentRelation_transport
      (I := X.components × X.components × X.Carrier × X.Carrier)
      (x := fun p => p.2.2.1) (q := fun p => p.2.1) (K.and_right _ _)
    rintro p _ ⟨ab,c,rfl,⟨a,b,rfl,ha,hb⟩,_⟩
    exact ⟨b,ha.1 ▸ hb⟩
  single := by
    apply X.separated_of hX
      (K.entails_trans (K.and_left _ _) (reduces_of_subset fun _ _ h => h.choose_spec.2))
      (K.entails_trans (K.and_right _ _) (reduces_of_subset fun _ _ h => h.choose_spec.2))
    rintro p _ ⟨a,b,rfl,ha,hb⟩
    exact X.componentRelation_nonempty ha hb
  total := reduces_of_subset fun q a ha => by
    obtain ⟨x,hq,hax⟩ := ha.2
    exact ⟨x.val,x.property,hq,hax⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    The same operation gives $G\circ F\le\rho$: a composite realizer contains two extent names whose
    representatives have the same class. For the other composite, a realizer of $F\circ G$ contains names of a common
    representative, so the two classes are equal and first projection realizes the assembly equality.
    Applying the one-inclusion criterion to these two inclusions proves both inverse laws.
    Thus $F,G$ induce an isomorphism between the original PER and the embedded assembly on $Q$.
    The preceding proposition supplies stability for every embedded assembly, completing both constructions.
-/
theorem to_from_components (X : RealizerPER.{r,u} K) (hX : X.Separated) :
    ((X.toComponents).comp (X.fromComponents hX)).Equivalent (FunctionalRelation.identity X) := by
  apply FunctionalRelation.equivalent_of_le
  let Γ : (X.Carrier × X.Carrier) × X.components → Set R :=
    K.predAnd (fun p => X.componentRelation p.1.1 p.2) (fun p => X.componentRelation p.1.2 p.2)
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  apply X.separated_of hX
    (K.entails_trans (K.and_left _ _) (reduces_of_subset fun _ _ h => h.choose_spec.2))
    (K.entails_trans (K.and_right _ _) (reduces_of_subset fun _ _ h => h.choose_spec.2))
  rintro p _ ⟨a,b,rfl,ha,hb⟩
  exact X.componentRelation_nonempty ha hb

theorem from_to_components (X : RealizerPER.{r,u} K) (hX : X.Separated) :
    ((X.fromComponents hX).comp X.toComponents).Equivalent
      (FunctionalRelation.identity X.componentAssembly.toRealizerPER) := by
  apply FunctionalRelation.equivalent_of_le
  refine ⟨K.firstProjection,?_⟩
  rintro ⟨q,q'⟩ _ ⟨x,a,b,rfl,⟨hx,hq,ha⟩,⟨_,hq',_⟩⟩
  exact ⟨a,K.application_firstProjection a b,hq.symm.trans hq',⟨⟨x,hx⟩,hq,ha⟩⟩

def componentIso (X : RealizerPER.{r,u} K) (hX : X.Separated) :
    X ≅ X.componentAssembly.toRealizerPER where
  hom := X.toComponents.toHom
  inv := (X.fromComponents hX).toHom
  hom_inv_id := Quotient.sound (X.to_from_components hX)
  inv_hom_id := Quotient.sound (X.from_to_components hX)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The category $\AsmCat{A}$ embeds fully and faithfully into the realizability topos $\RTCat{A}$ as the full subcategory
    of $\neg\neg$-separated objects. For each assembly, its canonical monomorphism into the constant object on its
    underlying set is $\neg\neg$-dense. Modest sets sit inside $\AsmCat{A}$ as a reflective subcategory, and hence
    embed into $\RTCat{A}$ as well. For $K_1$, modest sets correspond to the separated
    subquotients of the natural-numbers object; the larger class of discrete objects need not be separated. The
    next subsection records how $\RTCat{A}$ itself is
    built.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The earlier categories embed cleanly: $\AsmCat{K_1} \hookrightarrow \EffCat$ as the $\neg\neg$-separated objects, and
    $\ModCat{K_1} \hookrightarrow \AsmCat{K_1} \hookrightarrow \EffCat$ as the separated discrete objects. The
    canonical monomorphism
    from each assembly into the constant object on its underlying set is $\neg\neg$-dense.
-/
theorem assembly_separated (A : Assembly.{r,u} K) : A.toRealizerPER.Separated := by
  unfold Separated
  simp only [Assembly.extent_toRealizerPER]
  change K.Entails (K.predAnd A.pairExistence (K.predNeg (K.predNeg A.diagonal))) A.diagonal
  exact Assembly.diagonal_doubleNeg_stable A

/-- Every predicate-separated object is in the essential image of the assembly embedding. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: theorem
  title: Assembly reconstruction of separated PERs
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The category $\AsmCat{A}$ embeds fully and faithfully into the realizability topos $\RTCat{A}$ as the full subcategory
    of $\neg\neg$-separated objects. For each assembly, its canonical monomorphism into the constant object on its
    underlying set is $\neg\neg$-dense. Modest sets sit inside $\AsmCat{A}$ as a reflective subcategory, and hence
    embed into $\RTCat{A}$ as well. For $K_1$, modest sets correspond to the separated
    subquotients of the natural-numbers object; the larger class of discrete objects need not be separated. The
    next subsection records how $\RTCat{A}$ itself is
    built.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The earlier categories embed cleanly: $\AsmCat{K_1} \hookrightarrow \EffCat$ as the $\neg\neg$-separated objects, and
    $\ModCat{K_1} \hookrightarrow \AsmCat{K_1} \hookrightarrow \EffCat$ as the separated discrete objects. The
    canonical monomorphism
    from each assembly into the constant object on its underlying set is $\neg\neg$-dense.
-/
theorem separated_in_essentialImage (X : RealizerPER.{r,u} K) (hX : X.Separated) :
    (Assembly.realizerEmbedding (K := K)).essImage X :=
  ⟨X.componentAssembly,⟨(X.componentIso hX).symm⟩⟩

end PolishSpaceBook.PCARealizability.RealizerPER
