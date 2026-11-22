module

public import PolishSpaceBook.PCADiscreteAssemblies
public import PolishSpaceBook.PCARealizabilityEpis

@[expose] public section

/-! # Shared-name discreteness as a categorical subquotient

The ambient assembly has one point for each PCA element and that element as its
only name. In the numerical model this is the singleton-name natural-number
presentation. Both monicity and epicity below are categorical properties.
-/
namespace PolishSpaceBook.PCARealizability
open CategoryTheory RealizerPER
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}

namespace FunctionalRelation

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Conversely, the shared-name condition holds for $\NameObject{A}$ by modesty and is inherited by its
    subobject $S$. Let $F:S\to X$ be epic. From a common name $a\in E_X(x)\cap E_X(x')$, the uniform image
    criterion produces the same value $b$ in $F(s,x)$ and $F(s',x')$ for some $s,s'$.
    Applying source strictness to $b$ gives a common extent name of $s,s'$. The condition on $S$ converts
    it into equality evidence for $s,s'$. Extensionality transports $F(s,x)$ to $F(s',x)$, and
    single-valuedness then gives equality evidence for $x,x'$. This composite is uniform in $a$.
-/
theorem uniformDiscrete_of_covers {X Y : RealizerPER.{r,u} K} (F : FunctionalRelation X Y)
    (hF : F.Covers) (hX : X.UniformDiscrete) : Y.UniformDiscrete := by
  have hc := RealizerPER.entails_intersection hF Prod.fst Prod.snd
  apply K.entails_trans hc
  let Θ : (Y.Carrier × Y.Carrier) × (X.Carrier × X.Carrier) → Set R :=
    fun p => F.val p.2.1 p.1.1 ∩ F.val p.2.2 p.1.2
  apply reduces_cover (θ := Θ)
  · rintro p a ⟨⟨x,hx⟩,⟨x',hx'⟩⟩
    exact ⟨(x,x'),hx,hx'⟩
  · have hs := RealizerPER.entails_intersection (K.entails_trans F.strict (K.and_left _ _))
      (fun p : (Y.Carrier × Y.Carrier) × (X.Carrier × X.Carrier) => (p.2.1,p.1.1))
      (fun p : (Y.Carrier × Y.Carrier) × (X.Carrier × X.Carrier) => (p.2.2,p.1.2))
    have he : K.Entails Θ (fun p => X.rel p.2.1 p.2.2) :=
      K.entails_trans hs (K.reindex_entails
        (fun p : (Y.Carrier × Y.Carrier) × (X.Carrier × X.Carrier) => p.2) hX)
    have h₁ : K.Entails Θ (fun p => F.val p.2.1 p.1.1) := reduces_of_subset fun _ _ h => h.1
    have h₂ : K.Entails Θ (fun p => F.val p.2.2 p.1.2) := reduces_of_subset fun _ _ h => h.2
    exact F.single_of (F.ext_of he h₁ (F.strict_right_of h₁)) h₂

/-- Equality of source representatives gives equality of any two related outputs. -/
theorem nonempty_map {X Y : RealizerPER.{r,u} K} (F : FunctionalRelation X Y)
    {x x' : X.Carrier} {y y' : Y.Carrier} (he : (X.rel x x').Nonempty)
    (hf : (F.val x y).Nonempty) (hf' : (F.val x' y').Nonempty) : (Y.rel y y').Nonempty := by
  obtain ⟨a,ha⟩ := he
  obtain ⟨b,hb⟩ := hf
  obtain ⟨c,hc⟩ := hf'
  obtain ⟨s,hs⟩ := F.strict
  obtain ⟨_,_,l,r,rfl,_,hr⟩ := hs (x,y) b hb
  obtain ⟨e,he⟩ := F.extensional
  obtain ⟨v,_,hv⟩ := he (x,x',y,y) (K.pair (K.pair a b) r) ⟨_,_,rfl,⟨_,_,rfl,ha,hb⟩,hr⟩
  obtain ⟨t,ht⟩ := F.single
  obtain ⟨w,_,hw⟩ := ht (x',y,y') (K.pair v c) ⟨_,_,rfl,hv,hc⟩
  exact ⟨w,hw⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Separation is also inherited by monomorphisms. Indeed, for a monomorphism $F:S\to Y$ with separated
    codomain, extent names for $s,s'$ give $F$-realizers at some $y,y'$ by totality. If $\rho_S(s,s')$ is
    inhabited, extensionality and single-valuedness make $\rho_Y(y,y')$ inhabited. Separation of $Y$
    converts the computed target extent names into target-equality evidence. Extensionality of $F$ and
    its uniform injectivity then yield source-equality evidence, uniformly in the original input.
    Thus an object isomorphic to an embedded assembly is separated. Together with the shared-name
    criterion for modest presentations, this proves both directions of the final assertion.
    \end{proof}
-/
theorem separated_of_mono {X Y : RealizerPER.{r,u} K} (F : FunctionalRelation X Y)
    [Mono (C := RealizerPER K) F.toHom] (hY : Y.Separated) : X.Separated := by
  unfold RealizerPER.Separated
  have h₁ := K.reindex_entails (fun p : X.Carrier × X.Carrier => p.1) F.total
  have h₂ := K.reindex_entails (fun p : X.Carrier × X.Carrier => p.2) F.total
  apply K.entails_trans (K.and_intro
    (K.and_intro
      (K.entails_trans (K.entails_trans (K.and_left _ _) (K.and_left _ _)) h₁)
      (K.entails_trans (K.entails_trans (K.and_left _ _) (K.and_right _ _)) h₂))
    (K.and_right _ _))
  let Θ : (X.Carrier × X.Carrier) × (Y.Carrier × Y.Carrier) → Set R :=
    K.predAnd (K.predAnd (fun p => F.val p.1.1 p.2.1) (fun p => F.val p.1.2 p.2.2))
      (K.predNeg (K.predNeg (fun p => X.rel p.1.1 p.1.2)))
  apply reduces_cover (θ := Θ)
  · rintro p _ ⟨ab,c,rfl,⟨a,b,rfl,⟨y,ha⟩,⟨y',hb⟩⟩,hc⟩
    exact ⟨(y,y'),K.pair a b,c,rfl,⟨a,b,rfl,ha,hb⟩,hc⟩
  · have hf₁ : K.Entails Θ (fun p => F.val p.1.1 p.2.1) :=
      K.entails_trans (K.and_left _ _) (K.and_left _ _)
    have hf₂ : K.Entails Θ (fun p => F.val p.1.2 p.2.2) :=
      K.entails_trans (K.and_left _ _) (K.and_right _ _)
    have he : K.Entails Θ (fun p => Y.rel p.2.1 p.2.2) := by
      apply Y.separated_of hY (F.strict_right_of hf₁) (F.strict_right_of hf₂)
      rintro p _ ⟨ab,c,rfl,⟨a,b,rfl,ha,hb⟩,hc⟩
      exact F.nonempty_map ((K.mem_doubleNeg_iff _ _ c).mp hc) ⟨a,ha⟩ ⟨b,hb⟩
    exact K.entails_trans (K.and_intro (F.ext_of (F.strict_left_of hf₁) hf₁ he) hf₂)
      (K.reindex_entails (fun p : (X.Carrier × X.Carrier) × (Y.Carrier × Y.Carrier) =>
        (p.1.1,p.1.2,p.2.2)) F.injective_of_mono)

end FunctionalRelation

theorem RealizerPER.separated_of_mono_hom {X Y : RealizerPER.{r,u} K}
    (f : X ⟶ Y) [hf : Mono f] (hY : Y.Separated) : X.Separated := by
  revert hf
  induction f using Quotient.inductionOn with
  | h F =>
    intro hF
    let : Mono (C := RealizerPER K) F.toHom := hF
    exact F.separated_of_mono hY

/-- The assembly embedding preserves monomorphisms, even for tests from arbitrary PERs. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    \begin{proof}
    Suppose $d$ witnesses the shared-name condition for $X$. Put
    $$S:=\{a\in A:\exists x\;a\in E_X(x)\}$$
    and give each $a\in S$ only the name $a$. The inclusion $S\hookrightarrow A$ is tracked by the identity.
    Its graph is a monomorphism even when tested by arrows from arbitrary realizer-valued PERs: equality
    after composition with this graph gives a uniform transformation between the original relation
    realizers, because equality of the included values forces equality of their preimages. First projection
    extracts the original relation realizer. Thus this is a subobject of $\NameObject{A}$.
-/
theorem assembly_graph_mono {A B : Assembly.{r,u} K} (f : Assembly.Hom A B)
    (hf : Function.Injective f.toFun) :
    Mono (C := RealizerPER K) f.toFunctionalRelation.toHom where
  right_cancellation {Z} g h := by
    refine Quotient.inductionOn₂ g h fun G H he => ?_
    have hcomp := ((FunctionalRelation.toHom_eq_iff _ _).mp he).1
    apply Quotient.sound
    apply FunctionalRelation.equivalent_of_le
    have hG : K.Entails (fun p : Z.Carrier × A.Carrier => G.val p.1 p.2)
        (fun p => f.toFunctionalRelation.val p.2 (f.toFun p.2)) :=
      K.and_intro (G.strict_right_of (K.entails_refl _))
        (f.toRealizerPERMap.map_of (G.strict_right_of (K.entails_refl _)))
    have hGF := relationComp_intro (K.entails_refl _) hG
    have hHF := K.entails_trans hGF (K.reindex_entails (fun p : Z.Carrier × A.Carrier => (p.1,f.toFun p.2)) hcomp)
    apply K.entails_trans hHF
    apply reduces_cover
      (θ := K.predAnd (fun p : (Z.Carrier × A.Carrier) × A.Carrier => H.val p.1.1 p.2)
        (fun p => f.toFunctionalRelation.val p.2 (f.toFun p.1.2))) (fun _ _ h => h)
    refine ⟨K.firstProjection,?_⟩
    rintro p _ ⟨a,b,rfl,ha,⟨c,d,rfl,_,hd⟩⟩
    refine ⟨a,K.application_firstProjection a (K.pair c d),?_⟩
    change a ∈ H.val p.1.1 p.1.2
    rw [← hf hd.1]
    exact ha

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{NameObject}
    \end{mathmeta}
    Let $\NameObject{A}$ be the embedded assembly with underlying set $A$ and realizability relation
    $$a\Vdash_{\NameObject{A}} b\quad\Longleftrightarrow\quad a=b.$$
    A subquotient of this object means an object $X$ admitting a diagram
    $$\NameObject{A}\xleftarrow{\ m\ }S\xrightarrow{\ q\ }X,$$
    where $m$ is a monomorphism and $q$ is an epimorphism in $\RTCat{A}$.
-/
def nameAssembly (K : PartialCombinatoryAlgebra R) : Assembly.{r,max r u} K where
  Carrier := ULift.{u} R
  realizes a n := a = n.down
  inhabited n := ⟨n.down,rfl⟩

theorem nameAssembly_modest : (nameAssembly.{r,u} K).Modest := by
  intro a x y hx hy
  exact ULift.ext (hx.symm.trans hy)

def supportedNames (X : RealizerPER.{r,max r u} K) : Assembly.{r,max r u} K where
  Carrier := {n : ULift.{u} R // ∃ x, n.down ∈ X.extent x}
  realizes a n := a = n.val.down
  inhabited n := ⟨n.val.down,rfl⟩

def nameInclusion (X : RealizerPER.{r,max r u} K) :
    Assembly.Hom (supportedNames X) (nameAssembly.{r,u} K) where
  toFun := Subtype.val
  tracked := ⟨K.identity,fun _ a ha => ⟨a,K.application_identity a,ha⟩⟩

instance nameInclusion_mono (X : RealizerPER.{r,max r u} K) :
    Mono (C := RealizerPER K) (nameInclusion X).toFunctionalRelation.toHom :=
  assembly_graph_mono _ Subtype.val_injective

/-- A representative is chosen in the ambient mathematics, never by the tracker. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For each $a\in S$, choose an underlying representative $x_a$ with $a\in E_X(x_a)$.
    The function $a\mapsto x_a$ preserves equality, tracked by the identity: a source-equality name is
    $a$ itself, which realizes $\rho_X(x_a,x_a)$. Its graph $F:S\to X$ is therefore functional.
    Given any $a\in E_X(x)$, the chosen representative $x_a$ and $x$ share the name $a$, so
    $$a\longmapsto\PCAPair{a}{da}\in F(a,x)$$
    provides uniform image coverage. The preceding proposition makes $F$ epic. The choice of $x_a$ is made
    only in the underlying mathematics: this tracker uses $a,d$ and never computes $x_a$.
-/
noncomputable def nameQuotient (X : RealizerPER.{r,max r u} K) :
    Map (supportedNames X).toRealizerPER X where
  toFun n := Classical.choose n.property
  preserves := by
    apply reduces_of_subset
    rintro ⟨n,m⟩ a ⟨e,ha⟩
    change n = m at e
    subst m
    change a = n.val.down at ha
    exact ha ▸ Classical.choose_spec n.property

theorem nameQuotient_covers (X : RealizerPER.{r,max r u} K) (hX : X.UniformDiscrete) :
    (nameQuotient X).graph.Covers := by
  obtain ⟨d,hd⟩ := hX
  refine ⟨K.paired K.identity d,fun x a ha => ?_⟩
  let n : (supportedNames X).Carrier := ⟨⟨a⟩,x,ha⟩
  have hn : a ∈ X.extent ((nameQuotient X).toFun n) := Classical.choose_spec n.property
  obtain ⟨b,hb,he⟩ := hd ((nameQuotient X).toFun n,x) a ⟨hn,ha⟩
  exact ⟨K.pair a b,K.application_paired (K.application_identity a) hb,n,a,b,rfl,⟨rfl,rfl⟩,he⟩

/-- A subquotient is given by an actual mono and epi with a common domain. -/
def IsNameSubquotient (X : RealizerPER.{r,max r u} K) : Prop :=
  ∃ S : RealizerPER.{r,max r u} K, ∃ m : S ⟶ (nameAssembly.{r,u} K).toRealizerPER,
    ∃ q : S ⟶ X, Mono m ∧ Epi q

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Subquotient criterion
-/
theorem uniformDiscrete_iff_nameSubquotient (X : RealizerPER.{r,max r u} K) :
    X.UniformDiscrete ↔ IsNameSubquotient X := by
  constructor
  · intro hX
    exact ⟨(supportedNames X).toRealizerPER,(nameInclusion X).toFunctionalRelation.toHom,
      (nameQuotient X).graph.toHom,inferInstance,
      FunctionalRelation.epi_of_covers _ (nameQuotient_covers X hX)⟩
  · rintro ⟨S,m,q,hm,hq⟩
    have hs : S.UniformDiscrete :=
      @RealizerPER.uniformDiscrete_of_mono_hom _ _ _ _ m hm
        ((RealizerPER.assembly_uniformDiscrete_iff_modest _).mpr nameAssembly_modest)
    revert hq
    induction q using Quotient.inductionOn with
    | h Q =>
      intro hQ
      let : Epi (C := RealizerPER K) Q.toHom := hQ
      exact Q.uniformDiscrete_of_covers Q.covers_of_epi hs

theorem separated_nameSubquotient_iff_modest (X : RealizerPER.{r,max r u} K) (hX : X.Separated) :
    IsNameSubquotient X ↔
      ∃ A : Assembly.{r,max r u} K, A.Modest ∧ Nonempty (X ≅ A.toRealizerPER) :=
  (uniformDiscrete_iff_nameSubquotient X).symm.trans (X.separated_uniformDiscrete_iff_modest hX)

/-- In the numerical lambda-index PCA, the ambient points and singleton names are natural numbers. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    For $A=K_1$, the assembly $\NameObject{K_1}$ has underlying set $\NN$ with $E(n)=\{n\}$.
    This is the standard presentation of the natural-numbers object of $\EffCat$ [@vanOosten2008].
    An object of $\EffCat$ is called \termdefineas{discrete object in the effective topos}{discrete} if it is
    a subquotient of this object. The proposition therefore identifies the separated discrete objects
    with the essential image of $\ModCat{K_1}$; here discrete is a categorical condition, not a topology
    on the underlying representatives.
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
theorem separated_numerical_subquotient_iff_modest
    (X : RealizerPER.{0,u} LambdaIndexPCA.indexPCA) (hX : X.Separated) :
    IsNameSubquotient X ↔ ∃ A : Assembly.{0,u} LambdaIndexPCA.indexPCA,
      A.Modest ∧ Nonempty (X ≅ A.toRealizerPER) :=
  separated_nameSubquotient_iff_modest X hX

/-- Both conditions hold on every object isomorphic to a modest assembly. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Subquotient criterion
-/
theorem separated_and_nameSubquotient_iff_modest (X : RealizerPER.{r,max r u} K) :
    (X.Separated ∧ IsNameSubquotient X) ↔
      ∃ A : Assembly.{r,max r u} K, A.Modest ∧ Nonempty (X ≅ A.toRealizerPER) := by
  constructor
  · rintro ⟨hs,hd⟩
    exact (separated_nameSubquotient_iff_modest X hs).mp hd
  · rintro ⟨A,hA,⟨e⟩⟩
    have hs := RealizerPER.separated_of_mono_hom e.hom (RealizerPER.assembly_separated A)
    exact ⟨hs,(separated_nameSubquotient_iff_modest X hs).mpr ⟨A,hA,⟨e⟩⟩⟩

end PolishSpaceBook.PCARealizability
