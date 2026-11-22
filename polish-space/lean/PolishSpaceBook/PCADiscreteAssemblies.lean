module

public import PolishSpaceBook.PCASeparatedAssemblies
public import PolishSpaceBook.PCARealizabilitySubobjects
public import PolishSpaceBook.ModestAssemblies

@[expose] public section

/-! # Shared names and modest presentations

The uniform shared-name criterion is invariant under isomorphism and inherited
by categorical subobjects. For separated PERs it characterizes presentations by
modest assemblies. Its identification with subquotients of the natural-numbers
object in the numerical model is a separate categorical step.
-/
namespace PolishSpaceBook.PCARealizability.RealizerPER
open CategoryTheory
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}

/-- One program converts a shared extent name into equality evidence. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    **Shared names and modest presentations.** For an arbitrary PCA $A$, consider the following condition
    on a realizer-valued PER $X$ with equality $\rho$ and extent $E$:
    $$E(x)\cap E(y)\le\rho(x,y)\qquad\text{uniformly in }x,y.$$
    Here the left side is the ordinary intersection of two subsets of $A$. Thus one tracker $d$ must
    satisfy $da\downarrow\in\rho(x,y)$ whenever the same $a$ belongs to both extents. Supplying two possibly
    different names, as in $E(x)\land E(y)$, would be a different and much stronger condition.
-/
def UniformDiscrete (X : RealizerPER.{r,u} K) : Prop :=
  K.Entails (fun p : X.Carrier × X.Carrier => X.extent p.1 ∩ X.extent p.2)
    (fun p => X.rel p.1 p.2)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    \begin{proof}
    For an embedded assembly, a realizer of equality forces its two arguments to be equal. Hence the
    shared-name condition implies modesty. Conversely, modesty makes the arguments equal whenever they
    share a name; that same name then realizes their equality. The identity combinator tracks this direction.
-/
theorem assembly_uniformDiscrete_iff_modest (A : Assembly.{r,u} K) :
    A.toRealizerPER.UniformDiscrete ↔ A.Modest := by
  constructor
  · rintro ⟨d,hd⟩ a x y hx hy
    obtain ⟨b,_,hb⟩ := hd (x,y) a ⟨⟨rfl,hx⟩,⟨rfl,hy⟩⟩
    exact hb.1
  · intro hA
    apply reduces_of_subset
    intro p a ha
    exact ⟨hA a ha.1.2 ha.2.2,ha.1.2⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Now suppose $X$ is separated and satisfies the condition. In its reconstructed assembly on
    $Q=\SetQuotient{S}{\approx}$, a common name of two classes names representatives $x,y$ of those classes.
    Applying $d$ gives a realizer in $\rho(x,y)$, so $x\approx y$ and the classes coincide. Thus the
    reconstructed assembly is modest, and the previously constructed name-preserving isomorphism gives
    the required presentation. Conversely, an embedded modest assembly satisfies the condition by the
    first paragraph, and the condition transports along any isomorphism.
    \end{proof}
-/
theorem componentAssembly_modest (X : RealizerPER.{r,u} K) (hX : X.UniformDiscrete) :
    X.componentAssembly.Modest := by
  rintro a q q' ⟨x,hx,ha⟩ ⟨y,hy,hb⟩
  obtain ⟨d,hd⟩ := hX
  obtain ⟨b,_,he⟩ := hd (x.val,y.val) a ⟨ha,hb⟩
  exact hx.symm.trans (((X.component_eq_iff x y).mpr ⟨b,he⟩).trans hy)

/-- A single-valued partial application retains intersections under the same tracker. -/
theorem entails_intersection {I J : Type*} {φ ψ : I → Set R} (h : K.Entails φ ψ)
    (f g : J → I) :
    K.Entails (fun j => φ (f j) ∩ φ (g j)) (fun j => ψ (f j) ∩ ψ (g j)) := by
  obtain ⟨t,ht⟩ := h
  refine ⟨t,fun j a ha => ?_⟩
  obtain ⟨b,hb,hbf⟩ := ht (f j) a ha.1
  obtain ⟨c,hc,hcg⟩ := ht (g j) a ha.2
  have e : b = c := Part.some_injective (hb.symm.trans hc)
  exact ⟨b,hb,hbf,e ▸ hcg⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Given $a\in E_X(x)\cap E_X(x')$, totality gives the same value $u:=ta$ in both $F(x,y)$ and
    $F(x',y')$ for some $y,y'$. Application is single-valued, so $v:=su$ belongs to both target extents.
    Put
    $$w:=dv,\qquad z:=e\PCAPair{\PCAPair{lu}{u}}{w}.$$
    Then $w\in\rho_Y(y,y')$, $z\in F(x,y')$, and $j\PCAPair{z}{u}\in\rho_X(x,x')$.
    Abstracting this fixed composite over $a$ gives the required tracker. The points $y,y'$ witness
    membership in unions; the computation does not select them. Applying this argument to an isomorphism
    and its inverse proves invariance under isomorphism.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    To prove inheritance by subobjects, let a functional relation $F:X\to Y$ represent a monomorphism,
    and suppose $Y$ has tracker $d$ for the condition. Let $t$ track totality of $F$, and let $l,s$ extract
    source and target extents from an $F$-realizer. Let $e$ track extensionality of $F$. Finally, the uniform
    injectivity criterion for monomorphisms in §{sec:effective-topos-subobjects-truth-values} supplies a tracker
    $j$ taking two $F$-realizers with a common target to a source-equality realizer. These constructions use
    only the PCA operations, so the same criterion applies here.
-/
theorem uniformDiscrete_of_mono {X Y : RealizerPER.{r,u} K}
    (F : FunctionalRelation X Y) [Mono (C := RealizerPER K) F.toHom]
    (hY : Y.UniformDiscrete) : X.UniformDiscrete := by
  have ht := entails_intersection F.total Prod.fst Prod.snd
  apply K.entails_trans ht
  let Θ : (X.Carrier × X.Carrier) × (Y.Carrier × Y.Carrier) → Set R :=
    fun p => F.val p.1.1 p.2.1 ∩ F.val p.1.2 p.2.2
  apply reduces_cover (θ := Θ) ?_
  · let f : ((X.Carrier × X.Carrier) × (Y.Carrier × Y.Carrier)) → X.Carrier × Y.Carrier :=
      fun p => (p.1.1,p.2.1)
    let g : ((X.Carrier × X.Carrier) × (Y.Carrier × Y.Carrier)) → X.Carrier × Y.Carrier :=
      fun p => (p.1.2,p.2.2)
    have hs := entails_intersection (K.entails_trans F.strict (K.and_right _ _)) f g
    have he : K.Entails Θ (fun p => Y.rel p.2.1 p.2.2) :=
      K.entails_trans hs (K.reindex_entails (fun p : (X.Carrier × X.Carrier) × (Y.Carrier × Y.Carrier) => p.2) hY)
    have h₁ : K.Entails Θ (fun p => F.val p.1.1 p.2.1) :=
      reduces_of_subset fun _ _ h => h.1
    have h₂ : K.Entails Θ (fun p => F.val p.1.2 p.2.2) :=
      reduces_of_subset fun _ _ h => h.2
    exact K.entails_trans (K.and_intro (F.ext_of (F.strict_left_of h₁) h₁ he) h₂)
      (K.reindex_entails (fun p : (X.Carrier × X.Carrier) × (Y.Carrier × Y.Carrier) => (p.1.1,p.1.2,p.2.2))
        (FunctionalRelation.injective_of_mono F))
  · rintro p a ⟨⟨y,hy⟩,⟨y',hy'⟩⟩
    exact ⟨(y,y'),hy,hy'⟩

theorem uniformDiscrete_of_mono_hom {X Y : RealizerPER.{r,u} K}
    (f : X ⟶ Y) [hf : Mono f] (hY : Y.UniformDiscrete) : X.UniformDiscrete := by
  revert hf
  induction f using Quotient.inductionOn with
  | h F =>
    intro hF
    let : Mono (C := RealizerPER K) F.toHom := hF
    exact uniformDiscrete_of_mono F hY

theorem uniformDiscrete_iso_iff {X Y : RealizerPER.{r,u} K} (e : X ≅ Y) :
    X.UniformDiscrete ↔ Y.UniformDiscrete :=
  ⟨fun h => uniformDiscrete_of_mono_hom e.inv h,
    fun h => uniformDiscrete_of_mono_hom e.hom h⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Shared-name criterion
-/
theorem separated_uniformDiscrete_iff_modest (X : RealizerPER.{r,u} K) (hX : X.Separated) :
    X.UniformDiscrete ↔ ∃ A : Assembly.{r,u} K, A.Modest ∧ Nonempty (X ≅ A.toRealizerPER) := by
  constructor
  · intro h
    exact ⟨X.componentAssembly,X.componentAssembly_modest h,⟨X.componentIso hX⟩⟩
  · rintro ⟨A,hA,⟨e⟩⟩
    exact (uniformDiscrete_iso_iff e).mpr ((assembly_uniformDiscrete_iff_modest A).mpr hA)

end PolishSpaceBook.PCARealizability.RealizerPER
