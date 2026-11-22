module

public import PolishSpaceBook.PCARealizabilityPER
public import PolishSpaceBook.AssemblyDoubleNegation
public import Mathlib.CategoryTheory.Functor.FullyFaithful

@[expose] public section

/-! # The general PCA assembly embedding

Functional graphs preserve names and recover the unique underlying function
using totality. Trackers receive only realizers, never underlying elements.
-/
namespace PolishSpaceBook.Assembly
open CategoryTheory PCARealizability PCARealizability.RealizerPER
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}

def toRealizerPER (A : Assembly.{r,u} K) : RealizerPER.{r,u} K where
  Carrier := A.Carrier
  rel x y := {a | x = y ∧ a ∈ (existence A) x}
  symmetry := reduces_of_subset fun p _ h => by
    rcases h with ⟨hxy,ha⟩
    exact ⟨hxy.symm,hxy ▸ ha⟩
  transitivity := by
    refine ⟨K.firstProjection,?_⟩
    rintro p _ ⟨a,b,rfl,ha,hb⟩
    exact ⟨a,K.application_firstProjection a b,ha.1.trans hb.1,ha.2⟩

@[simp] theorem extent_toRealizerPER (A : Assembly.{r,u} K) (x : A.Carrier) : A.toRealizerPER.extent x = (existence A) x := by
  ext a
  simp [RealizerPER.extent,toRealizerPER]

/-- A tracker for the underlying function also tracks the diagonal equality. -/
def Hom.toRealizerPERMap {A B : Assembly.{r,u} K} (f : Hom A B) : Map A.toRealizerPER B.toRealizerPER where
  toFun := f.toFun
  preserves := by
    obtain ⟨e,he⟩ := f.tracked
    refine ⟨e, fun p a ha => ?_⟩
    obtain ⟨b,hb,hbB⟩ := he p.1 a ha.2
    exact ⟨b,hb,congrArg f.toFun ha.1,hbB⟩

/-- The graph construction keeps both the input extent and output equality. -/
def Hom.toFunctionalRelation {A B : Assembly.{r,u} K} (f : Hom A B) : FunctionalRelation A.toRealizerPER B.toRealizerPER :=
  f.toRealizerPERMap.graph

theorem Hom.toFunctionalRelation_id (A : Assembly.{r,u} K) :
    (Hom.id A).toFunctionalRelation.Equivalent (FunctionalRelation.identity A.toRealizerPER) := by
  apply FunctionalRelation.equivalent_of_le
  exact K.and_right _ _

theorem Hom.toFunctionalRelation_comp {A B C : Assembly.{r,u} K} (f : Hom A B) (g : Hom B C) :
    (f.toFunctionalRelation.comp g.toFunctionalRelation).Equivalent (Hom.comp f g).toFunctionalRelation := by
  apply FunctionalRelation.equivalent_of_le
  let Γ : (A.Carrier × C.Carrier) × B.Carrier → Set R :=
    K.predAnd (fun p => f.toFunctionalRelation.val p.1.1 p.2) (fun p => g.toFunctionalRelation.val p.2 p.1.2)
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  have hx : K.Entails Γ (fun p => A.toRealizerPER.extent p.1.1) :=
    K.entails_trans (K.and_left _ _) (K.and_left _ _)
  have he : K.Entails Γ (fun p => B.toRealizerPER.rel (f.toFun p.1.1) p.2) :=
    K.entails_trans (K.and_left _ _) (K.and_right _ _)
  have hg : K.Entails Γ (fun p => C.toRealizerPER.rel (g.toFun p.2) p.1.2) :=
    K.entails_trans (K.and_right _ _) (K.and_right _ _)
  exact K.and_intro hx (C.toRealizerPER.trans_of (g.toRealizerPERMap.map_of he) hg)

/-- The standard embedding sends tracked functions to their functional graphs. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For the embedding, repeat the graph argument of §{sec:tte-domains-eff-subcategories} with PCA names.
    A tracker $r$ of $f:X\to Y$ gives totality of its graph by
    $a\mapsto\PCAPair{a}{ra}$. The identity and composition laws use projections, equality preservation,
    and transitivity; the one-inclusion criterion turns the resulting inclusions into equivalences.
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
def realizerEmbedding : Assembly.{r,u} K ⥤ RealizerPER.{r,u} K where
  obj := toRealizerPER
  map f := f.toFunctionalRelation.toHom
  map_id A := Quotient.sound (Hom.toFunctionalRelation_id A)
  map_comp f g := Quotient.sound (Hom.toFunctionalRelation_comp f g).symm

/-- The graph has a realizer precisely at the value of the underlying function. -/
theorem Hom.graph_nonempty_iff {A B : Assembly.{r,u} K} (f : Hom A B) (x : A.Carrier) (y : B.Carrier) :
    (f.toFunctionalRelation.val x y).Nonempty ↔ f.toFun x = y := by
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨b,c,_,_,hc⟩ := ha
    exact hc.1
  · rintro rfl
    obtain ⟨a,ha⟩ := A.inhabited x
    obtain ⟨e,he⟩ := f.tracked
    obtain ⟨b,hb,hbB⟩ := he x a ha
    exact ⟨K.pair a b,a,b,rfl,⟨rfl,ha⟩,rfl,hbB⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: theorem
  title: Assembly reconstruction of separated PERs
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    A graph is inhabited precisely at $y=f(x)$, proving faithfulness.
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
instance realizerEmbedding_faithful : (realizerEmbedding (K := K)).Faithful where
  map_injective := by
    intro A B f g h
    apply Hom.ext
    intro x
    have heq := (FunctionalRelation.toHom_eq_iff f.toFunctionalRelation g.toFunctionalRelation).mp h
    obtain ⟨a,ha⟩ := (f.graph_nonempty_iff x (f.toFun x)).mpr rfl
    obtain ⟨e,he⟩ := heq.1
    obtain ⟨b,_,hb⟩ := he (x,f.toFun x) a ha
    exact ((g.graph_nonempty_iff x (f.toFun x)).mp ⟨b,hb⟩).symm

/-- Totality and separated equality yield a unique underlying output element. -/
theorem relation_value_existsUnique {A B : Assembly.{r,u} K}
    (F : FunctionalRelation A.toRealizerPER B.toRealizerPER) (x : A.Carrier) :
    ∃! y, (F.val x y).Nonempty := by
  obtain ⟨a,ha⟩ := A.inhabited x
  obtain ⟨t,ht⟩ := F.total
  obtain ⟨b,_,y,hy⟩ := ht x a (by simpa only [extent_toRealizerPER,existence,Set.mem_ofPred_eq] using ha)
  refine ⟨y,⟨b,hy⟩,?_⟩
  rintro y' ⟨c,hc⟩
  obtain ⟨v,hv⟩ := F.single
  obtain ⟨d,_,hd⟩ := hv (x,y',y) (K.pair c b) ⟨c,b,rfl,hc,hy⟩
  exact hd.1

/-- This choice is an underlying set function, not a procedure for selecting representatives. -/
noncomputable def relationValue {A B : Assembly.{r,u} K}
    (F : FunctionalRelation A.toRealizerPER B.toRealizerPER) (x : A.Carrier) : B.Carrier :=
  (relation_value_existsUnique F x).choose

theorem relationValue_spec {A B : Assembly.{r,u} K}
    (F : FunctionalRelation A.toRealizerPER B.toRealizerPER) (x : A.Carrier) :
    (F.val x (relationValue F x)).Nonempty :=
  (relation_value_existsUnique F x).choose_spec.1

theorem value_eq_relationValue {A B : Assembly.{r,u} K}
    (F : FunctionalRelation A.toRealizerPER B.toRealizerPER) {x : A.Carrier} {y : B.Carrier}
    (h : (F.val x y).Nonempty) : y = relationValue F x :=
  (relation_value_existsUnique F x).choose_spec.2 y h

/-- The output-extent tracker computes a realizer of the unique underlying value. -/
theorem relationValue_tracked {A B : Assembly.{r,u} K}
    (F : FunctionalRelation A.toRealizerPER B.toRealizerPER) :
    K.Entails (existence A) (fun x => (existence B) (relationValue F x)) := by
  have ht : K.Entails (existence A) (fun x => {a | ∃ y, a ∈ F.val x y}) := by
    obtain ⟨t, ht⟩ := F.total
    exact ⟨t, fun x a ha =>
      ht x a (by simpa only [extent_toRealizerPER,existence,Set.mem_ofPred_eq] using ha)⟩
  apply K.entails_trans ht
  let Γ : A.Carrier × B.Carrier → Set R := fun p => F.val p.1 p.2
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  have hs : K.Entails Γ (fun p => (existence B) p.2) := by
    simpa only [extent_toRealizerPER] using F.strict_right_of (K.entails_refl Γ)
  obtain ⟨e,he⟩ := hs
  refine ⟨e,fun p a ha => ?_⟩
  obtain ⟨b,hb,hbB⟩ := he p a ha
  refine ⟨b,hb,?_⟩
  change b ∈ existence B (relationValue F p.1)
  rw [← value_eq_relationValue F ⟨a,ha⟩]
  exact hbB

/-- Recover the tracked underlying map without computing an underlying representative. -/
noncomputable def homOfRelation {A B : Assembly.{r,u} K}
    (F : FunctionalRelation A.toRealizerPER B.toRealizerPER) : Hom A B :=
  ⟨relationValue F,relationValue_tracked F⟩

theorem homOfRelation_correct {A B : Assembly.{r,u} K}
    (F : FunctionalRelation A.toRealizerPER B.toRealizerPER) : F.Equivalent (homOfRelation F).toFunctionalRelation := by
  apply FunctionalRelation.equivalent_of_le
  let Γ : A.Carrier × B.Carrier → Set R := fun p => F.val p.1 p.2
  have hs : K.Entails Γ (fun p => (existence B) p.2) := by
    simpa only [extent_toRealizerPER] using F.strict_right_of (K.entails_refl Γ)
  have hr : K.Entails Γ (fun p => B.toRealizerPER.rel (relationValue F p.1) p.2) := by
    obtain ⟨e,he⟩ := hs
    refine ⟨e,fun p a ha => ?_⟩
    obtain ⟨b,hb,hbB⟩ := he p a ha
    have hy := value_eq_relationValue F ⟨a,ha⟩
    exact ⟨b,hb,hy.symm,hy ▸ hbB⟩
  exact K.and_intro (F.strict_left_of (K.entails_refl Γ)) hr

/-- Every arrow between embedded assemblies comes from a tracked function. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: theorem
  title: Assembly reconstruction of separated PERs
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For fullness, totality and
    single-valuedness of a functional relation determine a unique underlying value at each element.
    If $u$ tracks totality and $v$ extracts the output extent, then
    $\PCAAbstract{a}{v(ua)}$ tracks this function. Strictness gives a uniform inclusion of the original
    relation into its graph, hence their equivalence. This uses the same argument over arbitrary names,
    without computing underlying elements.
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
instance realizerEmbedding_full : (realizerEmbedding (K := K)).Full where
  map_surjective := by
    intro A B h
    induction h using Quotient.inductionOn with
    | h F => exact ⟨homOfRelation F,Quotient.sound (homOfRelation_correct F).symm⟩

end PolishSpaceBook.Assembly
