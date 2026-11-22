module

public import PolishSpaceBook.LambdaRealizabilityExponentials
public import Mathlib.CategoryTheory.Functor.FullyFaithful

@[expose] public section

/-! # Assemblies and their fully faithful embedding into realizability PERs

Trackers use the concrete numerical lambda application graph. Every element of an
assembly has a realizer; choosing underlying elements never supplies a program
with a semantic representative as an extra input.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open CategoryTheory RealizerPER
universe u

/-- An assembly is covered by its natural-number realizers. -/
structure Assembly where
  Carrier : Type u
  realizes : Carrier → Set ℕ
  inhabited : ∀ x, (realizes x).Nonempty

namespace Assembly

/-- Morphisms are functions with a single uniform tracker, not functions equipped with a chosen index. -/
structure Hom (A B : Assembly.{u}) where
  toFun : A.Carrier → B.Carrier
  tracked : Reduces A.realizes (fun x => B.realizes (toFun x))

@[ext] theorem Hom.ext {A B : Assembly.{u}} {f g : Hom A B} (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

def Hom.id (A : Assembly.{u}) : Hom A A := ⟨fun x => x, reduces_refl _⟩

def Hom.comp {A B C : Assembly.{u}} (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨g.toFun ∘ f.toFun, reduces_trans f.tracked (reindex_reduces f.toFun g.tracked)⟩

instance assemblyCategory : Category Assembly.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext (fun _ => rfl)
  comp_id _ := Hom.ext (fun _ => rfl)
  assoc _ _ _ := Hom.ext (fun _ => rfl)

/-- The diagonal equality retains the realizers of its source element. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    The identity operation tracks symmetry, and the first projection from $\NatPair{e}{e'}$ tracks transitivity.
    Thus this is a realizer-valued PER. The passage to morphisms requires the following additional argument.
-/
def toPER (A : Assembly.{u}) : RealizerPER.{u} where
  Carrier := A.Carrier
  rel x y := {a | x = y ∧ a ∈ A.realizes x}
  symmetry := reduces_of_subset fun p _ h => by
    rcases h with ⟨hxy,ha⟩
    exact ⟨hxy.symm,hxy ▸ ha⟩
  transitivity := by
    let φ : A.Carrier × A.Carrier × A.Carrier → Set ℕ := fun p => {a | p.1 = p.2.2 ∧ a ∈ A.realizes p.1}
    let ψ : A.Carrier × A.Carrier × A.Carrier → Set ℕ := fun p => {a | p.2.1 = p.2.2 ∧ a ∈ A.realizes p.2.1}
    apply reduces_trans (ψ := realizabilityAnd φ ψ)
    · exact reduces_of_subset fun p _ h => ⟨⟨h.1.1.trans h.2.1,h.1.2⟩,h.2⟩
    · exact reduces_and_left _ _

@[simp] theorem extent_toPER (A : Assembly.{u}) (x : A.Carrier) : A.toPER.extent x = A.realizes x := by
  ext a
  simp [RealizerPER.extent,toPER]

/-- A tracker for the underlying function also tracks the diagonal equality. -/
def Hom.toPERMap {A B : Assembly.{u}} (f : Hom A B) : Map A.toPER B.toPER where
  toFun := f.toFun
  preserves := by
    obtain ⟨e,he⟩ := (reduces_iff _ _).mp f.tracked
    apply (reduces_iff _ _).mpr
    refine ⟨e, fun p a ha => ?_⟩
    obtain ⟨b,hb,hbB⟩ := he p.1 a ha.2
    exact ⟨b,hb,congrArg f.toFun ha.1,hbB⟩

/-- The graph construction keeps both the input extent and output equality. -/
def Hom.toRelation {A B : Assembly.{u}} (f : Hom A B) : FunctionalRelation A.toPER B.toPER :=
  f.toPERMap.graph

theorem Hom.toRelation_id (A : Assembly.{u}) :
    (Hom.id A).toRelation.Equivalent (FunctionalRelation.identity A.toPER) := by
  apply FunctionalRelation.equivalent_of_le
  exact reduces_and_right _ _

theorem Hom.toRelation_comp {A B C : Assembly.{u}} (f : Hom A B) (g : Hom B C) :
    (f.toRelation.comp g.toRelation).Equivalent (Hom.comp f g).toRelation := by
  apply FunctionalRelation.equivalent_of_le
  let Γ : (A.Carrier × C.Carrier) × B.Carrier → Set ℕ :=
    realizabilityAnd (fun p => f.toRelation.val p.1.1 p.2) (fun p => g.toRelation.val p.2 p.1.2)
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  have hx : Reduces Γ (fun p => A.toPER.extent p.1.1) :=
    reduces_trans (reduces_and_left _ _) (reduces_and_left _ _)
  have he : Reduces Γ (fun p => B.toPER.rel (f.toFun p.1.1) p.2) :=
    reduces_trans (reduces_and_left _ _) (reduces_and_right _ _)
  have hg : Reduces Γ (fun p => C.toPER.rel (g.toFun p.2) p.1.2) :=
    reduces_trans (reduces_and_right _ _) (reduces_and_right _ _)
  exact reduces_and_intro hx (C.toPER.trans_of (g.toPERMap.map_of he) hg)

/-- The standard embedding sends tracked functions to their functional graphs. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    A tracker for $f$ also sends each realizer of $x\sim_A x'$ to one of $f(x)\sim_B f(x')$.
    The graph construction in §{sec:effective-topos-finite-limits} therefore gives a functional relation.
    For the identity, projecting the second entry sends $\Gamma_{\mathrm{id}}(x,y)$ into $x\sim_A y$.
    For composition, a realizer of the composite graphs contains realizers of $E_A(x)$, $f(x)\sim_B y$, and
    $g(y)\sim_C z$ for some $y$. Apply the equality tracker for $g$ to the middle component and then transitivity
    in $C$; pair the result with the input extent. This uniformly realizes $\Gamma_{g\circ f}(x,z)$.
    The one-inclusion criterion in §{sec:effective-topos-subobjects-truth-values} turns both inclusions into equivalences,
    proving the functor laws.
-/
def embedding : Assembly.{u} ⥤ RealizerPER.{u} where
  obj := toPER
  map f := f.toRelation.toHom
  map_id A := Quotient.sound (Hom.toRelation_id A)
  map_comp f g := Quotient.sound (Hom.toRelation_comp f g).symm

/-- The graph has a realizer precisely at the value of the underlying function. -/
theorem Hom.graph_nonempty_iff {A B : Assembly.{u}} (f : Hom A B) (x : A.Carrier) (y : B.Carrier) :
    (f.toRelation.val x y).Nonempty ↔ f.toFun x = y := by
  constructor
  · rintro ⟨a,ha⟩
    exact ha.2.1
  · rintro rfl
    obtain ⟨a,ha⟩ := A.inhabited x
    obtain ⟨e,he⟩ := (reduces_iff _ _).mp f.tracked
    obtain ⟨b,hb,hbB⟩ := he x a ha
    refine ⟨Nat.pair a b, ?_⟩
    simp only [Hom.toRelation,Map.graph,Hom.toPERMap,toPER,RealizerPER.extent,Set.mem_ofPred_eq,Nat.unpair_pair]
    exact ⟨⟨trivial,ha⟩,trivial,hbB⟩

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    For faithfulness, $\Gamma_f(x,y)$ is nonempty exactly when $y=f(x)$. The forward implication follows from the diagonal
    relation in $B$. For the reverse implication, choose a realizer of $x$ and apply a tracker for $f$; pair the input
    and output. Thus equivalent graph relations determine the same underlying function.
-/
instance embedding_faithful : embedding.{u}.Faithful where
  map_injective := by
    intro A B f g h
    apply Hom.ext
    intro x
    have heq := (FunctionalRelation.toHom_eq_iff f.toRelation g.toRelation).mp h
    obtain ⟨a,ha⟩ := (f.graph_nonempty_iff x (f.toFun x)).mpr rfl
    obtain ⟨e,he⟩ := (reduces_iff _ _).mp heq.1
    obtain ⟨b,_,hb⟩ := he (x,f.toFun x) a ha
    exact ((g.graph_nonempty_iff x (f.toFun x)).mp ⟨b,hb⟩).symm

/-- Totality and separated equality yield a unique underlying output element. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    For fullness, let $F:A\to B$ be any functional relation between the displayed PERs. Given $x$, choose an element of
    $E_A(x)$ and apply totality of $F$. This proves that $F(x,y)$ is nonempty for some $y$.
    Single-valuedness and the diagonal relation in $B$ make this $y$ unique; define $f(x)=y$.
    If $u_F$ tracks totality and $r_F$ extracts the output extent from strictness, then
    $$a\longmapsto r_F(u_F(a))$$
    tracks $f$. Indeed, $u_F(a)\in F(x,y)$ for some $y$, and uniqueness gives $y=f(x)$.
    The program computes a numerical realizer, not a representative $y$ of the underlying set.
    Finally, if $b\in F(x,y)$, uniqueness gives $y=f(x)$, and the two strictness projections produce
    $$\NatPair{\ell_F(b)}{r_F(b)}\in\Gamma_f(x,y).$$
    This is a uniform inclusion $F\le\Gamma_f$; the same one-inclusion criterion gives $F\equiv\Gamma_f$.
    Hence every arrow between embedded assemblies comes from an assembly morphism.
    \end{proof}
-/
theorem relation_value_existsUnique {A B : Assembly.{u}}
    (F : FunctionalRelation A.toPER B.toPER) (x : A.Carrier) :
    ∃! y, (F.val x y).Nonempty := by
  obtain ⟨a,ha⟩ := A.inhabited x
  obtain ⟨t,ht⟩ := (reduces_iff _ _).mp F.total
  obtain ⟨b,_,y,hy⟩ := ht x a (by simpa only [extent_toPER] using ha)
  refine ⟨y,⟨b,hy⟩,?_⟩
  rintro y' ⟨c,hc⟩
  obtain ⟨v,hv⟩ := (reduces_iff _ _).mp F.single
  obtain ⟨d,_,hd⟩ := hv (x,y',y) (Nat.pair c b) (by
    simpa only [realizabilityAnd,Set.mem_ofPred_eq,Nat.unpair_pair] using And.intro hc hy)
  exact hd.1

/-- This choice is an underlying set function, not a procedure for selecting representatives. -/
noncomputable def relationValue {A B : Assembly.{u}}
    (F : FunctionalRelation A.toPER B.toPER) (x : A.Carrier) : B.Carrier :=
  (relation_value_existsUnique F x).choose

theorem relationValue_spec {A B : Assembly.{u}}
    (F : FunctionalRelation A.toPER B.toPER) (x : A.Carrier) :
    (F.val x (relationValue F x)).Nonempty :=
  (relation_value_existsUnique F x).choose_spec.1

theorem value_eq_relationValue {A B : Assembly.{u}}
    (F : FunctionalRelation A.toPER B.toPER) {x : A.Carrier} {y : B.Carrier}
    (h : (F.val x y).Nonempty) : y = relationValue F x :=
  (relation_value_existsUnique F x).choose_spec.2 y h

/-- The output-extent tracker computes a realizer of the unique underlying value. -/
theorem relationValue_tracked {A B : Assembly.{u}}
    (F : FunctionalRelation A.toPER B.toPER) :
    Reduces A.realizes (fun x => B.realizes (relationValue F x)) := by
  have ht : Reduces A.realizes (fun x => {a | ∃ y, a ∈ F.val x y}) := by
    obtain ⟨t, ht⟩ := (reduces_iff _ _).mp F.total
    exact (reduces_iff _ _).mpr ⟨t, fun x a ha =>
      ht x a (by simpa only [extent_toPER] using ha)⟩
  apply reduces_trans ht
  let Γ : A.Carrier × B.Carrier → Set ℕ := fun p => F.val p.1 p.2
  apply reduces_cover (θ := Γ) (fun _ _ h => h)
  have hs : Reduces Γ (fun p => B.realizes p.2) := by
    simpa only [extent_toPER] using F.strict_right_of (reduces_refl Γ)
  obtain ⟨e,he⟩ := (reduces_iff _ _).mp hs
  apply (reduces_iff _ _).mpr
  refine ⟨e,fun p a ha => ?_⟩
  obtain ⟨b,hb,hbB⟩ := he p a ha
  exact ⟨b,hb,value_eq_relationValue F ⟨a,ha⟩ ▸ hbB⟩

/-- Recover the tracked underlying map without computing an underlying representative. -/
noncomputable def homOfRelation {A B : Assembly.{u}}
    (F : FunctionalRelation A.toPER B.toPER) : Hom A B :=
  ⟨relationValue F,relationValue_tracked F⟩

theorem homOfRelation_correct {A B : Assembly.{u}}
    (F : FunctionalRelation A.toPER B.toPER) : F.Equivalent (homOfRelation F).toRelation := by
  apply FunctionalRelation.equivalent_of_le
  let Γ : A.Carrier × B.Carrier → Set ℕ := fun p => F.val p.1 p.2
  have hs : Reduces Γ (fun p => B.realizes p.2) := by
    simpa only [extent_toPER] using F.strict_right_of (reduces_refl Γ)
  have hr : Reduces Γ (fun p => B.toPER.rel (relationValue F p.1) p.2) := by
    obtain ⟨e,he⟩ := (reduces_iff _ _).mp hs
    apply (reduces_iff _ _).mpr
    refine ⟨e,fun p a ha => ?_⟩
    obtain ⟨b,hb,hbB⟩ := he p a ha
    have hy := value_eq_relationValue F ⟨a,ha⟩
    exact ⟨b,hb,hy.symm,hy ▸ hbB⟩
  exact reduces_and_intro (F.strict_left_of (reduces_refl Γ)) hr

/-- Every arrow between embedded assemblies comes from a tracked function. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: theorem
  title: Fully faithful assembly embedding
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    In particular, this embeds \termforwardas{modest set}{modest} assemblies, in which each realizer realizes at most
    one element. We next construct the assembly associated with a represented space and the numerical tracker induced
    by a Type-Two realizer.
-/
instance embedding_full : embedding.{u}.Full where
  map_surjective := by
    intro A B h
    induction h using Quotient.inductionOn with
    | h F => exact ⟨homOfRelation F,Quotient.sound (homOfRelation_correct F).symm⟩

/-- Modesty means that no numerical realizer is shared by two distinct elements. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    In particular, this embeds \termforwardas{modest set}{modest} assemblies, in which each realizer realizes at most
    one element. We next construct the assembly associated with a represented space and the numerical tracker induced
    by a Type-Two realizer.
-/
def IsModest (A : Assembly.{u}) : Prop :=
  ∀ x y a, a ∈ A.realizes x → a ∈ A.realizes y → x = y

end Assembly
end PolishSpaceBook.LambdaIndexPCA
