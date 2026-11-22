module

public import PolishSpaceBook.PERAssemblies

@[expose] public section

/-! # PER morphisms presented by trackers on names

A tracker is defined on the source support and sends related names to related
names. Equal morphisms need only agree modulo the target PER on that support.
-/
namespace PolishSpaceBook.PER
open CategoryTheory
universe u
variable {A : Type u} {K : PartialCombinatoryAlgebra A}
variable {R S T : PER K}

def RelationTracker (R S : PER K) (r : A) : Prop :=
  ∀ a a', R.rel a a' → ∃ b b',
    K.application r a = Part.some b ∧ K.application r a' = Part.some b' ∧ S.rel b b'

theorem relationTracker_identity (R : PER K) : RelationTracker R R K.identity :=
  fun a a' h => ⟨a,a',K.application_identity a,K.application_identity a',h⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    The identity combinator induces the identity on classes. If $r$ and $s$ track successive morphisms,
    $$\PCAAbstract{a}{s(ra)}$$
    is defined on the first support and takes names related by the first PER to names related by the final PER.
    It induces the composite function. The category laws follow from the laws for functions, and the
    assignment to modest assemblies is consequently a fully faithful functor.
-/
theorem relationTracker_comp {r s : A} (hr : RelationTracker R S r) (hs : RelationTracker S T s) :
    RelationTracker R T (K.composition r s) := by
  intro a a' h
  obtain ⟨b,b',hb,hb',hbb'⟩ := hr a a' h
  obtain ⟨c,c',hc,hc',hcc'⟩ := hs b b' hbb'
  refine ⟨c,c',?_,?_,hcc'⟩
  · rw [K.application_composition,hb,Part.bind_some,hc]
  · rw [K.application_composition,hb',Part.bind_some,hc']

theorem supported_output {r : A} (h : RelationTracker R S r) (a : R.Support) :
    ∃ b, K.application r a.val = Part.some b ∧ S.rel b b := by
  obtain ⟨b,b',hb,hb',hh⟩ := h a.val a.val a.property
  have e : b = b' := Part.some_injective (hb.symm.trans hb')
  subst b'
  exact ⟨b,hb,hh⟩

noncomputable def output {r : A} (h : RelationTracker R S r) (a : R.Support) : S.Support :=
  ⟨(supported_output h a).choose,(supported_output h a).choose_spec.2⟩

theorem application_output {r : A} (h : RelationTracker R S r) (a : R.Support) :
    K.application r a.val = Part.some (output h a).val := (supported_output h a).choose_spec.1

theorem output_related {r : A} (h : RelationTracker R S r) {a a' : R.Support}
    (haa' : R.rel a.val a'.val) : S.rel (output h a).val (output h a').val := by
  obtain ⟨b,b',hb,hb',hbb'⟩ := h a.val a'.val haa'
  have eb := Part.some_injective ((application_output h a).symm.trans hb)
  have eb' := Part.some_injective ((application_output h a').symm.trans hb')
  rw [eb,eb']
  exact hbb'

noncomputable def inducedFunction {r : A} (h : RelationTracker R S r) :
    R.assembly.Carrier → S.assembly.Carrier :=
  Quotient.lift (fun a => Quotient.mk S.supportSetoid (output h a))
    (fun _ _ haa' => Quotient.sound (output_related h haa'))

theorem tracks_inducedFunction {r : A} (h : RelationTracker R S r) :
    Assembly.Tracks R.assembly S.assembly r (inducedFunction h) := by
  rintro _ a ⟨ha,rfl⟩
  exact ⟨(output h ⟨a,ha⟩).val,application_output h ⟨a,ha⟩,
    (output h ⟨a,ha⟩).property,rfl⟩

noncomputable def induced {r : A} (h : RelationTracker R S r) : R.assembly ⟶ S.assembly where
  toFun := inducedFunction h
  tracked := ⟨r,tracks_inducedFunction h⟩

theorem tracks_induced {r : A} (h : RelationTracker R S r) :
    Assembly.Tracks R.assembly S.assembly r (induced h) := tracks_inducedFunction h

theorem related_of_common_class {a b : A} {q : S.assembly.Carrier}
    (ha : S.assembly.realizes a q) (hb : S.assembly.realizes b q) : S.rel a b := by
  obtain ⟨haa,ea⟩ := ha
  obtain ⟨hbb,eb⟩ := hb
  exact Quotient.exact (ea.trans eb.symm)

theorem relationTracker_of_tracks {r : A} {f : R.assembly ⟶ S.assembly}
    (hr : Assembly.Tracks R.assembly S.assembly r f) : RelationTracker R S r := by
  intro a a' haa'
  have ha := R.trans haa' (R.symm.symm _ _ haa')
  have ha' := R.trans (R.symm.symm _ _ haa') haa'
  let q := Quotient.mk R.supportSetoid ⟨a,ha⟩
  obtain ⟨b,hb,hfb⟩ := hr q a ⟨ha,rfl⟩
  obtain ⟨b',hb',hfb'⟩ := hr q a' ⟨ha',Quotient.sound (R.symm.symm _ _ haa')⟩
  exact ⟨b,b',hb,hb',related_of_common_class hfb hfb'⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Every class has a member, and a name belongs to only one class, so $\PERAssembly{R}$ is a modest assembly.
    The tracker conditions make the induced function independent of the representative and make $r$ a tracker
    of that function as an assembly morphism. Conversely, a tracker of an assembly morphism between these
    quotients is defined on every name in $\PERSupport{R}$. Related input names realize the same class, so
    both output names realize the same image class and are $S$-related. Thus the morphisms on the two sides
    are exactly the same tracked functions. Equality of the induced functions is precisely the displayed
    condition on pairs of trackers.
-/
theorem relationTracker_iff_exists_morphism (r : A) :
    RelationTracker R S r ↔ ∃ f : R ⟶ S, Assembly.Tracks R.assembly S.assembly r f.hom := by
  constructor
  · intro h
    exact ⟨InducedCategory.homMk (induced h),tracks_induced h⟩
  · rintro ⟨f,hf⟩
    exact relationTracker_of_tracks hf

theorem every_morphism_induced (f : R ⟶ S) :
    ∃ (r : A) (h : RelationTracker R S r), f.hom = induced h := by
  obtain ⟨r,hr⟩ := f.hom.tracked
  have h := relationTracker_of_tracks hr
  exact ⟨r,h,Assembly.modest_exponential R.assembly S.modest_assembly r hr (tracks_induced h)⟩

theorem induced_eq_iff {r s : A} (hr : RelationTracker R S r) (hs : RelationTracker R S s) :
    induced hr = induced hs ↔ ∀ a : R.Support, S.rel (output hr a).val (output hs a).val := by
  constructor
  · intro h a
    exact Quotient.exact (congrArg (fun f : R.assembly ⟶ S.assembly =>
      f (Quotient.mk R.supportSetoid a)) h)
  · intro h
    apply Assembly.Hom.ext
    intro q
    exact Quotient.inductionOn q (fun a => Quotient.sound (h a))

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    A tracker $r$ from a PER $R$ to a PER $S$ must satisfy
    $$\begin{aligned}
    a\in\PERSupport{R}&\quad\Longrightarrow\quad ra\downarrow\ \land\ ra\in\PERSupport{S},\\
    a\mathrel{R}a'&\quad\Longrightarrow\quad (ra)\mathrel{S}(ra').
    \end{aligned}$$
    It induces the function $\EquivalenceClass{R}{a}\mapsto\EquivalenceClass{S}{ra}$ on classes.
    Define $\PERCat{A}$ to have PERs on $A$ as objects and these induced functions as morphisms. In particular,
    two trackers $r,s$ represent the same morphism exactly when
    $$\forall a\in\PERSupport{R},\quad (ra)\mathrel{S}(sa).$$
    No agreement or definedness outside the source support is required.
-/
/-- The equivalence of trackers tests only source-support inputs and target equivalence of outputs. -/
theorem induced_eq_iff_on_support {r s : A} (hr : RelationTracker R S r) (hs : RelationTracker R S s) :
    induced hr = induced hs ↔ ∀ a b c, R.rel a a →
      K.application r a = Part.some b → K.application s a = Part.some c → S.rel b c := by
  rw [induced_eq_iff]
  constructor
  · intro h a b c ha hb hc
    have e := Part.some_injective ((application_output hr ⟨a,ha⟩).symm.trans hb)
    have e' := Part.some_injective ((application_output hs ⟨a,ha⟩).symm.trans hc)
    simpa only [e,e'] using h ⟨a,ha⟩
  · intro h a
    exact h a.val _ _ a.property (application_output hr a) (application_output hs a)

end PolishSpaceBook.PER
