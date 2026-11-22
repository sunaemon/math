module

public import PolishSpaceBook.ModestAssemblies
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

/-! # Partial equivalence relations and their modest assemblies

A PER is symmetric and transitive on PCA names; its support carries an ordinary
setoid. The quotient is realized by exactly the names in each equivalence class.
-/
namespace PolishSpaceBook
open CategoryTheory
universe u
variable {A : Type u}

structure PER (K : PartialCombinatoryAlgebra A) where
  rel : A → A → Prop
  symm : Std.Symm rel
  isTrans : IsTrans A rel

namespace PER
variable {K : PartialCombinatoryAlgebra A}

theorem trans (R : PER K) {a b c : A} (h : R.rel a b) (h' : R.rel b c) : R.rel a c :=
  R.isTrans.trans a b c h h'

def Support (R : PER K) := {a : A // R.rel a a}

def supportSetoid (R : PER K) : Setoid R.Support where
  r a b := R.rel a.val b.val
  iseqv := ⟨fun a => a.property,fun h => R.symm.symm _ _ h,fun h h' => R.trans h h'⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{PERSupport,PERAssembly,PERCat}
    \end{mathmeta}
    A \termuse{partial equivalence relation} $R$ on $A$ is a symmetric and transitive relation. Its
    \termdefineas{support of a partial equivalence relation}{support} is
    $$\PERSupport{R}:=\{a\in A:a\mathrel{R}a\}.$$
    If $a\mathrel{R}b$, symmetry and transitivity put both names in the support. The restriction of $R$ to
    its support is therefore an equivalence relation. Define the assembly
    $$|\PERAssembly{R}|:=\SetQuotient{\PERSupport{R}}{R},\qquad
     a\Vdash_{\PERAssembly{R}}\EquivalenceClass{R}{b}\quad\Longleftrightarrow\quad a\mathrel{R}b.$$
    Thus a class is realized by exactly its members.
-/
def assembly (R : PER K) : Assembly.{u,u} K where
  Carrier := Quotient R.supportSetoid
  realizes a q := ∃ ha : R.rel a a, Quotient.mk R.supportSetoid ⟨a,ha⟩ = q
  inhabited q := Quotient.inductionOn q (fun a => ⟨a.val,a.property,rfl⟩)

theorem modest_assembly (R : PER K) : Assembly.Modest R.assembly := by
  rintro a x y ⟨ha,rfl⟩ ⟨ha',rfl⟩
  rfl

def modest (R : PER K) : ModestAssembly.{u,u} K := ⟨R.assembly,R.modest_assembly⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    \begin{mathmeta}
      \define{ModestPER}
    \end{mathmeta}
    For the reverse construction, let $X$ be modest and define
    $$a\mathrel{\ModestPER{X}}b\quad\Longleftrightarrow\quad
    \exists x\in|X|\,(a\Vdash_X x\land b\Vdash_X x).$$
    Symmetry is immediate. For transitivity, the common middle name forces the two witnessed elements to
    coincide by modesty, so the outer names realize that same element. Hence this is a PER. Its support
    consists exactly of the names realizing elements of $X$.
-/
def ofModest (X : ModestAssembly.{u,u} K) : PER K where
  rel a b := ∃ x, X.obj.realizes a x ∧ X.obj.realizes b x
  symm := ⟨by rintro a b ⟨x,ha,hb⟩; exact ⟨x,hb,ha⟩⟩
  isTrans := ⟨by
    rintro a b c ⟨x,ha,hb⟩ ⟨y,hb',hc⟩
    have h := X.property b hb hb'
    subst y
    exact ⟨x,ha,hc⟩⟩

/-- Recover the PER exactly from the names of its quotient assembly. -/
theorem ofModest_modest_rel (R : PER K) (a b : A) :
    (ofModest R.modest).rel a b ↔ R.rel a b := by
  constructor
  · rintro ⟨q,⟨ha,ea⟩,⟨hb,eb⟩⟩
    exact Quotient.exact (ea.trans eb.symm)
  · intro h
    have ha := R.trans h (R.symm.symm _ _ h)
    have hb := R.trans (R.symm.symm _ _ h) h
    exact ⟨Quotient.mk R.supportSetoid ⟨a,ha⟩,⟨ha,rfl⟩,
      ⟨hb,Quotient.sound (R.symm.symm _ _ h)⟩⟩

noncomputable def decodeName (X : ModestAssembly.{u,u} K) (a : (ofModest X).Support) :
    X.obj.Carrier := a.property.choose

theorem realizes_decodeName (X : ModestAssembly.{u,u} K) (a : (ofModest X).Support) :
    X.obj.realizes a.val (decodeName X a) := a.property.choose_spec.1

noncomputable def decode (X : ModestAssembly.{u,u} K) : (ofModest X).assembly.Carrier → X.obj.Carrier :=
  Quotient.lift (decodeName X) (by
    rintro a b ⟨x,ha,hb⟩
    exact (X.property a.val (realizes_decodeName X a) ha).trans
      (X.property b.val hb (realizes_decodeName X b)))

theorem realizes_decode (X : ModestAssembly.{u,u} K) {a : A} {q : (ofModest X).assembly.Carrier}
    (h : (ofModest X).assembly.realizes a q) : X.obj.realizes a (decode X q) := by
  rcases h with ⟨ha,rfl⟩
  exact realizes_decodeName X ⟨a,ha⟩

noncomputable def encode (X : ModestAssembly.{u,u} K) (x : X.obj.Carrier) :
    (ofModest X).assembly.Carrier :=
  Quotient.mk (ofModest X).supportSetoid
    ⟨(X.obj.inhabited x).choose,⟨x,(X.obj.inhabited x).choose_spec,(X.obj.inhabited x).choose_spec⟩⟩

theorem realizes_encode (X : ModestAssembly.{u,u} K) {a : A} {x : X.obj.Carrier}
    (ha : X.obj.realizes a x) : (ofModest X).assembly.realizes a (encode X x) :=
  ⟨⟨x,ha,ha⟩,Quotient.sound ⟨x,ha,(X.obj.inhabited x).choose_spec⟩⟩

theorem decode_encode (X : ModestAssembly.{u,u} K) (x : X.obj.Carrier) :
    decode X (encode X x) = x := by
  obtain ⟨a,ha⟩ := X.obj.inhabited x
  exact X.property a (realizes_decode X (realizes_encode X ha)) ha

theorem encode_decode (X : ModestAssembly.{u,u} K) (q : (ofModest X).assembly.Carrier) :
    encode X (decode X q) = q := by
  refine Quotient.inductionOn q (fun a => ?_)
  apply Quotient.sound
  exact ⟨decodeName X a,(X.obj.inhabited (decodeName X a)).choose_spec,realizes_decodeName X a⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Send $\EquivalenceClass{\ModestPER{X}}{a}$ to the unique element of $X$ realized by $a$.
    This is well-defined and surjective because every element has a realizer, and it is injective by the
    definition of the relation. Its inverse sends an element to the class of any of its realizers, a class
    independent of that choice. Both functions preserve every input name, so both are tracked by the
    identity combinator. They give an isomorphism $\PERAssembly{\ModestPER{X}}\cong X$ without requiring a
    computable choice of realizers. Starting instead with $R$, two names realize the same class exactly
    when they are $R$-related, so $\ModestPER{\PERAssembly{R}}=R$. These constructions prove essential
    surjectivity and hence the claimed equivalence.
-/
/-- Both directions preserve every input name; choice occurs only in the underlying set functions. -/
noncomputable def reconstructionIso (X : ModestAssembly.{u,u} K) : (ofModest X).assembly ≅ X.obj where
  hom := {
    toFun := decode X
    tracked := ⟨K.identity,fun _ a ha => ⟨a,K.application_identity a,realizes_decode X ha⟩⟩ }
  inv := {
    toFun := encode X
    tracked := ⟨K.identity,fun _ a ha => ⟨a,K.application_identity a,realizes_encode X ha⟩⟩ }
  hom_inv_id := Assembly.Hom.ext (encode_decode X)
  inv_hom_id := Assembly.Hom.ext (decode_encode X)

instance perCategory : Category (PER K) :=
  inferInstanceAs (Category (InducedCategory (Assembly K) assembly))

def toModest : PER K ⥤ ModestAssembly.{u,u} K where
  obj := modest
  map f := ObjectProperty.homMk f.hom

abbrev fullyFaithfulToModest : (toModest (K := K)).FullyFaithful where
  preimage f := InducedCategory.homMk f.hom

instance toModestFull : (toModest (K := K)).Full := fullyFaithfulToModest.full
instance toModestFaithful : (toModest (K := K)).Faithful := fullyFaithfulToModest.faithful

instance toModestEssSurj : (toModest (K := K)).EssSurj where
  mem_essImage X := ⟨ofModest X,⟨ObjectProperty.isoMk _ (reconstructionIso X)⟩⟩

instance toModestIsEquivalence : (toModest (K := K)).IsEquivalence where

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: PER presentation of modest sets
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the numerical lambda-index PCA $A=K_1$, these are the categories of
    \termdefineas{numbered set}{numbered sets} and \termdefineas{PER-set}{PER-sets} on $\NN$.
    The construction gives an equivalence, rather than a literal identification of their underlying data.
    Morphisms are computed on names by the partial recursive functions represented by the lambda indices;
    the computation must be defined on the source support and respect the target PER. Different indices
    may induce the same function on classes.
-/
noncomputable def equivalence : PER K ≌ ModestAssembly.{u,u} K := toModest.asEquivalence

end PER
end PolishSpaceBook
