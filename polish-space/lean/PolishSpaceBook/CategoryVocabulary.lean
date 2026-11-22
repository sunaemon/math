module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.Cat.CartesianClosed
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Subobject.Classifier.Defs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Widesubcategory

@[expose] public section

/-! # The appendix's categorical vocabulary in mathlib's canonical interfaces

The aliases below expose the standard definitions used by the assembly and PER
constructions. They do not identify Lean universe levels with membership in a
particular set-theoretic Grothendieck universe.
-/
namespace PolishSpaceBook.CategoryVocabulary
open CategoryTheory Limits Opposite
universe u v u' v'

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{category} $\mathcal C$ consists of:
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   a set $\Ob{\mathcal C}$ of \termdefineas{category object}{objects} $A, B, C, \ldots$;
    *   for each ordered pair $(A, B)$ of objects, a set $\HomSet{\mathcal C}{A}{B}$ of
        \termdefineas{category morphism}{morphisms} or \termdefineas{category arrow}{arrows} $f : A \to B$;
    *   for each object $A$, an \termdefine{identity morphism} $\mathrm{id}_A : A \to A$;
    *   for each triple $(A, B, C)$, a \termdefine{composition} map $\HomSet{\mathcal C}{B}{C} \times \HomSet{\mathcal
        C}{A}{B} \to \HomSet{\mathcal C}{A}{C}$, written $(g, f) \mapsto g \circ f$;
-/
abbrev CategoryData (C : Type u) := CategoryStruct.{v} C
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    subject to the \termdefineas{identity law}{identity laws} $f \circ \mathrm{id}_A = f = \mathrm{id}_B \circ f$ for $f : A
    \to B$ and the \termdefine{associativity law} $h \circ (g \circ f) = (h \circ g) \circ f$. The hom-set $\HomSet{\mathcal
    C}{A}{B}$ is also written $\mathrm{Hom}_{\mathcal C}(A, B)$. By §{sec:cat-universe} the categories in this appendix are
    locally $U$-small, with $\Ob{\mathcal C}$ either $U$-small or $U$-large.
-/
abbrev CategoryLaws (C : Type u) := Category.{v} C

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    subject to the \termdefineas{identity law}{identity laws} $f \circ \mathrm{id}_A = f = \mathrm{id}_B \circ f$ for $f : A
    \to B$ and the \termdefine{associativity law} $h \circ (g \circ f) = (h \circ g) \circ f$. The hom-set $\HomSet{\mathcal
    C}{A}{B}$ is also written $\mathrm{Hom}_{\mathcal C}(A, B)$. By §{sec:cat-universe} the categories in this appendix are
    locally $U$-small, with $\Ob{\mathcal C}$ either $U$-small or $U$-large.
-/
theorem identity_laws {X Y : C} (f : X ⟶ Y) :
    𝟙 X ≫ f = f ∧ f ≫ 𝟙 Y = f := ⟨Category.id_comp f, Category.comp_id f⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    subject to the \termdefineas{identity law}{identity laws} $f \circ \mathrm{id}_A = f = \mathrm{id}_B \circ f$ for $f : A
    \to B$ and the \termdefine{associativity law} $h \circ (g \circ f) = (h \circ g) \circ f$. The hom-set $\HomSet{\mathcal
    C}{A}{B}$ is also written $\mathrm{Hom}_{\mathcal C}(A, B)$. By §{sec:cat-universe} the categories in this appendix are
    locally $U$-small, with $\Ob{\mathcal C}$ either $U$-small or $U$-large.
-/
theorem associative {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := Category.assoc f g h

abbrev Isomorphism (X Y : C) := X ≅ Y
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A morphism $f : A \to B$ is an \termdefine{isomorphism} if there exists $g : B \to A$ with $g \circ f = \mathrm{id}_A$
    and $f \circ g = \mathrm{id}_B$. A \termdefine{monomorphism} (or \termuseas{monomorphism}{mono}) is a left-cancellative
    arrow: $f \circ g = f \circ g'$ implies $g = g'$. An \termdefine{epimorphism} is right-cancellative.
-/
abbrev Monomorphism {X Y : C} (f : X ⟶ Y) := Mono f
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A morphism $f : A \to B$ is an \termdefine{isomorphism} if there exists $g : B \to A$ with $g \circ f = \mathrm{id}_A$
    and $f \circ g = \mathrm{id}_B$. A \termdefine{monomorphism} (or \termuseas{monomorphism}{mono}) is a left-cancellative
    arrow: $f \circ g = f \circ g'$ implies $g = g'$. An \termdefine{epimorphism} is right-cancellative.
-/
abbrev Epimorphism {X Y : C} (f : X ⟶ Y) := Epi f

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A morphism $f : A \to B$ is an \termdefine{isomorphism} if there exists $g : B \to A$ with $g \circ f = \mathrm{id}_A$
    and $f \circ g = \mathrm{id}_B$. A \termdefine{monomorphism} (or \termuseas{monomorphism}{mono}) is a left-cancellative
    arrow: $f \circ g = f \circ g'$ implies $g = g'$. An \termdefine{epimorphism} is right-cancellative.
-/
theorem isIso_iff_inverse {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∃ g : Y ⟶ X, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y := by
  constructor
  · intro hf
    let := hf
    exact ⟨inv f, IsIso.hom_inv_id f, IsIso.inv_hom_id f⟩
  · rintro ⟨g, hfg, hgf⟩
    exact ⟨⟨g, hfg, hgf⟩⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A morphism $f : A \to B$ is an \termdefine{isomorphism} if there exists $g : B \to A$ with $g \circ f = \mathrm{id}_A$
    and $f \circ g = \mathrm{id}_B$. A \termdefine{monomorphism} (or \termuseas{monomorphism}{mono}) is a left-cancellative
    arrow: $f \circ g = f \circ g'$ implies $g = g'$. An \termdefine{epimorphism} is right-cancellative.
-/
theorem mono_cancellation {X Y Z : C} (f : X ⟶ Y) [Mono f]
    (g h : Z ⟶ X) (e : g ≫ f = h ≫ f) : g = h := (cancel_mono f).mp e

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A morphism $f : A \to B$ is an \termdefine{isomorphism} if there exists $g : B \to A$ with $g \circ f = \mathrm{id}_A$
    and $f \circ g = \mathrm{id}_B$. A \termdefine{monomorphism} (or \termuseas{monomorphism}{mono}) is a left-cancellative
    arrow: $f \circ g = f \circ g'$ implies $g = g'$. An \termdefine{epimorphism} is right-cancellative.
-/
theorem epi_cancellation {X Y Z : C} (f : X ⟶ Y) [Epi f]
    (g h : Y ⟶ Z) (e : f ≫ g = f ≫ h) : g = h := (cancel_epi f).mp e

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{opcat}
    \end{mathmeta}
    The \termdefineas{opposite category}{opposite category} $\opcat{\mathcal C}$ has the same objects and reverses arrows:
    $\HomSet{\opcat{\mathcal C}}{A}{B} = \HomSet{\mathcal C}{B}{A}$, with composition reversed. The
    \termdefine{product category} $\mathcal C \times \mathcal D$ has pairs of objects and pairs of morphisms, composed
    coordinate-wise.
-/
abbrev OppositeObjects := Cᵒᵖ
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \begin{mathmeta}
      \define{opcat}
    \end{mathmeta}
    The \termdefineas{opposite category}{opposite category} $\opcat{\mathcal C}$ has the same objects and reverses arrows:
    $\HomSet{\opcat{\mathcal C}}{A}{B} = \HomSet{\mathcal C}{B}{A}$, with composition reversed. The
    \termdefine{product category} $\mathcal C \times \mathcal D$ has pairs of objects and pairs of morphisms, composed
    coordinate-wise.
-/
abbrev ProductObjects := C × D
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Functors.** A \termdefine{functor} $F : \mathcal C \to \mathcal D$ assigns to each object $A$ of $\mathcal C$ an
    object $F(A)$ of $\mathcal D$, and to each morphism $f : A \to B$ a morphism $F(f) : F(A) \to F(B)$, in such a way that
    $F(\mathrm{id}_A) = \mathrm{id}_{F(A)}$ and $F(g \circ f) = F(g) \circ F(f)$. A \termdefine{contravariant functor}
    $\mathcal C \to \mathcal D$ is the same data as a functor $\opcat{\mathcal C} \to \mathcal D$.
-/
abbrev CovariantFunctor := C ⥤ D
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Functors.** A \termdefine{functor} $F : \mathcal C \to \mathcal D$ assigns to each object $A$ of $\mathcal C$ an
    object $F(A)$ of $\mathcal D$, and to each morphism $f : A \to B$ a morphism $F(f) : F(A) \to F(B)$, in such a way that
    $F(\mathrm{id}_A) = \mathrm{id}_{F(A)}$ and $F(g \circ f) = F(g) \circ F(f)$. A \termdefine{contravariant functor}
    $\mathcal C \to \mathcal D$ is the same data as a functor $\opcat{\mathcal C} \to \mathcal D$.
-/
abbrev ContravariantFunctor := Cᵒᵖ ⥤ D

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For each object $A$, the \termdefine{representable functor} $\HomSet{\mathcal C}{A}{-} : \mathcal C \to \SetCat$ sends
    $B$ to the hom-set $\HomSet{\mathcal C}{A}{B}$ and $f : B \to B'$ to post-composition $f_* : g \mapsto f \circ g$.
    Dually, $\HomSet{\mathcal C}{-}{A} : \opcat{\mathcal C} \to \SetCat$ uses pre-composition.
-/
def covariantRepresentable (A : C) : C ⥤ Type v := coyoneda.obj (op A)
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For each object $A$, the \termdefine{representable functor} $\HomSet{\mathcal C}{A}{-} : \mathcal C \to \SetCat$ sends
    $B$ to the hom-set $\HomSet{\mathcal C}{A}{B}$ and $f : B \to B'$ to post-composition $f_* : g \mapsto f \circ g$.
    Dually, $\HomSet{\mathcal C}{-}{A} : \opcat{\mathcal C} \to \SetCat$ uses pre-composition.
-/
def contravariantRepresentable (A : C) : Cᵒᵖ ⥤ Type v := yoneda.obj A

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Natural transformations.** Given functors $F, G : \mathcal C \to \mathcal D$, a \termdefine{natural transformation}
    $\eta : F \Rightarrow G$ assigns to each object $A$ of $\mathcal C$ a morphism $\eta_A : F(A) \to G(A)$ of $\mathcal D$
    — its \termdefineas{component of a natural transformation}{component} at $A$ — such that for every $f : A \to B$ the
    \termdefine{naturality square} commutes:
    $$G(f) \circ \eta_A \;=\; \eta_B \circ F(f).$$
    A natural transformation whose every component is an isomorphism is a \termdefine{natural isomorphism}, written $\eta :
    F \cong G$.
-/
abbrev Transformation (F G : C ⥤ D) := F ⟶ G
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Natural transformations.** Given functors $F, G : \mathcal C \to \mathcal D$, a \termdefine{natural transformation}
    $\eta : F \Rightarrow G$ assigns to each object $A$ of $\mathcal C$ a morphism $\eta_A : F(A) \to G(A)$ of $\mathcal D$
    — its \termdefineas{component of a natural transformation}{component} at $A$ — such that for every $f : A \to B$ the
    \termdefine{naturality square} commutes:
    $$G(f) \circ \eta_A \;=\; \eta_B \circ F(f).$$
    A natural transformation whose every component is an isomorphism is a \termdefine{natural isomorphism}, written $\eta :
    F \cong G$.
-/
abbrev NaturalIsomorphism (F G : C ⥤ D) := F ≅ G

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Natural transformations.** Given functors $F, G : \mathcal C \to \mathcal D$, a \termdefine{natural transformation}
    $\eta : F \Rightarrow G$ assigns to each object $A$ of $\mathcal C$ a morphism $\eta_A : F(A) \to G(A)$ of $\mathcal D$
    — its \termdefineas{component of a natural transformation}{component} at $A$ — such that for every $f : A \to B$ the
    \termdefine{naturality square} commutes:
    $$G(f) \circ \eta_A \;=\; \eta_B \circ F(f).$$
    A natural transformation whose every component is an isomorphism is a \termdefine{natural isomorphism}, written $\eta :
    F \cong G$.
-/
theorem natural_iso_iff_components {F G : C ⥤ D} (η : F ⟶ G) :
    IsIso η ↔ ∀ X, IsIso (η.app X) := NatTrans.isIso_iff_isIso_app η

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Natural transformations.** Given functors $F, G : \mathcal C \to \mathcal D$, a \termdefine{natural transformation}
    $\eta : F \Rightarrow G$ assigns to each object $A$ of $\mathcal C$ a morphism $\eta_A : F(A) \to G(A)$ of $\mathcal D$
    — its \termdefineas{component of a natural transformation}{component} at $A$ — such that for every $f : A \to B$ the
    \termdefine{naturality square} commutes:
    $$G(f) \circ \eta_A \;=\; \eta_B \circ F(f).$$
    A natural transformation whose every component is an isomorphism is a \termdefine{natural isomorphism}, written $\eta :
    F \cong G$.
-/
theorem naturality {F G : C ⥤ D} (η : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    η.app X ≫ G.map f = F.map f ≫ η.app Y := (η.naturality f).symm

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The collection of functors $\mathcal C \to \mathcal D$ together with natural transformations forms a category
    $\functorCat{\mathcal C}{\mathcal D}$, the **functor category**. When both categories are $U$-small, it is the
    exponential object of
    $\mathcal C$ and $\mathcal D$ in $\CatCat$. When $\mathcal C$ is $U$-small and $\mathcal D$ is locally
    $U$-small, $\functorCat{\mathcal C}{\mathcal D}$
    is again locally $U$-small.
-/
abbrev FunctorObjects := C ⥤ D

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The collection of functors $\mathcal C \to \mathcal D$ together with natural transformations forms a category
    $\functorCat{\mathcal C}{\mathcal D}$, the **functor category**. When both categories are $U$-small, it is the
    exponential object of
    $\mathcal C$ and $\mathcal D$ in $\CatCat$. When $\mathcal C$ is $U$-small and $\mathcal D$ is locally
    $U$-small, $\functorCat{\mathcal C}{\mathcal D}$
    is again locally $U$-small.
-/
theorem functor_homs_small (E : Type u) [Category.{u} E]
    (F : Type u') [Category.{u} F] (P Q : E ⥤ F) : Small.{u} (P ⟶ Q) := inferInstance

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The collection of functors $\mathcal C \to \mathcal D$ together with natural transformations forms a category
    $\functorCat{\mathcal C}{\mathcal D}$, the **functor category**. When both categories are $U$-small, it is the
    exponential object of
    $\mathcal C$ and $\mathcal D$ in $\CatCat$. When $\mathcal C$ is $U$-small and $\mathcal D$ is locally
    $U$-small, $\functorCat{\mathcal C}{\mathcal D}$
    is again locally $U$-small.
-/
abbrev smallCategoryExponential (E : Type u) [Category.{u} E] : Closed (Cat.of E) :=
  Cat.closed E

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The **Yoneda lemma** is the basic structural fact: for any locally $U$-small $\mathcal C$, any functor $F : \mathcal C
    \to \SetCat$, and any object $A$ of $\mathcal C$, evaluation at $\mathrm{id}_A$ gives a bijection
    $$\HomSet{\functorCat{\mathcal C}{\SetCat}}{\HomSet{\mathcal C}{A}{-}}{F} \;\cong\; F(A),$$
    natural in both arguments. In particular, when $\mathcal C$ is $U$-small, $A \mapsto \HomSet{\mathcal C}{A}{-}$ embeds
    $\opcat{\mathcal C}$ fully and faithfully into the functor category $\functorCat{\mathcal C}{\SetCat}$.
-/
def covariantYonedaEquiv (A : C) (F : C ⥤ Type v) :
    (covariantRepresentable A ⟶ F) ≃ F.obj A := coyonedaEquiv

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The **Yoneda lemma** is the basic structural fact: for any locally $U$-small $\mathcal C$, any functor $F : \mathcal C
    \to \SetCat$, and any object $A$ of $\mathcal C$, evaluation at $\mathrm{id}_A$ gives a bijection
    $$\HomSet{\functorCat{\mathcal C}{\SetCat}}{\HomSet{\mathcal C}{A}{-}}{F} \;\cong\; F(A),$$
    natural in both arguments. In particular, when $\mathcal C$ is $U$-small, $A \mapsto \HomSet{\mathcal C}{A}{-}$ embeds
    $\opcat{\mathcal C}$ fully and faithfully into the functor category $\functorCat{\mathcal C}{\SetCat}$.
-/
def covariantYonedaNaturality : coyonedaPairing C ≅ coyonedaEvaluation C := coyonedaLemma C

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The **Yoneda lemma** is the basic structural fact: for any locally $U$-small $\mathcal C$, any functor $F : \mathcal C
    \to \SetCat$, and any object $A$ of $\mathcal C$, evaluation at $\mathrm{id}_A$ gives a bijection
    $$\HomSet{\functorCat{\mathcal C}{\SetCat}}{\HomSet{\mathcal C}{A}{-}}{F} \;\cong\; F(A),$$
    natural in both arguments. In particular, when $\mathcal C$ is $U$-small, $A \mapsto \HomSet{\mathcal C}{A}{-}$ embeds
    $\opcat{\mathcal C}$ fully and faithfully into the functor category $\functorCat{\mathcal C}{\SetCat}$.
-/
theorem covariantYoneda_full : (coyoneda (C := C)).Full := inferInstance
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The **Yoneda lemma** is the basic structural fact: for any locally $U$-small $\mathcal C$, any functor $F : \mathcal C
    \to \SetCat$, and any object $A$ of $\mathcal C$, evaluation at $\mathrm{id}_A$ gives a bijection
    $$\HomSet{\functorCat{\mathcal C}{\SetCat}}{\HomSet{\mathcal C}{A}{-}}{F} \;\cong\; F(A),$$
    natural in both arguments. In particular, when $\mathcal C$ is $U$-small, $A \mapsto \HomSet{\mathcal C}{A}{-}$ embeds
    $\opcat{\mathcal C}$ fully and faithfully into the functor category $\functorCat{\mathcal C}{\SetCat}$.
-/
theorem covariantYoneda_faithful : (coyoneda (C := C)).Faithful := inferInstance

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A functor $F : \mathcal C \to \mathcal D$ is \termdefine{faithful} when each induced map $\HomSet{\mathcal C}{A}{B} \to
    \HomSet{\mathcal D}{F(A)}{F(B)}$ is injective, \termdefineas{full functor}{full} when it is surjective, and
    \termdefine{essentially surjective} when every object of $\mathcal D$ is isomorphic to some $F(A)$.
-/
abbrev FullFunctor (F : C ⥤ D) := F.Full
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A functor $F : \mathcal C \to \mathcal D$ is \termdefine{faithful} when each induced map $\HomSet{\mathcal C}{A}{B} \to
    \HomSet{\mathcal D}{F(A)}{F(B)}$ is injective, \termdefineas{full functor}{full} when it is surjective, and
    \termdefine{essentially surjective} when every object of $\mathcal D$ is isomorphic to some $F(A)$.
-/
abbrev FaithfulFunctor (F : C ⥤ D) := F.Faithful
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A functor $F : \mathcal C \to \mathcal D$ is \termdefine{faithful} when each induced map $\HomSet{\mathcal C}{A}{B} \to
    \HomSet{\mathcal D}{F(A)}{F(B)}$ is injective, \termdefineas{full functor}{full} when it is surjective, and
    \termdefine{essentially surjective} when every object of $\mathcal D$ is isomorphic to some $F(A)$.
-/
abbrev EssentiallySurjectiveFunctor (F : C ⥤ D) := F.EssSurj
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Equivalences.** A functor $F : \mathcal C \to \mathcal D$ is an \termdefine{equivalence of categories} if there exists
    a functor $G : \mathcal D \to \mathcal C$ together with natural isomorphisms $G \circ F \cong \mathrm{id}_{\mathcal C}$
    and $F \circ G \cong \mathrm{id}_{\mathcal D}$. Equivalently, $F$ is full, faithful, and essentially surjective. The
    unit and counit of an adjoint equivalence give the displayed natural isomorphisms.
-/
abbrev EquivalenceData := C ≌ D

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Equivalences.** A functor $F : \mathcal C \to \mathcal D$ is an \termdefine{equivalence of categories} if there exists
    a functor $G : \mathcal D \to \mathcal C$ together with natural isomorphisms $G \circ F \cong \mathrm{id}_{\mathcal C}$
    and $F \circ G \cong \mathrm{id}_{\mathcal D}$. Equivalently, $F$ is full, faithful, and essentially surjective. The
    unit and counit of an adjoint equivalence give the displayed natural isomorphisms.
-/
noncomputable def equivalenceOfFullFaithfulEssSurj (F : C ⥤ D)
    [F.Full] [F.Faithful] [F.EssSurj] : C ≌ D := by
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    It is
    \termdefineas{full subcategory}{full} when $\HomSet{\mathcal C'}{A}{B} = \HomSet{\mathcal C}{A}{B}$ for every pair of
    objects of $\mathcal
    C'$, so the only choice in defining $\mathcal C'$ is which objects to include.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{subcategory} $\mathcal C' \IncludedIn \mathcal C$ is a category whose objects and morphisms are subsets of
    those of $\mathcal C$, with composition and identities inherited from $\mathcal C$.
-/
abbrev SubcategoryObjects (P : ObjectProperty C) (Q : MorphismProperty P.FullSubcategory)
    [Q.IsMultiplicative] := WideSubcategory Q

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    It is
    \termdefineas{full subcategory}{full} when $\HomSet{\mathcal C'}{A}{B} = \HomSet{\mathcal C}{A}{B}$ for every pair of
    objects of $\mathcal
    C'$, so the only choice in defining $\mathcal C'$ is which objects to include.
-/
abbrev FullObjects (P : ObjectProperty C) := P.FullSubcategory
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Adjunctions.** A functor $F : \mathcal C \to \mathcal D$ is \termdefine{left adjoint} to a functor $U : \mathcal D \to
    \mathcal C$, written $\adjunction{F}{U}$, when there is a bijection
    $$\HomSet{\mathcal D}{F(A)}{B} \;\cong\; \HomSet{\mathcal C}{A}{U(B)}$$
    natural in $A$ and $B$. The natural transformation $\eta : \mathrm{id}_{\mathcal C} \Rightarrow U \circ F$ obtained by
    transposing the identities $\mathrm{id}_{F(A)}$ is the \termdefineas{adjunction unit}{unit}; the natural transformation
    $\varepsilon : F \circ U \Rightarrow \mathrm{id}_{\mathcal D}$ obtained dually is the
    \termdefineas{adjunction counit}{counit}. The two satisfy the \termdefineas{triangle identity}{triangle identities}
    $\varepsilon F \circ F \eta=
    \mathrm{id}_F$ and $U \varepsilon \circ \eta U = \mathrm{id}_U$.
-/
abbrev AdjunctionData (F : C ⥤ D) (U : D ⥤ C) := F ⊣ U

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Adjunctions.** A functor $F : \mathcal C \to \mathcal D$ is \termdefine{left adjoint} to a functor $U : \mathcal D \to
    \mathcal C$, written $\adjunction{F}{U}$, when there is a bijection
    $$\HomSet{\mathcal D}{F(A)}{B} \;\cong\; \HomSet{\mathcal C}{A}{U(B)}$$
    natural in $A$ and $B$. The natural transformation $\eta : \mathrm{id}_{\mathcal C} \Rightarrow U \circ F$ obtained by
    transposing the identities $\mathrm{id}_{F(A)}$ is the \termdefineas{adjunction unit}{unit}; the natural transformation
    $\varepsilon : F \circ U \Rightarrow \mathrm{id}_{\mathcal D}$ obtained dually is the
    \termdefineas{adjunction counit}{counit}. The two satisfy the \termdefineas{triangle identity}{triangle identities}
    $\varepsilon F \circ F \eta=
    \mathrm{id}_F$ and $U \varepsilon \circ \eta U = \mathrm{id}_U$.
-/
def adjunctionHomEquiv {F : C ⥤ D} {U : D ⥤ C} (a : F ⊣ U) (X : C) (Y : D) :
    (F.obj X ⟶ Y) ≃ (X ⟶ U.obj Y) := a.homEquiv X Y

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Terminal objects and products.** A \termdefine{terminal object} $1 \in \mathcal C$ is one such that for every $A$
    there is a unique morphism $A \to 1$. Terminal objects are unique up to unique isomorphism.
-/
abbrev Terminal (T : C) := IsTerminal T
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Terminal objects and products.** A \termdefine{terminal object} $1 \in \mathcal C$ is one such that for every $A$
    there is a unique morphism $A \to 1$. Terminal objects are unique up to unique isomorphism.
-/
def terminalUniqueness {S T : C} (hS : IsTerminal S) (hT : IsTerminal T) : S ≅ T :=
  hS.uniqueUpToIso hT
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{binary product} of $A$ and $B$ is an object $A \times B$ together with projections $\pi_A : A \times B \to
    A$ and $\pi_B : A \times B \to B$ such that for every pair of arrows $f : C \to A$, $g : C \to B$ there is a unique
    $\langle f, g\rangle : C \to A \times B$ with $\pi_A \circ \langle f, g\rangle = f$ and $\pi_B \circ \langle f, g\rangle
    = g$. Finite products are built from binary products and the terminal object.
-/
abbrev ProductCone (A B : C) := BinaryFan A B
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{binary product} of $A$ and $B$ is an object $A \times B$ together with projections $\pi_A : A \times B \to
    A$ and $\pi_B : A \times B \to B$ such that for every pair of arrows $f : C \to A$, $g : C \to B$ there is a unique
    $\langle f, g\rangle : C \to A \times B$ with $\pi_A \circ \langle f, g\rangle = f$ and $\pi_B \circ \langle f, g\rangle
    = g$. Finite products are built from binary products and the terminal object.
-/
abbrev UniversalProduct {A B : C} (s : BinaryFan A B) := IsLimit s
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **General limits.** For a $U$-small category $J$ — the \termdefineas{diagram shape}{shape} — and a functor $D : J \to
    \mathcal C$ — a \termdefineas{categorical diagram}{diagram} of shape $J$ — a \termdefineas{cone over a diagram}{cone}
    over $D$ from an object $A$ is a natural transformation $\mathrm{const}_A \Rightarrow D$ from the constant functor at
    $A$. A \termdefineas{categorical limit}{limit} of $D$ is a cone $(L, \lambda_j : L \to D(j))$ that is universal: every
    other cone factors uniquely through it. Specializing $J$ recovers terminal objects ($J = \emptyset$), products ($J$
    discrete), equalizers ($J$ a parallel pair), and pullbacks ($J$ a cospan). A category is \termdefine{finitely complete}
    if it has all finite limits; equivalently, it has a terminal object, all binary products, and all equalizers.
    \termdefineas{U-completeness}{$U$-completeness} means having limits of all $U$-small diagrams.
-/
abbrev Diagram (J : Type*) [Category* J] := J ⥤ C
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **General limits.** For a $U$-small category $J$ — the \termdefineas{diagram shape}{shape} — and a functor $D : J \to
    \mathcal C$ — a \termdefineas{categorical diagram}{diagram} of shape $J$ — a \termdefineas{cone over a diagram}{cone}
    over $D$ from an object $A$ is a natural transformation $\mathrm{const}_A \Rightarrow D$ from the constant functor at
    $A$. A \termdefineas{categorical limit}{limit} of $D$ is a cone $(L, \lambda_j : L \to D(j))$ that is universal: every
    other cone factors uniquely through it. Specializing $J$ recovers terminal objects ($J = \emptyset$), products ($J$
    discrete), equalizers ($J$ a parallel pair), and pullbacks ($J$ a cospan). A category is \termdefine{finitely complete}
    if it has all finite limits; equivalently, it has a terminal object, all binary products, and all equalizers.
    \termdefineas{U-completeness}{$U$-completeness} means having limits of all $U$-small diagrams.
-/
abbrev ConeData {J : Type*} [Category* J] (F : J ⥤ C) := Cone F
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **General limits.** For a $U$-small category $J$ — the \termdefineas{diagram shape}{shape} — and a functor $D : J \to
    \mathcal C$ — a \termdefineas{categorical diagram}{diagram} of shape $J$ — a \termdefineas{cone over a diagram}{cone}
    over $D$ from an object $A$ is a natural transformation $\mathrm{const}_A \Rightarrow D$ from the constant functor at
    $A$. A \termdefineas{categorical limit}{limit} of $D$ is a cone $(L, \lambda_j : L \to D(j))$ that is universal: every
    other cone factors uniquely through it. Specializing $J$ recovers terminal objects ($J = \emptyset$), products ($J$
    discrete), equalizers ($J$ a parallel pair), and pullbacks ($J$ a cospan). A category is \termdefine{finitely complete}
    if it has all finite limits; equivalently, it has a terminal object, all binary products, and all equalizers.
    \termdefineas{U-completeness}{$U$-completeness} means having limits of all $U$-small diagrams.
-/
abbrev UniversalCone {J : Type*} [Category* J] {F : J ⥤ C} (s : Cone F) := IsLimit s
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termdefineas{colimit}{Colimits} are the dual notion, obtained by reversing arrows: initial objects, coproducts,
    coequalizers, pushouts, and filtered colimits.
-/
abbrev CoconeData {J : Type*} [Category* J] (F : J ⥤ C) := Cocone F
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    \termdefineas{colimit}{Colimits} are the dual notion, obtained by reversing arrows: initial objects, coproducts,
    coequalizers, pushouts, and filtered colimits.
-/
abbrev UniversalCocone {J : Type*} [Category* J] {F : J ⥤ C} (s : Cocone F) := IsColimit s

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **General limits.** For a $U$-small category $J$ — the \termdefineas{diagram shape}{shape} — and a functor $D : J \to
    \mathcal C$ — a \termdefineas{categorical diagram}{diagram} of shape $J$ — a \termdefineas{cone over a diagram}{cone}
    over $D$ from an object $A$ is a natural transformation $\mathrm{const}_A \Rightarrow D$ from the constant functor at
    $A$. A \termdefineas{categorical limit}{limit} of $D$ is a cone $(L, \lambda_j : L \to D(j))$ that is universal: every
    other cone factors uniquely through it. Specializing $J$ recovers terminal objects ($J = \emptyset$), products ($J$
    discrete), equalizers ($J$ a parallel pair), and pullbacks ($J$ a cospan). A category is \termdefine{finitely complete}
    if it has all finite limits; equivalently, it has a terminal object, all binary products, and all equalizers.
    \termdefineas{U-completeness}{$U$-completeness} means having limits of all $U$-small diagrams.
-/
theorem finiteLimits_from_products_equalizers [HasFiniteProducts C] [HasEqualizers C] :
    HasFiniteLimits C := hasFiniteLimits_of_hasEqualizers_and_finite_products

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Exponentials.** A category $\mathcal C$ with finite products has \termdefineas{exponential}{exponentials} if for every
    pair of objects $A, B$ there is an object $\catExp{A}{B}$ — also written $[A, B]$ or $A \Rightarrow B$ — together with
    an \termdefine{evaluation} morphism $\evalMap : \catExp{A}{B} \times A \to B$ such that for every $f : C \times A \to B$
    there is a unique $\overline f : C \to \catExp{A}{B}$ — its \termdefine{transpose} or \termdefine{currying} — with
    $\evalMap \circ (\overline f \times \mathrm{id}_A) = f$. Equivalently, $- \times A$ has a right adjoint $(-)^A$, and the
    exponential adjunction
    $$\HomSet{\mathcal C}{C \times A}{B} \;\cong\; \HomSet{\mathcal C}{C}{\catExp{A}{B}}$$
    is natural in $C$ and $B$.
-/
abbrev ExponentialAdjunction [CartesianMonoidalCategory C] (A : C) (E : C ⥤ C) :=
  MonoidalCategory.tensorRight A ⊣ E

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Cartesian closed categories.** A \termdefine{cartesian closed category} (CCC) is a category with a terminal object,
    all binary products, and all exponentials.
-/
abbrev CartesianClosed [CartesianMonoidalCategory C] := MonoidalClosed C

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Subobjects.** Two monomorphisms $m : S \hookrightarrow A$ and $m' : S' \hookrightarrow A$ into the same object are
    \termdefineas{equivalent monomorphisms}{equivalent} if each factors through the other by an isomorphism. A
    \termdefine{subobject} of $A$ is an equivalence class of monos into $A$.
-/
abbrev Subobjects (A : C) := Subobject A
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Subobject classifier.** In a category with finite limits, a \termdefine{subobject classifier} is a monomorphism
    $\mathrm{true} : 1 \hookrightarrow \SubobjectClassifier$ such that for every monomorphism $m : S \hookrightarrow A$
    there is a unique morphism $\chi_m : A \to \SubobjectClassifier$ — the \termdefine{characteristic map} of $m$ — fitting
    into a pullback square
    $$\begin{array}{ccc} S & \longrightarrow & 1 \\ {\scriptstyle m}\downarrow & & \downarrow{\scriptstyle \mathrm{true}} \\
    A & \xrightarrow{\;\chi_m\;} & \SubobjectClassifier \end{array}$$
    Thus $\SubobjectClassifier$ represents the functor $\Subobjects{-} : \opcat{\mathcal C} \to \SetCat$, and subobjects of
    $A$ correspond bijectively to morphisms $A \to \SubobjectClassifier$:
    $$\Subobjects{A} \;\cong\; \HomSet{\mathcal C}{A}{\SubobjectClassifier}.$$
-/
abbrev SubobjectClassifier := Subobject.Classifier C

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Subobject classifier.** In a category with finite limits, a \termdefine{subobject classifier} is a monomorphism
    $\mathrm{true} : 1 \hookrightarrow \SubobjectClassifier$ such that for every monomorphism $m : S \hookrightarrow A$
    there is a unique morphism $\chi_m : A \to \SubobjectClassifier$ — the \termdefine{characteristic map} of $m$ — fitting
    into a pullback square
    $$\begin{array}{ccc} S & \longrightarrow & 1 \\ {\scriptstyle m}\downarrow & & \downarrow{\scriptstyle \mathrm{true}} \\
    A & \xrightarrow{\;\chi_m\;} & \SubobjectClassifier \end{array}$$
    Thus $\SubobjectClassifier$ represents the functor $\Subobjects{-} : \opcat{\mathcal C} \to \SetCat$, and subobjects of
    $A$ correspond bijectively to morphisms $A \to \SubobjectClassifier$:
    $$\Subobjects{A} \;\cong\; \HomSet{\mathcal C}{A}{\SubobjectClassifier}.$$
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Propositions.** An \termdefineas{internal proposition}{proposition} in context $\Gamma = (x_1 : A_1, \ldots, x_n :
    A_n)$ is a morphism $A_1 \times \cdots \times A_n \to \SubobjectClassifier$, equivalently a subobject of $A_1 \times
    \cdots \times A_n$.
-/
noncomputable def classifierHomEquiv [HasPullbacks C] (c : Subobject.Classifier C) (A : C) :
    (A ⟶ c.Ω) ≃ Subobject A := c.representableBy.homEquiv

/-- The elementary-topos axioms, with the cartesian structure already chosen. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Elementary toposes.** An \termdefine{elementary topos} is a category $\mathcal E$ that is finitely complete, cartesian
    closed, and equipped with a subobject classifier.
-/
def IsElementaryTopos [CartesianMonoidalCategory C] : Prop :=
  HasFiniteLimits C ∧ Nonempty (MonoidalClosed C) ∧ HasSubobjectClassifier C

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Types and terms.** Each object $A$ of $\mathcal E$ is a \termdefineas{internal type}{type}. Closed terms of type $A$
    are global elements $1 \to A$, and a term $t(x_1, \ldots, x_n)$ of type $B$ in free variables $x_i : A_i$ is a morphism
    $A_1 \times \cdots \times A_n \to B$. Substitution is composition.
-/
abbrev TermInContext (Γ B : C) := Γ ⟶ B
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Types and terms.** Each object $A$ of $\mathcal E$ is a \termdefineas{internal type}{type}. Closed terms of type $A$
    are global elements $1 \to A$, and a term $t(x_1, \ldots, x_n)$ of type $B$ in free variables $x_i : A_i$ is a morphism
    $A_1 \times \cdots \times A_n \to B$. Substitution is composition.
-/
abbrev ClosedTerm [HasTerminal C] (A : C) := (⊤_ C) ⟶ A
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Propositions.** An \termdefineas{internal proposition}{proposition} in context $\Gamma = (x_1 : A_1, \ldots, x_n :
    A_n)$ is a morphism $A_1 \times \cdots \times A_n \to \SubobjectClassifier$, equivalently a subobject of $A_1 \times
    \cdots \times A_n$.
-/
abbrev PropositionInContext (Γ : C) := Subobject Γ

end PolishSpaceBook.CategoryVocabulary
