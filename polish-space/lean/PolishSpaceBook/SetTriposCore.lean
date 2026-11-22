module

public import PolishSpaceBook.TriposToposForcingRealizability
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Order.Category.HeytAlg

@[expose] public section

/-! # Shared set-based tripos interface and base-change proofs -/
namespace PolishSpaceBook
open CategoryTheory Limits Opposite
universe u v

theorem realizabilityExists_baseChange {R : Type v} {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I}
    (h : IsPullback g' f' f g) (φ : RealizabilityPredicate R I) :
    realizabilityReindex g (realizabilityExists f φ) =
      realizabilityExists f' (realizabilityReindex g' φ) := by
  funext j
  apply Set.ext
  intro e
  change (∃ i, f i = g j ∧ e ∈ φ i) ↔ ∃ i', f' i' = j ∧ e ∈ φ (g' i')
  constructor
  · rintro ⟨i, hi, he⟩
    obtain ⟨i', hg', hf'⟩ := Types.exists_of_isPullback h i j hi
    exact ⟨i', hf', hg' ▸ he⟩
  · rintro ⟨i', hf', he⟩
    refine ⟨g' i', ?_, he⟩
    have hw : f (g' i') = g (f' i') := ConcreteCategory.congr_hom h.w i'
    exact hw.trans (congrArg g hf')

theorem realizabilityForall_baseChange {R : Type v} (K : RealizerAbstraction R) {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I}
    (h : IsPullback g' f' f g) (φ : RealizabilityPredicate R I) :
    realizabilityReindex g (realizabilityForall K f φ) =
      realizabilityForall K f' (realizabilityReindex g' φ) := by
  funext j
  apply Set.ext
  intro e
  change (∀ i, f i = g j → ∀ n, ∃ b, K.app e n b ∧ b ∈ φ i) ↔
    ∀ i', f' i' = j → ∀ n, ∃ b, K.app e n b ∧ b ∈ φ (g' i')
  constructor
  · intro he i' hf' n
    apply he (g' i') _ n
    have hw : f (g' i') = g (f' i') := ConcreteCategory.congr_hom h.w i'
    exact hw.trans (congrArg g hf')
  · intro he i hi n
    obtain ⟨i', hg', hf'⟩ := Types.exists_of_isPullback h i j hi
    simpa only [hg'] using he i' hf' n

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termdefine{tripos} over the base category $\mathcal C =
    \SetCat = \SetCatU$ is a functor
    $$\mathcal P : \opcat{\mathcal C} \to \HeytAlgCat$$
    to the category of $U$-small Heyting algebras, satisfying:
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   for each map $f : I \to J$ in $\mathcal C$, the homomorphism $\mathcal P(f) : \mathcal P(J) \to \mathcal P(I)$ has
        both a left adjoint $\exists_f$ and a right adjoint $\forall_f$ (the Heyting analogue of quantifiers along $f$);
    *   the \termdefine{Beck--Chevalley condition} holds: in pullback squares of $\mathcal C$, reindexing commutes
        with the corresponding
        adjoints as monotone maps. The adjoints themselves need not be morphisms of $\HeytAlgCat$;
    *   there is a \termdefine{generic predicate} — an element $\sigma \in \mathcal P(\Sigma)$ for some $\Sigma \in \mathcal
        C$ such that every $\varphi \in \mathcal P(I)$ is of the form $\mathcal P(f)(\sigma)$ for some $f : I \to \Sigma$,
        generally not unique.
-/
structure SetTripos where
  predicates : (Type u)ᵒᵖ ⥤ HeytAlg.{u}
  existsAlong : {I J : Type u} → (I → J) → predicates.obj (op I) →o predicates.obj (op J)
  forallAlong : {I J : Type u} → (I → J) → predicates.obj (op I) →o predicates.obj (op J)
  exists_adjunction : ∀ {I J : Type u} (f : I → J),
    GaloisConnection (existsAlong f) (predicates.map (↾f).op)
  forall_adjunction : ∀ {I J : Type u} (f : I → J),
    GaloisConnection (predicates.map (↾f).op) (forallAlong f)
  exists_beckChevalley : ∀ {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I},
    IsPullback g' f' f g → ∀ a : predicates.obj (op I),
      (predicates.map g.op) (existsAlong f a) = existsAlong f' ((predicates.map g'.op) a)
  forall_beckChevalley : ∀ {I I' J J' : Type u}
    {f : I ⟶ J} {g : J' ⟶ J} {f' : I' ⟶ J'} {g' : I' ⟶ I},
    IsPullback g' f' f g → ∀ a : predicates.obj (op I),
      (predicates.map g.op) (forallAlong f a) = forallAlong f' ((predicates.map g'.op) a)
  genericObject : Type u
  genericPredicate : predicates.obj (op genericObject)
  generic : ∀ {I : Type u} (a : predicates.obj (op I)),
    ∃ f : I → genericObject, (predicates.map (↾f).op) genericPredicate = a

end PolishSpaceBook
