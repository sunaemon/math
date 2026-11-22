module

public import PolishSpaceBook.SetTheoryGrothendieckModels

@[expose] public section

/-! # Set-theoretic size of the category of sets in a Grothendieck universe -/
namespace PolishSpaceBook.SetTheoryModels
universe u
namespace IsGrothendieckUniverse
variable {U : ZFSet.{u}} (hU : IsGrothendieckUniverse U)
include hU

/-- The size conditions refer to sets and actual membership, not Lean levels. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   A set is \termuseas{U-small}{$U$-small} if it is an element of $U$, in the sense of §{sec:inaccessible-universes}.
    *   A category $\mathcal C$ is \termuseas{U-small}{$U$-small} if $\Ob{\mathcal C}$ is $U$-small and every hom-set
        $\HomSet{\mathcal C}{A}{B}$ is $U$-small.
    *   A category is \termdefineas{locally U-small}{locally $U$-small} if every $\HomSet{\mathcal C}{A}{B}$ is $U$-small,
        with $\Ob{\mathcal C}$ allowed to be a $U$-large set.
    *   The unsubscripted symbol $\SetCat$ denotes the category $\SetCatU$ of $U$-small sets and functions; it is locally
        $U$-small but not $U$-small.
-/
def CategoryLocallySmall (U O : ZFSet.{u}) (H : O → O → ZFSet.{u}) : Prop :=
  ∀ x y, H x y ∈ U

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   A set is \termuseas{U-small}{$U$-small} if it is an element of $U$, in the sense of §{sec:inaccessible-universes}.
    *   A category $\mathcal C$ is \termuseas{U-small}{$U$-small} if $\Ob{\mathcal C}$ is $U$-small and every hom-set
        $\HomSet{\mathcal C}{A}{B}$ is $U$-small.
    *   A category is \termdefineas{locally U-small}{locally $U$-small} if every $\HomSet{\mathcal C}{A}{B}$ is $U$-small,
        with $\Ob{\mathcal C}$ allowed to be a $U$-large set.
    *   The unsubscripted symbol $\SetCat$ denotes the category $\SetCatU$ of $U$-small sets and functions; it is locally
        $U$-small but not $U$-small.
-/
def CategorySmall (U O : ZFSet.{u}) (H : O → O → ZFSet.{u}) : Prop :=
  O ∈ U ∧ CategoryLocallySmall U O H

lemma orderedPair_mem {x y : ZFSet.{u}} (hx : x ∈ U) (hy : y ∈ U) :
    ZFSet.pair x y ∈ U :=
  hU.pair_mem (hU.singleton_mem hx) (hU.pair_mem hx hy)

lemma product_mem {x y : ZFSet.{u}} (hx : x ∈ U) (hy : y ∈ U) :
    ZFSet.prod x y ∈ U := by
  apply hU.subset_mem (hU.powerset_mem (hU.powerset_mem (hU.union_mem hx hy)))
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hz
  apply ZFSet.mem_powerset.mpr
  intro t ht
  change t ∈ ({{a}, {a, b}} : ZFSet.{u}) at ht
  rcases ZFSet.mem_pair.mp ht with rfl | rfl
  · apply ZFSet.mem_powerset.mpr
    intro z hz
    rw [ZFSet.mem_singleton] at hz
    subst z
    exact ZFSet.mem_union.mpr (Or.inl ha)
  · apply ZFSet.mem_powerset.mpr
    intro z hz
    rcases ZFSet.mem_pair.mp hz with rfl | rfl
    · exact ZFSet.mem_union.mpr (Or.inl ha)
    · exact ZFSet.mem_union.mpr (Or.inr hb)

lemma functions_mem {x y : ZFSet.{u}} (hx : x ∈ U) (hy : y ∈ U) :
    ZFSet.funs x y ∈ U :=
  hU.subset_mem (hU.powerset_mem (hU.product_mem hx hy)) ZFSet.sep_subset

/-- In particular, natural transformations form a subclass of these component
assignments when the indexing objects and each component hom-set belong to U. -/
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
lemma familyFunctionSubclass_mem {I N : ZFSet.{u}} (hI : I ∈ U)
    (H : I → ZFSet.{u}) (hH : ∀ i, H i ∈ U)
    (hN : N ⊆ ZFSet.funs I (ZFSet.iUnion H)) : N ∈ U :=
  hU.subset_mem (hU.functions_mem hI (hU.indexedUnion_mem hI H hH)) hN

/-- A function includes its graph, domain, and codomain as in the book. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    $\SetCat$ (sets and functions, where a function is a triple consisting of a graph, a domain, and a codomain)
-/
noncomputable def setFunctionHom (x y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun f : ZFSet.funs x y => ZFSet.pair f.val (ZFSet.pair x y))

lemma setFunctionHom_mem {x y : ZFSet.{u}} (hx : x ∈ U) (hy : y ∈ U) :
    setFunctionHom x y ∈ U :=
  hU.range_mem (hU.functions_mem hx hy) _ (fun f =>
    hU.orderedPair_mem (hU.transitive.mem_trans f.property (hU.functions_mem hx hy))
      (hU.orderedPair_mem hx hy))

omit hU in
/-- The set of all objects is U itself and is not an element of U. -/
theorem objects_not_small (U : ZFSet.{u}) : U ∉ U := by
  intro h
  exact (lt_irrefl U.rank) (ZFSet.rank_lt_of_mem h)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    *   A set is \termuseas{U-small}{$U$-small} if it is an element of $U$, in the sense of §{sec:inaccessible-universes}.
    *   A category $\mathcal C$ is \termuseas{U-small}{$U$-small} if $\Ob{\mathcal C}$ is $U$-small and every hom-set
        $\HomSet{\mathcal C}{A}{B}$ is $U$-small.
    *   A category is \termdefineas{locally U-small}{locally $U$-small} if every $\HomSet{\mathcal C}{A}{B}$ is $U$-small,
        with $\Ob{\mathcal C}$ allowed to be a $U$-large set.
    *   The unsubscripted symbol $\SetCat$ denotes the category $\SetCatU$ of $U$-small sets and functions; it is locally
        $U$-small but not $U$-small.
-/
theorem setCategory_size :
    CategoryLocallySmall U U (fun x y => setFunctionHom x.val y.val) ∧
      ¬ CategorySmall U U (fun x y => setFunctionHom x.val y.val) :=
  ⟨fun x y => hU.setFunctionHom_mem x.property y.property,
    fun h => objects_not_small U h.1⟩

/-- Equivalence classes are actual sets of representatives. No selector is used. -/
noncomputable def relationClasses (S : ZFSet.{u}) (E : ZFSet.{u} → ZFSet.{u} → Prop) :
    ZFSet.{u} := ZFSet.range (fun f : S => S.sep (fun g => E f.val g))

lemma relationClasses_mem {S : ZFSet.{u}} (hS : S ∈ U)
    (E : ZFSet.{u} → ZFSet.{u} → Prop) : relationClasses S E ∈ U :=
  hU.range_mem hS _ (fun _ => hU.subset_mem hS ZFSet.sep_subset)

/-- Apply this to the subclass of functional relations and mutual entailment. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Whenever a subsection below says "category" without qualification, the reader may assume locally $U$-small. "Small"
    without qualification means $U$-small. For the realizability constructions of
    §{sec:realizability-pca}–§{sec:realizability-tripos} this is enough: the carrier of $K_1$ is $\NN \in U$, every assembly
    and tripos predicate uses $U$-small data, and the resulting effective topos $\EffCat$ is locally $U$-small.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    Setting $\mathcal C = \SetCatU$ and $\mathcal P = \mathcal P_{K_1}$ in the realizability tripos
    gives
    $$\EffCat \;:=\; \SetCatU[\mathcal P_{K_1}].$$
    An object of $\EffCat$ is a $U$-small set $I$ together with a $\mathcal P_{K_1}$-PER $\sim$, which one can read as: $I$
    is a set of *would-be elements*, and $\sim(i, j)$ specifies the realizers witnessing that $i$ and $j$ name the same
    actual element. The extent $E_\sim(i) = \sim(i, i)$ is the set of realizers of $i$, recovering the assembly perspective
    when $\sim$ is the equality PER. Each object and morphism uses $U$-small data, although the collection of all
    objects is $U$-large, so $\EffCat$ is locally $U$-small in the sense
    of §{sec:cat-universe}.
-/
lemma functionalRelationClasses_mem {I J A S : ZFSet.{u}}
    (hI : I ∈ U) (hJ : J ∈ U) (hA : A ∈ U)
    (hS : S ⊆ ZFSet.funs (ZFSet.prod I J) (ZFSet.powerset A))
    (E : ZFSet.{u} → ZFSet.{u} → Prop) : relationClasses S E ∈ U :=
  hU.relationClasses_mem
    (hU.subset_mem (hU.functions_mem (hU.product_mem hI hJ) (hU.powerset_mem hA)) hS) E

/-- Functional-relation homs are quotients of subclasses of this relation set.
Every such quotient is a family of subsets of the same small relation set. -/
lemma relationHomQuotient_mem {I J A Q : ZFSet.{u}}
    (hI : I ∈ U) (hJ : J ∈ U) (hA : A ∈ U)
    (hQ : Q ⊆ ZFSet.powerset (ZFSet.funs (ZFSet.prod I J) (ZFSet.powerset A))) :
    Q ∈ U :=
  hU.subset_mem
    (hU.powerset_mem (hU.functions_mem (hU.product_mem hI hJ) (hU.powerset_mem hA))) hQ

end IsGrothendieckUniverse
end PolishSpaceBook.SetTheoryModels
