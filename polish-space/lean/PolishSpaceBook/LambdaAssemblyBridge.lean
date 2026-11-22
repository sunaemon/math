module

public import PolishSpaceBook.Assemblies
public import PolishSpaceBook.LambdaAssemblies
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

/-! # The numerical instance of the general assembly category

The two assembly presentations have identical application graphs. Conversion
keeps underlying functions and every tracker, so the existing fully faithful
embedding can be reused without another proof about functional relations.
-/
namespace PolishSpaceBook.Assembly
open CategoryTheory
universe u

theorem numerical_application_iff (r a b : ℕ) :
    LambdaIndexPCA.indexPCA.application r a = Part.some b ↔ LambdaIndexPCA.App r a b := by
  rw [Part.eq_some_iff,LambdaIndexPCA.mem_indexPCA_iff]

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: prose
  excerpt: |
    For the numerical lambda-index PCA, the assemblies defined here and those in
    §{sec:tte-domains-eff-subcategories} have the same underlying sets, realization relations, and tracked
    functions. Changing the presentation keeps each tracker unchanged. Thus the fully faithful graph
    embedding proved there applies to $\AsmCat{K_1}$ as defined in this appendix.
-/
noncomputable def toNumerical : Assembly.{0,u} LambdaIndexPCA.indexPCA ⥤ LambdaIndexPCA.Assembly.{u} where
  obj X := {
    Carrier := X.Carrier
    realizes x := {a | X.realizes a x}
    inhabited := X.inhabited }
  map f := {
    toFun := f
    tracked := by
      obtain ⟨r,hr⟩ := f.tracked
      apply (LambdaIndexPCA.reduces_iff _ _).mpr
      exact ⟨r,fun x a ha => by
        obtain ⟨b,hb,hb'⟩ := hr x a ha
        exact ⟨b,(numerical_application_iff r a b).mp hb,hb'⟩⟩ }
  map_id _ := LambdaIndexPCA.Assembly.Hom.ext (fun _ => rfl)
  map_comp _ _ := LambdaIndexPCA.Assembly.Hom.ext (fun _ => rfl)

def fromNumericalObject (X : LambdaIndexPCA.Assembly.{u}) :
    Assembly.{0,u} LambdaIndexPCA.indexPCA where
  Carrier := X.Carrier
  realizes a x := a ∈ X.realizes x
  inhabited := X.inhabited

def toNumericalFullyFaithful : toNumerical.{u}.FullyFaithful where
  preimage f := {
    toFun := f.toFun
    tracked := by
      obtain ⟨r,hr⟩ := (LambdaIndexPCA.reduces_iff _ _).mp f.tracked
      exact ⟨r,fun x a ha => by
        obtain ⟨b,hb,hb'⟩ := hr x a ha
        exact ⟨b,(numerical_application_iff r a b).mpr hb,hb'⟩⟩ }
  map_preimage _ := LambdaIndexPCA.Assembly.Hom.ext (fun _ => rfl)
  preimage_map _ := Hom.ext (fun _ => rfl)

instance toNumericalFull : toNumerical.{u}.Full := toNumericalFullyFaithful.full
instance toNumericalFaithful : toNumerical.{u}.Faithful := toNumericalFullyFaithful.faithful

instance toNumericalEssSurj : toNumerical.{u}.EssSurj where
  mem_essImage X := ⟨fromNumericalObject X,⟨eqToIso (by cases X; rfl)⟩⟩

instance toNumericalIsEquivalence : toNumerical.{u}.IsEquivalence where

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
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the numerical lambda-index PCA, the assemblies defined here and those in
    §{sec:tte-domains-eff-subcategories} have the same underlying sets, realization relations, and tracked
    functions. Changing the presentation keeps each tracker unchanged. Thus the fully faithful graph
    embedding proved there applies to $\AsmCat{K_1}$ as defined in this appendix.
-/
noncomputable def numericalEquivalence :
    Assembly.{0,u} LambdaIndexPCA.indexPCA ≌ LambdaIndexPCA.Assembly.{u} := toNumerical.asEquivalence

/-- The general assembly API embeds into the chapter's actual functional-relation category. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the numerical lambda-index PCA, the assemblies defined here and those in
    §{sec:tte-domains-eff-subcategories} have the same underlying sets, realization relations, and tracked
    functions. Changing the presentation keeps each tracker unchanged. Thus the fully faithful graph
    embedding proved there applies to $\AsmCat{K_1}$ as defined in this appendix.
-/
noncomputable def numericalEmbedding :
    Assembly.{0,u} LambdaIndexPCA.indexPCA ⥤ LambdaIndexPCA.RealizerPER.{u} :=
  toNumerical ⋙ LambdaIndexPCA.Assembly.embedding

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the numerical lambda-index PCA, the assemblies defined here and those in
    §{sec:tte-domains-eff-subcategories} have the same underlying sets, realization relations, and tracked
    functions. Changing the presentation keeps each tracker unchanged. Thus the fully faithful graph
    embedding proved there applies to $\AsmCat{K_1}$ as defined in this appendix.
-/
instance numericalEmbeddingFull : numericalEmbedding.{u}.Full :=
  inferInstanceAs (toNumerical ⋙ LambdaIndexPCA.Assembly.embedding).Full

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    For the numerical lambda-index PCA, the assemblies defined here and those in
    §{sec:tte-domains-eff-subcategories} have the same underlying sets, realization relations, and tracked
    functions. Changing the presentation keeps each tracker unchanged. Thus the fully faithful graph
    embedding proved there applies to $\AsmCat{K_1}$ as defined in this appendix.
-/
instance numericalEmbeddingFaithful : numericalEmbedding.{u}.Faithful :=
  inferInstanceAs (toNumerical ⋙ LambdaIndexPCA.Assembly.embedding).Faithful

end PolishSpaceBook.Assembly
