module

public import PolishSpaceBook.PCADiscreteSubquotients
public import PolishSpaceBook.PCASubobjectNegation
public import Mathlib.CategoryTheory.Subobject.Lattice

@[expose] public section

/-! # Assemblies as dense categorical subobjects of constant objects

The predicate image used in the appendix is the image presentation of the
actual monomorphism in the PER category. Its double-negation closure is the
largest categorical subobject, using the existing supplied-name trackers.
-/
namespace PolishSpaceBook.PCARealizability.RealizerPER
open CategoryTheory
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}

/-- An extent-to-predicate tracker gives a section of the restriction inclusion. -/
theorem StrictPredicate.subobject_eq_top_of_extent {X : RealizerPER.{r,u} K}
    (P : StrictPredicate X) (h : K.Entails X.extent P.val) : P.subobject = ⊤ := by
  apply le_antisymm le_top
  rw [Subobject.top_eq_id]
  have he : K.Entails (fun p : X.Carrier × X.Carrier => X.rel p.1 p.2)
      (fun p => P.val p.2) := K.entails_trans (X.extent_right_of (K.entails_refl _))
        (K.reindex_entails Prod.snd h)
  exact Subobject.mk_le_mk_of_comm (P.lift (FunctionalRelation.identity X) he).toHom
    (Quotient.sound (P.lift_inclusion (FunctionalRelation.identity X) he))

end PolishSpaceBook.PCARealizability.RealizerPER

namespace PolishSpaceBook.Assembly
open CategoryTheory PCARealizability PCARealizability.RealizerPER
universe r u
variable {R : Type r} {K : PartialCombinatoryAlgebra R}

/-- The identity on underlying elements is monic even against arbitrary PER objects. -/
instance toConstant_realizer_mono (A : Assembly.{r,u} K) :
    Mono (C := RealizerPER K) (toConstant A).toFunctionalRelation.toHom :=
  assembly_graph_mono (toConstant A) (fun _ _ h => h)

/-- The earlier predicate image is the range predicate of this categorical graph. -/
theorem toConstant_image_predicate (A : Assembly.{r,u} K) :
    (toConstant A).toFunctionalRelation.imagePredicate.val = constantImage A := by
  funext y
  apply Set.ext
  intro a
  change (∃ x, ∃ b c, a = K.pair b c ∧ (x = x ∧ A.realizes b x) ∧ (x = y ∧ True)) ↔
    ∃ x, ∃ b c, a = K.pair b c ∧ A.realizes b x ∧ (x = y ∧ True)
  simp only [true_and]

/-- Its image presentation represents the monomorphism itself as a subobject. -/
theorem toConstant_subobject (A : Assembly.{r,u} K) :
    Subobject.mk (toConstant A).toFunctionalRelation.toHom =
      (toConstant A).toFunctionalRelation.imagePredicate.subobject :=
  Subobject.mk_eq_mk_of_comm _ _ (toConstant A).toFunctionalRelation.imageIso
    (toConstant A).toFunctionalRelation.imageIso_inclusion

/-- The existing density tracker, paired with the supplied extent, fills the closure. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For the earlier monomorphism from an assembly $X$ into the constant object $C$, the image predicate is $J$.
    Its closure is $E_C\land\neg\neg J$, where $E_C(y)=A$ for every $y$.
    Given a name $a\in E_C(y)$, the density tracker supplies a name $b\in(\neg\neg J)(y)$;
    pairing them gives a name of the closure. First projection gives the reverse entailment.
    By the subobject-order criterion, the closure of this monomorphism is therefore the whole object $C$.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Assembly equality and double negation.** Write $\neg\varphi:=\varphi\to\bot$.
    For an assembly $X$ over $A$, put
    $$\begin{aligned}
    E(x)&:=\{a\in A:a\Vdash_X x\},\\
    \delta(x,y)&:=\begin{cases}E(x),&x=y,\\\emptyset,&x\ne y,\end{cases}\\
    D(x,y)&:=E(x)\land E(y).
    \end{aligned}$$
    In the PER presentation, $\neg\neg$-separation says that equality is stable under double negation
    when the existence evidence for both arguments is retained:
    $$D\land\neg\neg\delta\le\delta.$$
    A monomorphism is $\neg\neg$-dense when double negation of its image predicate is the top predicate
    on its codomain.
-/
theorem toConstant_doubleNeg_closure_top (A : Assembly.{r,u} K) :
    (doubleNegClosureOperator (constant K A.Carrier).toRealizerPER)
      (Subobject.mk (toConstant A).toFunctionalRelation.toHom) = ⊤ := by
  rw [toConstant_subobject]
  change subobjectDoubleNeg _ = ⊤
  rw [subobjectDoubleNeg_predicate]
  apply StrictPredicate.subobject_eq_top_of_extent
  apply K.and_intro (K.entails_refl _)
  rw [toConstant_image_predicate]
  apply K.entails_trans (reduces_of_subset fun _ _ _ => Set.mem_univ _)
  exact constantImage_doubleNeg_dense A

/-- The assembly's stable equality and its actual dense monomorphism into the constant object. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: statement
  kind: proposition
  title: Double negation for assemblies
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
theorem dense_constant_embedding (A : Assembly.{r,u} K) :
    A.toRealizerPER.Separated ∧
      Mono (C := RealizerPER K) (toConstant A).toFunctionalRelation.toHom ∧
      (doubleNegClosureOperator (constant K A.Carrier).toRealizerPER)
        (Subobject.mk (toConstant A).toFunctionalRelation.toHom) = ⊤ :=
  ⟨assembly_separated A, inferInstance, toConstant_doubleNeg_closure_top A⟩

end PolishSpaceBook.Assembly
