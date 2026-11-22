module

public import PolishSpaceBook.ModestAssemblies
public import PolishSpaceBook.PCARealizabilityLogic

@[expose] public section

/-! # Double negation on assembly predicates

The stability entailment retains the ambient existence predicates. Its tracker
extracts an already supplied name; it never decides equality or chooses a name.
-/
namespace PolishSpaceBook.PartialCombinatoryAlgebra
universe u v
variable {A : Type u} (K : PartialCombinatoryAlgebra A) {I : Type v}

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
def predNeg (φ : RealizabilityPredicate A I) : RealizabilityPredicate A I :=
  K.predImp φ (fun _ => ∅)

theorem mem_predNeg_iff (φ : RealizabilityPredicate A I) (i : I) (a : A) :
    a ∈ K.predNeg φ i ↔ φ i = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨c,_,hc⟩ := h b hb
    exact hc
  · intro h b hb
    simp [h] at hb

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    For any predicate $\varphi$ and index $i$, the implication clause gives
    $$\begin{aligned}
    a\in(\neg\varphi)(i)&\quad\Longleftrightarrow\quad\varphi(i)=\emptyset,\\
    a\in(\neg\neg\varphi)(i)&\quad\Longleftrightarrow\quad\varphi(i)\ne\emptyset.
    \end{aligned}$$
    Indeed, no computation can return an element of the empty set, while an implication with empty domain
    has no input obligations. The second equivalence also uses that the PCA is nonempty. These are
    external descriptions of the realizer sets, not a procedure for deciding whether they are empty.
-/
theorem mem_doubleNeg_iff (φ : RealizabilityPredicate A I) (i : I) (a : A) :
    a ∈ K.predNeg (K.predNeg φ) i ↔ (φ i).Nonempty := by
  classical
  rw [K.mem_predNeg_iff]
  constructor
  · intro h
    by_contra hn
    have he : φ i = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hk := (K.mem_predNeg_iff φ i K.k).mpr he
    simp [h] at hk
  · rintro ⟨b,hb⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have he := (K.mem_predNeg_iff φ i c).mp hc
    simp [he] at hb

theorem entails_doubleNeg (φ : RealizabilityPredicate A I) :
    K.Entails φ (K.predNeg (K.predNeg φ)) :=
  ⟨K.identity,fun i a ha =>
    ⟨a,K.application_identity a,(K.mem_doubleNeg_iff φ i a).mpr ⟨a,ha⟩⟩⟩

theorem doubleNeg_dense (φ : RealizabilityPredicate A I) (h : ∀ i, (φ i).Nonempty) :
    K.Entails (fun _ => Set.univ) (K.predNeg (K.predNeg φ)) :=
  ⟨K.identity,fun i a _ =>
    ⟨a,K.application_identity a,(K.mem_doubleNeg_iff φ i a).mpr (h i)⟩⟩

end PartialCombinatoryAlgebra

namespace Assembly
open CategoryTheory
universe u v
variable {A : Type u} {K : PartialCombinatoryAlgebra A}

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
def existence (X : Assembly.{u,v} K) : RealizabilityPredicate A X.Carrier :=
  fun x => {a | X.realizes a x}

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
def diagonal (X : Assembly.{u,v} K) : RealizabilityPredicate A (X.Carrier × X.Carrier) :=
  fun p => {a | p.1 = p.2 ∧ X.realizes a p.1}

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
def pairExistence (X : Assembly.{u,v} K) : RealizabilityPredicate A (X.Carrier × X.Carrier) :=
  K.predAnd (fun p => existence X p.1) (fun p => existence X p.2)

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Since every element of an assembly has a realizer, $(\neg\neg\delta)(x,y)$ is $A$ when $x=y$
    and empty otherwise.
-/
theorem mem_doubleNeg_diagonal_iff (X : Assembly.{u,v} K) (x y : X.Carrier) (a : A) :
    a ∈ K.predNeg (K.predNeg (diagonal X)) (x,y) ↔ x = y := by
  rw [K.mem_doubleNeg_iff]
  constructor
  · rintro ⟨b,hb⟩
    exact hb.1
  · intro h
    obtain ⟨b,hb⟩ := X.inhabited x
    exact ⟨b,h,hb⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    An input realizer of $D\land\neg\neg\delta$ has the form
    $$\PCAPair{\PCAPair{a}{b}}{c},\qquad a\in E(x),\quad b\in E(y),\quad
    c\in(\neg\neg\delta)(x,y).$$
    The last membership implies $x=y$. Thus the tracker
    $$\PCAAbstract{w}{\mathsf l(\mathsf l w)}$$
    returns $a\in\delta(x,y)$, proving stability.
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
theorem diagonal_doubleNeg_stable (X : Assembly.{u,v} K) :
    K.Entails (K.predAnd (pairExistence X) (K.predNeg (K.predNeg (diagonal X))))
      (diagonal X) := by
  refine ⟨K.composition K.firstProjection K.firstProjection,?_⟩
  rintro ⟨x,y⟩ _ ⟨_,c,rfl,⟨a,b,rfl,ha,_⟩,hc⟩
  refine ⟨a,?_,(mem_doubleNeg_diagonal_iff X x y c).mp hc,ha⟩
  rw [K.application_composition,K.application_firstProjection,Part.bind_some,K.application_firstProjection]

/-- Every name realizes every element of a constant assembly. -/
def constant (K : PartialCombinatoryAlgebra A) (S : Type v) : Assembly.{u,v} K where
  Carrier := S
  realizes _ _ := True
  inhabited _ := ⟨K.k,trivial⟩

def toConstant (X : Assembly.{u,v} K) : X ⟶ constant K X.Carrier where
  toFun := id
  tracked := ⟨K.identity,fun _ a _ => ⟨a,K.application_identity a,trivial⟩⟩

instance toConstant_mono (X : Assembly.{u,v} K) : Mono (toConstant X) :=
  (mono_iff_injective (toConstant X)).mpr (fun _ _ h => h)

theorem doubleNeg_diagonal_eq_constant (X : Assembly.{u,v} K) :
    K.predNeg (K.predNeg (diagonal X)) = diagonal (constant K X.Carrier) := by
  funext p
  apply Set.ext
  intro a
  change a ∈ K.predNeg (K.predNeg (diagonal X)) (p.1,p.2) ↔ p.1 = p.2 ∧ True
  rw [mem_doubleNeg_diagonal_iff]
  simp only [and_true]

/-- Reflection of equality, with both source extents retained, is the PER monicity criterion. -/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    The identity combinator tracks the underlying identity
    map into $C$. Equality in $C$ is exactly $\neg\neg\delta$, so the same tracker reflects equality
    on the two source extents; this is the monomorphism condition in the PER presentation.
-/
theorem constant_diagonal_reflects (X : Assembly.{u,v} K) :
    K.Entails (K.predAnd (pairExistence X) (diagonal (constant K X.Carrier))) (diagonal X) := by
  rw [← doubleNeg_diagonal_eq_constant X]
  exact diagonal_doubleNeg_stable X

/-- The graph of the canonical map into the constant object. -/
def constantGraph (X : Assembly.{u,v} K) (x y : X.Carrier) : Set A :=
  K.predAnd (existence X) (fun z => diagonal (constant K X.Carrier) (z,y)) x

def constantImage (X : Assembly.{u,v} K) : RealizabilityPredicate A X.Carrier :=
  fun y => {a | ∃ x, a ∈ constantGraph X x y}

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Let $\delta_C$ denote equality in $C$. The image predicate of this map is
    $$J(y):=\bigcup_{x\in|X|}\bigl(E(x)\land\delta_C(x,y)\bigr).$$
    A realizer in this union is a pair whose first component realizes $x$ and whose second component
    forces $x=y$. First projection therefore tracks $J\le E$.
-/
theorem constantImage_entails_existence (X : Assembly.{u,v} K) :
    K.Entails (constantImage X) (existence X) := by
  refine ⟨K.firstProjection,?_⟩
  rintro y _ ⟨x,a,b,rfl,ha,hab⟩
  have hxy : x = y := hab.1
  subst y
  exact ⟨a,K.application_firstProjection a b,ha⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Conversely,
    $\PCAAbstract{a}{\PCAPair{a}{a}}$ tracks $E\le J$, using the witness $x=y$ in the union.
-/
theorem existence_entails_constantImage (X : Assembly.{u,v} K) :
    K.Entails (existence X) (constantImage X) := by
  refine ⟨K.paired K.identity K.identity,fun x a ha => ?_⟩
  exact ⟨K.pair a a,K.application_paired (K.application_identity a) (K.application_identity a),
    x,a,a,rfl,ha,rfl,trivial⟩

/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  target: proof
  excerpt: |
    Thus the image predicate is uniformly equivalent to $E$. Each of its values is nonempty, so
    $(\neg\neg J)(y)=A$ for every $y$. The identity combinator consequently tracks
    $\top\le\neg\neg J$, proving density. All these programs use supplied names; none selects a realizer
    from an external element.
-/
theorem constantImage_doubleNeg_dense (X : Assembly.{u,v} K) :
    K.Entails (fun _ => Set.univ) (K.predNeg (K.predNeg (constantImage X))) := by
  apply K.doubleNeg_dense
  intro x
  obtain ⟨a,ha⟩ := X.inhabited x
  exact ⟨K.pair a a,x,a,a,rfl,ha,rfl,trivial⟩

theorem existence_doubleNeg_dense (X : Assembly.{u,v} K) :
    K.Entails (fun _ => Set.univ) (K.predNeg (K.predNeg (existence X))) :=
  K.doubleNeg_dense (existence X) X.inhabited

end Assembly
end PolishSpaceBook
