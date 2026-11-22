module

public import PolishSpaceBook.LambdaAssemblies
public import PolishSpaceBook.LambdaComputableNames
public import PolishSpaceBook.LambdaRealizers

@[expose] public section

/-! # Computable-point assemblies and uniform lambda index transformations

A name index computes every coordinate. The index transformer constructs syntax
for applying the fixed Type-Two program to the universal evaluator at that index.
It never evaluates a name merely to construct its transformed index.
-/
namespace PolishSpaceBook.LambdaIndexPCA
open NamedLambda NamedLambda.AlphaTerm
universe u v

/-- The index supplies the whole name, with no extra oracle. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A point $p\in\BaireSpace$ is \termdefineas{computable point}{computable} if some index $e$ computes its digits, so
    $\varphi_e(n)=p(n)$ for every $n$. A partial map $\PartialFunctionMap{F}{\BaireSpace}{\BaireSpace}$ is a
    \termdefine{computable map on Baire space} if it has a Type-Two lambda realizer in the preceding definition. Thus the
    same closed term computes every output coordinate at every point of the specified domain. It may also produce outputs
    outside that domain.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Polish spaces and TTE in realizability.** A \termuse{computable Polish space} $X$ in the sense of
    §{sec:computable-polish-tte} has a Cauchy representation $\PartialFunctionMap{\rho_X}{\BaireSpace}{X}$ with range all of
    $X$. Over $K_1$, however, realizers are natural-number indices for computable procedures. Thus the direct
    \termuse{assembly} attached to $\rho_X$ has as underlying set the **computable points** of $X$: an index $e$ realizes
    $x$ when $e$ computes a total $\rho_X$-name for $x$. This is a modest assembly because two distinct points cannot share
    the same Cauchy name, but it does not contain the noncomputable external points of $X$ as elements.
-/
def ComputesName (e : ℕ) (p : ℕ → ℕ) : Prop := ∀ n, App e n (p n)

theorem ComputesName.unique {e : ℕ} {p q : ℕ → ℕ}
    (hp : ComputesName e p) (hq : ComputesName e q) : p = q :=
  funext fun n => app_unique (hp n) (hq n)

theorem ComputesName.eval {e : ℕ} {p : ℕ → ℕ} (h : ComputesName e p) :
    NumericalComputes (evalProgram e) p :=
  ⟨evalProgram_closed e, fun n => (evalProgram_runs_iff e n (p n)).mpr (h n)⟩

/-- A total syntax transformation, with the exact closed program it constructs. -/
theorem application_indices (P : AlphaTerm) (hP : P.Closed) :
    ∃ t : ℕ → ℕ, (∃ k, ∀ e, App k e (t e)) ∧
      ∀ e, Term.closedProgram (t e) = app P (evalProgram e) := by
  obtain ⟨M,hM⟩ := Quotient.exists_rep P
  obtain ⟨U,hU⟩ := Quotient.exists_rep outputSearchTerm
  have hM' : mk M = P := hM
  have hU' : mk U = outputSearchTerm := hU
  let t (e : ℕ) := (Term.app M (Term.app U (Term.churchNumeral e))).code
  have hn : NumericalComputes numeralCodeTerm (fun e => (Term.churchNumeral e).code) :=
    ⟨numeralCodeTerm_closed,numeralCodeTerm_apply⟩
  have ht := (numericalConstant_computes M.code).applicationCode
    ((numericalConstant_computes U.code).applicationCode hn)
  obtain ⟨k,hk⟩ := Term.closedProgram_surjective _ ht.1
  refine ⟨t,⟨k,fun e => ?_⟩,fun e => ?_⟩
  · unfold App
    rw [hk]
    exact ht.2 e
  · have hm : mk (Term.app M (Term.app U (Term.churchNumeral e))) =
        app P (evalProgram e) := by
      change app (mk M) (app (mk U) (mk (Term.churchNumeral e))) = _
      rw [hM',hU',Term.mk_churchNumeral]
      rfl
    have hc := closed_app hP (evalProgram_closed e)
    exact (closedProgram_code_of_closed _ (hm.symm ▸ hc)).trans hm


/-- Code generation is total on all indices; correctness only needs valid names. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: lemma
  title: From name transformers to index transformers
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    Put $U:=\LambdaOutputSearch$, the universal evaluator from §{sec:lambda-output-search}, and choose
    fixed named representatives of $P,U$. The term $U\ChurchNumeral{e}$ computes the same numerical partial function
    as index $e$. Define
    $$t(e):=\LambdaSyntaxCode{P(U\ChurchNumeral{e})}.$$
    This is a computation of finite syntax. More explicitly, put $c(a,b):=3\NatPair{a}{b}+1$, the application-code
    constructor. Then
    $$t(e)=c\bigl(\LambdaSyntaxCode{P},c(\LambdaSyntaxCode{U},\LambdaSyntaxCode{\ChurchNumeral{e}})\bigr).$$
    The closed programs $\LambdaNumeralCodeProgram$ and $\LambdaTaggedCode{1}$, together with constant programs and
    composition, compute this formula on every input $e$. No name is executed during this code construction.

    Suppose now that $\varphi_e=p\in D$. Substitute the closed numerical program $U\ChurchNumeral{e}$ for the oracle
    in the computation of $P$ on $p$. Each oracle query at $n$ is replaced by its finite beta reduction to
    $\ChurchNumeral{p(n)}$. The substitution argument in §{sec:lambda-input-composition} gives
    $$P(U\ChurchNumeral{e})\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{F(p)(n)}.$$
    The term whose code is $t(e)$ is closed. Decoding that code therefore gives precisely this program, proving the
    claimed equality of total names.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    In particular, this embeds \termforwardas{modest set}{modest} assemblies, in which each realizer realizes at most
    one element. We next construct the assembly associated with a represented space and the numerical tracker induced
    by a Type-Two realizer.
-/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This is the external TTE formulation. §{sec:effective-topos} instead uses natural-number realizers.
    A TTE realizer induces a recursive transformation of indices for computable names, hence a morphism
    between computable-point assemblies as in §{sec:inside-effective-topos}. This translation does not
    identify arbitrary external names with natural-number indices.
-/
theorem typeTwo_index_transform {D : Set (ℕ → ℕ)} {F : D → (ℕ → ℕ)}
    {P : AlphaTerm} (hP : TypeTwoComputes P F) :
    ∃ t : ℕ → ℕ, (∃ k, ∀ e, App k e (t e)) ∧
      ∀ (p : D) e, ComputesName e p.val → ComputesName (t e) (F p) := by
  obtain ⟨t,ht,hprogram⟩ := application_indices P hP.1
  refine ⟨t,ht,fun p e he n => ?_⟩
  unfold App
  rw [hprogram]
  exact (hP.numerical_output p he.eval).2 n

/-- A point has an index for a total name in the representation domain. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    A \termuse{represented space} is a set $X$ together with a partial surjection
    $\PartialFunctionMap{\delta_X}{\BaireSpace}{X}$. A name of $x$ is a point $p\in\DomainOf{\delta_X}$ with
    $\delta_X(p)=x$. A point $x$ is \termdefineas{computable point in represented space}{computable} if it has a computable
    name.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Polish spaces and TTE in realizability.** A \termuse{computable Polish space} $X$ in the sense of
    §{sec:computable-polish-tte} has a Cauchy representation $\PartialFunctionMap{\rho_X}{\BaireSpace}{X}$ with range all of
    $X$. Over $K_1$, however, realizers are natural-number indices for computable procedures. Thus the direct
    \termuse{assembly} attached to $\rho_X$ has as underlying set the **computable points** of $X$: an index $e$ realizes
    $x$ when $e$ computes a total $\rho_X$-name for $x$. This is a modest assembly because two distinct points cannot share
    the same Cauchy name, but it does not contain the noncomputable external points of $X$ as elements.
-/
def HasComputableName {X : Type u} (δ : Representation X) (x : X) : Prop :=
  ∃ p : δ.domain, δ.toFun p = x ∧ ∃ e, ComputesName e p.val

/-- The support is restricted to points which actually have realizers. -/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: prose
  excerpt: |
    For a representation $\delta$ of $X$, let $A_\delta$ have underlying set
    $$|A_\delta|:=\{x\in X:\exists p\in\DomainOf\delta\ \exists e\in\NN\ (\delta(p)=x\ \land\ \varphi_e=p)\}$$
    and realization relation
    $$e\Vdash_{A_\delta}x\quad\Longleftrightarrow\quad
      \exists p\in\DomainOf\delta\ (\delta(p)=x\ \land\ \varphi_e=p).$$
    These are exactly the \termforwardas{computable point in represented space}{computable points} for $\delta$.
    Every such point has a realizer by definition. For a computable Polish space, take $\delta=\rho_X$.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Polish spaces and TTE in realizability.** A \termuse{computable Polish space} $X$ in the sense of
    §{sec:computable-polish-tte} has a Cauchy representation $\PartialFunctionMap{\rho_X}{\BaireSpace}{X}$ with range all of
    $X$. Over $K_1$, however, realizers are natural-number indices for computable procedures. Thus the direct
    \termuse{assembly} attached to $\rho_X$ has as underlying set the **computable points** of $X$: an index $e$ realizes
    $x$ when $e$ computes a total $\rho_X$-name for $x$. This is a modest assembly because two distinct points cannot share
    the same Cauchy name, but it does not contain the noncomputable external points of $X$ as elements.
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    The $K_1$ construction above instead retains only computable
    points.
-/
def computablePointAssembly {X : Type u} (δ : Representation X) : Assembly.{u} where
  Carrier := {x : X // HasComputableName δ x}
  realizes x := {e | ∃ p : δ.domain, δ.toFun p = x.val ∧ ComputesName e p.val}
  inhabited x := by
    obtain ⟨p,hp,e,he⟩ := x.property
    exact ⟨e,p,hp,he⟩

/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: statement
  kind: proposition
  title: Computable-point assemblies
-/
/-@ booklink:
  source: polish-space-book/inside-effective-topos.md
  target: proof
  excerpt: |
    \begin{proof}[Proof]
    If an index realizes both $x$ and $y$, uniqueness of numerical outputs makes the two names equal coordinatewise.
    Applying $\delta$ gives $x=y$, proving modesty. Let $F$ realize $f$, and let $t$ be the index transformer in the
    preceding lemma. If $e$ realizes $x$ via a name $p$, then $t(e)$ computes the valid name $F(p)$, and
    $$\delta_Y(F(p))=f(\delta_X(p))=f(x).$$
    Thus $f(x)$ is a computable point, and one index computing $t$ tracks the restricted function for every input
    realizer. The underlying functions of the induced identity and composite are the identity and composite of the
    restricted functions. Assembly morphisms are determined by these functions, so the two functor laws follow.
    \end{proof}
-/
/-@ booklink:
  source: polish-space-book/appendix-category-theory-realizability.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    **Polish spaces and TTE in realizability.** A \termuse{computable Polish space} $X$ in the sense of
    §{sec:computable-polish-tte} has a Cauchy representation $\PartialFunctionMap{\rho_X}{\BaireSpace}{X}$ with range all of
    $X$. Over $K_1$, however, realizers are natural-number indices for computable procedures. Thus the direct
    \termuse{assembly} attached to $\rho_X$ has as underlying set the **computable points** of $X$: an index $e$ realizes
    $x$ when $e$ computes a total $\rho_X$-name for $x$. This is a modest assembly because two distinct points cannot share
    the same Cauchy name, but it does not contain the noncomputable external points of $X$ as elements.
-/
theorem computablePointAssembly_modest {X : Type u} (δ : Representation X) :
    (computablePointAssembly δ).IsModest := by
  rintro x y e ⟨p,hp,he⟩ ⟨q,hq,he'⟩
  have hpq : p = q := Subtype.ext (he.unique he')
  exact Subtype.ext (hp.symm.trans ((congrArg δ.toFun hpq).trans hq))

/-- The same output name proves that the image point belongs to the support. -/
theorem hasComputableName_map {X : Type u} {Y : Type v}
    {δX : Representation X} {δY : Representation Y} {f : X → Y}
    (hf : HasComputableRealizer δX δY f) {x : X} (hx : HasComputableName δX x) :
    HasComputableName δY (f x) := by
  obtain ⟨F,⟨P,hP⟩,hF⟩ := hf
  obtain ⟨t,_,ht⟩ := typeTwo_index_transform hP
  obtain ⟨p,hp,e,he⟩ := hx
  exact ⟨F p,(hF p).trans (congrArg f hp),t e,ht p e he⟩

/-- A Type-Two computable map induces an assembly morphism with a numerical tracker. -/
/-@ booklink:
  source: polish-space-book/appendix-type-two-computation.md
  exclude-books: polish-space-ch1
  target: prose
  excerpt: |
    This is the external TTE formulation. §{sec:effective-topos} instead uses natural-number realizers.
    A TTE realizer induces a recursive transformation of indices for computable names, hence a morphism
    between computable-point assemblies as in §{sec:inside-effective-topos}. This translation does not
    identify arbitrary external names with natural-number indices.
-/
def computablePointMap {X Y : Type u}
    {δX : Representation X} {δY : Representation Y} {f : X → Y}
    (hf : HasComputableRealizer δX δY f) :
    Assembly.Hom (computablePointAssembly δX) (computablePointAssembly δY) where
  toFun x := ⟨f x.val,hasComputableName_map hf x.property⟩
  tracked := by
    obtain ⟨F,⟨P,hP⟩,hF⟩ := hf
    obtain ⟨t,⟨k,hk⟩,ht⟩ := typeTwo_index_transform hP
    apply (reduces_iff _ _).mpr
    refine ⟨k,fun x e he => ?_⟩
    obtain ⟨p,hp,he⟩ := he
    exact ⟨t e,hk e,F p,(hF p).trans (congrArg f hp),ht p e he⟩

theorem computablePointMap_id {X : Type u} (δ : Representation X) :
    computablePointMap (hasComputableRealizer_id δ) = Assembly.Hom.id _ := by
  apply Assembly.Hom.ext
  intro x
  exact Subtype.ext rfl

theorem computablePointMap_comp {X Y Z : Type u}
    {δX : Representation X} {δY : Representation Y} {δZ : Representation Z}
    {f : X → Y} {g : Y → Z} (hf : HasComputableRealizer δX δY f)
    (hg : HasComputableRealizer δY δZ g) :
    computablePointMap (hg.comp hf) =
      (computablePointMap hf).comp (computablePointMap hg) := by
  apply Assembly.Hom.ext
  intro x
  exact Subtype.ext rfl

end PolishSpaceBook.LambdaIndexPCA
