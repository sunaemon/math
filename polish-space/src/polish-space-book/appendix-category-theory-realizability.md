# Appendix: Category Theory and Realizability {#sec:appendix-category-realizability}
\index{realizability}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
付録の目的・依存関係・読者への導入で、新しい構成や証明を置く段落ではない。任意PCA上の個々の構成は後続の命題・証明で別に監査した。)
--> This appendix supplies the general categorical and realizability infrastructure for
§{sec:domain-theory-quasi-polish}, §{sec:effective-topos}, and §{sec:inside-effective-topos}.
It fixes the vocabulary and proves the constructions that work over an arbitrary partial combinatory algebra.
The effective-topos chapters specialize this infrastructure to numerical lambda-program indices and carry out the
concrete PER calculations. None of this background is needed for the classical descriptive set theory of the earlier
chapters.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
四段階の章構成と参照先の案内。各節の実際の定義・構成・証明は別に接続し、この導入から一括して形式化済みとは扱わない。)
--> The appendix has four stages. §{sec:cat-language} introduces the language of
\termdefine{category theory} and fixes the universe convention. §{sec:cat-structure} records the universal
properties and internal logic used to recognize a topos. §{sec:realizability-data} develops partial combinatory
algebras, assemblies, and modest sets. §{sec:realizability-tripos} constructs predicates and PERs over a general
PCA, including the assembly and modest-presentation results needed for comparison with TTE.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
具体的な有効トポスの読む順序とMac Lane、Mac Lane–Moerdijk、van Oostenへの文献案内。
参照先の数学的主張は独立の監査対象であり、この案内には追加の局所的証明がない。)
--> For the concrete effective topos, begin with the Kleene predicates in §{sec:effective-topos-construction},
then follow the objects, arrows, and finite limits in §{sec:effective-topos-objects-morphisms} and
§{sec:effective-topos-finite-limits}. The classifier and exponential calculations in
§{sec:effective-topos-subobjects-truth-values}–§{sec:effective-topos-topos-theorem} establish the topos structure.
§{sec:inside-effective-topos} then uses that structure for computable-point assemblies and internal principles.
Standard references are [@MacLane1998] for categories, [@MacLaneMoerdijk1992] for toposes and sheaves, and
[@vanOosten2008] for realizability.<!--
formalization: skip-end
-->

## Categorical Language and Size {#sec:cat-language}

### Size and universe convention {#sec:cat-universe}

Fix a Grothendieck universe $U$ with $\omega \in U$, in the sense of §{sec:inaccessible-universes}. The size conventions
for the rest of this appendix are:
\begin{mathmeta}
  \define{Ob}
  \define{HomSet}
\end{mathmeta}

*   A set is \termuseas{U-small}{$U$-small} if it is an element of $U$, in the sense of §{sec:inaccessible-universes}.
*   A category $\mathcal C$ is \termuseas{U-small}{$U$-small} if $\Ob{\mathcal C}$ is $U$-small and every hom-set
    $\HomSet{\mathcal C}{A}{B}$ is $U$-small.
*   A category is \termdefineas{locally U-small}{locally $U$-small} if every $\HomSet{\mathcal C}{A}{B}$ is $U$-small,
    with $\Ob{\mathcal C}$ allowed to be a $U$-large set.
*   The unsubscripted symbol $\SetCat$ denotes the category $\SetCatU$ of $U$-small sets and functions; it is locally
    $U$-small but not $U$-small.

Whenever a subsection below says "category" without qualification, the reader may assume locally $U$-small. "Small"
without qualification means $U$-small. For the realizability constructions of
§{sec:realizability-pca}–§{sec:realizability-tripos} this is enough: the carrier of $K_1$ is $\NN \in U$, every assembly
and tripos predicate uses $U$-small data, and the resulting effective topos $\EffCat$ is locally $U$-small.

### Categories, functors, and natural transformations {#sec:cat-basics}
\index{category}
\index{functor}
\index{natural transformation}

A \termdefine{category} $\mathcal C$ consists of:

*   a set $\Ob{\mathcal C}$ of \termdefineas{category object}{objects} $A, B, C, \ldots$;
*   for each ordered pair $\Pair{A}{B}$ of objects, a set $\HomSet{\mathcal C}{A}{B}$ of
    \termdefineas{category morphism}{morphisms} or \termdefineas{category arrow}{arrows} $f : A \to B$;
*   for each object $A$, an \termdefine{identity morphism} $\mathrm{id}_A : A \to A$;
*   for each triple $\Tuple{A, B, C}$, a \termdefine{composition} map $\HomSet{\mathcal C}{B}{C} \times \HomSet{\mathcal
    C}{A}{B} \to \HomSet{\mathcal C}{A}{C}$, written $\Pair{g}{f} \mapsto g \circ f$;

subject to the \termdefineas{identity law}{identity laws} $f \circ \mathrm{id}_A = f = \mathrm{id}_B \circ f$ for $f : A
\to B$ and the \termdefine{associativity law} $h \circ (g \circ f) = (h \circ g) \circ f$. The hom-set $\HomSet{\mathcal
C}{A}{B}$ is also written $\mathrm{Hom}_{\mathcal C}(A, B)$. By §{sec:cat-universe} the categories in this appendix are
locally $U$-small, with $\Ob{\mathcal C}$ either $U$-small or $U$-large.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
集合の関数三つ組はSetTheoryCategorySize、assemblyの関数と存在的trackerはAssemblies、
関係の商による射はPCARealizabilityPERに狭い抜粋で接続した。残りはTop、Pol、domain、Meas、
Catという標準的な圏の例の列挙で、ここで各圏の新しい構成や性質の証明を提示していない。)
--> The basic examples are:
\begin{mathmeta}
  \define{TopCat,PolCat,DomOmegaCat,MesCat,CatCat}
\end{mathmeta}<!--
formalization: skip-end
-->
$\SetCat$ (sets and functions, where a function is a triple consisting of a graph, a domain, and a codomain)<!--
formalization: skip-begin (引用・背景説明・読書案内:
集合の関数三つ組はSetTheoryCategorySize、assemblyの関数と存在的trackerはAssemblies、
関係の商による射はPCARealizabilityPERに狭い抜粋で接続した。残りはTop、Pol、domain、Meas、
Catという標準的な圏の例の列挙で、ここで各圏の新しい構成や性質の証明を提示していない。)
--> , $\TopCat$
(topological spaces and continuous maps), $\PolCat$ (Polish spaces and continuous maps), $\DomOmegaCat$
($\omega$-continuous dcpos and Scott-continuous maps), $\MesCat$ (measurable spaces and measurable maps), and $\CatCat$
($U$-small categories and functors). The morphisms here are the standard structure-preserving maps;<!--
formalization: skip-end
-->  assembly
morphisms in §{sec:realizability-assemblies} are also underlying functions, with trackers
required to exist. The functional-relation presentation of the topos in §{sec:realizability-tripos} gives
morphisms as equivalence classes of relations instead.

A morphism $f : A \to B$ is an \termdefine{isomorphism} if there exists $g : B \to A$ with $g \circ f = \mathrm{id}_A$
and $f \circ g = \mathrm{id}_B$. A \termdefine{monomorphism} (or \termuseas{monomorphism}{mono}) is a left-cancellative
arrow: $f \circ g = f \circ g'$ implies $g = g'$. An \termdefine{epimorphism} is right-cancellative.

\begin{mathmeta}
  \define{opcat}
\end{mathmeta}
The \termdefineas{opposite category}{opposite category} $\opcat{\mathcal C}$ has the same objects and reverses arrows:
$\HomSet{\opcat{\mathcal C}}{A}{B} = \HomSet{\mathcal C}{B}{A}$, with composition reversed. The
\termdefine{product category} $\mathcal C \times \mathcal D$ has pairs of objects and pairs of morphisms, composed
coordinate-wise.

**Functors.** A \termdefine{functor} $F : \mathcal C \to \mathcal D$ assigns to each object $A$ of $\mathcal C$ an
object $F(A)$ of $\mathcal D$, and to each morphism $f : A \to B$ a morphism $F(f) : F(A) \to F(B)$, in such a way that
$F(\mathrm{id}_A) = \mathrm{id}_{F(A)}$ and $F(g \circ f) = F(g) \circ F(f)$. A \termdefine{contravariant functor}
$\mathcal C \to \mathcal D$ is the same data as a functor $\opcat{\mathcal C} \to \mathcal D$.

For each object $A$, the \termdefine{representable functor} $\HomSet{\mathcal C}{A}{-} : \mathcal C \to \SetCat$ sends
$B$ to the hom-set $\HomSet{\mathcal C}{A}{B}$ and $f : B \to B'$ to post-composition $f_* : g \mapsto f \circ g$.
Dually, $\HomSet{\mathcal C}{-}{A} : \opcat{\mathcal C} \to \SetCat$ uses pre-composition.

**Natural transformations.** Given functors $F, G : \mathcal C \to \mathcal D$, a \termdefine{natural transformation}
$\eta : F \Rightarrow G$ assigns to each object $A$ of $\mathcal C$ a morphism $\eta_A : F(A) \to G(A)$ of $\mathcal D$
— its \termdefineas{component of a natural transformation}{component} at $A$ — such that for every $f : A \to B$ the
\termdefine{naturality square} commutes:
$$G(f) \circ \eta_A \;=\; \eta_B \circ F(f).$$
A natural transformation whose every component is an isomorphism is a \termdefine{natural isomorphism}, written $\eta :
F \cong G$.

\begin{mathmeta}
  \define{functorCat}
\end{mathmeta}

The collection of functors $\mathcal C \to \mathcal D$ together with natural transformations forms a category
$\functorCat{\mathcal C}{\mathcal D}$, the **functor category**. When both categories are $U$-small, it is the
exponential object of
$\mathcal C$ and $\mathcal D$ in $\CatCat$. When $\mathcal C$ is $U$-small and $\mathcal D$ is locally
$U$-small, $\functorCat{\mathcal C}{\mathcal D}$
is again locally $U$-small.

The **Yoneda lemma** is the basic structural fact: for any locally $U$-small $\mathcal C$, any functor $F : \mathcal C
\to \SetCat$, and any object $A$ of $\mathcal C$, evaluation at $\mathrm{id}_A$ gives a bijection
$$\HomSet{\functorCat{\mathcal C}{\SetCat}}{\HomSet{\mathcal C}{A}{-}}{F} \;\cong\; F(A),$$
natural in both arguments. In particular, when $\mathcal C$ is $U$-small, $A \mapsto \HomSet{\mathcal C}{A}{-}$ embeds
$\opcat{\mathcal C}$ fully and faithfully into the functor category $\functorCat{\mathcal C}{\SetCat}$.

### Subcategories, equivalences, and adjunctions {#sec:cat-equivalences}

A \termdefine{subcategory} $\mathcal C' \IncludedIn \mathcal C$ is a category whose objects and morphisms are subsets of
those of $\mathcal C$, with composition and identities inherited from $\mathcal C$. It is
\termdefineas{full subcategory}{full} when $\HomSet{\mathcal C'}{A}{B} = \HomSet{\mathcal C}{A}{B}$ for every pair of
objects of $\mathcal
C'$, so the only choice in defining $\mathcal C'$ is which objects to include. <!--
formalization: skip-begin (引用・背景説明・読書案内:
一般の対象・射の制限は標準MorphismPropertyによるSubcategoryObjects、
充満部分圏はObjectProperty.FullSubcategoryに接続した。残るTop上のPolという例は標準圏の命名例で、
この段落でPolish空間の新しい性質を証明しない。)
--> The full subcategory of $\TopCat$ on
Polish spaces is $\PolCat$.<!--
formalization: skip-end
-->

A functor $F : \mathcal C \to \mathcal D$ is \termdefine{faithful} when each induced map $\HomSet{\mathcal C}{A}{B} \to
\HomSet{\mathcal D}{F(A)}{F(B)}$ is injective, \termdefineas{full functor}{full} when it is surjective, and
\termdefine{essentially surjective} when every object of $\mathcal D$ is isomorphic to some $F(A)$.

**Equivalences.** A functor $F : \mathcal C \to \mathcal D$ is an \termdefine{equivalence of categories} if there exists
a functor $G : \mathcal D \to \mathcal C$ together with natural isomorphisms $G \circ F \cong \mathrm{id}_{\mathcal C}$
and $F \circ G \cong \mathrm{id}_{\mathcal D}$. Equivalently, $F$ is full, faithful, and essentially surjective. The
unit and counit of an adjoint equivalence give the displayed natural isomorphisms.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
同値が構造を保存するという標準的な圏論の概説。章頭で参照するMac Laneの背景理論であり、この付録の局所的な構成の証明として提示されていない。
具体的なPERとmodest assemblyの同値は別の定理と証明で接続済み。)
--> Equivalence is the appropriate notion of sameness for categories. Two equivalent categories share every property
invariant under iso-replacement of objects, including the existence and shape of all limits, exponentials, and the
subobject classifier introduced below.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \define{adjunction}
\end{mathmeta}

**Adjunctions.** A functor $F : \mathcal C \to \mathcal D$ is \termdefine{left adjoint} to a functor $U : \mathcal D \to
\mathcal C$, written $\adjunction{F}{U}$, when there is a bijection
$$\HomSet{\mathcal D}{F(A)}{B} \;\cong\; \HomSet{\mathcal C}{A}{U(B)}$$
natural in $A$ and $B$. The natural transformation $\eta : \mathrm{id}_{\mathcal C} \Rightarrow U \circ F$ obtained by
transposing the identities $\mathrm{id}_{F(A)}$ is the \termdefineas{adjunction unit}{unit}; the natural transformation
$\varepsilon : F \circ U \Rightarrow \mathrm{id}_{\mathcal D}$ obtained dually is the
\termdefineas{adjunction counit}{counit}. The two satisfy the \termdefineas{triangle identity}{triangle identities}
$\varepsilon F \circ F \eta=
\mathrm{id}_F$ and $U \varepsilon \circ \eta U = \mathrm{id}_U$.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
自由・忘却、離散位相の例と随伴関手定理を紹介する標準背景。Mac Laneに委ねる一般理論で、付録でsolution-set
theoremや局所可呈示性を構成・証明してはいない。局所的に必要なassembly exponentialの随伴は別に証明済み。)
--> Adjunctions encode universal constructions. The free–forgetful pairs in algebra, the discrete-topology and
underlying-set functors, and the cartesian-closed exponential adjunction $\adjunction{- \times A}{(-)^A}$ used below are
all instances. The slogan is that left adjoints preserve colimits and right adjoints preserve limits, and in the
presence of a solution-set condition every limit-preserving functor between locally presentable categories has a left
adjoint.<!--
formalization: skip-end
-->

## Categorical Structure and Internal Logic {#sec:cat-structure}

### Limits, exponentials, and cartesian closure {#sec:cat-ccc}

**Terminal objects and products.** A \termdefine{terminal object} $1 \in \mathcal C$ is one such that for every $A$
there is a unique morphism $A \to 1$. Terminal objects are unique up to unique isomorphism. <!--
formalization: skip-begin (引用・背景説明・読書案内:
終対象の定義と一意性はcanonical IsTerminalとuniqueUpToIsoへ接続した。
未リンク部分は集合・位相空間の1点対象という標準例だけで、新しい局所的構成の証明を示す箇所ではない。)
--> In $\SetCat$ a singleton is
terminal; in $\TopCat$ a one-point space is.<!--
formalization: skip-end
-->

A \termdefine{binary product} of $A$ and $B$ is an object $A \times B$ together with projections $\pi_A : A \times B \to
A$ and $\pi_B : A \times B \to B$ such that for every pair of arrows $f : C \to A$, $g : C \to B$ there is a unique
$\Pairing{f}{g} : C \to A \times B$ with $\pi_A \circ \Pairing{f}{g} = f$ and $\pi_B \circ \Pairing{f}{g}
= g$. Finite products are built from binary products and the terminal object.

**General limits.** For a $U$-small category $J$ — the \termdefineas{diagram shape}{shape} — and a functor $D : J \to
\mathcal C$ — a \termdefineas{categorical diagram}{diagram} of shape $J$ — a \termdefineas{cone over a diagram}{cone}
over $D$ from an object $A$ is a natural transformation $\mathrm{const}_A \Rightarrow D$ from the constant functor at
$A$. A \termdefineas{categorical limit}{limit} of $D$ is a cone $\Pair{L}{\lambda_j : L \to D(j)}$ that is universal:
every
other cone factors uniquely through it. Specializing $J$ recovers terminal objects ($J = \emptyset$), products ($J$
discrete), equalizers ($J$ a parallel pair), and pullbacks ($J$ a cospan). A category is \termdefine{finitely complete}
if it has all finite limits; equivalently, it has a terminal object, all binary products, and all equalizers.
\termdefineas{U-completeness}{$U$-completeness} means having limits of all $U$-small diagrams.

\termdefineas{colimit}{Colimits} are the dual notion, obtained by reversing arrows: initial objects, coproducts,
coequalizers, pushouts, and filtered colimits.

\begin{mathmeta}
  \define{catExp,evalMap}
\end{mathmeta}

**Exponentials.** A category $\mathcal C$ with finite products has \termdefineas{exponential}{exponentials} if for every
pair of objects $A, B$ there is an object $\catExp{A}{B}$ — also written $[A, B]$ or $A \Rightarrow B$ — together with
an \termdefine{evaluation} morphism $\evalMap : \catExp{A}{B} \times A \to B$ such that for every $f : C \times A \to B$
there is a unique $\overline f : C \to \catExp{A}{B}$ — its \termdefine{transpose} or \termdefine{currying} — with
$\evalMap \circ (\overline f \times \mathrm{id}_A) = f$. Equivalently, $- \times A$ has a right adjoint $(-)^A$, and the
exponential adjunction
$$\HomSet{\mathcal C}{C \times A}{B} \;\cong\; \HomSet{\mathcal C}{C}{\catExp{A}{B}}$$
is natural in $C$ and $B$.

**Cartesian closed categories.** A \termdefine{cartesian closed category} (CCC) is a category with a terminal object,
all binary products, and all exponentials. <!--
formalization: skip-begin (引用・背景説明・読書案内:
CCCの定義は標準CartesianMonoidalCategory/MonoidalClosedに接続した。残りは型付きlambda計算の意味付け、
Set・compactly generated Hausdorff・Topの標準的な背景例、およびdomain章が主張していない同値への注意である。
Top非CCCなどの外部理論を局所的に証明したとは扱わない。)
--> CCCs are the natural setting for typed lambda calculus: types are objects,
terms are morphisms, lambda abstraction is currying, and application is evaluation. The categories $\SetCat$, the
category of compactly generated Hausdorff spaces, and any topos are cartesian closed; $\TopCat$ itself is *not*. The
admissible domain representations in §{sec:domains-tte-equivalence} connect quasi-Polish spaces with domain
approximations, but do not assert that quasi-Polish spaces form a cartesian closed category or that they are equivalent
to a category of maximal-point domains.<!--
formalization: skip-end
-->

### Subobject classifiers and elementary toposes {#sec:cat-toposes}
\index{subobject classifier}
\index{elementary topos}

\begin{mathmeta}
  \define{SubobjectClassifier,Subobjects}
\end{mathmeta}

**Subobjects.** Two monomorphisms $m : S \hookrightarrow A$ and $m' : S' \hookrightarrow A$ into the same object are
\termdefineas{equivalent monomorphisms}{equivalent} if each factors through the other by an isomorphism. A
\termdefine{subobject} of $A$ is an equivalence class of monos into $A$. <!--
formalization: skip-begin (引用・背景説明・読書案内:
モノ射の同型による同値類としての定義はmathlib標準Subobjectへ接続した。残りの集合の場合の部分集合との対応と因子化による順序はMac
Lane–Moerdijkの標準的な用語説明で、この付録の局所的な新規証明ではない。
任意PCAでの具体的な述語・部分対象の対応と順序の主張は後続で別に証明・接続済み。)
--> In $\SetCat$ this recovers the ordinary subsets
of $A$. The collection of subobjects of $A$ is a poset under factorization, written $\Subobjects{A}$.<!--
formalization: skip-end
-->

**Subobject classifier.** In a category with finite limits, a \termdefine{subobject classifier} is a monomorphism
$\mathrm{true} : 1 \hookrightarrow \SubobjectClassifier$ such that for every monomorphism $m : S \hookrightarrow A$
there is a unique morphism $\chi_m : A \to \SubobjectClassifier$ — the \termdefine{characteristic map} of $m$ — fitting
into a pullback square
$$\begin{array}{ccc} S & \longrightarrow & 1 \\ {\scriptstyle m}\downarrow & & \downarrow{\scriptstyle \mathrm{true}} \\
A & \xrightarrow{\;\chi_m\;} & \SubobjectClassifier \end{array}$$
Thus $\SubobjectClassifier$ represents the functor $\Subobjects{-} : \opcat{\mathcal C} \to \SetCat$, and subobjects of
$A$ correspond bijectively to morphisms $A \to \SubobjectClassifier$:
$$\Subobjects{A} \;\cong\; \HomSet{\mathcal C}{A}{\SubobjectClassifier}.$$
<!--
formalization: skip-begin (引用・背景説明・読書案内:
分類子の定義とHom/Subobjectの表現同型は標準ClassifierとrepresentableBy.homEquivへ接続した。
残るSetの2値分類子と一般の内部論理が直観主義的になる理由はMac Lane–Moerdijkの背景説明で、一般トポス理論の新規証明を置いていない。
具体的な有効トポスの分類子は参照先で別に扱う。)
--> In $\SetCat$ the subobject classifier is the two-element set $\{\bot, \top\}$ with $\mathrm{true}(*) = \top$, and
characteristic maps are ordinary indicator functions. In a general topos the truth-value object need not have
Boolean complementation. This is why the
internal logic is generally intuitionistic; in $\SetCat$ it is classical.<!--
formalization: skip-end
-->

**Elementary toposes.** An \termdefine{elementary topos} is a category $\mathcal E$ that is finitely complete, cartesian
closed, and equipped with a subobject classifier. <!--
formalization: skip-begin (引用・背景説明・読書案内:
初等トポスの3条件はIsElementaryToposに標準的な圏論の型で記録した。有限余極限、Heyting部分対象、power objects、
epi–mono分解が従うという一般トポス理論は章頭で指定するMac Lane–Moerdijkの外部背景として使う。
一般定理をこの短い定義だけからLeanで証明済みとは扱わない。)
--> From this short list one derives that $\mathcal E$ also has finite
colimits, that $\Subobjects{A}$ is a Heyting algebra for every $A$, that the \termdefine{power object}
$\catExp{A}{\SubobjectClassifier}$ exists and represents subobjects of products $A \times -$, and that every morphism
factors as an epi followed by a mono.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
標準例の箇条書きを導入する見出し文だけで、数学的主張や局所的証明を含まない。)
--> The standard examples are:<!--
formalization: skip-end
-->

*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    Setの2値分類子という標準的な背景例とpresheaf記号のmathmeta宣言。集合の分類子をここで新たに構成・証明する段落ではなく、
    章頭で指定したMac Lane–Moerdijkの基本例である。)
    --> $\SetCat$ itself, where $\SubobjectClassifier = \{\bot, \top\}$.
\begin{mathmeta}
  \define{presheafCat}
\end{mathmeta}<!--
formalization: skip-end
-->

*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    presheafの篩、sheafの開集合、実現可能性という標準例の概説。Mac Lane–Moerdijk、van Oosten、
    および後続の具体的計算への参照であり、一般presheaf/sheafトポスの定理をこの付録の局所的証明とは扱わない。)
    -->
    The category $\presheafCat{\mathcal C}$ of \termdefineas{presheaf}{presheaves} on a $U$-small category $\mathcal C$,
    with $\SubobjectClassifier(C)$ given by the sieves on $C$.
\begin{mathmeta}
  \define{ShCat}
\end{mathmeta}
*   The category $\ShCat{X}$ of \termdefineas{sheaf}{sheaves} on a topological space $X$ — or, more generally, on a
    Grothendieck site — with $\SubobjectClassifier(U)$ the open subsets of $U$.
*   The \termuse{effective topos} $\EffCat$ of §{sec:effective-topos}, constructed from realizability data via the
    tripos-to-topos passage of §{sec:realizability-tripos}.<!--
    formalization: skip-end
    -->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
有効トポスの命題PERと特性写像の説明はLambdaRealizabilityTruthValuesのtruthValues/characterist
icMapに狭く接続した。残る閉篩とsheafの切断・大域要素、一般にassemblyでないという説明はMac Lane–Moerdijkとvan
Oostenの標準的背景の区別で、ここにはその新規証明がない。)
--> For sheaves on a site, the classifier is described by closed sieves; the open-subset description above
is its specialization to a topological space. Its global elements correspond to subterminal objects, which
alone do not describe all of its sections.<!--
formalization: skip-end
-->  In $\EffCat$, $\SubobjectClassifier$ is the PER object of
propositions with equality witnessed by implications in both directions, as described in
§{sec:effective-topos-construction}. <!--
formalization: skip-begin (引用・背景説明・読書案内:
有効トポスの命題PERと特性写像の説明はLambdaRealizabilityTruthValuesのtruthValues/characterist
icMapに狭く接続した。残る閉篩とsheafの切断・大域要素、一般にassemblyでないという説明はMac Lane–Moerdijkとvan
Oostenの標準的背景の区別で、ここにはその新規証明がない。)
--> It is not in general an assembly. A morphism $A \to \SubobjectClassifier$
classifies a predicate in the internal sense, not merely its external truth value at each element $a$.<!--
formalization: skip-end
-->

### Internal logic of a topos {#sec:cat-internal-logic}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Mitchell–Bénabou内部言語の一般存在を紹介する背景。章頭のMac
Lane–Moerdijkおよび末尾のPittsを参照する一般圏論的論理であり、全初等トポスの高階論理の健全性を局所的に形式化済みとは主張しない。)
-->
Every elementary topos $\mathcal E$ supports an interpretation of higher-order logic in which connectives are read off
the categorical structure. The interpretation is called the \termdefine{internal language} or
\termdefineas{Mitchell--Benabou language}{Mitchell–Bénabou language} and takes the following form.<!--
formalization: skip-end
-->

**Types and terms.** Each object $A$ of $\mathcal E$ is a \termdefineas{internal type}{type}. Closed terms of type $A$
are global elements $1 \to A$, and a term $t(x_1, \ldots, x_n)$ of type $B$ in free variables $x_i : A_i$ is a morphism
$A_1 \times \cdots \times A_n \to B$. Substitution is composition.

**Propositions.** An \termdefineas{internal proposition}{proposition} in context $\Gamma = (x_1 : A_1, \ldots, x_n :
A_n)$ is a morphism $A_1 \times \cdots \times A_n \to \SubobjectClassifier$, equivalently a subobject of $A_1 \times
\cdots \times A_n$. <!--
formalization: skip-begin (引用・背景説明・読書案内:
文脈内命題を分類子への射または部分対象と読む定義はCategoryVocabularyのPropositionInContext/classifier
HomEquivに接続した。残る任意の初等トポスの部分対象がHeyting代数をなすという一般定理はMac Lane–Moerdijkの外部背景。
任意PCAの具体的なHeyting fiberは別に構成済みで、それと一般定理を混同しない。)
--> The lattice of propositions in context $\Gamma$ is the Heyting algebra $\Subobjects{A_1 \times
\cdots \times A_n}$, so the propositional connectives are interpreted by Heyting-algebra operations:<!--
formalization: skip-end
-->

*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    任意の初等トポスにおける内部言語の結合子の標準的意味論の一覧。Mac Lane–Moerdijk/Pittsの背景理論であり、
    一般トポスの部分対象代数の構成を局所的に証明していない。PCA述語の具体的演算と普遍性は後続の別命題で接続済み。)
    --> $\top$ and $\bot$ are the top and bottom subobjects;<!--
    formalization: skip-end
    -->
*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    任意の初等トポスにおける内部言語の結合子の標準的意味論の一覧。Mac Lane–Moerdijk/Pittsの背景理論であり、
    一般トポスの部分対象代数の構成を局所的に証明していない。PCA述語の具体的演算と普遍性は後続の別命題で接続済み。)
    --> $\varphi \land \psi$ is intersection of subobjects;<!--
    formalization: skip-end
    -->
*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    任意の初等トポスにおける内部言語の結合子の標準的意味論の一覧。Mac Lane–Moerdijk/Pittsの背景理論であり、
    一般トポスの部分対象代数の構成を局所的に証明していない。PCA述語の具体的演算と普遍性は後続の別命題で接続済み。)
    --> $\varphi \lor \psi$ is union (image of the cotuple);<!--
    formalization: skip-end
    -->
*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    任意の初等トポスにおける内部言語の結合子の標準的意味論の一覧。Mac Lane–Moerdijk/Pittsの背景理論であり、
    一般トポスの部分対象代数の構成を局所的に証明していない。PCA述語の具体的演算と普遍性は後続の別命題で接続済み。)
    --> $\varphi \to \psi$ is the Heyting implication, i.e., the largest subobject whose meet with $\varphi$ lies inside
    $\psi$;<!--
    formalization: skip-end
    -->
*   <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    任意の初等トポスにおける内部言語の結合子の標準的意味論の一覧。Mac Lane–Moerdijk/Pittsの背景理論であり、
    一般トポスの部分対象代数の構成を局所的に証明していない。PCA述語の具体的演算と普遍性は後続の別命題で接続済み。)
    --> $\neg \varphi$ is $\varphi \to \bot$.<!--
    formalization: skip-end
    -->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
任意の初等トポスの量化子随伴とBeck–Chevalleyという一般内部言語の理論。Mac
Lane–Moerdijk/Pittsを外部背景として使い、局所証明を提示しない。PCA
triposの量化子の実装・随伴・BC証明は後続の別命題で実際に接続している。)
-->
**Quantifiers.** For a projection $\pi : \Gamma \times A \to \Gamma$, pulling back gives a Heyting-algebra map $\pi^* :
\Subobjects{\Gamma} \to \Subobjects{\Gamma \times A}$, and this map has both adjoints. Its \termuse{left adjoint}
$\exists_\pi$ interprets the existential quantifier $\exists x : A.\, \varphi(x, \vec y)$, and its
\termdefine{right adjoint} $\forall_\pi$ interprets $\forall x : A.\, \varphi(x, \vec y)$. The Beck–Chevalley condition
guarantees that
quantification commutes with substitution.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
power object、対角線、内包・記述を含む高階内部言語の一般的意味論の概説で、Mac Lane–Moerdijk/Pittsの外部理論。
具体的なPCA関係の局所計算から全一般健全性を証明したとは扱わない。)
-->
**Higher-order features.** The power object $\catExp{A}{\SubobjectClassifier}$ interprets the type "subset of $A$," and
the equality predicate $=_A$ is the characteristic map of the diagonal $\Delta_A : A \hookrightarrow A \times A$.
Together these support the full schema of intuitionistic higher-order logic: comprehension, extensionality of subsets,
function-extensionality, and the description operator inside the topos's image-factorization system.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Booleanトポス、sheafの例、内部ACと外部のepi分裂の区別という一般的な背景説明。Mac Lane–Moerdijk/van
Oostenと明示的な有効トポス章への参照であり、この段落で新たな反例の証明を提示しない。参照先の具体的な非一様性の証明は独立に監査する。)
-->
**Why intuitionistic.** The Heyting algebras $\Subobjects{A}$ are not in general Boolean. Excluded middle $\varphi \lor
\neg \varphi$ holds for every $\varphi$ iff the topos is \termdefine{Boolean}, which fails, for example, for
$\ShCat{X}$ when $X$ is the real line, and for $\EffCat$.
Non-discreteness alone is insufficient: an indiscrete space can have a Boolean sheaf topos. The choice
principle $\mathrm{AC}$ in its full categorical form likewise
fails: the external categorical condition that every epi splits is stronger than internal $\mathrm{AC}$.
Internal existence of a section must not be confused with a chosen global section. For $\EffCat$, the
failure of these classical principles is exactly the failure recorded in §{sec:effective-topos-internal-logic}, with the
realizability semantics supplying explicit counter-realizers.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
全初等トポスに対する内部高階論理の健全性はMac Lane–Moerdijk/Pittsの外部定理。
CT・MPのtrackerやKLS/Ceitinが別途必要という参照案内であり、それらがトポス公理だけから従うとはしない。
本文に局所的な健全性証明やKLS証明はない。)
-->
**Internal language and soundness.** The interpretation is sound: any formula derivable in intuitionistic higher-order
logic from a set of axioms holds in any topos satisfying the interpretations of those axioms. Every elementary topos
also carries an internal language in which its categorical constructions can be expressed and checked by this soundness
theorem. The topos axioms alone do not validate the additional principles listed in
§{sec:effective-topos-internal-logic}. Church's Thesis and Markov's Principle require their standard recursive trackers
in $K_1$ realizability, while the Continuity Principle uses the substantive
Kreisel--Lacombe--Shoenfield/Ceitin effective-operations theorem.<!--
formalization: skip-end
-->

## Realizers and Assemblies {#sec:realizability-data}

### Partial combinatory algebras {#sec:realizability-pca}

\begin{mathmeta}
  \vars{a,b,c,e,k,m,n,r,r_*,d_*,x,y,z}{Nat}
  \vars{A}{Set(PCAElement)}
  \vars{\alpha,\alpha_*,\beta,\gamma,\epsilon,\pi,\rho,\chi,\zeta}{Elem(A)}
\end{mathmeta}
<!--
formalization: skip-begin (引用・背景説明・読書案内:
PCAの導入とFeferman、K1、K2の歴史的背景。
実際のPCA公理と抽象化の局所的証明は直後のdefinition/proposition/proofで独立に接続済み。
この歴史紹介から各モデルの構成を一括して形式化済みとはしない。)
--> Realizability replaces the abstract notion of "evidence for a proposition" with computation in a fixed algebraic
structure. The structure is a \termdefine{partial combinatory algebra} (PCA), introduced abstractly by Feferman to
capture the common features of Kleene's first algebra (numerical recursion), Kleene's second algebra (Baire-space
recursion), and combinatory-logic models of the lambda calculus.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \type{pca-term}
  \notationtype{\subst}{pca-term}{SubstPCA}
  \vars{t,u,v,\theta}{pca-term}
  \define{SubstPCA,PCAAbstract}
\end{mathmeta}

\begin{definition*} A \termdefine{partial applicative structure} $\Pair{A}{\cdot}$ is a set $A$ together with a partial
binary operation $\PartialFunctionMap{\cdot}{A \times A}{A}$, written $\alpha\cdot \beta$ or simply $\alpha\beta$ and
associated to the
left. The application is total when $\alpha\cdot \beta$ is defined for all $\alpha, \beta$, partial otherwise. We use
Kleene equality
$\simeq$: $t \simeq u$ means that either both sides are undefined or both are defined and equal.

A partial combinatory algebra is a partial applicative structure $A$ in which there exist elements $\mathsf k, \mathsf s
\in A$ — the \termdefineas{combinator}{combinators} — such that for every $\alpha, \beta, \gamma\in A$:

\begin{itemize}
\item $\mathsf k \cdot \alpha\cdot \beta\simeq \alpha$ — and in particular $\mathsf k \cdot \alpha$ is always defined;
\item $\mathsf s \cdot \alpha\cdot \beta$ is always defined, and $\mathsf s \cdot \alpha\cdot \beta\cdot \gamma\simeq
(\alpha\cdot \gamma) \cdot (\beta
\cdot \gamma)$.
\end{itemize}

\end{definition*}

\begin{proposition*}[\termdefineas{abstraction theorem}{Abstraction theorem}]
Let $n\ge1$, and let $t(\xi_1,\ldots,\xi_n)$ be an applicative term with distinct displayed variables,
constants from $A$, and any fixed additional parameters. There is an element
$$\epsilon=\PCAAbstract{\xi_1,\ldots,\xi_n}{t}\in A$$
such that, for every tuple of arguments,
$$\epsilon\cdot \alpha_1\cdots \alpha_n\simeq t\subst{\xi_1,\ldots,\xi_n}{\alpha_1,\ldots,\alpha_n}.$$
Moreover, $\epsilon\cdot \alpha_1\cdots \alpha_{n-1}$ is always defined. The same element works for all arguments once
the
additional parameters have been fixed.
\end{proposition*}

\begin{proof}
First construct a term abstracting one variable by structural recursion:
$$\begin{aligned}
\PCAAbstract{\xi}{\xi}&:=\mathsf s\mathsf k\mathsf k,\\
\PCAAbstract{\xi}{\eta}&:=\mathsf k \eta&&(\eta\ne \xi),\\
\PCAAbstract{\xi}{\gamma}&:=\mathsf k \gamma&&(\gamma\in A),\\
\PCAAbstract{\xi}{(uv)}&:=\mathsf s\,(\PCAAbstract{\xi}{u})\,(\PCAAbstract{\xi}{v}).
\end{aligned}$$
The constant clause applies to an element of the algebra, not to an unevaluated compound expression.
Keep two assertions in the induction: the abstracted term has a value for every assignment of the remaining
parameters, and applying that value gives exactly the original partial value after substitution.

In the variable case, the $\mathsf s$ axiom ensures that $\mathsf s\mathsf k\mathsf k$ is defined, and
$$\mathsf s\mathsf k\mathsf k\,\alpha\simeq(\mathsf k \alpha)(\mathsf k \alpha)\simeq \alpha.$$
The last equality uses both the definedness of the constant-function application and its defining law.
For another variable or an algebra constant, the constant-function axioms give both assertions directly.

For an application, let $\pi,\rho$ be the values of the two abstracted subterms. They exist by induction.
The element $\mathsf s \pi\rho$ is defined, and
$$\mathsf s \pi\rho\,\alpha\simeq(\pi\alpha)(\rho\alpha)
\simeq (u\subst{\xi}{\alpha})(v\subst{\xi}{\alpha}).$$
Every application here is strict: if an argument computation or the final application is undefined, both sides
are undefined. Thus the induction proves equality of partial values, including their domains.

For several variables, abstract the last displayed variable first and repeat toward the first.
Successive uses of the one-variable identity give the displayed equality. After any proper prefix of arguments,
the remaining expression is still an abstraction and hence has a value by the first assertion of the induction.
In particular, all arguments except the last can be supplied without losing definedness. The construction
retains every undisplayed parameter and does not use the argument values when choosing the abstracted element.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
遅延固定点および再帰的定義可能性の標準結果はBauer §2.5への明示的引用による外部入力。
PCAAbstractionの抽象化・proper-prefix definednessだけで遅延固定点を証明済みとしない。
局所的に実際に構成したpair/selector/case等は後続の別証明で接続済み。)
--> Partial application requires a delayed fixed-point construction, rather than an unqualified translation of
§{sec:lambda-indices}. There is a combinator $\zeta$ such that $\zeta\cdot \alpha$ is always defined and
$\zeta\cdot \alpha\cdot \beta\simeq \alpha\cdot(\zeta\cdot \alpha)\cdot \beta$. Thus represented recursive
equations
$\chi\cdot\alpha\simeq\theta(\chi,\alpha)$ have solutions when the right side is supplied by a two-argument
applicative term.
For the delayed construction and further discussion of abstraction, see [@BauerRealizabilityNotes, §2.5].
Booleans, pairs, projections, conditional, natural numbers, and primitive-recursive operations all become
internally definable.<!--
formalization: skip-end
-->

**Kleene's first algebra $K_1$.** The carrier is $\NN$, and application is
$$e\cdot n\simeq\varphi_e(n),\qquad
\varphi_e(n)=m\quad\Longleftrightarrow\quad P_e\ChurchNumeral{n}\to_\beta^*\ChurchNumeral{m}.$$
Here $P_e$ is the closed lambda program with index $e$ from §{sec:lambda-indices}. Uniqueness of numerical outputs
makes this a partial function. This is the algebra underlying $\EffCat$. We construct its combinators using the
lambda programs for syntax codes and finite reduction certificates from §{sec:lambda-input-universal-evaluation}.

\begin{proposition*}[
\termdefineas{lambda-index partial combinatory algebra}{Lambda indices form a partial combinatory algebra}]
The numerical application just defined makes $\NN$ a partial combinatory algebra. Its combinators satisfy the stated
Kleene equalities, including equality of the domains of the two sides.
\end{proposition*}

\begin{proof}
For $\mathsf k$, fix a variable name $u$ and put
$$\kappa(a):=\LambdaSyntaxCode{\lambdaab{u}{\ChurchNumeral{a}}}.$$
The numeral-code and abstraction-code programs compute this total numerical function. Choose an index
$\mathsf k$ for that closed numerical program. Then
$$
\mathsf k\cdot a=\kappa(a),\qquad \kappa(a)\cdot b=a.
$$
The first application constructs a constant program's code; the second executes that constant program. Both are
always defined. In particular, $\mathsf k$ is a numerical index computing codes, rather than the raw term
$\lambdaab{x}{\lambdaab{y}{x}}$.

For $\mathsf s$, the final computation must have a numerical output precisely when all three applications
$a\cdot c$, $b\cdot c$, and $(a\cdot c)\cdot(b\cdot c)$ have values. Let $C(e,n,k)\in\{0,1\}$ be the numerical
answer of $\LambdaOutputCandidate$ on these inputs. Thus if $k=\NatPair{m}{r}$, success certifies a finite reduction
of $P_e\ChurchNumeral{n}$ to $\ChurchNumeral{m}$, and every such reduction is accepted at some bound $r$.
Encode an input and a trial by
$$
\begin{aligned}
z&=\NatPair{a}{\NatPair{b}{c}},&
k&=\NatPair{d_1}{\NatPair{d_2}{d_3}},\\
d_1&=\NatPair{x}{r_1},&d_2&=\NatPair{y}{r_2},\qquad d_3=\NatPair{m}{r_3}.
\end{aligned}
$$
The total trial function is
$$T(z,k):=C(a,c,d_1)\,C(b,c,d_2)\,C(x,y,d_3).$$
Numerical projections, three applications of the candidate tester, and multiplication give a closed lambda program
$\mathcal T$ computing $T$ on the paired input $\NatPair{z}{k}$. A successful trial certifies exactly
$$a\cdot c=x,\qquad b\cdot c=y,\qquad x\cdot y=m.$$

Let $F$ extract $m$ from the trial code and search for a successful trial:
$$
\begin{aligned}
F&:=\lambdaab{k}{\LambdaNumericProjection{1}
  (\LambdaNumericProjection{2}(\LambdaNumericProjection{2}\,k))},\\
Q&:=\lambdaab{z}{\LambdaResultSearch
  \bigl(\lambdaab{k}{\LambdaZeroTest\,(\mathcal T(\LambdaNumericPair\,z\,k))
    \,\ChurchNumeral{1}\,\ChurchNumeral{0}}\bigr)\,F}.
\end{aligned}
$$
All these terms are closed. The zero test reverses the trial answer because result search stops at zero.
If the three applications have values, their finite certificates give a successful trial. Every successful trial has
the same output, by uniqueness of the two intermediate values and the final value. Result search therefore returns
that value. If any required application lacks a value, every trial fails; the no-output part of the result-search
lemma excludes every numerical output, regardless of reduction order. Consequently
$$
Q\ChurchNumeral{\NatPair{a}{\NatPair{b}{c}}}\to_\beta^*\ChurchNumeral{m}
\quad\Longleftrightarrow\quad
\exists x,y\;\bigl(a\cdot c=x\ \land\ b\cdot c=y\ \land\ x\cdot y=m\bigr).
$$

It remains to delay this computation until the third argument. Fix named representatives of $Q$ and numerical
pairing, and define
$$\sigma(a,b):=\LambdaSyntaxCode{\lambdaab{u}{
 Q(\LambdaNumericPair\,\ChurchNumeral{a}\,(\LambdaNumericPair\,\ChurchNumeral{b}\,u))}}.$$
This is a total syntax operation: numeral-code, application-code, and abstraction-code programs compute it without
executing $Q$. Let $G$ be the resulting closed program on the paired input, and put
$$H:=\lambdaab{a}{\lambdaab{b}{G(\LambdaNumericPair\,a\,b)}},\qquad
\sigma_0(a):=\LambdaSyntaxCode{H\ChurchNumeral{a}}.$$
Fix a named representative of $H$. The function $\sigma_0$ is again a total computed syntax operation, so choose an
index $\mathsf s$ for its program. Then
$$\mathsf s\cdot a=\sigma_0(a),\qquad \sigma_0(a)\cdot b=\sigma(a,b).$$
Both applications are always defined. Applying the program with code $\sigma(a,b)$ to $\ChurchNumeral{c}$ reduces
to $Q\ChurchNumeral{\NatPair{a}{\NatPair{b}{c}}}$. The exact-output equivalence above therefore proves
$$\mathsf s\cdot a\cdot b\cdot c\simeq(a\cdot c)\cdot(b\cdot c),$$
including the case where either side is undefined. This completes the construction using only lambda terms and
beta reduction.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
K2と任意tracker/計算可能部分代数の区別はBauer §3.5.5の明示的引用によるモデル比較。本文はK2の組合子やrelative
realizabilityを局所的に構成・証明しない。数値lambda添字のK1構成とは区別する。)
--> \begin{mathmeta}
  \define{RTCat}
\end{mathmeta}
**Kleene's second algebra $K_2$.** The carrier is $\BaireSpace$, with application defined by treating $f \in
\BaireSpace$ as a partial continuous functional on $\BaireSpace$ via the standard "consult $f$ on initial segments"
protocol. It underlies the *function* realizability topos $\RTCat{K_2}$. Allowing arbitrary elements as trackers
gives continuous name transformations. Restricting trackers to the computable subalgebra while retaining all
Baire-space names gives relative realizability, the Kleene–Vesley setting. These are different choices of
realizability model [@BauerRealizabilityNotes, §3.5.5].<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Scott powerset、D∞、coalgebraicなどのPCAの例を列挙する文献的背景で、具体的構成・性質の証明を提示していない。
各PCAからトポスを得る一般定理は明示的に後のtripos-to-topos定理に委ね、局所構成と区別する。)
--> **Other examples.** Combinatory algebras themselves, Scott's $\PowerSet{\omega}$-model, untyped lambda models like
$D_\infty$, and certain coalgebraic models all yield PCAs. Each one supports its own realizability topos via the
construction of §{sec:realizability-tripos}; comparing them is the realizability-theoretic analogue of comparing
different forcing notions.<!--
formalization: skip-end
-->

### Assemblies and modest sets {#sec:realizability-assemblies}
\index{assembly}
\index{modest set}

\begin{mathmeta}
  \define{AsmCat,PCAPair}
\end{mathmeta}
Fix a PCA $A$. The category of \termuseas{assembly}{assemblies} $\AsmCat{A}$ is the first realizability category built
over $A$ and is where the external concept of "set with realizers" lives intrinsically.

**Assemblies.** An \termdefine{assembly} $X = \Pair{\UnderlyingSet{X}}{\Vdash_X}$ is a set $\UnderlyingSet{X}$ — its
\termdefine{underlying set} —
together with a function
$$\Vdash_X \;:\; \UnderlyingSet{X} \to \SetDifference{\PowerSet{A}}{\{\emptyset\}}$$
assigning to each element $x \in \UnderlyingSet{X}$ a non-empty set $\Vdash_X x \IncludedIn A$ of
\termdefineas{assembly realizer}{realizers} of $x$. We read $a \Vdash_X x$ as "$a$ realizes $x$" or "$a$ is a name for
$x$." The non-emptiness
condition is essential: every element must be realizable.

A \termdefine{morphism of assemblies} $f : X \to Y$ is a function $f : \UnderlyingSet{X} \to \UnderlyingSet{Y}$ on
underlying sets that is
\termdefineas{tracked morphism}{tracked} by some $r \in A$, meaning: for every $x \in \UnderlyingSet{X}$ and every $a
\Vdash_X x$, the
application $r \cdot a$ is defined and $r \cdot a \Vdash_Y f(x)$. The realizer $r$ is part of the data only
existentially; two morphisms with the same underlying function but distinct trackers are identified.

\begin{proposition*}[\termdefineas{category of assemblies}{Category of assemblies}]
Assemblies and tracked functions form a category. Equality of morphisms is equality of their underlying functions.
\end{proposition*}

\begin{proof}
Put $\mathsf i:=\mathsf s\mathsf k\mathsf k$. The abstraction theorem gives
$\mathsf i a\simeq a$, so this element tracks every identity function.
If $r$ tracks $f:X\to Y$ and $s$ tracks $g:Y\to Z$, the element
$$\PCAAbstract{a}{s(ra)}$$
tracks their composite. Indeed, an input realizer first yields a realizer of the intermediate element, and the
second tracker then yields a realizer of the final element. Both applications are defined on the required inputs.
The identity and associativity laws are the corresponding laws for functions. They do not require equality of
chosen trackers, since a tracker is only required to exist.
\end{proof}

\begin{lemma*}[\termdefineas{pairing in a partial combinatory algebra}{PCA pairing}]
There is a pairing operation $\PCAPair{a}{b}$ whose construction is tracked by one element, and there are fixed
projection elements $\mathsf l,\mathsf r$ such that
$$\mathsf l\PCAPair{a}{b}=a,\qquad \mathsf r\PCAPair{a}{b}=b.$$
Every encoded pair and both displayed projections are defined.
\end{lemma*}

\begin{proof}
Use abstraction to set
$$\mathsf p:=\PCAAbstract{a,b,c}{cab},\qquad
\PCAPair{a}{b}:=\mathsf p a b.$$
The proper-prefix clause of the abstraction theorem makes every pair defined, and its computation rule gives
$$\PCAPair{a}{b}\,c\simeq cab.$$
Thus the same element constructs pairs for every pair of inputs.

Set $\mathsf q:=\mathsf k\mathsf i$. The constant-function and identity laws imply
$\mathsf k a b=a$ and $\mathsf q a b=b$. Hence
$$\mathsf l:=\PCAAbstract{w}{w\mathsf k},\qquad
\mathsf r:=\PCAAbstract{w}{w\mathsf q}$$
have the required projection laws. The selector is applied to the two components only after the encoded pair
receives it; no value of an unrelated application is required to construct the pair.
\end{proof}

\begin{proposition*}[\termdefineas{finite limits of assemblies}{Finite limits of assemblies}]
The category $\AsmCat{A}$ has finite limits. Terminal objects, binary products, and equalizers have the usual
underlying sets with the realizer sets described below.
\end{proposition*}

\begin{proof}
The terminal assembly has a singleton as underlying set, realized by every element of the PCA.
The identity combinator tracks the unique function into it, so it is terminal.

For the product, take the usual set product and put
$$\PCAPair{a}{b}\Vdash_{X\times Y}\Pair{x}{y}
\quad\text{when }a\Vdash_X x\text{ and }b\Vdash_Y y.$$
These are exactly the realizers of the product. Every pair of elements has one because each component has a
realizer. The two projection elements track the set projections. If two maps into the factors have trackers
$r,s$, their pairing is tracked by
$$\PCAAbstract{a}{\mathsf p(ra)(sa)}.$$
For a valid input, both component computations are defined and realize the required components, so the
constructed pair realizes the required element of the product. The projection equations and uniqueness of the
mediating map follow from equality of the underlying functions. Thus this is a categorical product.

For parallel morphisms $f,g:X\to Y$, take
$$E:=\{x\in\UnderlyingSet{X}:f(x)=g(x)\},\qquad
 a\Vdash_E x\quad\Longleftrightarrow\quad a\Vdash_X x.$$
The identity combinator tracks the inclusion. Any morphism equalizing the two maps factors uniquely through this
subset as a function. Its original tracker still works because restricting the underlying set does not change
the realizer set of any retained element. This proves the equalizer property. Terminal objects, binary products,
and equalizers give all finite limits by the standard finite-limit construction.
\end{proof}

\begin{proposition*}[\termdefineas{finite colimits of assemblies}{Finite colimits of assemblies}]
The category $\AsmCat{A}$ has finite colimits, computed on underlying sets with the realizer sets described below.
\end{proposition*}

\begin{proof}
The empty set with no realizers is initial: its unique map to any assembly is tracked
vacuously by any element.

For the binary coproduct, use the disjoint union $\UnderlyingSet{X}\disjointUnion\UnderlyingSet{Y}$ with injections
$i,j$ and prescribe
$$\begin{aligned}
\PCAPair{\mathsf k}{a}&\Vdash_{X+Y}i(x)
&&\text{when }a\Vdash_X x,\\
\PCAPair{\mathsf q}{b}&\Vdash_{X+Y}j(y)
&&\text{when }b\Vdash_Y y.
\end{aligned}$$
These are exactly the realizers of the indicated elements. Each realizer set is nonempty, and the injections
are tracked by $\mathsf p\mathsf k$ and $\mathsf p\mathsf q$ respectively.

Given morphisms out of the two summands with trackers $r,s$, track their combined function by
$$\PCAAbstract{w}{\bigl((\mathsf l w)r s\bigr)(\mathsf r w)}.$$
The first projection recovers the tag. Applied to the two tracker elements, this tag returns the tracker for the
required summand; only then is that tracker applied to the payload obtained by the second projection.
Thus the result on the left summand is $ra$, and the result on the right summand is $sb$, with exactly the
corresponding domain of definition. The unused branch need not be defined on that payload.
The two injection equations and uniqueness are those of the disjoint union of sets, proving the coproduct property.

For parallel morphisms $f,g:X\to Y$, let $E$ be the equivalence relation on $\UnderlyingSet{Y}$ generated by the pairs
$\Pair{f(x)}{g(x)}$, and put $Q:=\SetQuotient{\UnderlyingSet{Y}}{E}$. Define
$$a\Vdash_Q\EquivalenceClass{E}{y}
\quad\Longleftrightarrow\quad
\exists z\in\UnderlyingSet{Y}\,\bigl(\Pair{z}{y}\in E\land a\Vdash_Y z\bigr).$$
This is independent of the representative and gives a nonempty realizer set to every class. The quotient map
is tracked by the identity combinator and equalizes the two given morphisms.

If a morphism $h:Y\to Z$ equalizes them, its underlying function is constant on the generating pairs, hence on
all equivalence classes, and so it induces a unique function on the quotient. Any tracker of the original
morphism tracks this induced function. Indeed, a realizer of a class realizes some representative, and the
original tracker sends it to a realizer of that representative's image, which is the required class image.
The computation takes only the input realizer; it does not choose a representative or decide equivalence of
representatives. This proves the coequalizer property. Initial objects, binary coproducts, and coequalizers give
all finite colimits by the standard finite-colimit construction.
\end{proof}

\begin{proposition*}[\termdefineas{exponentials of assemblies}{Exponentials of assemblies}]
The category $\AsmCat{A}$ is cartesian closed. The underlying set of $\catExp{X}{Y}$ consists of the tracked
functions $\UnderlyingSet{X}\to\UnderlyingSet{Y}$, and a realizer of such a function is any of its trackers.
\end{proposition*}

\begin{proof}
Each function in this underlying set has a tracker by definition, so the prescribed realizer sets give an
assembly. Evaluation and its tracker are
$$\evalMap:\catExp{X}{Y}\times X\to Y,\qquad
\evalMap\Pair{f}{x}=f(x),\qquad
\mathsf e:=\PCAAbstract{w}{(\mathsf l w)(\mathsf r w)}.$$
Indeed, if $r$ tracks $f$ and $b\Vdash_X x$, then
$\mathsf e\PCAPair{r}{b}\simeq rb$ is defined and realizes $f(x)$.

Let $h:Z\times X\to Y$ be tracked by $r$. Define its transpose and the corresponding tracker by
$$\overline h(z)(x):=h(z,x),\qquad
\mathsf c_r:=\PCAAbstract{a,b}{r(\PCAPair{a}{b})}.$$
The abstraction theorem ensures that $\mathsf c_r a$ is defined for every $a\in A$, and that
$$(\mathsf c_r a)b\simeq r(\PCAPair{a}{b}).$$
If $a\Vdash_Z z$ and $b\Vdash_X x$, the right side is defined and realizes $h(z,x)$.
Thus $\mathsf c_r a$ tracks the section $x\mapsto h(z,x)$. Every $z$ has a realizer, so every such section
belongs to $\catExp{X}{Y}$. Moreover, the same element $\mathsf c_r$ takes every realizer of $z$ to a tracker
of that section, and hence tracks $\overline h:Z\to\catExp{X}{Y}$. This construction uses the supplied
realizer; it does not require a computable choice of a realizer for each underlying element.

The equation
$$\evalMap\circ(\overline h\times\mathrm{id}_X)=h$$
holds on underlying elements. Conversely, if a morphism $f:Z\to\catExp{X}{Y}$ satisfies
$\evalMap\circ(f\times\mathrm{id}_X)=h$, then $f(z)(x)=h(z,x)$ for all $z,x$, so $f=\overline h$.
Morphisms are equal when their underlying functions are equal, irrespective of their trackers.
This proves the universal property of the exponential.

For fixed $X$, postcomposition by a morphism $g:Y\to Y'$ gives the morphism
$\catExp{X}{Y}\to\catExp{X}{Y'}$ obtained by transposing $g\circ\evalMap$.
It sends $f$ to $g\circ f$, so identities and composition are preserved.
The bijection given by transposition,
$$\HomSet{\AsmCat{A}}{Z\times X}{Y}\cong
\HomSet{\AsmCat{A}}{Z}{\catExp{X}{Y}},$$
is natural: precomposing in $Z$ or postcomposing in $Y$ commutes with the rule
$\overline h(z)(x)=h(z,x)$. Thus the exponential functor is right adjoint to the product functor,
which proves cartesian closedness.
\end{proof}

**Modest sets.** A \termdefine{modest set} is an assembly $X$ in which distinct elements have disjoint realizer sets:
$$x \ne x' \;\Longrightarrow\; \Vdash_X x \cap \Vdash_X x' = \emptyset.$$
Equivalently, each realizer realizes at most one element. This implies that the map
$\UnderlyingSet{X} \to \SetDifference{\PowerSet{A}}{\{\emptyset\}}$ is injective, but injectivity alone does not imply
disjointness.
\begin{mathmeta}
  \define{ModCat}
\end{mathmeta}
Write $\ModCat{A} \IncludedIn \AsmCat{A}$ for the full subcategory on modest sets.

\begin{lemma*}[\termdefineas{monomorphisms of assemblies}{Monomorphisms of assemblies}]
A morphism of assemblies is a monomorphism if and only if its underlying function is injective.
\end{lemma*}

\begin{proof}
An injective underlying function cancels on the left of a composition, so its morphism is a monomorphism.
Conversely, let $m:X\to Y$ be a monomorphism and suppose $m(x)=m(x')$. Each element of $X$ gives a morphism
from the terminal assembly: if $a$ realizes that element, the constant abstraction
$\PCAAbstract{b}{a}$ tracks the constant function. The two morphisms corresponding to $x,x'$ become equal
after composition with $m$, so cancellation makes them equal. Evaluating at the unique element of the
terminal assembly gives $x=x'$.
\end{proof}

\begin{proposition*}[\termdefineas{closure properties of modest sets}{Closure properties of modest sets}]
The category $\ModCat{A}$ is cartesian closed, using the terminal object, products, and exponentials of
$\AsmCat{A}$. It is closed under subobjects in $\AsmCat{A}$.
In fact, $\catExp{X}{Y}$ is modest whenever $Y$ is modest, even if $X$ is an arbitrary assembly.
\end{proposition*}

\begin{proof}
The terminal assembly is modest because it has only one element. Suppose a realizer names two elements
of a product of modest sets. Applying the first projection gives a common realizer of their first
components, so those components are equal; the second projection gives equality of the second components.
Thus the product is modest.

Now let $r$ track two functions $f,g:X\to Y$, where $Y$ is modest. For each $x\in\UnderlyingSet{X}$, choose any
$a\Vdash_X x$. The single value $ra$ is defined and realizes both $f(x)$ and $g(x)$, so $f(x)=g(x)$.
Hence $f=g$, proving that $\catExp{X}{Y}$ is modest. The product projections, evaluation, and transposes
already constructed for assemblies are morphisms in the full subcategory. Their universal properties
therefore restrict to that subcategory, proving that it is cartesian closed.

Finally, let $m:X\to Y$ be a monomorphism with $Y$ modest, and let $r$ track it. If $a$ realizes both
$x$ and $x'$ in $X$, then $ra$ realizes both $m(x)$ and $m(x')$. Modesty of $Y$ gives
$m(x)=m(x')$, and injectivity of the underlying function gives $x=x'$. Thus $X$ is modest.
\end{proof}

\begin{proposition*}[\termdefineas{modest reflection}{Modest reflection}]
Every assembly has a universal morphism to a modest assembly: every morphism from it to a modest
assembly factors uniquely through this morphism. Consequently, the inclusion of $\ModCat{A}$ into
$\AsmCat{A}$ has a left adjoint, so it is a reflective subcategory.
\end{proposition*}

\begin{proof}
For an assembly $X$, let $E$ be the equivalence relation on $\UnderlyingSet{X}$ generated by
$$x\mathrel{R}y\quad\Longleftrightarrow\quad
\exists a\in A\,(a\Vdash_X x\land a\Vdash_X y).$$
Set $Q:=\SetQuotient{\UnderlyingSet{X}}{E}$ and give each class all the realizers of its representatives:
$$a\Vdash_Q\EquivalenceClass{E}{x}\quad\Longleftrightarrow\quad
\exists y\in\UnderlyingSet{X}\,\bigl(\Pair{y}{x}\in E\land a\Vdash_X y\bigr).$$
Every class has a realizer. If two classes share a realizer, some representatives share it, so they
are related by $R$ and the classes coincide. Thus $Q$ is modest, and the quotient map $q:X\to Q$
is tracked by the identity combinator.

Let $f:X\to Y$ have tracker $r$, with $Y$ modest. Whenever $x\mathrel{R}y$, a common input realizer
$a$ gives a common output realizer $ra$ of $f(x),f(y)$, so $f(x)=f(y)$. Thus $f$ is constant on
$E$-classes and induces a unique function $\overline f:Q\to Y$. The same $r$ tracks it: any realizer
of a class realizes some representative, and its image realizes the common value of $f$ on that class.
This gives $\overline f\circ q=f$, with uniqueness inherited from the quotient of sets. No computable
choice of representatives is used.

For a morphism between assemblies, compose with the quotient map of its target and factor through
the quotient of its source. Uniqueness of factorization gives the identity and composition laws,
and precomposition with the quotient map gives the natural hom-set bijection for the adjunction.
\end{proof}

\begin{mathmeta}
  \define{PERSupport,PERAssembly,PERCat}
\end{mathmeta}
A \termuse{partial equivalence relation} $R$ on $A$ is a symmetric and transitive relation. Its
\termdefineas{support of a partial equivalence relation}{support} is
$$\PERSupport{R}:=\{a\in A:a\mathrel{R}a\}.$$
If $a\mathrel{R}b$, symmetry and transitivity put both names in the support. The restriction of $R$ to
its support is therefore an equivalence relation. Define the assembly
$$\UnderlyingSet{\PERAssembly{R}}:=\SetQuotient{\PERSupport{R}}{R},\qquad
 a\Vdash_{\PERAssembly{R}}\EquivalenceClass{R}{b}\quad\Longleftrightarrow\quad a\mathrel{R}b.$$
Thus a class is realized by exactly its members.

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

\begin{proposition*}[\termdefineas{PER presentation of modest sets}{PER presentation of modest sets}]
The assignment $R\mapsto\PERAssembly{R}$, acting as the identity on the induced functions, gives an
equivalence of categories
$$\PERCat{A}\simeq\ModCat{A}.$$
\end{proposition*}

\begin{proof}
Every class has a member, and a name belongs to only one class, so $\PERAssembly{R}$ is a modest assembly.
The tracker conditions make the induced function independent of the representative and make $r$ a tracker
of that function as an assembly morphism. Conversely, a tracker of an assembly morphism between these
quotients is defined on every name in $\PERSupport{R}$. Related input names realize the same class, so
both output names realize the same image class and are $S$-related. Thus the morphisms on the two sides
are exactly the same tracked functions. Equality of the induced functions is precisely the displayed
condition on pairs of trackers.

The identity combinator induces the identity on classes. If $r$ and $s$ track successive morphisms,
$$\PCAAbstract{a}{s(ra)}$$
is defined on the first support and takes names related by the first PER to names related by the final PER.
It induces the composite function. The category laws follow from the laws for functions, and the
assignment to modest assemblies is consequently a fully faithful functor.

\begin{mathmeta}
  \define{ModestPER}
\end{mathmeta}
For the reverse construction, let $X$ be modest and define
$$a\mathrel{\ModestPER{X}}b\quad\Longleftrightarrow\quad
\exists x\in\UnderlyingSet{X}\,(a\Vdash_X x\land b\Vdash_X x).$$
Symmetry is immediate. For transitivity, the common middle name forces the two witnessed elements to
coincide by modesty, so the outer names realize that same element. Hence this is a PER. Its support
consists exactly of the names realizing elements of $X$.

Send $\EquivalenceClass{\ModestPER{X}}{a}$ to the unique element of $X$ realized by $a$.
This is well-defined and surjective because every element has a realizer, and it is injective by the
definition of the relation. Its inverse sends an element to the class of any of its realizers, a class
independent of that choice. Both functions preserve every input name, so both are tracked by the
identity combinator. They give an isomorphism $\PERAssembly{\ModestPER{X}}\cong X$ without requiring a
computable choice of realizers. Starting instead with $R$, two names realize the same class exactly
when they are $R$-related, so $\ModestPER{\PERAssembly{R}}=R$. These constructions prove essential
surjectivity and hence the claimed equivalence.
\end{proof}

For the numerical lambda-index PCA $A=K_1$, these are the categories of
\termdefineas{numbered set}{numbered sets} and \termdefineas{PER-set}{PER-sets} on $\NN$.
The construction gives an equivalence, rather than a literal identification of their underlying data.
Morphisms are computed on names by the partial recursive functions represented by the lambda indices;
the computation must be defined on the source support and respect the target PER. Different indices
may induce the same function on classes.

**Polish spaces and TTE in realizability.** A \termuse{computable Polish space} $X$ in the sense of
§{sec:computable-polish-tte} has a Cauchy representation $\PartialFunctionMap{\rho_X}{\BaireSpace}{X}$ with range all of
$X$. Over $K_1$, however, realizers are natural-number indices for computable procedures. Thus the direct
\termuse{assembly} attached to $\rho_X$ has as underlying set the **computable points** of $X$: an index $e$ realizes
$x$ when $e$ computes a total $\rho_X$-name for $x$. This is a modest assembly because two distinct points cannot share
the same Cauchy name, but it does not contain the noncomputable external points of $X$ as elements.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
K1で計算可能点だけを残す部分はcomputablePointAssemblyへ狭く接続した。残りは名前上のTTEとK2/relative
realizabilityの概念的比較で、先行TTE章およびBauer §3.5.5の引用付きモデル説明を振り返る。
K2全点のPCA構成やrelativeトポスとの圏同値を局所的に証明したとは扱わない。)
--> The full represented space $X$ is therefore better read one level up, through its name space and equality PER: names
$p,q\in \DomainOf{\rho_X}$ represent the same element exactly when $\rho_X(p)=\rho_X(q)$, and computable maps are
tracked by Type-Two realizers transforming names.<!--
formalization: skip-end
-->  The $K_1$ construction above instead retains only computable
points. <!--
formalization: skip-begin (引用・背景説明・読書案内:
K1で計算可能点だけを残す部分はcomputablePointAssemblyへ狭く接続した。残りは名前上のTTEとK2/relative
realizabilityの概念的比較で、先行TTE章およびBauer §3.5.5の引用付きモデル説明を振り返る。
K2全点のPCA構成やrelativeトポスとの圏同値を局所的に証明したとは扱わない。)
--> In the $K_2$ assembly setting,
all names can be retained and arbitrary trackers give continuous TTE maps. Requiring computable trackers
in relative realizability recovers the computable TTE maps. This is the categorical form of the
distinction already used in §{sec:computable-polish-tte}: computability is evidence on names, not a claim that every
external point has a computable name.<!--
formalization: skip-end
-->

The category $\AsmCat{A}$ embeds fully and faithfully into the realizability topos $\RTCat{A}$ as the full subcategory
of $\neg\neg$-separated objects. For each assembly, its canonical monomorphism into the constant object on its
underlying set is $\neg\neg$-dense. Modest sets sit inside $\AsmCat{A}$ as a reflective subcategory, and hence
embed into $\RTCat{A}$ as well. For $K_1$, modest sets correspond to the separated
subquotients of the natural-numbers object; the larger class of discrete objects need not be separated. The
next subsection records how $\RTCat{A}$ itself is
built.

## The tripos-to-topos construction {#sec:realizability-tripos}
\index{tripos}
\index{tripos-to-topos construction}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
triposの歴史と構成の動機付けの概説。Hyland–Johnstone–Pitts、van Oostenの一般理論に関する背景で、
ここで具体的なfree-completionの普遍性を証明してはいない。実際のPCA tripos/PER構成は後続で独立に監査済み。)
-->
The realizability topos cannot be obtained as a presheaf or sheaf topos in any obvious way, because realizers are not
the same data as covers. Hyland, Johnstone, and Pitts identified the missing intermediate notion: a \termforward{tripos}
packages the propositional fragment of the internal logic separately from the type structure, and a topos is then
reconstructed from the tripos via a free completion that adds quotients and subobjects.<!--
formalization: skip-end
-->

### Triposes and Realizability Predicates {#sec:realizability-predicates}

\begin{mathmeta}
  \define{HeytAlgCat}
  \vars{S}{Set(Elem(A))}
  \vars{A}{Set(PCAElement)}
  \vars{a,b,e,r,s,u,v}{Elem(A)}
\end{mathmeta}

A \termdefine{tripos} over the base category $\mathcal C =
\SetCat = \SetCatU$ is a functor
$$\mathcal P : \opcat{\mathcal C} \to \HeytAlgCat$$
to the category of $U$-small Heyting algebras, satisfying:

*   for each map $f : I \to J$ in $\mathcal C$, the homomorphism $\mathcal P(f) : \mathcal P(J) \to \mathcal P(I)$ has
    both a left adjoint $\exists_f$ and a right adjoint $\forall_f$ (the Heyting analogue of quantifiers along $f$);
*   the \termdefine{Beck--Chevalley condition} holds: in pullback squares of $\mathcal C$, reindexing commutes
    with the corresponding
    adjoints as monotone maps. The adjoints themselves need not be morphisms of $\HeytAlgCat$;
*   there is a \termdefine{generic predicate} — an element $\sigma \in \mathcal P(\Sigma)$ for some $\Sigma \in \mathcal
    C$ such that every $\varphi \in \mathcal P(I)$ is of the form $\mathcal P(f)(\sigma)$ for some $f : I \to \Sigma$,
    generally not unique.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
triposの各要素の論理的な読み方と一般高階意味論の標準的説明。SetTriposの公理およびPCAの実際の実装は別箇所で接続し、
一般の高階健全性はPitts/van Oostenの外部理論として扱う。)
--> Read $\mathcal P(I)$ as the Heyting algebra of "predicates on $I$," with substitution $\mathcal P(f)$, quantifiers
$\exists_f, \forall_f$, and a generic predicate playing the role of a propositional truth value. A tripos is enough data
to interpret intuitionistic higher-order logic in the type structure of $\mathcal C$.<!--
formalization: skip-end
-->

**The realizability tripos over a PCA.** Fix a PCA $A$ with $U$-small carrier and put
$$\mathcal P_A(I):=\funcspace{I}{\PowerSet{A}}.$$
Write $\varphi\le\psi$ when one $r\in A$ satisfies
$r\cdot a\downarrow\in\psi(i)$ for every $i\in I$ and $a\in\varphi(i)$.
Use the pairing and selectors constructed in §{sec:realizability-assemblies} to define
$$\begin{aligned}
\top(i)&:=A,\qquad \bot(i):=\emptyset,\\
(\varphi\land\psi)(i)&:=\{\PCAPair{a}{b}:a\in\varphi(i),\ b\in\psi(i)\},\\
(\varphi\lor\psi)(i)&:=\{\PCAPair{\mathsf k}{a}:a\in\varphi(i)\}\\
&\qquad\cup\{\PCAPair{\mathsf q}{b}:b\in\psi(i)\},\\
(\varphi\to\psi)(i)&:=\{r\in A:\forall a\in\varphi(i),\ r\cdot a\downarrow\in\psi(i)\}.
\end{aligned}$$
Here the tags are the two selector elements of the PCA; no natural-number structure on $A$ is assumed.

\begin{proposition*}[\termdefineas{realizability operations over a PCA}{Realizability operations over a PCA}]
Uniform entailment is a preorder with the displayed finite meets, finite joins, and implication.
Its quotient by mutual entailment is a Heyting algebra. Reindexing
$f^\ast\psi:=\psi\circ f$ induces a Heyting homomorphism, and these homomorphisms form a contravariant functor.
\end{proposition*}

\begin{proof}
The identity combinator proves reflexivity. Given successive trackers $r,s$, the element
$\PCAAbstract{a}{s(ra)}$ proves transitivity. The identity also tracks reduction to $\top$ and reduction
from $\bot$, the latter vacuously.

For conjunction, the two projections eliminate a pair, and trackers $r,s$ with a common source combine as
$\PCAAbstract{a}{\mathsf p(ra)(sa)}$. For disjunction, the injections are tracked by $\mathsf p\mathsf k$
and $\mathsf p\mathsf q$. The eliminator for trackers $r,s$ is
$$\PCAAbstract{w}{\bigl((\mathsf l w)r s\bigr)(\mathsf r w)}.$$
The tag selects the appropriate tracker before it receives the payload, so the unused branch need not be
defined on that input. These are the meet and join universal properties.

For implication, a tracker $r$ of $\theta\land\varphi\le\psi$ gives
$$\PCAAbstract{a,b}{r(\PCAPair{a}{b})}$$
as a tracker of $\theta\le(\varphi\to\psi)$: the first application is always defined and returns a tracker
of the required implication. Conversely, a tracker $r$ of the latter reduction gives
$$\PCAAbstract{w}{\bigl(r(\mathsf l w)\bigr)(\mathsf r w)}$$
for the former. This proves the implication adjunction, including definedness on the required inputs.

These universal properties imply monotonicity of meet and join. Implication is contravariant in its first
argument and covariant in its second. Applying them in both directions shows that the operations descend to
mutual-entailment classes. Their universal properties descend as well, giving the Heyting algebra. Reindexing
keeps the same tracker and commutes pointwise with every displayed operation. It therefore induces a Heyting
homomorphism; the identity and composition laws already hold on predicates.
\end{proof}

Quantifiers along $f:I\to J$ are defined on representatives by
$$\begin{aligned}
(\exists_f\varphi)(j)&:=\bigcup_{f(i)=j}\varphi(i),\\
(\forall_f\varphi)(j)&:=\{e\in A:\forall i,\ f(i)=j\Longrightarrow{}\\
&\hspace{28mm}\forall a\in A,\ e\cdot a\downarrow\in\varphi(i)\}.
\end{aligned}$$
An empty union is $\emptyset$, while on an empty fiber the universal clause gives all of $A$.
The universal clause is the guarded intersection $\bigcap_{f(i)=j}(\top\to\varphi(i))$.

\begin{proposition*}[\termdefineas{realizability tripos over a PCA}{Realizability tripos over a PCA}]
The quotient Heyting algebras, reindexing, and these quantifiers form a tripos on the specified set base.
In particular, $\exists_f\dashv f^\ast\dashv\forall_f$, both Beck--Chevalley equalities hold, and the
membership predicate on $\PowerSet{A}$ is generic.
\end{proposition*}

\begin{proof}
For the existential adjunction, the same tracker works in both directions, since membership in the union
means membership in some fiber component. For the universal adjunction, fix $a_0:=\mathsf k$.
If $u$ tracks $\psi\le\forall_f\varphi$, the element
$$\PCAAbstract{a}{(ua)a_0}$$
tracks $f^\ast\psi\le\varphi$. Conversely, if $v$ tracks the latter, use
$$\PCAAbstract{a,b}{va}$$
to track the former. Its first application always returns a code, and applying that code to any argument
has exactly the same partial value as $va$. Thus the outer computation does not require $va$ to be defined;
this is essential on empty fibers. The adjunctions imply monotonicity of both quantifiers, so they preserve
mutual entailment and descend, with the same adjunctions, to the quotient algebras.

For a pullback square with $f:I\to J$, $g:J'\to J$, $f':I'\to J'$, and $g':I'\to I$, the map
$i'\mapsto g'(i')$ identifies the fiber of $f'$ over $j'$ with the fiber of $f$ over $g(j')$.
Replacing one fiber by the other leaves the union clause unchanged. It also leaves the guarded universal
clause unchanged, since the guard ranges over the same $A$ on both sides. Hence
$$g^\ast\exists_f\varphi=\exists_{f'}g'^\ast\varphi,\qquad
 g^\ast\forall_f\varphi=\forall_{f'}g'^\ast\varphi.$$
These equalities hold already on predicates, including empty fibers, and therefore on their classes.

Finally, put $\sigma(S):=S$ for $S\in\PowerSet{A}$. For any predicate $\varphi$, the map
$i\mapsto\varphi(i)$ pulls $\sigma$ back to $\varphi$ exactly. Every quotient class has a representative,
so the class of $\sigma$ is generic. This proves the tripos axioms.
\end{proof}

### PER Completion and Assemblies {#sec:realizability-per-completion}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
任意triposに対する標準PER完成の定義を紹介する外部一般理論。直後で一般tripos-to-topos定理を用いる旨を明示し、van
Oosten/Pittsを参照する。この付録で局所的に証明する任意PCA上のRealizerPER、FunctionalRelation、
相互一様含意の商、category lawsは独立した命題・証明に接続済みで、一般tripos全体の実装と同一視しない。)
--> Given a tripos $\mathcal P$ over the specified set base $\mathcal C$, the
\termdefine{tripos-to-topos construction} forms the
\termdefineas{topos from a tripos}{topos $\mathcal C[\mathcal P]$} as follows. Its objects are pairs $\Pair{I}{
\sim}$ where $I \in \mathcal C$ and
$\sim \in \mathcal P(I \times I)$ satisfies, internally in the tripos's logic, the axioms of a partial equivalence
relation: symmetry $\sim\Pair{i}{j} \le \sim\Pair{j}{i}$ and transitivity $\sim\Pair{i}{j} \land \sim\Pair{j}{k} \le
\sim\Pair{i}{k}$. A morphism
$\Pair{I}{\sim} \to \Pair{J}{\approx}$ is represented by $F \in \mathcal P(I \times J)$ behaving like a functional
relation, modulo
mutual entailment: it is
$\sim/\approx$-strict and -extensional, single-valued, and total on the \termuseas{effective topos extent}{extent}
$E_\sim(i) := \sim\Pair{i}{i}$.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
一般tripos-to-topos定理を呼び出す箇所として本文自身が明示する外部入力。van
Oosten/Pittsの一般定理を局所証明したとは扱わず、指定されていない普遍性も主張しない。具体的PCAと有効トポスのPER計算は別に監査する。)
--> The tripos-to-topos theorem makes $\mathcal C[\mathcal P]$ an elementary topos. The construction uses
functional relations and their uniform realizability data, not just pointwise logical operations.
§{sec:effective-topos-construction} gives the concrete PER presentation and identifies where the general
theorem is invoked. We do not assert a universal property without specifying the relevant categories and morphisms.<!--
formalization: skip-end
-->

For the numerical lambda-index PCA, the assemblies defined here and those in
§{sec:tte-domains-eff-subcategories} have the same underlying sets, realization relations, and tracked
functions. Changing the presentation keeps each tracker unchanged. Thus the fully faithful graph
embedding proved there applies to $\AsmCat{K_1}$ as defined in this appendix.

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

\begin{proposition*}[\termdefineas{double negation for assemblies}{Double negation for assemblies}]
Every assembly has $\neg\neg$-stable equality in the displayed sense. Give $\UnderlyingSet{X}$ the constant
assembly structure $C$, in which every name realizes every element. The identity function on the
underlying set induces a $\neg\neg$-dense monomorphism from $X$ to $C$ in the realizability topos.
\end{proposition*}

\begin{proof}
For any predicate $\varphi$ and index $i$, the implication clause gives
$$\begin{aligned}
a\in(\neg\varphi)(i)&\quad\Longleftrightarrow\quad\varphi(i)=\emptyset,\\
a\in(\neg\neg\varphi)(i)&\quad\Longleftrightarrow\quad\varphi(i)\ne\emptyset.
\end{aligned}$$
Indeed, no computation can return an element of the empty set, while an implication with empty domain
has no input obligations. The second equivalence also uses that the PCA is nonempty. These are
external descriptions of the realizer sets, not a procedure for deciding whether they are empty.
Since every element of an assembly has a realizer, $(\neg\neg\delta)\Pair{x}{y}$ is $A$ when $x=y$
and empty otherwise.

An input realizer of $D\land\neg\neg\delta$ has the form
$$\PCAPair{\PCAPair{a}{b}}{c},\qquad a\in E(x),\quad b\in E(y),\quad
c\in(\neg\neg\delta)\Pair{x}{y}.$$
The last membership implies $x=y$. Thus the tracker
$$\PCAAbstract{w}{\mathsf l(\mathsf l w)}$$
returns $a\in\delta(x,y)$, proving stability. The identity combinator tracks the underlying identity
map into $C$. Equality in $C$ is exactly $\neg\neg\delta$, so the same tracker reflects equality
on the two source extents; this is the monomorphism condition in the PER presentation.

Let $\delta_C$ denote equality in $C$. The image predicate of this map is
$$J(y):=\bigcup_{x\in\UnderlyingSet{X}}\bigl(E(x)\land\delta_C(x,y)\bigr).$$
A realizer in this union is a pair whose first component realizes $x$ and whose second component
forces $x=y$. First projection therefore tracks $J\le E$. Conversely,
$\PCAAbstract{a}{\PCAPair{a}{a}}$ tracks $E\le J$, using the witness $x=y$ in the union.
Thus the image predicate is uniformly equivalent to $E$. Each of its values is nonempty, so
$(\neg\neg J)(y)=A$ for every $y$. The identity combinator consequently tracks
$\top\le\neg\neg J$, proving density. All these programs use supplied names; none selects a realizer
from an external element.
\end{proof}

The functional-relation construction above works over every PCA. Composition is
$$ (G\circ F)\Pair{x}{z}:=\bigcup_y\{\PCAPair{a}{b}:a\in F(x,y),\ b\in G(y,z)\}, $$
and equality of arrows is mutual uniform entailment. Pairing and projections, together with the
strictness, extensionality, and PER trackers, prove the identity and associativity laws exactly as in
§{sec:effective-topos-objects-morphisms}. Intermediate points occur only as witnesses in these unions.
The one-inclusion criterion from §{sec:effective-topos-subobjects-truth-values} also applies: for total
functional relations, a uniform inclusion in one direction implies a uniform inclusion in the other.
Its proof uses strictness, totality, single-valuedness, and extensionality, all available over any PCA.

\begin{theorem*}[\termdefineas{assembly reconstruction of separated PERs}{Assembly reconstruction of separated PERs}]
The graph construction gives a fully faithful functor from $\AsmCat{A}$ to the category of
realizer-valued PERs over $A$. Every such PER whose equality satisfies the displayed
$\neg\neg$-stability condition is isomorphic to an embedded assembly.
\end{theorem*}

\begin{proof}
For the embedding, repeat the graph argument of §{sec:tte-domains-eff-subcategories} with PCA names.
A tracker $r$ of $f:X\to Y$ gives totality of its graph by
$a\mapsto\PCAPair{a}{ra}$. The identity and composition laws use projections, equality preservation,
and transitivity; the one-inclusion criterion turns the resulting inclusions into equivalences.
A graph is inhabited precisely at $y=f(x)$, proving faithfulness. For fullness, totality and
single-valuedness of a functional relation determine a unique underlying value at each element.
If $u$ tracks totality and $v$ extracts the output extent, then
$\PCAAbstract{a}{v(ua)}$ tracks this function. Strictness gives a uniform inclusion of the original
relation into its graph, hence their equivalence. This uses the same argument over arbitrary names,
without computing underlying elements.

For the converse, let $\rho$ be the equality PER of an object with underlying set $I$, and put
$E(x):=\rho(x,x)$. Restrict first to the supported representatives and then form their external quotient:
$$\begin{aligned}
S&:=\{x\in I:E(x)\ne\emptyset\},\\
x\approx y&\quad\Longleftrightarrow\quad\rho(x,y)\ne\emptyset\quad\Pair{x}{y}\in S,\\
Q&:=\SetQuotient{S}{\approx}.
\end{aligned}$$
This is an equivalence relation: reflexivity uses the definition of the support, and the symmetry and
transitivity trackers send inhabited realizer sets to inhabited realizer sets. Representatives with
empty extent are excluded even when the underlying set contains them.

Give each class every name of each of its representatives:
$$a\Vdash_Q q\quad\Longleftrightarrow\quad
\exists x\in S\,\bigl(\EquivalenceClass{\approx}{x}=q\land a\in E(x)\bigr).$$
Every class has such a name, so this defines an assembly. Define relations in the two directions by
$$F(x,q)=G(q,x):=
\begin{cases}
E(x),&x\in S\text{ and }\EquivalenceClass{\approx}{x}=q,\\
\emptyset,&\text{otherwise}.
\end{cases}$$
No value of a tracker depends on choosing a representative of a class.

Both relations are strict: duplicate the input name to obtain the two extent realizers.
They are total using the identity tracker. In the forward direction an extent name realizes the forward relation at
the class of its representative; in the reverse direction a name of a class already
realizes some representative. These representatives witness membership, but are not computed outputs.
For extensionality, a realizer of $\rho(x,x')$ gives an extent realizer of $x'$ and implies that their
classes agree. This transports the displayed relations; assembly equality identifies the two class
arguments. For single-valuedness of $F$, the two classes are equal to the class of the same
representative, and first projection supplies a name of that class.

Let $s$ track the assumed stability condition. If $a\in E(x)$ and $b\in E(y)$ with
$\rho(x,y)\ne\emptyset$, put $w:=\PCAPair{a}{b}$. Then $w$ realizes the two extents and also belongs
to $(\neg\neg\rho)\Pair{x}{y}$, so
$$s\PCAPair{w}{w}\downarrow\in\rho(x,y).$$
This is a fixed operation on the supplied names. For single-valuedness of $G$, two names coming from
the same class give the required nonempty equality set by the quotient definition. The displayed
operation therefore supplies a realizer of equality, proving that $G$ is functional.

The same operation gives $G\circ F\le\rho$: a composite realizer contains two extent names whose
representatives have the same class. For the other composite, a realizer of $F\circ G$ contains names of a common
representative, so the two classes are equal and first projection realizes the assembly equality.
Applying the one-inclusion criterion to these two inclusions proves both inverse laws.
Thus $F,G$ induce an isomorphism between the original PER and the embedded assembly on $Q$.
The preceding proposition supplies stability for every embedded assembly, completing both constructions.
\end{proof}

### Subobjects and Modest Presentations {#sec:realizability-subobjects}

Fix a realizer-valued PER $X$ with equality $\rho$ and
extent $E(x):=\rho(x,x)$. The restriction and subobject-presentation proofs in
§{sec:effective-topos-finite-limits} and §{sec:effective-topos-subobjects-truth-values} use only the
uniform operations already constructed over a PCA. Thus every subobject of $X$ has a presentation
$\PERRestriction{X}{\varphi}\hookrightarrow X$, where
$$\varphi\le E,\qquad \rho(x,y)\land\varphi(x)\le\varphi(y).$$
Moreover, one such subobject lies below another exactly when their predicates admit a uniform entailment.
Indeed, an entailment gives a factorization by the restriction lemma. Conversely, a factorization
transforms a name in the first predicate into an inclusion realizer at some intermediate point;
extensionality of the second predicate transports that name back to the original point.

\begin{mathmeta}
  \define{RelativeNegation,DoubleNegationClosure}
\end{mathmeta}
On strict extensional predicates define
$$\RelativeNegation{X}{\varphi}:=E\land\neg\varphi,\qquad
\DoubleNegationClosure{X}{\varphi}:=E\land\neg\neg\varphi.$$
The extent factors are necessary: a predicate on an object must carry evidence that its argument exists.

\begin{proposition*}[\termdefineas{double-negation closure of subobjects}{Double-negation closure of subobjects}]
Relative negation represents the pseudocomplement in $\Subobjects{X}$. The operation
$\DoubleNegationClosure{X}{\varphi}$ is independent of the predicate presentation and induces a
monotone, extensive, idempotent map on $\Subobjects{X}$, equal to double pseudocomplementation.
A subobject presented by $\varphi$ is closed under this operation exactly when
$E\land\neg\neg\varphi\le\varphi$ uniformly.
\end{proposition*}

\begin{proof}
Both displayed predicates are strict by first projection. To check extensionality of the closure,
a name of $\rho(x,y)$ supplies a name of $E(y)$. If $\varphi(x)$ is inhabited, extensionality of
$\varphi$ makes $\varphi(y)$ inhabited, so any supplied name realizes its double negation.
For relative negation, if $\varphi(x)$ is empty but $\varphi(y)$ were inhabited, symmetry of $\rho$
and extensionality of $\varphi$ would give a contradiction. Thus $\varphi(y)$ is empty, and again
any supplied name realizes the required negation. Pairing with the computed extent gives uniform
trackers in both cases.

The empty predicate represents the least subobject, and conjunction represents the meet: a predicate
entails a conjunction exactly when it entails both components. The implication adjunction gives
$$\psi\land\varphi\le\bot\quad\Longleftrightarrow\quad
\psi\le\RelativeNegation{X}{\varphi}$$
for every strict extensional $\psi$, since its strictness already supplies $E$. This proves the
pseudocomplement universal property. On an input carrying an $E(x)$-name, the set
$(E\land\neg\varphi)(x)$ is empty exactly when $\varphi(x)$ is inhabited. Applying the negation clause
once more therefore gives
$$\RelativeNegation{X}{(\RelativeNegation{X}{\varphi})}\equiv
\DoubleNegationClosure{X}{\varphi},$$
with the identity tracker in both directions.

Strictness and double-negation introduction give
$\varphi\le\DoubleNegationClosure{X}{\varphi}$. If $\varphi\le\psi$, inhabitedness of $\varphi(x)$
implies inhabitedness of $\psi(x)$, so the same pair of names realizes the corresponding closure
inclusion. This proves monotonicity and independence of the presentation. A name of
$\DoubleNegationClosure{X}{(\DoubleNegationClosure{X}{\varphi})}$ implies that $\varphi(x)$ is inhabited;
retaining its extent component and its second name gives a name of $\DoubleNegationClosure{X}{\varphi}$.
The reverse entailment is extensivity. Hence the induced operation is idempotent. Finally, its fixed
points are exactly those presentations admitting the stated reverse entailment.

For the earlier monomorphism from an assembly $X$ into the constant object $C$, the image predicate is $J$.
Its closure is $E_C\land\neg\neg J$, where $E_C(y)=A$ for every $y$.
Given a name $a\in E_C(y)$, the density tracker supplies a name $b\in(\neg\neg J)(y)$;
pairing them gives a name of the closure. First projection gives the reverse entailment.
By the subobject-order criterion, the closure of this monomorphism is therefore the whole object $C$.
\end{proof}

\begin{proposition*}[\termdefineas{closed diagonal criterion for realizability}{Closed diagonal criterion}]
The diagonal subobject of $X\times X$ is closed under double-negation closure exactly when
$$\bigl(E(x)\land E(y)\bigr)\land\neg\neg\rho(x,y)\le\rho(x,y)$$
uniformly in both representatives. Thus the predicate condition used in the assembly reconstruction
is precisely categorical $\neg\neg$-separation.
\end{proposition*}

\begin{proof}
The product has underlying pairs, equality given by componentwise conjunction, and extent
$D(x,y):=E(x)\land E(y)$. Pairing functional relations proves its product universal property as in
§{sec:effective-topos-finite-limits}. The equality predicate $\delta(x,y):=\rho(x,y)$ is strict and
extensional on this product: symmetry and transitivity extract both extents and transport equality
in the two coordinates. It therefore defines a monomorphism from
$\PERRestriction{(X\times X)}{\delta}$ into the product.

The function $x\mapsto\Pair{x}{x}$ preserves equality into this restriction, and first projection preserves
equality back to $X$. Their composite on $X$ is the identity. For the other composite, an extent
realizer in the restriction has the form $\PCAPair{\PCAPair{a}{b}}{c}$, where the three components
realize $E(x),E(y),\rho(x,y)$. The transformation
$$\PCAPair{\PCAPair{a}{b}}{c}\longmapsto\PCAPair{\PCAPair{a}{c}}{a}$$
realizes equality between $\Pair{x}{x}$ and $\Pair{x}{y}$ in the restriction. Hence the graphs of the two functions
are inverse arrows. The resulting isomorphism commutes with the inclusion into the product, so this
restriction represents the actual diagonal subobject. Applying the preceding proposition to
$\delta$ with ambient extent $D$ proves the criterion. In particular, the assembly reconstruction
applies to every object with closed diagonal, and embedded assemblies have closed diagonals.
\end{proof}

**Shared names and modest presentations.** For an arbitrary PCA $A$, consider the following condition
on a realizer-valued PER $X$ with equality $\rho$ and extent $E$:
$$E(x)\cap E(y)\le\rho(x,y)\qquad\text{uniformly in }x,y.$$
Here the left side is the ordinary intersection of two subsets of $A$. Thus one tracker $d$ must
satisfy $da\downarrow\in\rho(x,y)$ whenever the same $a$ belongs to both extents. Supplying two possibly
different names, as in $E(x)\land E(y)$, would be a different and much stronger condition.

\begin{proposition*}[\termdefineas{shared-name criterion for modest presentations}{Shared-name criterion}]
The shared-name condition is inherited by subobjects and is invariant under isomorphism. An embedded
assembly satisfies it exactly when the assembly is modest. Consequently, a $\neg\neg$-separated object
satisfies it exactly when it is isomorphic to an embedded modest assembly.
\end{proposition*}

\begin{proof}
For an embedded assembly, a realizer of equality forces its two arguments to be equal. Hence the
shared-name condition implies modesty. Conversely, modesty makes the arguments equal whenever they
share a name; that same name then realizes their equality. The identity combinator tracks this direction.

To prove inheritance by subobjects, let a functional relation $F:X\to Y$ represent a monomorphism,
and suppose $Y$ has tracker $d$ for the condition. Let $t$ track totality of $F$, and let $l,s$ extract
source and target extents from an $F$-realizer. Let $e$ track extensionality of $F$. Finally, the uniform
injectivity criterion for monomorphisms in §{sec:effective-topos-subobjects-truth-values} supplies a tracker
$j$ taking two $F$-realizers with a common target to a source-equality realizer. These constructions use
only the PCA operations, so the same criterion applies here.

Given $a\in E_X(x)\cap E_X(x')$, totality gives the same value $u:=ta$ in both $F(x,y)$ and
$F(x',y')$ for some $y,y'$. Application is single-valued, so $v:=su$ belongs to both target extents.
Put
$$w:=dv,\qquad z:=e\PCAPair{\PCAPair{lu}{u}}{w}.$$
Then $w\in\rho_Y(y,y')$, $z\in F(x,y')$, and $j\PCAPair{z}{u}\in\rho_X(x,x')$.
Abstracting this fixed composite over $a$ gives the required tracker. The points $y,y'$ witness
membership in unions; the computation does not select them. Applying this argument to an isomorphism
and its inverse proves invariance under isomorphism.

Now suppose $X$ is separated and satisfies the condition. In its reconstructed assembly on
$Q=\SetQuotient{S}{\approx}$, a common name of two classes names representatives $x,y$ of those classes.
Applying $d$ gives a realizer in $\rho(x,y)$, so $x\approx y$ and the classes coincide. Thus the
reconstructed assembly is modest, and the previously constructed name-preserving isomorphism gives
the required presentation. Conversely, an embedded modest assembly satisfies the condition by the
first paragraph, and the condition transports along any isomorphism.
\end{proof}

\begin{proposition*}[\termdefineas{uniform image criterion for epimorphisms}{Uniform image criterion for epimorphisms}]
A functional relation $F:X\to Y$ represents an epimorphism exactly when
$$E_Y(y)\le I_F(y),\qquad I_F(y):=\bigcup_{x\in X}F(x,y),$$
uniformly in $y$. The resulting computation returns a realizer in the image; it need not compute a
preimage point $x$.
\end{proposition*}

\begin{proof}
Suppose first that the displayed entailment holds and that $G\circ F=H\circ F$.
From $b\in G(y,z)$, strictness and the assumed entailment give $a\in F(x,y)$ for some $x$.
The realizer $\PCAPair{a}{b}$ lies in $(G\circ F)\Pair{x}{z}$, so the assumed equality transforms it into
$\PCAPair{c}{e}\in(H\circ F)\Pair{x}{z}$, with $c\in F(x,y')$ and $e\in H(y',z)$ for some $y'$.
Single-valuedness of $F$ gives a realizer of $\rho_Y(y,y')$ from $a,c$.
Symmetry and extensionality of $H$ then transform $e$ into an $H(y,z)$-realizer. Every operation is
uniform in the original input $b$. Thus $G\le H$, and the one-inclusion criterion gives $G=H$.
This proves the categorical cancellation property.

\begin{mathmeta}
  \define{PCATruthValues}
\end{mathmeta}
For the converse, use the truth-value PER $\PCATruthValues{A}$ on $\PowerSet{A}$, with
$$S\sim_\Omega T:=(S\to T)\land(T\to S).$$
The implication adjunction gives the equality-preserving map $y\mapsto\varphi(y)$ for every strict
extensional predicate $\varphi$. Its graph is
$$\chi_\varphi(y,S):=E_Y(y)\land\bigl(\varphi(y)\sim_\Omega S\bigr).$$
If $\chi_\varphi=\chi_\psi$, an input $a\in\varphi(y)$ first gives a realizer of
$\chi_\varphi(y,\varphi(y))$ by strictness and the identity implications. Transform it into a realizer
of $\chi_\psi(y,\varphi(y))$ and apply the implication $\varphi(y)\to\psi(y)$ to $a$.
This gives $\varphi\le\psi$ uniformly, and reversing the arrows gives $\psi\le\varphi$.

Now take $\varphi:=I_F$ and $\psi:=E_Y$. An $F(x,y)$-realizer belongs to $I_F(y)$ and supplies
$E_Y(y)$. Combined with a realizer of $\chi_{I_F}(y,S)$, it therefore supplies an $S$-realizer.
Parameter abstraction gives constant transformers $E_Y(y)\to S$ and $S\to E_Y(y)$ from these
supplied names. Hence
$$\chi_{I_F}\circ F\le\chi_{E_Y}\circ F,$$
and the one-inclusion criterion gives equality. If $F$ is epic, cancel it to obtain
$\chi_{I_F}=\chi_{E_Y}$. The preceding argument yields $E_Y\le I_F$, as required.
\end{proof}

\begin{mathmeta}
  \define{NameObject}
\end{mathmeta}
Let $\NameObject{A}$ be the embedded assembly with underlying set $A$ and realizability relation
$$a\Vdash_{\NameObject{A}} b\quad\Longleftrightarrow\quad a=b.$$
A subquotient of this object means an object $X$ admitting a diagram
$$\NameObject{A}\xleftarrow{\ m\ }S\xrightarrow{\ q\ }X,$$
where $m$ is a monomorphism and $q$ is an epimorphism in $\RTCat{A}$.

\begin{proposition*}[\termdefineas{subquotient criterion for shared names}{Subquotient criterion}]
An object $X$ satisfies the shared-name condition exactly when it is a subquotient of $\NameObject{A}$.
Consequently, among $\neg\neg$-separated objects, these subquotients are exactly the objects isomorphic
to embedded modest assemblies.
\end{proposition*}

\begin{proof}
Suppose $d$ witnesses the shared-name condition for $X$. Put
$$S:=\{a\in A:\exists x\;a\in E_X(x)\}$$
and give each $a\in S$ only the name $a$. The inclusion $S\hookrightarrow A$ is tracked by the identity.
Its graph is a monomorphism even when tested by arrows from arbitrary realizer-valued PERs: equality
after composition with this graph gives a uniform transformation between the original relation
realizers, because equality of the included values forces equality of their preimages. First projection
extracts the original relation realizer. Thus this is a subobject of $\NameObject{A}$.

For each $a\in S$, choose an underlying representative $x_a$ with $a\in E_X(x_a)$.
The function $a\mapsto x_a$ preserves equality, tracked by the identity: a source-equality name is
$a$ itself, which realizes $\rho_X(x_a,x_a)$. Its graph $F:S\to X$ is therefore functional.
Given any $a\in E_X(x)$, the chosen representative $x_a$ and $x$ share the name $a$, so
$$a\longmapsto\PCAPair{a}{da}\in F(a,x)$$
provides uniform image coverage. The preceding proposition makes $F$ epic. The choice of $x_a$ is made
only in the underlying mathematics: this tracker uses $a,d$ and never computes $x_a$.

Conversely, the shared-name condition holds for $\NameObject{A}$ by modesty and is inherited by its
subobject $S$. Let $F:S\to X$ be epic. From a common name $a\in E_X(x)\cap E_X(x')$, the uniform image
criterion produces the same value $b$ in $F(s,x)$ and $F(s',x')$ for some $s,s'$.
Applying source strictness to $b$ gives a common extent name of $s,s'$. The condition on $S$ converts
it into equality evidence for $s,s'$. Extensionality transports $F(s,x)$ to $F(s',x)$, and
single-valuedness then gives equality evidence for $x,x'$. This composite is uniform in $a$.

Separation is also inherited by monomorphisms. Indeed, for a monomorphism $F:S\to Y$ with separated
codomain, extent names for $s,s'$ give $F$-realizers at some $y,y'$ by totality. If $\rho_S(s,s')$ is
inhabited, extensionality and single-valuedness make $\rho_Y(y,y')$ inhabited. Separation of $Y$
converts the computed target extent names into target-equality evidence. Extensionality of $F$ and
its uniform injectivity then yield source-equality evidence, uniformly in the original input.
Thus an object isomorphic to an embedded assembly is separated. Together with the shared-name
criterion for modest presentations, this proves both directions of the final assertion.
\end{proof}

For $A=K_1$, the assembly $\NameObject{K_1}$ has underlying set $\NN$ with $E(n)=\{n\}$.
This is the standard presentation of the natural-numbers object of $\EffCat$ [@vanOosten2008].
An object of $\EffCat$ is called \termdefineas{discrete object in the effective topos}{discrete} if it is
a subquotient of this object. The proposition therefore identifies the separated discrete objects
with the essential image of $\ModCat{K_1}$; here discrete is a categorical condition, not a topology
on the underlying representatives.

### Specializing to the Effective Topos {#sec:realizability-effective-specialization}

Setting $\mathcal C = \SetCatU$ and $\mathcal P = \mathcal P_{K_1}$ in the realizability tripos
gives
$$\EffCat \;:=\; \SetCatU[\mathcal P_{K_1}].$$
An object of $\EffCat$ is a $U$-small set $I$ together with a $\mathcal P_{K_1}$-PER $\sim$, which one can read as: $I$
is a set of *would-be elements*, and $\sim\Pair{i}{j}$ specifies the realizers witnessing that $i$ and $j$ name the same
actual element. The extent $E_\sim(i) = \sim\Pair{i}{i}$ is the set of realizers of $i$, recovering the assembly
perspective
when $\sim$ is the equality PER. Each object and morphism uses $U$-small data, although the collection of all
objects is $U$-large, so $\EffCat$ is locally $U$-small in the sense
of §{sec:cat-universe}. <!--
formalization: skip-begin (引用・背景説明・読書案内:
K1でのPER対象とextentはPCARealizabilityPER、
実際の集合宇宙内の関係同値類のサイズはSetTheoryCategorySize.functionalRelationClasses_memへ接続した
。未リンク部分は初等トポスなら有限余極限を持つという、上で引用する一般tripos-to-topos定理・一般トポス理論の帰結だけ。)
--> As an elementary topos, it has finite limits and colimits.<!--
formalization: skip-end
-->

The earlier categories embed cleanly: $\AsmCat{K_1} \hookrightarrow \EffCat$ as the $\neg\neg$-separated objects, and
$\ModCat{K_1} \hookrightarrow \AsmCat{K_1} \hookrightarrow \EffCat$ as the separated discrete objects. The
canonical monomorphism
from each assembly into the constant object on its underlying set is $\neg\neg$-dense. <!--
formalization: skip-begin (引用・背景説明・読書案内:
assemblyのseparated像、modestのseparated-discrete像、定数対象へのdense
monoは具体的なPCA定理に狭く接続した。残りは引用する一般tripos意味論での妥当性の読み方と、参照先の内部原理の要約。
CT/MPやKLS/Ceitinを新たに証明する箇所ではなく、特に連続性を純粋なトポス公理の帰結とは扱わない。)
--> The internal-logic computations
needed in §{sec:effective-topos-internal-logic} take place in the tripos
$\mathcal P_{K_1}$: a sentence is \termdefineas{valid in effective topos}{valid in $\EffCat$} iff the associated element
of $\mathcal P_{K_1}(1) = \PowerSet{K_1}$ contains a realizer. Church's Thesis and Markov's Principle are validated by
their standard $K_1$ realizers. The Continuity Principle is validated separately through the
Kreisel--Lacombe--Shoenfield/Ceitin theorem described in §{sec:effective-topos-internal-logic}.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
一般PCAごとの実現可能性モデルを比較する結びの概説。K2やdomainモデルは文献的背景で、
一般tripos-to-topos定理の外部入力に依存する。TTE/domainとの圏同値を主張しない旨も明示され、
追加の局所的構成・証明を提示しない。)
-->
A general PCA $A$ with $U$-small carrier gives a realizability topos $\RTCat{A} := \SetCatU[\mathcal P_A]$. With $A =
K_1$ this is $\EffCat$; with $A = K_2$ this is the function realizability topos modeling
continuous-but-not-necessarily-computable analysis; with $A$ a domain-theoretic PCA it produces realizability toposes
adapted to denotational semantics. The unified categorical framework places the external comparisons of
§{sec:domain-theory-quasi-polish} and §{sec:tte-domains-eff-subcategories} in a common setting without asserting a
categorical equivalence. TTE on Polish spaces, $\omega$-continuous-domain semantics, and computable analysis all
organize
finite information, while the choice of PCA determines whether the tracked evidence is recursive, continuous, or
domain-theoretic.<!--
formalization: skip-end
-->

## Further Reading {#sec:appendix-category-realizability-further-reading}
\index{further reading!category theory and realizability}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Goldblatt、Mac Lane–Moerdijk、Pittsの文献を選ぶための読書案内だけで、追加の局所的証明ではない。)
--> This appendix is a working toolkit, not a substitute for the standard references. For the categorical side of logic,
Goldblatt gives a compact route from elementary \termuse{category theory} to topos semantics [@Goldblatt1984], while Mac
Lane--Moerdijk develops sheaves, sites, and geometric logic at book length [@MacLaneMoerdijk1992]. Pitts's Handbook
chapter is the best next stop for categorical logic as a technical language, especially the passage from syntax to
categorical semantics [@Pitts2000].<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
KunenとGaoへの読書案内だけで、追加の局所的構成・証明ではない。)
-->
For forcing and \termuse{set theory}, Kunen remains the most direct source for the independence-proof background that
underlies Appendix §{sec:appendix-forcing-background} [@Kunen1980]. For invariant descriptive set theory, Gao is the
standard bridge from Polish-group actions to classification by Borel reducibility, and it is the natural companion to
the Polish-group and Borel-reducibility chapters [@Gao2009].<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
van OostenとBauerの実現可能性文献への読書案内だけで、追加の局所的証明ではない。)
-->
For realizability, van Oosten is the systematic reference for assemblies, modest sets, triposes, and the effective topos
[@vanOosten2008]. Bauer's notes are a useful complementary entry point because they keep the computational and
constructive readings visible while developing the realizability semantics [@BauerRealizabilityNotes].<!--
formalization: skip-end
-->

\cleardoublepage
\phantomsection
\addcontentsline{toc}{chapter}{Index}
\printindex
