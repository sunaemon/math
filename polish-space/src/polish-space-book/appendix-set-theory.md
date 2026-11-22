# Appendix: Set Theory {#sec:appendix-set-theory}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
付録の内容・論理付録との関係と標準参考文献を案内する導入文。個別の数学的主張は後続の構成・補題として対象に残す。)
--> This appendix specializes the logical apparatus of §{sec:appendix-logic} to the language of \termdefine{set theory},
$L_\in$. It develops ZFC, ordinals, transfinite recursion, cardinality and cofinality, the cumulative hierarchy,
universe conventions, and the Lévy hierarchy with its basic absoluteness results. Standard references are
[@Jech2003] and [@Kunen1980].\termref{absoluteness}<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
後続のforcing・Borel-code・measure・random forcing付録への依存関係を案内する文。
新規の模型・構成をここでは主張しない。)
--> The subsequent appendices use this background to develop forcing in §{sec:appendix-forcing-background},
Borel-code absoluteness in §{sec:appendix-borel-absoluteness}, measure absoluteness in
§{sec:appendix-measure-absoluteness}, and random forcing in §{sec:appendix-random-forcing}.
Each construction states the model axioms it needs.<!--
formalization: skip-end
-->

## ZFC axioms {#sec:zfc-axioms}
\index{ZFC}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後の公理リストと後続の略記の定義への案内。各公理と略記は別の本文単位として対象に残す。)
--> The following are the Zermelo–Fraenkel axioms with Choice. The abbreviations $\emptyset$, $\IncludedIn$, $\bigcup$,
$\bigcap$, $\cap$,
$\cup$, $\{a,b\}$, $\exists!$, $\mathrm{dom}$ used below are spelled out in terms of $\in$ and $=$ at the end of the
section.<!--
formalization: skip-end
-->

*   **Extensionality.** Two sets are equal iff they have the same elements: $\forall x\, \forall y\, [\forall z\,(z \in
    x \leftrightarrow z \in y) \to x = y]$.
*   **Pairing.** For any sets $a, b$, the set $\{a, b\}$ exists: $\forall a\, \forall b\, \exists p\, \forall x\,(x \in
    p \leftrightarrow x = a \lor x = b)$.
*   **Union.** For any set $x$, the set $\bigcup x$ exists: $\forall x\, \exists u\, \forall z\,(z \in u \leftrightarrow
    \exists y\,(z \in y \land y \in x))$.
*   **Power Set.** For any set $x$, the set $\PowerSet{x}$ of subsets of $x$ exists: $\forall x\, \exists p\, \forall
    z\,(z \in p \leftrightarrow z \IncludedIn x)$.
*   **Infinity.** An inductive set exists:
    $$\exists x\,\big[\exists e\,(e \in x \land \forall z\, z \notin e) \land \forall y \in x\, \exists s \in x\,
    \forall w\,(w \in s \leftrightarrow w \in y \lor w = y)\big].$$
    After the abbreviations below are introduced, this is:
    $$\exists x\,(\emptyset \in x \land \forall y \in x\,(y \cup \{y\} \in x)).$$
    The $\IncludedIn$-least such set is $\omega$.
*   **Replacement.** Replacement is a schema: one instance per formula $\varphi$, in which parameters are allowed. The
    image of a set under a definable function is a set: $\forall \vec p\,\forall x\, [(\forall a \in x\, \exists!\, b\,
    \varphi(a,b,\vec p)) \to \exists y\, \forall b\,(b \in y \leftrightarrow \exists a \in x\, \varphi(a,b,\vec p))]$.
*   **Foundation.** Every nonempty set has an $\in$-minimal element: $\forall x\,(x \ne \emptyset \to \exists y \in
    x\,(y \cap x = \emptyset))$. Equivalently, $\in$ is well-founded on sets. In particular, no set contains
    itself; this consequence
    alone is weaker than Foundation.
*   **Choice.** For any family of nonempty sets a choice function exists: $\forall x\,(\emptyset \notin x \to \exists
    f\,(\mathrm{FunGraph}(f) \land \mathrm{dom}\, f = x \land \forall a \in x\,\, f(a) \in a))$, where
    $\mathrm{FunGraph}(f)$ abbreviates "every element of $f$ is an ordered pair, and $\Pair{a}{b},\Pair{
a}{b'}\in f$ implies $b=b'$." <!--
    formalization: skip-begin (引用・背景説明・読書案内:
    8公理のfirst-order sentenceは既存の7リンクと追加したchoiceSentenceに接続した。
    Foundationからの自己所属排除も任意の所属構造でPairingとFoundationから証明した。
    残るZornの補題・well-ordering principleとの同値は名前だけを挙げる標準の背景で、この節が証明する局所的な同値定理ではない。
    choiceSentenceの定義をZornとの同値の証明として扱わない。)
    --> Equivalent: Zorn's lemma; the well-ordering principle.<!--
    formalization: skip-end
    -->

**Separation as a derived schema.** The Separation schema says that for any formula $\varphi(z,\vec p)$, with parameters
$\vec p$ allowed and with $y$ not free in $\varphi$, the subset $\{z \in x : \varphi(z,\vec p)\}$ exists:
$$\forall \vec p\,\forall x\, \exists y\, \forall z\,(z \in y \leftrightarrow z \in x \land \varphi(z,\vec p)).$$
<!--
formalization: skip-begin (引用・背景説明・読書案内:
Separationの式はseparationSentence、
Replacementからsingleton-or-emptyを作りUnionを取る冗長性の主張は任意の所属構造でのmodels_separation
_of_replacementへ接続した。残りはZermelo/Fraenkel/Skolem/Mirimanoff/von
Neumannの引用付き研究史と現代の公理リストの慣例・参考文献案内であり、局所的な証明義務ではない。)
--> Historically Separation came first: it was an axiom in Zermelo's original system $Z$ [@Zermelo1908], before Fraenkel
[@Fraenkel1922] and Skolem [@Skolem1923] independently added Replacement (giving $ZF$) and Mirimanoff [@Mirimanoff1917]
and von Neumann [@vonNeumann1925] introduced Foundation.<!--
formalization: skip-end
-->  In the presence of Replacement, however, Separation is
redundant: after $\emptyset$ has been derived from Infinity, replace each $a \in x$ by $\{a\}$ if $\varphi(a,\vec p)$
holds and by $\emptyset$ otherwise, then take the union of the resulting set. <!--
formalization: skip-begin (引用・背景説明・読書案内:
Separationの式はseparationSentence、
Replacementからsingleton-or-emptyを作りUnionを取る冗長性の主張は任意の所属構造でのmodels_separation
_of_replacementへ接続した。残りはZermelo/Fraenkel/Skolem/Mirimanoff/von
Neumannの引用付き研究史と現代の公理リストの慣例・参考文献案内であり、局所的な証明義務ではない。)
--> Many modern presentations therefore keep
it in the axiom list for convenience even though it is provable; see [@Kunen1980, §I.6] or [@Jech2003, Ch. 1] for the
standard development.<!--
formalization: skip-end
-->

\begin{lemma*}[Deriving Separation]
For each formula $\varphi(a,\vec p)$, its Separation instance follows from Extensionality, Pairing, Union,
Infinity, and one Replacement instance. The argument works inside any model of these axioms; transitivity
of the model is not required.
\end{lemma*}

\begin{proof}[Proof]
Fix an arbitrary $L_\in$-structure satisfying the hypotheses. Throughout this proof, $\in$ denotes
its interpreted membership relation, and all variables and quantifiers range over its domain.

Choose fresh variables $b,z$ and put
$$\theta(a,b,\vec p)\;:\equiv\;
\forall z\,(z\in b\leftrightarrow z=a\land\varphi(a,\vec p)).$$
If $\varphi(a,\vec p)$ holds, Pairing supplies $b=\{a\}$; otherwise the empty set supplied by Infinity is suitable.
In either case, Extensionality makes $b$ unique. This establishes the premise of Replacement without using
Separation.

Apply Replacement to $\theta$ on the given set $x$ to obtain a set $C$ satisfying
$$b\in C\quad\Longleftrightarrow\quad\exists a\in x\,\theta(a,b,\vec p).$$
Union now gives $\bigcup C$, and
$$\begin{aligned}
z\in\bigcup C
&\Longleftrightarrow\exists a\in x\,(z=a\land\varphi(a,\vec p))\\
&\Longleftrightarrow z\in x\land\varphi(z,\vec p).
\end{aligned}$$
Thus $\bigcup C$ is the required subset. Each step uses only the model's own quantifiers and axioms, so
no appeal to external elements or transitivity enters the derivation.
\end{proof}

Each abbreviation below is a conservative shorthand over $L_\in$, in the sense of the extension-by-definition framework
of §{sec:definitional-extensions}; see also [@Shoenfield1967, §4.6]. They come in three kinds:

*   **Relation abbreviations** (pure formula abbreviations), such as $\IncludedIn$ and $\exists!$: a new relation symbol
    is defined by an $L_\in$-formula. Always eliminable by inlining.
*   **Definitional extensions** introducing a new function or constant symbol, such as $\emptyset$, $\{a,b\}$, $\bigcup
    x$, $x\cap y$, and $\mathrm{dom}\,f$: the relevant \termuse{ZFC} axiom proves a $\forall \vec{x}\, \exists! y\,
    \varphi(\vec{x}, y)$ statement (existence), Extensionality supplies uniqueness, and adjoining a new function or
    constant symbol with defining property $\varphi$ gives a conservative extension.
*   **Contextual term notations**, such as the application $f(a)$ and the intersection $\bigcap x$ of a nonempty family:
    no total new function symbol is added when the notation is partial or convention-dependent. Instead the notation is
    unfolded *in context*: an atomic formula containing $f(a)$ is rewritten via $\Pair{a}{\cdot} \in f$, with
    quantifier scope determined by where $f(a)$ sits, as detailed below.

Every $L_\in$-sentence provable using the new notation is already provable in ZFC, so we may use the symbols freely and
unfold them only when proof-theoretic precision demands. Complexity claims are stricter: whenever
§{sec:zfc-absoluteness} calls a formula $\Delta_0$, $\Sigma_n$, or $\Pi_n$, the claim is about its unfolded $L_\in$
form. The definitions below are chosen so the routine atomic uses needed there unfold with only bounded
quantifiers.\termref{absoluteness}

*   $x \IncludedIn y \;:\equiv\; \forall z\,(z \in x \to z \in y)$ — pure first-order logic on $\in$.
*   $\exists!\, x\, \varphi(x) \;:\equiv\; \exists x\,[\varphi(x) \land \forall y\,(\varphi(y) \to y = x)]$ — pure
    first-order logic.
*   $\emptyset$ — the unique $e$ with $\forall z\,(z \notin e)$, whose existence follows directly from the
    displayed Infinity axiom, before Separation is derived.
    Afterwards, Separation with $z \ne z$ gives another construction.
*   $\{a, b\}$ — the unique $p$ with $\forall x\,(x \in p \leftrightarrow x = a \lor x = b)$, obtained by Pairing. The
    singleton is $\{a\} := \{a, a\}$, and finite sets $\{a_0,\ldots,a_n\}$ are defined by induction from Pairing and
    binary union.
*   $\bigcup x$ — the unique $u$ with $\forall z\,(z \in u \leftrightarrow \exists y\,(z \in y \land y \in x))$,
    obtained by Union. The binary union is $x \cup y := \bigcup \{x, y\}$.
*   $\bigcap x$ — contextual notation for nonempty families: if $x \ne \emptyset$, it denotes the unique $i$ with
    $\forall z\,(z \in i \leftrightarrow \forall y \in x\, z \in y)$. To construct it, choose some $a \in x$ and apply
    the derived Separation schema to $a$. Thus $\bigcap x$ is used only for nonempty families unless an ambient universe
    is explicitly specified.
*   $x \cap y$ — the unique $i$ with $\forall z\,(z \in i \leftrightarrow z \in x \land z \in y)$, obtained by the
    derived Separation schema applied to $x$.
*   Kuratowski's ordered pair $\Pair{a}{b} \;:=\; \{\{a\}, \{a, b\}\}$. A \termdefine{function graph} $f$ is a
    set of ordered pairs with $\Pair{a}{b}, \Pair{a}{b'} \in f \to b = b'$.
*   $f(a) = b \;:\equiv\; \Pair{a}{b} \in f$ — application as ordered-pair membership. This is a contextual
    notation for atomic formulas, not a new function symbol of $L_\in$: $f(a)$ has no value when $f$ is not a function
    graph or $a \notin \mathrm{dom}\, f$. The atomic forms "$f(a)=b$" and "$f(a)\in y$" abbreviate $\Pair{
a}{b}\in f$ and $\exists v \in \bigcup\bigcup f\,(\Pair{a}{v}\in f \land v\in y)$ respectively, so the
    displayed expansion remains bounded. Other uses of $f(a)$ are made only under hypotheses asserting that $f$ is a
    function graph and $a\in\mathrm{dom}\,f$, where the unique value makes the notation unambiguous. In proof-theoretic
    contexts with negations or repeated occurrences, unfold application before applying logical connectives.
*   $\mathrm{dom}\, f \;:=\; \{a : \exists b\,\Pair{a}{b} \in f\}$, obtained by the derived Separation schema on
    $\bigcup \bigcup f$.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
本文で関数をgraph/domain/codomainの組として呼ぶ場合と、ZFCが構成するgraphとの表記上の慣例の説明。
ここで新しい関数対象や同値定理を構成する箇所ではない。)
--> Throughout the main text, a function is often treated as a triple consisting of its graph, domain, and codomain; the
function graph above is the set that ZFC literally constructs.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
ZFとZFCの命名規約と本書でACを使う場面の列挙。Tychonoff・cardinality・successor-cardinal
regularityの証明をこの段落で展開せず、ここで新しい局所補題として使用しない背景説明。)
-->
ZF refers to the same list without Choice. Results in this text use AC routinely — Tychonoff for Polish products, every
set has a cardinality, regularity of successor cardinals.<!--
formalization: skip-end
-->

## Sets and proper classes {#sec:zfc-classes}

A \termdefineas{class in set theory}{class} is a collection of sets defined by a formula, $\{x : \varphi(x)\}$. A
\termdefine{class function} is a definable functional relation: a formula $\Phi(x,y)$ such that, for each set $x$ in the
intended domain class, there is a unique set $y$ with $\Phi(x,y)$. We write $F(x)=y$ for this unique value, but this is
still only shorthand for the defining formula. A class that is itself an element of the universe is a
\termdefineas{set in ZFC}{set}; one that is not is a \termdefine{proper class}. Standard examples of proper classes:

*   $V := \{x : x = x\}$, the universe of all sets.
*   $\mathrm{Ord} := \{x : \mathrm{Ord}(x)\}$, the class of ordinals.
*   $\mathrm{Card}$, the class of cardinals.

That $V$ and $\mathrm{Ord}$ are not sets is the \termdefine{Russell paradox} and \termdefine{Burali-Forti paradox}
respectively. <!--
formalization: skip-begin (引用・背景説明・読書案内:
冒頭の数学的主張は、任意の所属構造でSeparationから導くno_universal_set_of_separationと、
ZFSet上のno_set_of_all_ordinalsへ接続した。残る155–157行だけを対象外とする。
これはZFCの構文ではclassを新しい対象として加えず定義式の略記とする規約と、定義式の複雑さに応じた絶対性を後の節で扱うという読書案内であり、
この段落で追加の存在・閉包・絶対性定理を主張または証明していない。
Cardが真クラスであるという150–152行の例や略記の一般的保守性はこの判定に含めない。)
--> In ZFC, classes have no formal status — they are abbreviations for formulas — and quantifying over a
proper class reduces to quantifying over its defining formula. This is why the Lévy hierarchy matters for class-defined
objects: the complexity of the defining formula controls which absoluteness facts are available.\termref{absoluteness}
<!--
formalization: skip-end
-->

## Well-orders and the von Neumann ordinals {#sec:ordinals-von-neumann}
\index{well-order}
\index{von Neumann ordinal}

A \termdefine{well-order} on a set is a total order in which every nonempty subset has a least element. The natural
numbers under $<$ are the prototype. By contrast $\ZZ$ under $<$ is not well-ordered because $\ZZ$ itself has no least
element, and $\R$ under $<$ is not well-ordered because the open interval $\OpenInterval{0}{1} \StrictlyIncludedIn \R$
has no least
element. Two
well-orders are \termdefine{order-isomorphic} if some bijection between them preserves $<$.

\termdefineas{von Neumann ordinal}{Von Neumann's construction} packages well-order types as canonical sets. An
\termdefine{ordinal} is a transitive set well-ordered by $\in$, where *transitive* means every element is also a subset.
The first few:
$$
\begin{aligned}
0 &:= \emptyset, &
1 &:= \{0\}, &
2 &:= \{0,1\},\\
&\ldots, &
n &:= \{0,1,\ldots,n-1\}, &
\omega &:= \{0,1,2,\ldots\}.
\end{aligned}
$$
Each ordinal $\alpha$ is the set of strictly smaller ordinals, $\alpha = \{\beta : \beta < \alpha\}$, and the order $<$
on ordinals coincides with $\in$. The class $\mathrm{Ord}$ of all ordinals is itself well-ordered by $\in$ but is a
proper class, not a set, by the Burali-Forti paradox. Every well-order is in fact order-isomorphic to a unique ordinal —
see §{sec:ordinals-representation} after the recursion principle is in place.

In symbols, the von Neumann definition is the ZFC formula
$$\begin{aligned}
\mathrm{Ord}(x) \;&:\equiv\; \mathrm{Trans}(x) \;\wedge\; (\forall y \in x)\,\mathrm{Trans}(y), \\
\mathrm{Trans}(x) \;&:\equiv\; (\forall y \in x)(\forall z \in y)\; z \in x.
\end{aligned}$$
This formula is equivalent in ZF to the definition above. First, two ordinals are comparable by membership:
their intersection is an initial segment of each, and a proper initial segment of an ordinal is the predecessor
set of its least omitted element, hence that element itself. If the intersection were proper in both, it would
belong to itself, contradicting Foundation. Now apply membership induction to a transitive set all of whose
elements are transitive. Each of its elements has the same property and is therefore an ordinal by induction.
Comparability of ordinals and Foundation then make membership a well-order on the original transitive set.
The complexity classification and its forcing consequences appear in §{sec:zfc-absoluteness}.\termref{absoluteness}

## Successor and limit ordinals {#sec:ordinals-successor-limit}

The \termdefine{successor} of an ordinal $\alpha$ is $\alpha + 1 := \alpha \cup \{\alpha\}$, the next-larger ordinal. An
ordinal is a \termuse{successor} if it equals $\beta + 1$ for some $\beta$. A \termdefine{limit ordinal} is a nonzero
ordinal that is not a successor; the smallest limit ordinal is $\omega$. Larger limit ordinals built from arithmetic
appear in §{sec:ordinals-arithmetic}.

## Transfinite induction and recursion {#sec:ordinals-induction}

\begin{theorem*}[\termdefineas{transfinite induction}{Transfinite induction}]
To prove $P(\alpha)$ for every ordinal $\alpha$, it suffices to show that whenever $P(\beta)$
holds for every $\beta < \alpha$, then $P(\alpha)$ holds. Equivalently, a class of ordinals containing $0$, closed under
successor, and closed under suprema at limits is the class of all ordinals.
\end{theorem*}

\begin{proof}[Proof] Suppose the hypothesis holds but $P$ fails at some ordinal $\alpha_0$. By
§{sec:ordinals-successor-limit}, $\alpha_0+1$ is an ordinal, hence a set well-ordered by $\in$. Therefore
$$\{\alpha\in\alpha_0+1:\neg P(\alpha)\}$$
is a nonempty set of ordinals and has an $\in$-least element $\alpha^*$. By minimality, $P(\beta)$ holds for every
$\beta < \alpha^*$, so the hypothesis forces $P(\alpha^*)$ — contradicting $\neg P(\alpha^*)$.
Splitting the inductive step into zero, successor, and nonzero limit cases gives the equivalent formulation above.
\end{proof}

\begin{theorem*}[\termdefineas{transfinite recursion}{Transfinite recursion}]
Fix a class function $H$ assigning a set to each pair of sets.
For every ordinal $\gamma$, there is a unique function graph $f$ with domain $\gamma$ such that
$$f(\alpha)=H(\alpha,\restrict{f}{\alpha})\qquad(\alpha<\gamma).$$
The solutions on different ordinal domains agree on their common domain.
\end{theorem*}

\begin{proof}[Proof]
\emph{Uniqueness.} Two solutions $f,f'$ agree on their common domain by transfinite induction on $\alpha$.
If they agree below $\alpha$, then $\restrict{f}{\alpha}=\restrict{f'}{\alpha}$, so the same rule gives
$$f(\alpha)=H(\alpha,\restrict{f}{\alpha})=H(\alpha,\restrict{f'}{\alpha})=f'(\alpha).$$
In particular, there is at most one solution on any fixed ordinal domain.

\emph{Existence.} For each ordinal $\gamma$, construct a solution $f_\gamma$ on $\gamma+1$ by transfinite induction.
Suppose the solutions $f_\beta$ have been constructed for $\beta<\gamma$.
Agreement on common domains makes them compatible. Replacement collects these uniquely determined graphs into a set,
so their union $g:=\bigcup_{\beta<\gamma}f_\beta$ is a function graph. Its domain is
$$\bigcup_{\beta<\gamma}(\beta+1)=\gamma.$$
Indeed, each smaller ordinal belongs to its own successor, and the successor of any smaller ordinal is contained in
$\gamma$. For $\gamma=0$ this is the empty union, and $g=\emptyset$.

The graph $g$ satisfies the recursion equation at every earlier input: a partial solution containing that input
agrees with $g$ on its entire predecessor segment. Now set
$$f_\gamma:=g\cup\{\Pair{\gamma}{H(\gamma,g)}\}.$$
The new input is outside the domain of $g$, so this remains a function. Adding its value changes none of the earlier
restrictions, and its restriction to $\gamma$ is exactly $g$. Thus every required equation holds.
The same union construction gives a solution on any ordinal domain, including a limit domain, proving the theorem.
\end{proof}

Consequently, the assignment $F(\alpha):=f_\alpha(\alpha)$ defines a class function on all ordinals.
Agreement of the partial solutions shows that each $\restrict{F}{\gamma}$ is exactly the set-length solution on
$\gamma$. In particular,
$$F(\alpha)=H(\alpha,\restrict{F}{\alpha}).$$
Any other class function satisfying this equation agrees with $F$ by the same transfinite-induction argument.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
再帰で定義した全順序数上のclass assignment、その集合長の制限、再帰方程式、
一意性はordinalRecursion・ordinalRecursion_graph・ordinalRecursion_eq・ordinalRecu
rsion_uniqueの実装と既存リンクで確認した。残る256–259行だけを対象外とする。
ZFCでは各定義規則ごとのschemaとして読むという構文上の規約と、後のBorel階層・iterated jumpへの適用案内であり、
この残部で新たな存在・計算可能性・定義可能性定理を証明していない。
一般の外部HのLean関数を任意の内部モデルの定義可能なclassと同一視する判定ではない。)
--> In ZFC this is a schema for each defining rule $H$, not a set whose domain contains all ordinals.
It justifies the recursive definitions of the Borel hierarchy in §{sec:borel-hierarchy} and the iterated jump in
§{sec:effective-dst}.<!--
formalization: skip-end
-->

## Representation theorem {#sec:ordinals-representation}

The representation theorem is obtained by recursion on the given well-order itself.
We first record the fact that makes the resulting ordinal, and its representing map, unique.

\begin{lemma*}[\termdefine{Monotonicity of ordinal self-maps}]
Let $\gamma$ be an ordinal and let $g:\gamma\to\gamma$ be strictly increasing.
Then $\delta\le g(\delta)$ for every $\delta\in\gamma$.
\end{lemma*}
\begin{proof}[Proof]
If there is a counterexample, let $\delta$ be the least one. Then $g(\delta)<\delta$, so strict increase gives
$$g(g(\delta))<g(\delta).$$
Thus $g(\delta)$ is a smaller counterexample, a contradiction.
Equivalently, membership induction rules out $g(\delta)\in\delta$; ordinal comparison then gives
$\delta\IncludedIn g(\delta)$.
\end{proof}

\begin{theorem*}[\termdefine{Ordinal representation theorem}]
Every well-ordered set $\Pair{W}{<_W}$ is order-isomorphic to a unique ordinal.
The order-isomorphism onto that ordinal is also unique.
\end{theorem*}

\begin{proof}[Proof]
By recursion on $<_W$, define
$$f(x):=\{f(y):y<_W x\}\qquad(x\in W).$$
This recursion does not presuppose the representation theorem: the construction in §{sec:ordinals-induction}
works on predecessor segments of any well-order, using agreement on overlaps and Replacement to collect
the earlier partial solutions. In particular,
$$z\in f(x)\quad\Longleftrightarrow\quad
 \exists y<_W x\;z=f(y).$$
The map is injective. If $x\ne y$, one precedes the other, so one of $f(x),f(y)$ belongs to the other.
Equality would give a set belonging to itself, contrary to Foundation.
Consequently the recursive equation also gives
$$f(x)\in f(y)\quad\Longleftrightarrow\quad x<_W y.$$
For the reverse implication to the order relation, write $f(x)=f(z)$ with $z<_W y$ and use injectivity.

Each $f(x)$ is transitive. Indeed, if $u\in v\in f(x)$, then
$v=f(y)$ for some $y<_W x$ and $u=f(z)$ for some $z<_W y$.
Transitivity of $<_W$ gives $z<_W x$, hence $u\in f(x)$.
Every member of $f(x)$ is itself some $f(y)$ and is therefore transitive as well.
The transitive-set-of-transitive-sets characterization from §{sec:ordinals-von-neumann} shows that $f(x)$ is an ordinal.
The restriction of $f$ to $\{y\in W:y<_W x\}$ is an order-isomorphism onto $f(x)$:
surjectivity is the recursive equation, and the preceding equivalence preserves and reflects the order.

By Replacement, the image
$$\alpha:=\{f(x):x\in W\}$$
is a set. The recursive equation makes it transitive, and its members are ordinals, so $\alpha$ is an ordinal.
The map $f:W\to\alpha$ is bijective and preserves and reflects the order, hence is the required isomorphism.
For $W=\emptyset$, the construction gives $\alpha=\emptyset$ and the empty function.

For uniqueness of the ordinal, suppose $\alpha<\beta$ and there is an order-isomorphism $g:\beta\to\alpha$.
Composing with the inclusion into $\beta$ gives a strictly increasing self-map of $\beta$ whose value at
$\alpha\in\beta$ belongs to $\alpha$. This contradicts the monotonicity lemma.
Ordinal comparison therefore shows that any two isomorphic ordinals are equal.
Finally, for an order-automorphism $h:\alpha\to\alpha$, the lemma applied to $h$ and $h^{-1}$ gives
$$\delta\le h(\delta)\le h^{-1}(h(\delta))=\delta.$$
Thus $h$ is the identity. Composing one representation with the inverse of another shows that their maps agree
at every input.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
外部の表現定理と、内部の順序数・graphを得るための追加の閉包仮定を区別する読書案内。
internal_ordinal_representationがtransitivity・Pairing・Separation・Replacement
・internal minimaを明示してモデル内のα,Fを構成することを確認した。この段落自体は閉包の反例や新たな表現定理を証明せず、
認識・制限・内部Hartogsの議論を明示的に後の節へ委ねているため対象外。後節の実際の構成と証明をこの判定に含めない。)
--> The external representation theorem does not by itself put the representing ordinal or its graph inside a
transitive model. §{sec:internal-ordinal-representations} proves that internal construction, including
recognition and restriction of representations, before applying it to the internal Hartogs bound.<!--
formalization: skip-end
-->

## Ordinal arithmetic {#sec:ordinals-arithmetic}

Sum, product, and exponentiation of ordinals are defined by transfinite recursion:

*   **Sum.** $\alpha + 0 = \alpha$, $\alpha + (\beta+1) = (\alpha+\beta)+1$, and at limits $\alpha + \lambda =
    \sup_{\beta<\lambda}(\alpha + \beta)$. Concretely, $\alpha + \beta$ is the order type of $\alpha$ followed by
    $\beta$.
*   **Product.** $\alpha \cdot 0 = 0$, $\alpha \cdot (\beta+1) = \alpha \cdot \beta + \alpha$, and at limits $\alpha
    \cdot \lambda = \sup_{\beta<\lambda}(\alpha \cdot \beta)$. Concretely, the product is the order type of
    $\beta$ copies of $\alpha$ stacked end-to-end.
*   **Exponentiation.** $\alpha^0 = 1$, $\alpha^{\beta+1} = \alpha^\beta \cdot \alpha$, and at limits $\alpha^\lambda =
    \sup_{\beta<\lambda} \alpha^\beta$ (for $\alpha \ge 1$).

Ordinal arithmetic is non-commutative: $1 + \omega = \omega \ne \omega + 1$, and $2 \cdot \omega = \omega \ne \omega
\cdot 2$. The recursion is on the right argument: in $\alpha+\beta$, the initial $\alpha$-block is laid down first and
then extended by $\beta$; in $\alpha\cdot\beta$, the construction stacks $\beta$ many copies of $\alpha$ from left to
right. This is the source of the asymmetry.

A typical climb through the countable ordinals:
$$0,\, 1,\, 2,\, \ldots,\, \omega,\, \omega+1,\, \omega+2,\, \ldots,\, \omega \cdot 2,\, \omega \cdot 2 + 1,\, \ldots,\,
\omega^2,\, \ldots,\, \omega^\omega,\, \ldots,\, \varepsilon_0,\, \ldots$$
where $\varepsilon_0$ is the least fixed point of $\alpha \mapsto \omega^\alpha$. Every ordinal in this list is
countable as a set.

A notational warning: the expression $\omega^\omega$ above is \termdefine{ordinal exponentiation} as defined here, a
countable ordinal. The identical-looking expression $\BaireSpace$ used throughout the main text is the
\termuse{Baire space} of functions $\omega \to \omega$, an uncountable Polish space. Context fixes which is meant; the
rendered glyphs
coincide.

## Cardinality and $\omegaOneOrd$ {#sec:ordinals-cardinality}

A set has \termdefine{cardinality} at most $\kappa$ if it injects into $\kappa$. Every set is in bijection with a unique
cardinal, defined as the least ordinal of that cardinality.
\begin{mathmeta}
  \define{alephNull,alephCard}
\end{mathmeta}
The infinite cardinals are denoted $\alephNull < \alephCard{1} < \alephCard{2} < \cdots$ and indexed by ordinals.
\begin{mathmeta}
  \define{bethCard}
\end{mathmeta}
The \termdefineas{beth cardinal}{beth cardinals} $\bethCard{\alpha}$ are defined by transfinite recursion:
$$\bethCard{0} := \alephNull, \qquad \bethCard{\alpha+1} := 2^{\bethCard{\alpha}}, \qquad \bethCard{\lambda} :=
\sup_{\alpha<\lambda}\bethCard{\alpha} \text{ at limits } \lambda.$$
A set $x$ is \termuse{countable} if it injects into $\omega$. The explicit $L_\in$-formulas $\mathrm{Card}(\kappa)$
and $\mathrm{Countable}(x)$, together with their Lévy-hierarchy classification, are recorded in
§{sec:zfc-absoluteness}.\termref{absoluteness}

The first infinite ordinal $\omega$ has cardinality $\alephNull$ and is countably infinite. All ordinals between
$\omega$ and the **first uncountable ordinal** $\omegaOneOrd$ — that is, $\omega, \omega+1, \omega \cdot 2,
\omega^\omega, \varepsilon_0, \ldots$ — are countable as sets, however baroque their order type. The ordinal
$\omegaOneOrd$ itself is uncountable, of cardinality $\alephCard{1}$, and equals the set of all countable
ordinals.

## Cofinality and regularity {#sec:ordinals-cofinality}
\begin{mathmeta}
  \define{cf}
\end{mathmeta}

The \termdefine{cofinality} $\cf(\alpha)$ of a limit ordinal $\alpha$ is the least order type of an unbounded subset of
$\alpha$. Equivalently, the least $\kappa$ such that $\alpha = \sup\{\beta_\xi : \xi<\kappa\}$ for some increasing
sequence in $\alpha$ indexed by $\kappa$.

A limit ordinal is \termdefine{regular} if $\cf(\alpha) = \alpha$, otherwise \termdefine{singular}. Some authors reserve
this terminology for cardinals; here it is used for arbitrary limit ordinals. Examples:

*   $\cf(\omega) = \omega$, so $\omega$ is regular.
*   $\cf(\omega + \omega) = \omega$ via the sequence $\omega, \omega+1, \omega+2, \ldots$, so $\omega + \omega$ is
    singular.
*   $\cf(\omega^\omega) = \omega$ via $\omega, \omega^2, \omega^3, \ldots$, so $\omega^\omega$ is singular despite being
    a much larger ordinal.
*   Every successor cardinal $\alephCard{\alpha+1}$ is regular under the axiom of choice.

In particular $\omegaOneOrd = \alephCard{1}$ is regular: any countable subset of $\omegaOneOrd$ is
bounded
below $\omegaOneOrd$, since the supremum of countably many countable ordinals is itself countable. This is the
fact used in §{sec:borel-hierarchy} to show that the Borel hierarchy stabilizes at $\omegaOneOrd$.

## The cumulative hierarchy, reflection, and universes {#sec:zfc-cumulative-hierarchy}

ZFC's universe stratifies into the \termdefine{cumulative hierarchy} $V_\alpha$, defined by transfinite recursion on
ordinals:
$$V_0 := \emptyset, \qquad V_{\alpha+1} := \PowerSet{V_\alpha}, \qquad V_\lambda := \bigcup_{\alpha<\lambda} V_\alpha
\text{ at limits } \lambda.$$
Then $V = \bigcup_{\alpha \in \mathrm{Ord}} V_\alpha$ — by Foundation every set lies in some $V_\alpha$. The least
$\alpha$ with $x \in V_{\alpha+1}$ is the \termdefine{rank} of $x$; ranks of ordinals satisfy $\mathrm{rank}(\alpha) =
\alpha$. Each $V_\alpha$ is a transitive set, so the universe builds up in transitive layers.

\begin{theorem*}[\termdefine{finite reflection}] For every finite list $\Phi$ of $L_\in$-formulas there are arbitrarily
large ordinals $\alpha$ such that $V_\alpha$ reflects all formulas in $\Phi$: for every $\varphi(\vec x)\in\Phi$ and
every tuple $\vec a\in V_\alpha$,
$$
V\models\varphi(\vec a)
\quad\Longleftrightarrow\quad
V_\alpha\models\varphi^{V_\alpha}(\vec a).
$$
In fact, the reflecting ordinals contain a closed unbounded class. Consequently, for every finite list of ZFC axioms and
schema instances, some $V_\alpha$ satisfies that list.

\end{theorem*}

\begin{proof}[Proof]
Use implication, falsity, and universal quantification as the logical primitives; conjunction, negation,
and existential quantification are their usual abbreviations. Close the finite list $\Phi$ under subformulas.
For each quantified subformula $\forall x\,\psi(x,\vec y)$ and parameter tuple $\vec a$, let
$r_\psi(\vec a)$ be the least rank of a counterexample to $\psi(x,\vec a)$ if one exists, and let it be $0$
otherwise. This is the witness-rank construction for the existential formula $\exists x\,\neg\psi(x,\vec a)$.
For each ordinal $\beta$, set
$$F_\psi(\beta)=\sup\{r_\psi(\vec a):\vec a\in V_\beta\}+1.$$
Here the tuples have the fixed finite length appropriate to the subformula, and the supremum of the empty
set of ordinals is $0$. Replacement bounds the set of least witness ranks; choosing witnesses uniformly is
unnecessary.

Let $f(\beta)$ be the maximum of the finitely many bounds $F_\psi(\beta)$, or $0$ if there are none, and put
$$F(\beta)=\max\left\{\beta+1,\ \sup_{\gamma\le\beta}\bigl(f(\gamma)+1\bigr)\right\}.$$
Then $F$ is nondecreasing, $F(\beta)>\beta$, and $F_\psi(\beta)\le F(\beta)$ for every quantified subformula.

Let $C$ consist of the nonzero ordinals $\alpha$ such that $F(\beta)<\alpha$ for every $\beta<\alpha$.
These ordinals are limits, since $\beta+1\le F(\beta)<\alpha$ whenever $\beta<\alpha$.
To find one above any given ordinal $\gamma$, set
$$\alpha_0=\gamma,\qquad \alpha_{n+1}=F(\alpha_n),\qquad
\alpha=\sup_{n<\omega}\alpha_n.$$
The sequence is strictly increasing. For $\beta<\alpha$, choose $n$ with $\beta<\alpha_n$; then
$$F(\beta)\le F(\alpha_n)=\alpha_{n+1}<\alpha.$$
Thus $\alpha\in C$ and $\gamma<\alpha$.

The class $C$ is closed. Indeed, if $\alpha$ is the supremum of a nonempty set of members of $C$, then
$\alpha>0$. For each $\beta<\alpha$, some member $\delta$ of that set satisfies $\beta<\delta$, and hence
$F(\beta)<\delta\le\alpha$. Therefore $\alpha\in C$.

Fix $\alpha\in C$ and prove reflection by induction on the subformulas. Atomic formulas use the actual
membership and equality relations on $V_\alpha$; implication and falsity follow immediately from the induction
hypotheses. For a universal formula, truth in $V$ implies truth in $V_\alpha$ by applying the induction hypothesis
to each element of $V_\alpha$. Conversely, suppose the formula holds in $V_\alpha$ but fails in $V$, with parameters
$\vec a\in V_\alpha$. Since the tuple is finite and $\alpha$ is a limit, choose $\beta<\alpha$ with
$\vec a\in V_\beta$. A least-rank counterexample $x$ satisfies
$$\mathrm{rank}(x)<F_\psi(\beta)\le F(\beta)<\alpha,$$
so $x\in V_\alpha$. The induction hypothesis for the matrix makes this a counterexample inside $V_\alpha$ as well,
a contradiction. Thus every formula in $\Phi$ is reflected.

Finally, apply reflection to any chosen finite list of sentences true in $V$.
Every reflecting stage satisfies those sentences. In particular, this applies to any finite list of ZFC axioms
and schema instances.
\end{proof}

This is the theorem behind the common forcing convention "work in a sufficiently large finite fragment of ZFC."
Reflection supplies transitive sets $V_\alpha$ satisfying any prescribed finite fragment; compactness, downward
Löwenheim--Skolem, and Mostowski collapse then explain the countable-transitive-model reduction used in
§{sec:internal-model-closure}.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
数学的な二つの正の主張を分離して確認した。有限の真な公理列を満たす段階はfinite_true_sentences_reflectへ、
到達不能κのVκが全ZFCを満たす主張はinaccessible_stage_models_fullZFCへ接続した。
後者は仮定したモデル仕様ではなく、Grothendieck閉包から各公理文の充足・全パラメータ付きReplacementインスタンス・Choice
graphを証明し、8公理族からなる実際のfullZFCTheoryの標準Theory.Modelを構成する。残る冒頭の対比、
有限反映の量化順序から一つの全ZFCモデルを得たとは言わないという説明、追加のメタ理論的仮定に関する結びだけを背景説明として対象外にする。
ZFCでのモデル存在の不可能性や無矛盾性の形式的独立性を証明済みとする判定ではない。)
--> Reflection should be contrasted with inaccessible cardinals.<!--
formalization: skip-end
-->  Finite reflection is a theorem of ZFC and gives, separately
for each finite fragment, some transitive $V_\alpha$ satisfying that fragment. <!--
formalization: skip-begin (引用・背景説明・読書案内:
数学的な二つの正の主張を分離して確認した。有限の真な公理列を満たす段階はfinite_true_sentences_reflectへ、
到達不能κのVκが全ZFCを満たす主張はinaccessible_stage_models_fullZFCへ接続した。
後者は仮定したモデル仕様ではなく、Grothendieck閉包から各公理文の充足・全パラメータ付きReplacementインスタンス・Choice
graphを証明し、8公理族からなる実際のfullZFCTheoryの標準Theory.Modelを構成する。残る冒頭の対比、
有限反映の量化順序から一つの全ZFCモデルを得たとは言わないという説明、追加のメタ理論的仮定に関する結びだけを背景説明として対象外にする。
ZFCでのモデル存在の不可能性や無矛盾性の形式的独立性を証明済みとする判定ではない。)
--> It does not produce a single $V_\alpha$
satisfying all of ZFC.<!--
formalization: skip-end
-->  An inaccessible cardinal $\kappa$ is a stronger sufficient closure hypothesis ensuring
that $V_\kappa$ is a
transitive model of full ZFC. <!--
formalization: skip-begin (引用・背景説明・読書案内:
数学的な二つの正の主張を分離して確認した。有限の真な公理列を満たす段階はfinite_true_sentences_reflectへ、
到達不能κのVκが全ZFCを満たす主張はinaccessible_stage_models_fullZFCへ接続した。
後者は仮定したモデル仕様ではなく、Grothendieck閉包から各公理文の充足・全パラメータ付きReplacementインスタンス・Choice
graphを証明し、8公理族からなる実際のfullZFCTheoryの標準Theory.Modelを構成する。残る冒頭の対比、
有限反映の量化順序から一つの全ZFCモデルを得たとは言わないという説明、追加のメタ理論的仮定に関する結びだけを背景説明として対象外にする。
ZFCでのモデル存在の不可能性や無矛盾性の形式的独立性を証明済みとする判定ではない。)
--> Thus finite-fragment forcing arguments require only reflection, while arguments that
assume a transitive set model of full ZFC are making an additional metatheoretic consistency assumption. An inaccessible
cardinal is a standard stronger sufficient hypothesis for such a model, not something supplied by reflection.<!--
formalization: skip-end
-->

### Inaccessible cardinals and Grothendieck universes {#sec:inaccessible-universes}

\begin{mathmeta}
  \vars{I,x}{Set}
\end{mathmeta}
\index{inaccessible cardinal}
\index{Grothendieck universe}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
圏論付録で固定するGrothendieck宇宙という追加仮定と、この節の役割を案内する導入。宇宙の存在や新たな閉包・濃度命題をこの段落で証明せず、
具体的な定義と宇宙定理を後続段落で扱う。ZFCに対する仮定の強さの位置付けは背景説明として対象外にし、後続のstrong
limit・到達不能性・閉包例・宇宙公理の同値性はこの判定に含めない。)
--> The categorical appendix §{sec:appendix-category-realizability} works inside a fixed
**\termforward{Grothendieck universe}**, a hypothesis slightly stronger than ZFC alone. This subsection records the
cardinal-arithmetic background
and the universe convention used there.<!--
formalization: skip-end
-->

A nonzero cardinal $\kappa$ is a \termdefine{strong limit} if $2^\lambda < \kappa$ for every cardinal $\lambda <
\kappa$. An uncountable cardinal $\kappa$ is \termdefineas{inaccessible cardinal}{(strongly) inaccessible} if it is
regular in the sense of §{sec:ordinals-cofinality} and a strong limit.

The terminology is justified by closure under standard ZFC operations. If $\lambda < \kappa$ then
$\Card{\PowerSet{\lambda}}
= 2^\lambda < \kappa$ by the strong-limit property, and any union of fewer than $\kappa$ sets each of cardinality less
than $\kappa$ stays of cardinality less than $\kappa$ by regularity. The successor cardinals $\alephCard{\alpha+1}$ are
regular under AC but never strong limits, since $2^{\alephCard{\alpha}} \ge \alephCard{\alpha+1}$. The cardinal
$\bethCard{\omega} := \sup_n \bethCard{n}$ is a strong limit but $\cf(\bethCard{\omega}) = \omega < \bethCard{\omega}$,
hence singular. These two closure properties explain the terminology: starting below an inaccessible cardinal,
power sets and unions indexed by smaller sets do not reach it from below.

The existence of an inaccessible $\kappa$ implies that $V_\kappa$ is a transitive model of ZFC, hence implies
$\mathrm{Con}(\mathrm{ZFC})$. <!--
formalization: skip-begin (引用・背景説明・読書案内:
冒頭のモデル存在から無矛盾性への局所的な推論は、
実際のfullZFCTheoryを名前付き構文へ翻訳したnamedFullZFCTheoryとinaccessible_implies_namedZF
C_consistentへ接続した。有限変数文脈を名前へ翻訳する実装、意味保存、自由変数の範囲と閉文性を証明し、
本文の自然演繹Derivesの健全性からfalsumの非導出を得ている。
単なるIsSatisfiableを構文的Consistentと言い換えていない。
残る505–508行は明示的に名指された外部入力であるGödelの第二不完全性定理、その標準的帰結、大基数公理としての位置付けであり、
この節の局所証明対象外とする。算術化されたCon文や第二不完全性定理そのものを形式化済みとする判定ではない。)
--> Assuming ZFC is consistent, Gödel's second incompleteness theorem says that ZFC
does not prove $\mathrm{Con}(\mathrm{ZFC})$,
and so does not prove the existence of an inaccessible. The hypothesis "an \termuse{inaccessible cardinal} exists" is
one of the weakest standard \termdefineas{large cardinal axiom}{large-cardinal axioms}.<!--
formalization: skip-end
-->

**Grothendieck universes.** A \termdefine{Grothendieck universe} is a set $U$ satisfying:

*   **Transitivity.** $x \in y \in U$ implies $x \in U$.
*   **Pairing.** $x, y \in U$ implies $\{x, y\} \in U$.
*   **Power Set.** $x \in U$ implies $\PowerSet{x} \in U$.
*   **Indexed union.** If $I \in U$ and $f : I \to U$ is a function, then $\bigcup_{i \in I} f(i) \in U$.
*   **Infinity.** $\omega \in U$.

A set is \termdefineas{U-small}{$U$-small} if it is an element of $U$. A set that is not $U$-small is
\termdefineas{U-large}{$U$-large}.

\begin{theorem*}[\termdefineas{Grothendieck universe theorem}{Grothendieck}] A set $U$ is a Grothendieck universe iff $U
= V_\kappa$ for some inaccessible cardinal $\kappa$.

\end{theorem*}

\begin{proof}[Proof] \emph{$(\Leftarrow)$} First note the size bound: if $\kappa$ is inaccessible and
$\alpha<\kappa$, then $\Card{V_\alpha}<\kappa$. Induct on $\alpha$. The zero stage is empty; a successor stage is a
power set, so the strong-limit property applies. At a limit stage, regularity bounds the union of fewer than
$\kappa$ sets of cardinality less than $\kappa$. Every $x\in V_\kappa$ is a subset of a stage below $\kappa$,
so $\Card{x}<\kappa$ as well.

The set $V_\kappa$ is transitive. Pairing and power-set closure follow from the rank formulas
$$\mathrm{rk}(\{x,y\})=\max\{\mathrm{rk}(x)+1,\mathrm{rk}(y)+1\},\qquad
\mathrm{rk}(\PowerSet{x})=\mathrm{rk}(x)+1$$
and the fact that $\kappa$ is a limit ordinal. Also $\omega\in V_\kappa$, since $\omega<\kappa$.
For indexed unions, let $I\in V_\kappa$ and $f:I\to V_\kappa$. The size bound gives $\Card{I}<\kappa$;
regularity then gives
$$\mathrm{rk}\left(\bigcup_{i\in I}f(i)\right)
=\sup_{i\in I}\mathrm{rk}(f(i))<\kappa.$$
Thus the indexed union belongs to $V_\kappa$.

\emph{$(\Rightarrow)$} Let $\kappa:=U\cap\mathrm{Ord}$. Transitivity makes this an ordinal, and
$\omega\in U$ gives $\omega<\kappa$. Pairing and indexed unions give closure under singletons and binary
unions. Hence $\alpha\in U$ implies $\alpha+1=\alpha\cup\{\alpha\}\in U$ for ordinals, so $\kappa$ is a limit.
Indexed-union closure also gives
$$\sup_{i\in I}\alpha_i=\bigcup_{i\in I}\alpha_i\in U\cap\mathrm{Ord}=\kappa
\qquad(I\in U,\ \alpha_i<\kappa).$$

For $x\in U$, induction on membership gives $\mathrm{rk}(x)\in U$.
Indeed, each $y\in x$ belongs to $U$ by transitivity, so the induction hypothesis and successor closure give
$\mathrm{rk}(y)+1\in U$. Apply indexed-union closure over the index set $x$ to obtain
$$\mathrm{rk}(x)=\bigcup_{y\in x}\bigl(\mathrm{rk}(y)+1\bigr)\in U\cap\mathrm{Ord}=\kappa.$$
Thus $U\IncludedIn V_\kappa$.

Conversely, transfinite induction gives $V_\alpha\in U$ for every $\alpha<\kappa$.
The zero, successor, and limit recursions can be written together as
$$V_\alpha=\bigcup_{\beta<\alpha}\PowerSet{V_\beta}.$$
The index set $\alpha$ belongs to $U$, and the induction hypothesis followed by power-set closure puts each
term of this union in $U$. Now if $x\in V_\kappa$, its rank and the successor of its rank are below $\kappa$.
Hence $V_{\mathrm{rk}(x)+1}\in U$; since $x\in V_{\mathrm{rk}(x)+1}$, transitivity gives $x\in U$.
Therefore $U=V_\kappa$.

We next show that $\Card{x}<\Card{\kappa}$ for every $x\in U$. Otherwise, choice gives a surjection
$f:x\to\kappa$. All values of this map belong to $U$, so indexed-union closure gives
$$\bigcup_{i\in x}f(i)=\bigcup\kappa=\kappa\in U,$$
contrary to the definition of $\kappa$. In particular, $\kappa$ is an initial ordinal: its initial ordinal
$\mu=\Card{\kappa}$ satisfies $\mu\le\kappa$, and if $\mu<\kappa$, then $\mu\in U$ while $\Card{\mu}=\Card{\kappa}$,
contradicting the bound. Thus $\kappa$ is a cardinal and $\Card{x}<\kappa$ for every $x\in U$.

If $\lambda<\kappa$ is a cardinal, then $\lambda\in U$ and $\PowerSet{\lambda}\in U$, so the size bound gives
$2^\lambda=\Card{\PowerSet{\lambda}}<\kappa$. Thus $\kappa$ is a strong limit.
It is also regular. A cofinal sequence $\langle\alpha_i:i<\mu\rangle$ of length $\mu<\kappa$ would have
$\mu\in U$, so indexed-union closure would put its supremum $\kappa$ in $U$, again a contradiction.
Together with $\omega<\kappa$, this proves that $\kappa$ is inaccessible.
\end{proof}

The standard **universe axiom** asserts that every set is contained in some Grothendieck universe, equivalently that the
inaccessibles form a proper class. <!--
formalization: skip-begin (引用・背景説明・読書案内:
冒頭の宇宙公理と到達不能基数の真クラス性の同値は、
実際のZFSetに対するuniverse_axiom_iff_proper_class_inaccessiblesへ接続した。
membership版とsubset版の同値、到達不能な高さの非有界性、全到達不能初期順序数を一つのZFSetに集められないことまで証明しており、
単にproper-class型を仮定していない。残る578–579行の、
単一の到達不能基数の存在に対する相対的な強さの位置付けと圏論での採用慣行だけを背景説明として対象外とする。
この判定はZFC上の厳密な無矛盾性強度比較や独立性定理を形式化済みとするものではなく、
そのような証明・反例モデルを本文のこの段落で展開していないことに基づく。)
--> This is a strict strengthening of "an inaccessible exists" and is the convention
adopted in much of category theory after Grothendieck.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
固定Uの下でset・small・SetCatをどう読むかを宣言し、実現可能性の具体的構成を圏論付録へ委ねる規約。再読して、
omega_memという前提と、
SetTheoryCategorySizeでグラフ・始域・終域を持つ関数集合および実際の関係同値類がU内に属する証明を確認した。
LeanのTypeレベルを固定ZFSet宇宙への所属と同一視していない。ここでは新たな局所的構成をせず、委ね先の本文とサイズ証明は別に接続する。)
--> **Convention used below.** Fix once and for all a Grothendieck universe $U$ with $\omega \in U$. Throughout
§{sec:appendix-category-realizability}, "set" means $U$-small set, "small" means $U$-small, and the unsubscripted symbol
$\SetCat$ denotes the category $\SetCatU$ of $U$-small sets and functions. The PCA $K_1$ has carrier $\NN \in U$, so
each object and morphism in the realizability constructions of §{sec:appendix-category-realizability}
uses $U$-small data, and the resulting effective
topos $\EffCat$ is locally $U$-small.<!--
formalization: skip-end
-->

## The Lévy hierarchy and absoluteness {#sec:zfc-absoluteness}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}

A \termdefine{transitive model} is a transitive set or class $M$ in which the ZFC axioms (or some fragment) hold when
relativized to $M$. <!--
formalization: skip-begin (引用・背景説明・読書案内:
冒頭の推移的な集合・クラスモデルの定義はIsTransitiveSetModel・IsTransitiveClassModelへ接続し、
後者はClassDomain上の同じmembership-language理論の標準的充足を使う。
残る591–594行はforcing章と後の有効トポスへの読書案内および古典的集合論の解釈域変更と内部直観主義論理との概念上の対比であり、
この段落では新しい絶対性・forcing・実現可能性定理を証明しない。参照先の構成や証明のcoverageはこの判定に含めない。)
--> Forcing extensions $M[G]$ of countable transitive models are the standard testing ground for
independence proofs in §{sec:forcing}. The discussion here is classical set-theoretic absoluteness: forcing changes the
universe in which formulas are interpreted. The effective topos later changes the ambient logic itself, replacing
classical truth by internal intuitionistic/realizability truth.\termref{absoluteness}<!--
formalization: skip-end
-->

The \termdefineas{Levy hierarchy}{Lévy hierarchy} classifies set-theoretic formulas by quantifier complexity:

*   $\Delta_0 = \Sigma_0 = \Pi_0$: only bounded quantifiers $(\forall x \in y)$ and $(\exists x \in y)$.
*   $\Sigma_{n+1}$: $\exists x_1\cdots\exists x_k\, \varphi$ with $\varphi \in \Pi_n$.
*   $\Pi_{n+1}$: $\forall x_1\cdots\forall x_k\, \varphi$ with $\varphi \in \Sigma_n$.
*   $\Delta_{n+1}$: provably equivalent to both a $\Sigma_{n+1}$ and a $\Pi_{n+1}$ formula in ZFC.

For the positive levels, we also allow formulas provably equivalent over ZFC to these forms.

\begin{proposition*}
For every $n\in\NN$, each of $\Sigma_n$, $\Pi_n$, and $\Delta_n$ is closed under bounded universal and existential
quantification, with all other parameters retained. At positive levels the required equivalences are provable in ZFC.
\end{proposition*}

\begin{proof}
We first derive the instance of Collection needed for the prenex conversion. Fix a formula
$\theta(x,y,\vec p)$ and suppose $\forall x\in a\,\exists y\,\theta(x,y,\vec p)$.
For each $x\in a$, let $\alpha_x$ be the least ordinal such that some $y\in V_{\alpha_x}$ satisfies
$\theta(x,y,\vec p)$. Such a stage exists by the cumulative hierarchy in §{sec:zfc-cumulative-hierarchy}.
To find the least stage, start with any stage containing a witness and put its ordinal index inside a transitive
set. Separate the qualifying ordinals from that set and apply Foundation. Transitivity makes the resulting
member minimal among all qualifying ordinals; ordinal comparison makes it the unique least one.
Replacement collects the uniquely defined sets $V_{\alpha_x}$; their union $B$ contains a witness for every
$x\in a$. Consequently ZFC proves
$$
\forall x\in a\,\exists y\,\theta(x,y,\vec p)
\quad\Longleftrightarrow\quad
\exists B\,\forall x\in a\,\exists y\in B\,\theta(x,y,\vec p).
$$
The reverse implication is immediate. This argument selects least stages, without selecting individual witnesses.
The constructions take place inside any model of ZFC: ordinal comparison and induction follow from its
Foundation and Separation axioms, and the hierarchy is given by internal definable recursion. No external
well-foundedness of the model's membership relation is required.

Now induct simultaneously on the level for the two polarities. Level zero follows directly from the bounded
syntax. Suppose both polarities at level $n$ are closed under bounded quantification. Any finite existential
prefix with a $\Pi_n$ matrix can be compressed to one existential quantifier: replace two successive witnesses
by a set containing both, and quantify the two witnesses boundedly over that set. Pairing gives the equivalence,
and the induction hypothesis keeps the matrix in $\Pi_n$. A vacuous existential quantifier handles an empty
prefix. Thus a $\Sigma_{n+1}$ formula can be written, up to ZFC-provable equivalence, as
$\exists y\,\theta(x,y,\vec p)$ with $\theta\in\Pi_n$.

For a bounded existential quantifier, interchange the two existential quantifiers:
$$
\exists x\in a\,\exists y\,\theta(x,y,\vec p)
\quad\Longleftrightarrow\quad
\exists y\,\exists x\in a\,\theta(x,y,\vec p).
$$
For a bounded universal quantifier, use the displayed Collection equivalence.
In both cases the matrix following the new unbounded existential quantifier remains $\Pi_n$ by the induction
hypothesis. This proves both closures for $\Sigma_{n+1}$. Negation interchanges the two polarities and the two
bounded quantifiers, giving the closures for $\Pi_{n+1}$. Applying both results gives the closures for
$\Delta_{n+1}$. Bound variables are renamed throughout to retain the original free parameters and to keep each
bounding variable outside the scope of the quantifier it bounds.
\end{proof}

Bounded quantifiers are the abbreviations introduced in §{sec:definitional-extensions} for languages containing $\in$.
In the Lévy hierarchy, the quantifier is bounded only when the bounding object is already one of the available variables
or terms whose atomic uses have been eliminated by bounded unfolding in the sense of §{sec:definitional-extensions}.
This is why extension by definition and Lévy-complexity bookkeeping are kept separate.

A formula $\varphi$ is \termdefineas{absoluteness}{absolute} between transitive classes $M \IncludedIn N$ if
$\varphi^M \leftrightarrow
\varphi^N$ on parameters in $M$. The standard absoluteness theorem:

*   $\Delta_0$ formulas are absolute between any two transitive models.
*   $\Sigma_1$ formulas are upward absolute (preserved going from $M$ to $N \supseteq M$).
*   $\Pi_1$ formulas are downward absolute.

\begin{proof}[Proof] We first prove the $\Delta_0$ statement in the form used below. Let $M\IncludedIn N$ be transitive
models or transitive classes, and let the parameters $\vec p$ lie in $M$. We show by induction on $\Delta_0$ formulas
$\delta(\vec x)$ that
$$
M\models \delta(\vec p)
\quad\Longleftrightarrow\quad
N\models \delta(\vec p).
$$
After the bounded unfolding convention above, we may work in the pure language $L_\in$, so the only terms are variables.
The atomic cases are $u=v$ and $u\in v$. Since $M$ is a subclass of $N$ and both structures use the actual equality and
membership relations restricted to their elements, these atomic formulas have the same truth value for assignments from
$M$. Boolean connectives are immediate from the induction hypothesis.

It remains to check bounded quantifiers. Suppose $\delta(\vec p)$ has the form $\exists x\in a\,\psi(x,\vec p)$, where
$a\in M$. In $M$ this means that some $b\in M$ satisfies $b\in a$ and $M\models\psi(b,\vec p)$. Because $M$ is
transitive, every element of $a$ already lies in $M$. Hence the possible witnesses in $M$ are exactly the actual
elements of $a$:
$$
M\models \exists x\in a\,\psi(x,\vec p)
\quad\Longleftrightarrow\quad
\text{for some } b\in a,\; M\models\psi(b,\vec p).
$$
The same set $a$ belongs to $N$, and its elements are the same actual elements $b\in a$. For each such $b$, the
induction hypothesis gives
$$
M\models\psi(b,\vec p)
\quad\Longleftrightarrow\quad
N\models\psi(b,\vec p).
$$
Therefore
$$
M\models \exists x\in a\,\psi(x,\vec p)
\quad\Longleftrightarrow\quad
N\models \exists x\in a\,\psi(x,\vec p).
$$
The bounded universal case is the same argument with "for every" in place of "for some":
$$
M\models \forall x\in a\,\psi(x,\vec p)
\quad\Longleftrightarrow\quad
\text{for every } b\in a,\; M\models\psi(b,\vec p).
$$
Applying the induction hypothesis for each $b\in a$ gives
$$
\text{for every } b\in a,\; M\models\psi(b,\vec p)
\quad\Longleftrightarrow\quad
\text{for every } b\in a,\; N\models\psi(b,\vec p).
$$
Since $a$ has the same elements in $N$, this is equivalent to
$$
N\models \forall x\in a\,\psi(x,\vec p).
$$
This completes the induction and proves $\Delta_0$ absoluteness. For the non-nested formulation, compare each
transitive model with the common ambient membership structure. The inclusion argument needs no set-theoretic axioms
in the larger domain: transitivity of the smaller model already keeps every bounded witness in that smaller model.
With parameters in both models, their interpretations therefore agree with the same external
interpretation.\termref{absoluteness}

Now let $\varphi(\vec p)$ be $\Sigma_1$, say
$$
\varphi(\vec p)\equiv \exists x_1\cdots\exists x_n\,\delta(x_1,\ldots,x_n,\vec p),
$$
with $\delta$ $\Delta_0$. If $M\models\varphi(\vec p)$, choose witnesses $a_1,\ldots,a_n\in M$. By $\Delta_0$
absoluteness,\termref{absoluteness}
$$
N\models\delta(a_1,\ldots,a_n,\vec p),
$$
so $N\models\varphi(\vec p)$. Thus $\Sigma_1$ formulas are upward absolute.

Finally let $\theta(\vec p)$ be $\Pi_1$, say
$$
\theta(\vec p)\equiv \forall x_1\cdots\forall x_n\,\delta(x_1,\ldots,x_n,\vec p),
$$
with $\delta$ $\Delta_0$. Suppose $N\models\theta(\vec p)$. To show $M\models\theta(\vec p)$, take arbitrary
$a_1,\ldots,a_n\in M$. Since $M\IncludedIn N$, these are also elements of $N$, so
$$
N\models\delta(a_1,\ldots,a_n,\vec p).
$$
By $\Delta_0$ absoluteness, $M\models\delta(a_1,\ldots,a_n,\vec p)$. The tuple from $M$ was arbitrary, hence
$M\models\theta(\vec p)$. Thus $\Pi_1$ formulas are downward absolute.
\end{proof}\termref{absoluteness}

For formulas in the displayed syntactic forms, this proof uses only transitivity of $M$ and the actual
membership and equality relations on $M\IncludedIn N$; it needs no ZFC axioms in either domain.
For a formula merely provably equivalent over ZFC to one of those forms, both domains must also satisfy
axioms sufficient for that equivalence.

Forcing extensions $M[G]$ are transitive and contain $M$, so these tests explain which low-complexity assertions are
preserved by forcing and which can change.

**Bounded unfolding convention.** The formulas below use ordinary set-theoretic notation, but their hierarchy
classification is always made after bounded unfolding into $L_\in$. The following clauses instantiate the
$\Delta_0$-safe and contextual conventions of §{sec:definitional-extensions}.

First, atomic uses of pair notation are expanded contextually. For example,
$$
c \in \{a,b\}
\quad\text{means}\quad
c=a \lor c=b,
$$
and
$$
\Pair{a}{b} \in f
$$
means that some $q\in f$ is the Kuratowski pair of $a$ and $b$, with all witnesses bounded by $q$. Written out, this
says:
$$
\exists q\in f\,\bigl(q=\Pair{a}{b}\bigr),
$$
where $q=\Pair{a}{b}$ itself is expanded by quantifying only over $q$ and its elements. Thus atomic formulas
involving ordered pairs introduce bounded quantifiers only.

Here are explicit bounded expansions for the equalities used in this clause:
$$\begin{aligned}
u=\{a\}
&\Longleftrightarrow a\in u\land\forall z\in u\,(z=a),\\
v=\{a,b\}
&\Longleftrightarrow a\in v\land b\in v\land\forall z\in v\,(z=a\lor z=b),\\
q=\Pair{a}{b}
&\Longleftrightarrow\exists u\in q\,\exists v\in q\,\bigl(
 u=\{a\}\land v=\{a,b\}\\
&\qquad{}\land q=\{u,v\}\bigr).
\end{aligned}$$
In the last line, use the first two lines to expand the three remaining set equalities.
The witnesses $u,v$ are allowed to coincide when $a=b$.

The first two equivalences follow from Extensionality. For the last, an ordered pair has the displayed
singleton and unordered pair as members. Conversely, those two members together with $q=\{u,v\}$ give
$q=\{\{a\},\{a,b\}\}$. In a transitive domain, all elements inspected by these bounded clauses remain in the
domain. Thus the clauses recognize the actual singleton, unordered pair, and ordered pair; their correctness
requires no assumption that the domain contains every externally constructed set.

Second, application is not treated as a total function symbol. The expression $f(a)=c$ abbreviates the atomic graph
relation
$$
f(a)=c \;:\equiv\; \Pair{a}{c} \in f,
$$
and therefore unfolds by the bounded ordered-pair clause above. This is the systematic reason that the map predicates
below are genuinely $\Delta_0$.

**Maps.** With application read as graph membership, the assertion that $f$ is a function from $x$ to $y$ is:
$$
\begin{aligned}
f : x \to y \;:\equiv\;&
(\forall p \in f\, \exists a \in x\, \exists b \in y\, p = \Pair{a}{b})\\
&{}\land
\forall a \in x\, \exists b \in y\,
\bigl(f(a)=b \land \forall c \in y\,(f(a)=c \to c=b)\bigr).
\end{aligned}
$$
Every quantifier is bounded by $f$, $x$, or $y$, and the remaining pair/application notation unfolds with bounded
quantifiers. Hence $f:x\to y$ is $\Delta_0$.

For a transitive domain containing $f,x,y$, the first clause says exactly that $f\IncludedIn x\times y$:
each actual member of $f$ lies in the domain, and the bounded pair clause recognizes its actual coordinates.
The second clause gives a value for each actual $a\in x$ and uniqueness among values in $y$.
Any pair $\Pair{a}{c}\in f$ already has $c\in y$ by the first clause, so this bounded uniqueness
is uniqueness among all actual possible values. Conversely, an actual function supplies the same bounded
witnesses, all of which lie in the domain by transitivity. Thus the internal predicate and the actual
set-function condition agree; no closure under all external functions is used.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直後のInj/Surj/Bijの定義を導入する一行の見出し。数学的内容は次の独立した表示式の単位へ接続し、この案内文だけを対象外とする。)
--> The standard map properties are:<!--
formalization: skip-end
-->

$$
\begin{aligned}
\mathrm{Inj}_{x,y}(f)
&:\equiv\; f : x \to y \;\land{}\\
&\qquad \forall a \in x\, \forall b \in x\, \forall c \in y\,
(f(a)=c \land f(b)=c \to a=b),\\
\mathrm{Surj}_{x,y}(f)
&:\equiv\; f : x \to y \;\land\; \forall c \in y\, \exists a \in x\,(f(a)=c),\\
\mathrm{Bij}_{x,y}(f)
&:\equiv\; \mathrm{Inj}_{x,y}(f) \;\land\; \mathrm{Surj}_{x,y}(f).
\end{aligned}
$$

All quantifiers remain bounded by $f$, $x$, or $y$. Therefore $\mathrm{Inj}_{x,y}(f)$, $\mathrm{Surj}_{x,y}(f)$, and
$\mathrm{Bij}_{x,y}(f)$ are $\Delta_0$, hence absolute between transitive models containing the parameters.

**Cardinals and countability.**
$$
\begin{aligned}
\mathrm{Countable}(x)
&:\equiv\; \exists f\,\mathrm{Inj}_{x,\omega}(f).
\end{aligned}
$$
Here $\omega$ is supplied as a fixed parameter. The body is $\Delta_0$, so one outermost unbounded existential
puts $\mathrm{Countable}$ at $\Sigma_1$. It is therefore
upward absolute: if a transitive model already has an injection $x\to\omega$, any larger transitive model sees the same
injection. <!--
formalization: skip-begin (引用・背景説明・読書案内:
可算性の具体的なmembership-language式、固定したomegaパラメータ、
Sigma1分類と上向き絶対性はcountableSetFormula・countableSetFormula_sigmaOne・countableS
etFormula_upwardへ接続した。残る808–809行は、強制法で新しい単射が加わると逆方向は保たれないという非閉包の背景説明であり、
この段落では崩壊forcingの構成や反例モデルの証明を展開しない。AGENTS.mdのillustrative non-closure
warningsの方針に従ってこの残部だけを対象外とし、非Delta0性や崩壊forcingの存在を形式化済みとは数えない。)
--> It is not $\Delta_0$ in general. Forcing can make a previously uncountable set countable by adding a new
injection, a phenomenon called \termdefine{cardinal collapse}, so countability is not downward absolute.<!--
formalization: skip-end
-->

The ordinal predicate from §{sec:ordinals-von-neumann} is
$$
\begin{aligned}
\mathrm{Ord}(x)
&:\equiv \mathrm{Trans}(x) \land (\forall y\in x)\,\mathrm{Trans}(y),\\
\mathrm{Trans}(x)
&:\equiv (\forall y\in x)(\forall z\in y)\,z\in x.
\end{aligned}
$$
All quantifiers in these two formulas are bounded, so $\mathrm{Ord}(x)$ is $\Delta_0$.
For a transitive set or class $N$ containing $x$, every member $y$ of $x$ belongs to $N$,
and every member $z$ of $y$ also belongs to $N$.
Thus the internal formula $\mathrm{Trans}(x)$ says exactly that $x$ is actually transitive.
Applying the same argument to each $y\in x$ shows that the internal $\mathrm{Ord}(x)$ says exactly that $x$
is a transitive set of transitive sets, the von Neumann ordinal condition.
Consequently ordinalhood is absolute between transitive domains, without any ZFC assumption on those domains.
This concerns a fixed parameter already in both domains; it does not by itself rule out new ordinal elements.
The separate rank argument in §{sec:generic-extension}, with its ground-model closure hypotheses, gives
$\mathrm{Ord}^{M[G]}=\mathrm{Ord}^M$.

Now define cardinalhood by saying that $\kappa$ is an ordinal and no smaller ordinal bijects with it:
$$
\mathrm{Card}(\kappa)
\;:\equiv\;
\mathrm{Ord}(\kappa)
\land
\forall \alpha \in \kappa\, \neg \exists f\,\mathrm{Bij}_{\alpha,\kappa}(f).
$$
The predicate $\mathrm{Bij}_{\alpha,\kappa}(f)$ is $\Delta_0$, so $\exists f\,\mathrm{Bij}_{\alpha,\kappa}(f)$ is
$\Sigma_1$ and its negation is $\Pi_1$. Here the bounded universal quantifier can be moved past the universal
quantifier over $f$, giving the equivalent form
$$\forall f\,\bigl[\mathrm{Ord}(\kappa)\land
\forall\alpha\in\kappa\,\neg\mathrm{Bij}_{\alpha,\kappa}(f)\bigr].$$
Its matrix is $\Delta_0$, so $\mathrm{Card}(\kappa)$ is $\Pi_1$; this particular rearrangement needs no Collection.
Hence cardinalhood is downward
absolute: a cardinal of $V$ remains a cardinal in any transitive submodel containing it. <!--
formalization: skip-begin (引用・背景説明・読書案内:
実際の有界Bij式とOrd式から、全称fを先に置いたcardinalSetFormulaを構成し、
元の定義との意味の一致・Pi1分類・下向き絶対性を証明した。この具体的な全称量化子の交換はCollectionに依存せず、
正段階の一般的閉包ASTRA-COV-007の解消には数えない。残る846–848行の強制拡大で逆が失敗しうるという部分は非閉包の背景説明で、
この段落は新たな反例forcingを構成しない。AGENTS.mdのillustrative non-closure
warningsの方針により残部だけを対象外にし、基数崩壊の存在を形式化済みとはしない。)
--> The converse can fail after
forcing, because a cardinal of $M$ may cease to be a cardinal in $M[G]$ if the extension adds a new bijection from a
smaller ordinal.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
絶対性の階層が後続の強制法・独立性・無矛盾性の節で担う役割を説明する結びと参照。ここで独立した定理や新しい証明を展開しない。)
--> The hierarchy of absoluteness is the technical engine behind the independence and consistency results in
§{sec:forcing-absoluteness}.\termref{absoluteness}<!--
formalization: skip-end
-->
