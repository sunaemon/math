# Effective DST: Ranks, Borel Codes, and Refinements {#sec:effective-dst-ranks}
\index{effective descriptive set theory!ranks}

<!-- formalization: skip-begin (conceptual EDST/TTE bridge and chapter summary) -->
EDST is the technical bridge between three subjects:

1.  **Classical descriptive set theory** — provides the boldface framework parameterized over reals.
2.  **Recursion theory** — provides the lightface notion of "recursive predicate" and the recursive-ordinal
    scaffolding
    $\churchKleeneOrd$.
3.  **Computable analysis (TTE)** — the represented spaces of §{sec:cauchy-representation-admissibility} carry
    effective
    Borel and analytic structure. A computable Polish space comes with a computable metric presentation; its Cauchy
    representation lets us describe subsets by conditions on names and compute maps by transforming names.

\begin{mathmeta}
  \forward{EffCat}
\end{mathmeta}

These descriptions in terms of predicates and witnesses prepare for the realizability interpretation in $\EffCat$.
Relativizing lightface definitions to real parameters also explains their relation to the classical boldface classes.
The standard references are [@MansfieldWeitkamp1985] for the recursion-theoretic development and
[@Moschovakis2009] for the unified treatment of classical and effective sides.

<!-- formalization: skip-end -->

The bridge to TTE is concrete. If $X$ is a computable Polish space with Cauchy representation $\rho_X$, an effectively
open subset of $X$ is one whose preimage under $\rho_X$ is $\lSigma^0_1$ in $\DomainOf{\rho_X}$. A computable map
$f:X\to Y$ pulls effectively open sets of $Y$ back to effectively open sets of $X$, because a realizer for $f$
transforms Cauchy names before the semidecision procedure runs. Thus computable maps preserve effective openness under
preimages, whereas arbitrary Borel maps preserve Borel
measurability under preimages. <!--
formalization: skip-begin (引用・背景説明・読書案内:
名前での半決定の定義、realizer合成によるeffective-open逆像、およびBorel可測写像の可測集合逆像はそれぞれLeanに接続済み。
残りの一文だけは任意のBorel写像に階層レベル保存を期待してはならないという一般的注意で、具体的反例を局所的に証明していない。)
--> The latter need not preserve individual levels of the Borel hierarchy.<!--
formalization: skip-end
-->

<!-- formalization: skip-begin (chapter overview, references, and proof scope) -->
The previous chapter introduced the lightface hierarchy and recursive ordinals. This chapter develops the reusable
rank and coding tools: boundedness, norms and separation, uniform operations at a fixed parameter, and recursive
Borel expressions. The final section applies them to effective forms of the classical theorems.

§{sec:effective-dst-dichotomies} uses these tools for the Gandy--Harrington topology and the complete proofs of
Silver's dichotomy and HKL. Readers continuing to computable analysis can instead proceed from the effective versions
here to §{sec:computable-polish-tte}. The Kondo--Addison basis theorem and Spector--Gandy remain cited inputs;
they are identified where used below.
<!-- formalization: skip-end -->

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

This chapter requires recursive trees, relativization, and ordinal notations from §{sec:effective-dst}. Recall
the classical separation theorem in §{sec:lusin-separation} and refinement theorem in
§{sec:polish-topology-refinement} as targets for effective versions. On a first pass, follow boundedness,
basis and separation statements, and the parameter conventions in §{sec:edst-generic-conditions}. The uniform
Borel-code constructions explain how these statements are implemented; use
§{sec:lambda-effective-borel-programs} and §{sec:lambda-transfinite-tree-programs} when checking their
programs. Readers heading to Silver and HKL should retain the boundedness and separation tools before
§{sec:effective-dst-dichotomies}. Effective Cantor--Bendixson and Lusin--Suslin are separate applications of
the same coding infrastructure.

<!-- formalization: skip-end -->

## Boundedness and $\lPi^1_1$-completeness {#sec:edst-boundedness}

\begin{mathmeta}
  \vars{p,q,x}{Name}
  \vars{j,n}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
boundednessの役割を述べる導入・動機付け。定理は直後で別に提示され、ここは追加の局所証明を主張しない。)
--> The most useful single tool of effective DST is the boundedness theorem for $\lPi^1_1$. It is what makes recursive
ordinal bounds the right effective replacement for countable ordinal bounds.<!--
formalization: skip-end
-->

\begin{mathmeta}
  \define{WellFoundedTrees}
\end{mathmeta}
Let $\WellFoundedTrees\IncludedIn\BaireSpace$ be the set of codes for well-founded rooted trees on the natural
numbers. For $p\in\BaireSpace$, define
$$T_p:=\{t:\forall j\ (0<j\le\Length{t}\ \Longrightarrow\ p(\LambdaListCode{\restrict{t}{j}})\ne0)\}.$$
This is a prefix tree containing the empty word. Every rooted prefix tree has such a code: assign digit one
to the codes of its nodes and zero to all other word codes. Membership in $\WellFoundedTrees$ says
$$\forall x\in\BaireSpace\;\exists n\;\restrict{x}{n}\notin T_p,$$
so it is $\lPi^1_1$. Conversely, let $A\IncludedIn\BaireSpace$ be $\bPi^1_1$. Apply the pair-tree representation
of §{sec:edst-recursive-trees}, relative to a code for its complement, to obtain a tree $S$ such that
$$p\notin A\quad\Longleftrightarrow\quad
\exists q\;\forall n\;\Pair{\restrict{p}{n}}{\restrict{q}{n}}\in S.$$
Put $V_p=\{t:\Pair{\restrict{p}{\Length{t}}}{t}\in S\}$, adding the empty root if necessary; this does not add any
infinite
branch. Let $c(p)$ be its characteristic code under the preceding convention, so $T_{c(p)}=V_p$.
Each membership test uses only a finite prefix of the input, so $p\mapsto c(p)$ is continuous and recursive
relative to the chosen code. The section-tree test gives
$$p\in A\quad\Longleftrightarrow\quad c(p)\in\WellFoundedTrees.$$
For lightface data the map is recursive without an extra parameter. Hence $\WellFoundedTrees$ is
\termuseas{Gamma-complete}{$\bPi^1_1$-complete}, and the reduction is effective in the lightface case.

For a well-founded rooted tree $T$, write $\rho_T(t)$ for the rank of its node $t$ under strict extension,
and put $\rho(T):=\rho_T(\emptySeq)$. Thus terminal nodes have rank zero. The countability argument in
§{sec:borel-codes-rank} shows $\rho(T)<\omegaOneOrd$ for every individual tree.

\begin{lemma*}[\termdefineas{tree-rank comparison lemma}{Tree-rank comparison}]
Let $T$ and $S$ be trees with roots. Consider root-preserving maps $f:T\to S$ that send strict extensions in $T$ to
strict extensions in $S$.

\begin{enumerate}
\item if such a map exists and $S$ is well founded, then $T$ is well founded and $\rho(T)\leq\rho(S)$;
\item if $T$ and $S$ are well founded and $\rho(T)\leq\rho(S)$, then such a map exists.
\end{enumerate}
\end{lemma*}

\begin{proof}[Proof]
For (1), an infinite branch through $T$ would map to an infinite strict-extension chain in $S$. Once $T$ is known to be
well founded, induction upward from the terminal nodes gives
$$
\rho_T(t)\leq\rho_S(f(t))
$$
for every $t\in T$, and applying this at the roots gives the rank inequality.

For (2), send the root of $T$ to the root of $S$ and recurse down $T$. Maintain
$\rho_T(t)\leq\rho_S(f(t))$. If $u$ is an immediate successor of $t$, then
$\rho_T(u)<\rho_S(f(t))$. The definition of the rank at $f(t)$ therefore supplies a strict extension $v$ of $f(t)$
with $\rho_T(u)\leq\rho_S(v)$. Put $f(u)=v$. Choices for different successors may coincide, which is harmless because
only strict-extension preservation is required.
\end{proof}

\begin{theorem*}[\termdefineas{boundedness theorem for well-founded trees}{Boundedness theorem}]
The following two forms hold.

\begin{enumerate}
\item If $A\IncludedIn\WellFoundedTrees$ is $\bSigma^1_1$, then
$$\sup\{\rho(T_p):p\in A\}<\omegaOneOrd.$$
\item If $A\IncludedIn\WellFoundedTrees$ is $\lSigma^1_1$, then
$$\sup\{\rho(T_p):p\in A\}<\churchKleeneOrd.$$
\end{enumerate}
More generally, a $\lSigma^1_1(\varepsilon)$ family has a single $\varepsilon$-recursive well-order of type
$\alpha$ such that
$$\rho(T_p)<\alpha<\relativeChurchKleeneOrd{\varepsilon}\qquad(p\in A).$$
\end{theorem*}

\begin{proof}[Proof]
We prove the relative assertion first. Represent $A$ as $\pi_0([U])$ with an $\varepsilon$-recursive pair tree
$U$. A second pair tree will detect branches in the coded trees. For finite words $s,t$, put
$$\begin{aligned}
R(s,t)\quad\Longleftrightarrow\quad
&\forall j\ (0<j\le\Length{t}\ \Longrightarrow\\
&\quad[\LambdaListCode{\restrict{t}{j}}<\Length{s}\ \Longrightarrow\ s(\LambdaListCode{\restrict{t}{j}})\ne0]).
\end{aligned}$$
Only digits already present in $s$ are tested. Let $S$ consist of the equal-length pairs $\Pair{s}{t}$ for which
$R(\restrict{s}{n},\restrict{t}{n})$ holds for every $n\le\Length{s}$. This is a recursive pair tree;
§{sec:lambda-kleene-brouwer} gives its finite decision program.

For all $p,q\in\BaireSpace$,
$$\Pair{p}{q}\in[S]\quad\Longleftrightarrow\quad q\in[T_p].$$
Indeed, a branch of the coded tree passes every available digit test. Conversely, fix $j>0$ and take
$n\ge j$ with $n>\LambdaListCode{\restrict{q}{j}}$. The length-$n$ test then checks the required digit.
Moreover, $T_p\IncludedIn S_p$, where $S_p:=\{t:\Pair{\restrict{p}{\Length{t}}}{t}\in S\}$.
For every node of the coded tree, all the tests at its prefixes succeed. Both trees contain the empty root.
Thus the projections of $U$ and $S$ are disjoint, and $\rho(T_p)\le\rho(S_p)$ for $p\in A$.

For a word $w$, write $w_1,w_2$ for its coordinatewise numerical projections and $w_{21},w_{22}$ for
those of $w_2$. Form the single rooted tree
$$J:=\{\emptySeq\}\cup\{w:\Pair{w_1}{w_{21}}\in U\text{ and }\Pair{w_1}{w_{22}}\in S\}.$$
Its membership program extracts the three coordinates and runs the two finite decision programs at the original
parameter. An infinite branch would give a point in both projections, so $J$ is well founded.
For $p\in A$, choose a witness $u$ with $\Pair{p}{u}\in[U]$. The map
$$t\longmapsto\WordPair{\restrict{p}{\Length{t}}}{\WordPair{\restrict{u}{\Length{t}}}{t}}$$
sends $S_p$ into $J$, preserves the root and strict extension, and hence gives $\rho(S_p)\le\rho(J)$.
The witness is used only to compare ranks; the program deciding membership in the common tree does not choose it.

By §{sec:edst-recursive-tree-ranks}, the Kleene--Brouwer order of $J$ has an $\varepsilon$-recursive
presentation of type $\alpha$ with
$$\rho(T_p)\le\rho(S_p)\le\rho(J)<\alpha<\relativeChurchKleeneOrd{\varepsilon}\qquad(p\in A).$$
Taking the supremum gives a value at most $\alpha$, still strictly below the relative bound.
The constant-zero parameter gives the lightface assertion. For a boldface analytic family, choose a parameter
coding its pair-tree presentation. The relative bound is countable by §{sec:hyperarithmetic-hierarchy},
so the same argument proves the boldface assertion.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
boundednessの後続用途への参照と定性的なスローガンの説明。新しい構成や精密な追加命題を証明する箇所ではなく、
具体的な定理・適用は参照先で監査する。)
--> Boundedness is the engine behind the Suslin–Kleene direction of Kleene's theorem in
§{sec:edst-suslin-kleene} and behind the \termuse{boundedness theorem for well-founded trees} cited in
§{sec:borel-codes-why}. It also
underwrites the slogan that $\lPi^1_1$ predicates
are quantitatively rigid: one cannot witness a $\lPi^1_1$-complete property by an $\lSigma^1_1$-defined family without
leaving room for arbitrarily complex elements.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
後続のseparation・rank approximation・dichotomy節への道案内。
列挙した各構成をこの段落で新たに証明するという主張ではない。)
--> This theorem is the hinge between the effective and classical halves of the book. In
§{sec:edst-basis-norms-separation}, it gives effective Borel separators. In
§{sec:edst-coanalytic-ranks-silver}, it turns an analytic family inside a coanalytic set into a bounded-rank Borel
approximation. The full Glimm--Effros and Silver arguments use the splitting constructions proved in
§{sec:effective-dst-dichotomies}.<!--
formalization: skip-end
-->

## Basis, Norms, and Separation {#sec:edst-basis-norms-separation}

\begin{mathmeta}
  \vars{x,y,z,a,\varepsilon}{Name}
  \vars{s,t,s_*}{Seq(Nat)}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
後続のbasis・norm・separationの構成を導入する動機付けだけで、追加命題や証明ステップを提示していない。)
--> Boundedness becomes useful only after it is packaged into three working forms: basis theorems, coanalytic norms, and
separation. These are the steps that keep the later dichotomy proofs from becoming mysterious.<!--
formalization: skip-end
-->

A \termdefine{coanalytic norm} on a $\bPi^1_1$ set $A\IncludedIn\BaireSpace$ is an ordinal-valued map
$\varphi:A\to\omegaOneOrd$ whose initial segments
$$
A_{\le\alpha}:=\{x\in A:\varphi(x)\le\alpha\}
$$
are Borel and whose comparisons admit starred analytic and coanalytic extensions. Thus there are relations
$\leq_\Sigma,\leq_\Pi$ on the ambient space such that, for every fixed $y\in A$,
$$
x\leq_\Sigma y
\quad\Longleftrightarrow\quad
x\leq_\Pi y
\quad\Longleftrightarrow\quad
x\in A\text{ and }\varphi(x)\leq\varphi(y),
$$
with $\leq_\Sigma$ in $\bSigma^1_1$ and $\leq_\Pi$ in $\bPi^1_1$.

Analogous starred relations represent strict comparison. Agreement is required only when the right-hand
parameter lies in $A$; <!--
formalization: skip-begin (引用・背景説明・読書案内:
一般・effective norm定義とtree rankの実例はEffectiveRankProseに接続済み。
残りはAxAに制限した比較のanalytic性を誤って要求しないための一般的注意で、具体的反例の局所証明を提示していない。)
--> the comparison restricted to $A\times A$ need not itself be analytic.<!--
formalization: skip-end
-->
For a fixed $\varepsilon$, the effective version requires $A$ to be $\lPi^1_1(\varepsilon)$ and the two
comparison extensions to be $\lSigma^1_1(\varepsilon)$ and $\lPi^1_1(\varepsilon)$, respectively.
We construct this stronger version for tree ranks below.

Fix an $\varepsilon$-recursive pair tree $T$. Retain an empty root in its sections and put
$$T_x:=\{\emptySeq\}\cup\{t:\Pair{\restrict{x}{\Length{t}}}{t}\in T\},\qquad
A:=\{x:T_x\text{ is well founded}\}.$$
Then $A=\SetDifference{\BaireSpace}{\pi_0([T])}$. On $A$ define $\varphi(x):=\rho(T_x)$.
Let $L(x,y)$ assert that there is a root-preserving map from $T_x$ to $T_y$ preserving strict extension.
Let $K(x,y)$ assert the existence of a strict-extension-preserving map that sends the root to a nonempty node.
Define the four relations on the whole ambient space by
$$\begin{aligned}
x\leq_\Sigma y&\quad\Longleftrightarrow\quad L(x,y),&
x\leq_\Pi y&\quad\Longleftrightarrow\quad\neg K(y,x),\\
x<_\Sigma y&\quad\Longleftrightarrow\quad K(x,y),&
x<_\Pi y&\quad\Longleftrightarrow\quad\neg L(y,x).
\end{aligned}$$

\begin{proposition*}[\termdefineas{starred comparisons and Borel layers of tree ranks}{Starred
comparisons and Borel layers of tree ranks}]
The relations with subscript $\Sigma$ are $\lSigma^1_1(\varepsilon)$, and those with subscript $\Pi$ are
$\lPi^1_1(\varepsilon)$. For every $y\in A$,
$$\begin{aligned}
x\leq_\Sigma y\ \Longleftrightarrow\ x\leq_\Pi y
&\ \Longleftrightarrow\ x\in A\text{ and }\varphi(x)\le\varphi(y),\\
x<_\Sigma y\ \Longleftrightarrow\ x<_\Pi y
&\ \Longleftrightarrow\ x\in A\text{ and }\varphi(x)<\varphi(y).
\end{aligned}$$
Every value of $\varphi$ is countable, and $A_{\le\alpha}$ is Borel for every $\alpha<\omegaOneOrd$.
Thus this root-rank function is a \termuse{coanalytic norm}.
\end{proposition*}

\begin{proof}[Proof]
The complement of $A$ is the projection of the recursive pair tree, so $A$ is coanalytic at the original
parameter. Each node rank is countable. Indeed, well-founded induction shows that every ordinal below a node's
rank occurs as the rank of another node: in the defining supremum choose a successor whose rank still dominates
the desired ordinal and apply the induction hypothesis. There are only countably many nodes, so there are only
countably many ordinals below each rank.

For the comparison relations, encode the input pair by $z=\NamePair{x}{y}$ and form two pair trees
$$\begin{aligned}
U&:=\{\Pair{s}{t}:\Pair{s_1}{t}\in T\},\\
V&:=\{\Pair{s}{t}:\Pair{s_2}{t}\in T\},
\end{aligned}$$
where $s_1,s_2$ are the coordinatewise numerical projections. Their rooted sections are exactly $T_x,T_y$.
The list-map and coordinate-preimage programs of §{sec:lambda-kleene-brouwer} decide their membership.
Apply the finite map tests of §{sec:lambda-comparison-programs}, with either the empty-root or nonempty-root test.
Their projections are $L$ and $K$, respectively. All programs use the same $\varepsilon$. Swapping the two input
coordinates is another numerical pairing of projections, so the complements defining the two remaining relations
are coanalytic at that parameter.

Fix $y\in A$. If $x\in A$, tree-rank comparison identifies $L(x,y)$ with the non-strict rank inequality and
$K(x,y)$ with the strict inequality. For the latter, the root image has rank strictly below the target root;
conversely a strict rank inequality supplies a nonempty target node whose rank dominates the source root, after
which the same comparison construction applies. If $x\notin A$, no extension-preserving map can send its
ill-founded tree into the well-founded target. A branch in the ill-founded tree supplies both reverse maps,
by sending a word to the branch prefix of its length, or of its length plus one. Thus both analytic comparisons
and both coanalytic comparisons are false. This proves the two equivalences for every first argument.

For fixed $y\in A$, the set $\{x:L(x,y)\}$ and its complement $\{x:K(y,x)\}$ are analytic, since fixing a
coordinate is continuous. \termuse{Suslin's theorem} makes $A_{\le\varphi(y)}$ Borel.
Now fix $\alpha<\omegaOneOrd$ and let
$$D:=\{\beta\le\alpha:\exists y\in A\ (\varphi(y)=\beta)\}.$$
This is a countable set of ordinals. For each $\beta\in D$, choose $y_\beta\in A$ with
$\varphi(y_\beta)=\beta$. Then
$$A_{\le\alpha}=\bigcup_{\beta\in D}A_{\le\varphi(y_\beta)}.$$
For the forward inclusion use the rank of the given point as the index; the reverse inclusion follows from the
bound on every index. This is a countable union of Borel sets, including the empty union when no rank is attained
below the bound. The choices prove Borelness and are not asserted to be computable.
\end{proof}

\begin{corollary*}[\termdefineas{bounded Borel layers of tree ranks}{Bounded Borel layers of tree ranks}]
If $C\IncludedIn A$ is $\lSigma^1_1(\varepsilon)$, there is an $\varepsilon$-recursive well-order of type $\alpha$
such that
$$\sup\{\varphi(x):x\in C\}\le\alpha<\relativeChurchKleeneOrd{\varepsilon}.$$
In particular, $C\IncludedIn A_{\le\alpha}$, where the containing layer is Borel. In the boldface case, every analytic
subset of
$A$ is likewise contained in a countable-rank Borel layer.
\end{corollary*}

\begin{proof}[Proof]
Write $C=\pi_0([U_C])$ at the same parameter. The projections of $U_C$ and $T$ are disjoint. The joint tree in
§{sec:edst-boundedness} gives a single $\varepsilon$-recursive well-order whose type strictly bounds every
root rank of $T_x$ for $x\in C$. Taking the supremum gives the displayed inequality, and the preceding
proposition supplies the Borel layer. For an arbitrary analytic subset, encode the node sets of its pair-tree
presentation and of the fixed tree
in one parameter. This leaves the section trees and their ranks unchanged. The resulting relative ordinal
bound is countable.
\end{proof}

For the constant-zero parameter the bound is below $\churchKleeneOrd$. <!--
formalization: skip-begin (引用・背景説明・読書案内:
constant-zero parameterへの特殊化はsectionRank_uniform_boundへ接続済み。
未リンクの残りだけはordinal relabelingでeffective boundを保存すると読んではならないという適用範囲の注意で、
具体的relabelingの証明を提示しない。)
--> This effective bound concerns the
specified tree-rank norm; arbitrary ordinal relabelings of a norm need not preserve it.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
次のseparation形を紹介する一文だけ。命題と証明は直後の独立した監査対象。)
--> This immediately gives the separation form used later.<!--
formalization: skip-end
-->

\begin{statement*}[Effective Lusin separation from ranks] If $A_0,A_1\IncludedIn\BaireSpace$ are disjoint analytic
sets, then there is a Borel set $B$ with
$$
A_0\IncludedIn B\IncludedIn \SetDifference{\BaireSpace}{A_1}.
$$
Moreover, if both sets have pair-tree presentations decidable relative to a real parameter $a$, one can take
$B$ to be a tree-rank layer at an ordinal with an $a$-recursive well-order presentation. The labels of a Borel
code for this same $B$ are computable relative to $a$, so in particular $B$ is hyperarithmetic in $a$.

\end{statement*}

\begin{proof}[Proof] Apply the tree-rank coanalytic norm $\varphi$ to the coanalytic set
$\SetDifference{\BaireSpace}{A_1}$. Since $A_0$ is analytic and contained in that coanalytic set, boundedness gives
an ordinal $\alpha$ with $A_0\IncludedIn(\SetDifference{\BaireSpace}{A_1})_{\le\alpha}$.
Take this initial segment as $B$. It is Borel by the definition of the norm and is disjoint from $A_1$.

For the relative assertion, use the given pair trees $T_0,T_1$ for $A_0,A_1$, and take $\varphi(x)$ to be the root
rank of $(T_1)_x$. The joint tree $J$ in §{sec:lambda-recursive-borel-separation} is well founded, and its root
rank $\alpha$ bounds every $\varphi(x)$ for $x\in A_0$. Its Kleene--Brouwer presentation has larger
$a$-recursive order type, so downward closure gives an $a$-recursive well-order presentation of $\alpha$.
The rank-layer code constructed there has value exactly $B$: accessibility of the section root is equivalent
to $x\notin A_1$, and its rank is at most the rank of the root of $J$ exactly when $\varphi(x)\le\alpha$.
The closed lambda rank-label program computes this code at the same parameter $a$. This construction uses
the two tree deciders directly; it does not select an ordinal presentation or a branch. The existence of the
ordinal presentation and the computation of the separator are distinct conclusions.
\end{proof}

<!-- formalization: skip (Kondo--Addison is a cited specialist basis theorem) -->
The basis form is the witness-producing analogue. A basis theorem says that a nonempty definable set contains a witness
from a controlled class of reals. The version used in §{sec:forcing-absoluteness} is the
\termuseas{Kondo--Addison basis theorem}{Kondo--Addison basis theorem}: a nonempty coanalytic set relative to $a$ has a
member in $L[a]$. Producing that constructible member is the substance of the theorem; its proof uses the standard
leftmost-branch and absoluteness analysis, not merely the existence of a least nonempty rank layer. The point is that
$L[a]$ is absolute across forcing extensions with the same ordinals, which is why the theorem supplies the missing
witness in Shoenfield absoluteness.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
後続のdichotomy証明が用いる道具と依存しない外部道具を説明する案内。ここで新たなseparator構成やfusion命題を提示していない。)
--> For the dichotomy proofs, effective separation supplies definable enlargements and invariant separators. Boundedness
provides its rank-theoretic foundation.
The analytic-condition constructions in §{sec:effective-dst-dichotomies} keep these witnesses through fusion;
they do not require the Kondo--Addison basis theorem or a family of Borel partial bijections.<!--
formalization: skip-end
-->

## Uniform Codes and Fixed Parameters {#sec:edst-generic-conditions}

\begin{mathmeta}
  \vars{x,y,z,q,\varepsilon,\alpha,\beta}{Name}
  \vars{e,h,i,j,k,m,n}{Nat}
  \vars{s,t,u,v,u_*}{Seq(Nat)}
  \vars{r}{Fun(Seq(Nat),Prop)}
  \vars{f_*}{Fun(Seq(Nat),Seq(Nat))}
  \vars{\sigma,\tau}{Fun(Nat,Nat)}
\end{mathmeta}

\begin{proposition*}[\termdefineas{common parameter for analytic presentations}{A common parameter for
analytic presentations}]
Let $\Sequence{A_i}{i\in\NN}$ be any countable family of analytic subsets of $\BaireSpace$. There are a real
$\varepsilon$ and pair trees $T_i$ such that $A_i=\pi_0([T_i])$ and membership in $T_i$ is decided by
one lambda program relative to $\varepsilon$, jointly in the index and finite node. No computability of
the initially given family is assumed.
\end{proposition*}

\begin{proof}[Proof]
Choose closed sets $K_i\IncludedIn\BaireSpace\times\BaireSpace$ with $A_i=\pi_0(K_i)$, and set
$$T_i=\{\Pair{s}{t}:\Length{s}=\Length{t},\quad K_i\cap(\cyl{s}\times\cyl{t})\ne\emptyset\}.$$
These sets of nodes are synchronized and downward closed. If $\Pair{x}{y}\in K_i$, every pair of its equal-length
prefixes belongs to $T_i$. Conversely, if all those prefix pairs belong to $T_i$, choose a point of $K_i$
in each corresponding cylinder. These points converge to $\Pair{x}{y}$, since both coordinates agree with
it on increasingly long prefixes. Closedness gives $\Pair{x}{y}\in K_i$. Hence $[T_i]=K_i$, including when
$K_i$ is empty.

Encode all node tests in one parameter by
$$\varepsilon\bigl(\NatPair{i}{\NatPair{\LambdaListCode{s}}{\LambdaListCode{t}}}\bigr)
 =\begin{cases}1,&\Pair{s}{t}\in T_i,\\0,&\Pair{s}{t}\notin T_i.\end{cases}$$
The list code and numerical pairing are bijective, so this specifies every coordinate without ambiguity.
The closed lambda program that queries its parameter at its numerical input and returns the answer
now decides the joint predicate. Fixing the first component gives a decider for each tree.
This packs the required information into the parameter; it does not compute that parameter from an
unspecified presentation of the analytic sets.
\end{proof}

Thus any prescribed countable list of analytic data can be included before fixing the parameter.
Once it is fixed, all later condition refinements must stay relative to it. Adding a further arbitrary
analytic set later may require a different parameter and a different condition order.

For the uniformity assertion we make the finite comparison tests explicit. If $T$ is a pair tree, put
$$T_x:=\{u:u=[]\lor\Pair{\restrict{x}{\Length{u}}}{u}\in T\}.$$
Adding the empty root does not add a branch: membership at length $n+1$ in the original tree implies
membership at length $n$ by downward closure. Thus $T_x$ has a branch exactly when $x\in\pi_0([T])$.
Let $u_i$ be the unique word with code $i$.
For a finite word $t$, let $f_t(u)$ be the word coded by its entry $t_{\LambdaListCode{u}}$, using code zero when that
entry is absent. For an infinite sequence $q$, let $f_q(u)$ be the word coded by $q(\LambdaListCode{u})$.
Every map on finite words has this form for some $q$.

Define the finite section test by
$$R_T(s,u)\quad\Longleftrightarrow\quad u=[]\lor\Pair{\restrict{s}{\Length{u}}}{u}\in T.$$
Fix a root condition $r$, either $r(u)\Longleftrightarrow u=[]$ or $r(u)\Longleftrightarrow u\ne[]$.
At a pair $\Pair{s}{t}$, with $n=\Length{s}$, require $r(f_t([]))$ when $0<n$.
For each $i<n$, put $u=u_i$. If $\LambdaListCode{u}<n$, $\Length{u}\le n$, and $R_T(s,u)$, require both
$$\Length{f_t(u)}\le n\quad\Longrightarrow\quad R_S(s,f_t(u))$$
and, for every $j<n$ with $v=u_j$,
$$\begin{gathered}
\LambdaListCode{v}<n,\quad v\prefixOf u,\quad \Length{v}<\Length{u}\\
\Longrightarrow\quad f_t(v)\prefixOf f_t(u),\quad \Length{f_t(v)}<\Length{f_t(u)}.
\end{gathered}$$
Let $R_r(s,t)$ denote the conjunction of these requirements. The code guards are redundant inside the
bounded loops but indicate exactly which entries of an infinite map are available on synchronized prefixes.
The image-length guard is essential: membership in the target section must wait until the point prefix is long enough.

\begin{lemma*}[\termdefineas{finite comparison-map tests}{Finite comparison-map tests}]
Apply the finite-test tree construction of §{sec:edst-finite-check-trees} to $R_r$, and call the resulting
tree $C_r(T,S)$. Then $\Pair{x}{q}\in[C_r(T,S)]$ exactly when $f_q$ maps $T_x$ into $S_x$, preserves strict
extensions, and satisfies $r(f_q([]))$. If the input trees have a joint decider at parameter $\varepsilon$,
so do these comparison trees, uniformly in the family index.
\end{lemma*}

\begin{proof}[Proof]
A genuine map passes every test: if $\LambdaListCode{u}<n$, then $f_{\restrict{q}{n}}(u)=f_q(u)$, and if
$\Length{u}\le n$,
the finite section test at $\restrict{x}{n}$ agrees with membership in $T_x$.
Conversely, suppose every prefix test passes. The root is checked at length one. For any $u\in T_x$,
choose $n\ge\max\{\LambdaListCode{u}+1,\Length{u},\Length{f_q(u)}\}$. The image-membership test then proves
$f_q(u)\in S_x$.
For a strict prefix $v$ of $u$, choose $n\ge\max\{\LambdaListCode{u}+1,\LambdaListCode{v}+1,\Length{u}\}$; the edge
test proves strict
extension preservation. These bounds are used to verify the construction, not to compute the infinite map.
The finite tests use only list access, lengths, prefixes, the two tree deciders, and two bounded loops.
Their explicit lambda programs in §{sec:lambda-comparison-programs} use the original parameter throughout.
\end{proof}

\begin{proposition*}[\termdefineas{uniform lambda separation}{Uniform separation at a fixed parameter}]
For disjoint projections $A=\pi_0([T])$ and $B=\pi_0([S])$ of pair trees decidable relative to
$\varepsilon$, there are projections $D,D'$ at the same parameter such that
$$A\IncludedIn D\IncludedIn B^{\complement},\qquad D=(D')^{\complement}.$$
On the tree indices of §{sec:edst-pair-tree-indices}, two total numerical lambda programs produce indices
for $D$ and $D'$ from the paired input indices. The programs are defined on every pair of indices;
only the displayed conclusions require disjointness.
\end{proposition*}

\begin{proof}[Proof]
Take $D=\pi_0([C_{=}(S,T)])$ and $D'=\pi_0([C_{\ne}(T,S)])$, where the subscripts specify the two
root tests. At least one of $T_x,S_x$ is well founded. If both are well founded, the tree-rank comparison
lemma identifies the two conditions with $\rho(S_x)\le\rho(T_x)$ and $\rho(T_x)<\rho(S_x)$.
If just one is ill founded, a branch supplies the map into that tree, and a map in the other direction
would produce a branch in a well-founded tree. Thus the two conditions are complementary and give the
required inclusions. For indices, first use the delayed tree presentations, which form a jointly decidable
family on all indices. Apply the two comparison constructions to this family, then specialize each joint
decision program by inserting the paired input index into its fixed syntax. The specialization construction
of §{sec:edst-pair-tree-indices} is itself lambda-computable and preserves the projections.
No decision of disjointness and no enlargement of $\varepsilon$ occurs.
\end{proof}

Iterating these index transformations recursively therefore produces uniformly $\lDelta^1_1$ separators.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
再帰反復全体のlambdaプログラムとjointな正負のseparator
familyはrecursive_uniform_separatorsへ接続済み。
残る一文は個別のDelta11選択をuniformなfamilyと混同しないための一般的注意で、具体的非uniform
familyの証明を提示しない。)
--> An arbitrary sequence of separately $\lDelta^1_1$ choices would not supply the required uniformity.<!--
formalization: skip-end
-->

Write $A_e$ for the uniform pair-tree projections at the fixed parameter. Let $\sigma,\tau$ be the two total
index transformations supplied by uniform separation. For every $e=\NatPair{i}{j}$, put
$$\begin{aligned}
C&:=\{\NatPair{i}{j}:A_i\cap A_j=\emptyset\},\\
D_e&:=A_{\sigma(e)},\qquad D'_e:=A_{\tau(e)},\\
V_e&:=D_e,\qquad W_e:=(D'_e)^{\complement}.
\end{aligned}$$
The input programs need not be total: the delayed tree presentation defines $A_e$ for every index.
The trees presenting $D_e$ and $D'_e$ have joint deciders in $e$ and the finite node, obtained by
computing $\sigma(e)$ or $\tau(e)$ before running the uniform indexed-tree decider.

\begin{proposition*}[\termdefineas{codes for complemented relative projections}{Codes for sets and their complements}]
The family $V$ is uniformly analytic and $W$ is uniformly coanalytic at the original parameter, and
$$e\in C\quad\Longrightarrow\quad V_e=W_e.$$
Every set whose two sides have relative pair-tree presentations is $V_e$ for some $e\in C$.
Thus the valid codes describe exactly the complemented relative projections.
\end{proposition*}

\begin{proof}[Proof]
Uniformity follows from the joint tree deciders. If $e\in C$, separation gives
$D_e=(D'_e)^{\complement}$, so $V_e=W_e$ and both sides of $V_e$ have the required presentations.
Conversely, given such a set $A$, choose indices with $A_i=A$ and $A_j=A^{\complement}$.
Then $e=\NatPair{i}{j}$ is valid, and the separation inclusions give
$$A\IncludedIn D_e\IncludedIn(A^{\complement})^{\complement}=A.$$
Hence $D_e=A$. This is an existence assertion for codes of a given set, not a procedure selecting codes
from unspecified set data.
\end{proof}

\begin{proposition*}[\termdefineas{uniform witnesses to invalid codes}{Uniform witnesses to invalid codes}]
There is a jointly decidable family of pair trees $U_e$ at the original parameter such that
$$\pi_0([U_e])=\{z\in\BaireSpace:e\notin C\}.$$
Moreover, a total numerical lambda program transforms $e$ into an analytic index for this projection.
Thus invalidity has a uniform analytic witness, and $C$ is coanalytic; no decision of validity is required.
\end{proposition*}

\begin{proof}[Proof]
For any pair tree $T$, first take the inverse image of its projection under the first coordinate of a
coded pair, then project to the second coordinate. The resulting tree $N(T)$ has the exact body identity
$$[N(T)]=\{\Pair{z}{q}:\Pair{\NameProjection{1}{q}}{\NameProjection{2}{q}}\in[T]\}.$$
Its projection is therefore the whole space when $\pi_0([T])$ is nonempty, and empty otherwise.
The new point $z$ is unused; the witness stores the omitted point and the old witness. The word
transformations and finite tests in these two operations preserve joint decidability in a family index.

For $e=\NatPair{i}{j}$, take the intersection tree for $A_i\cap A_j$ and apply $N$ to it.
A witness in $U_e$ stores a point $x$ and two witnesses for $x\in A_i$ and $x\in A_j$, as
$\NamePair{x}{\NamePair{\alpha}{\beta}}$. Conversely, such a point and two witnesses give a branch over every $z$.
This proves the displayed projection identity, including empty input trees. Computing the projections of
$e$, pairing witnesses, and retaining $e$ through the word operations gives one joint tree decider.
Specializing it gives the claimed numerical index transformation. The whole-space/empty-space description
is a statement about the projection; it is not a test deciding which case holds.
\end{proof}

\begin{proposition*}[\termdefineas{uniform analytic kernel tests}{Uniform analytic kernel tests}]
Families of pair-tree projections with a joint decision program are closed under binary union,
intersection, and inverse images under the two point projections. From such a family $A_e$ one can
also construct a joint tree family for $\{z:A_e\ne\emptyset\}$. The intersection $\bigcap_e A_e$
has a pair-tree presentation at the same parameter.
\end{proposition*}

\begin{proof}[Proof]
Retain the family index through each word transformation using the wrapper of
§{sec:lambda-lusin-image-programs}. For intersections, split the witness into two coordinates and run both
deciders. For a binary union, the first witness entry selects the first tree when zero and the second
otherwise; apply the union construction of §{sec:edst-uniform-countable-operations} while retaining
the family index. For nonemptiness, use $N(T_e)$ from the preceding proof. Finally, the uniform
intersection construction stores one witness row for each index and checks finitely many guarded
entries at each stage. These operations compute only finite tree tests; they do not decide whether
a projected set is empty.
\end{proof}

In the kernel arguments, invalidity and failures of homogeneity or invariance will enter as analytic
alternatives, uniformly in the code. This interface uses separation directly and does not require a
completeness theorem for a separate Borel-expression syntax.

\begin{lemma*}[\termdefineas{numerical quantifiers as tree projections}{Numerical quantifiers as tree projections}]
Fix $\varepsilon\in\BaireSpace$. Suppose the numerical predicate $R(e,n,k)$ is jointly decidable by a
lambda program relative to $\varepsilon$. Then
$$A:=\{x\in\BaireSpace:\forall n\,\exists k\ R(x(0),n,k)\}$$
and its complement have pair-tree presentations decidable at the same parameter.
\end{lemma*}

\begin{proof}[Proof]
For $A$, let the witness $q$ store a suitable number $q(n)$ for every $n$ and impose
$$R(x(0),n,q(n))\qquad(n\in\NN).$$
For the complement, let $q(0)$ name an input for which every trial fails and impose
$$\neg R(x(0),q(0),k)\qquad(k\in\NN).$$
In either case row $i$ reads only the first $i+1$ entries of the point and witness. On arbitrary finite
words, read missing entries as zero; this makes each row a total decidable predicate on word codes.
The bounded-prefix construction of §{sec:lambda-recursive-borel-separation} turns these rows, with bound
$i+1$, into a decidable pair tree. A branch satisfies every row, and every pair satisfying the rows is
a branch. Projecting the first tree yields $A$: existence of all the numerical witnesses permits choosing
the sequence $q$. Projecting the second yields its complement: a single failed input can be stored in
a constant sequence. This is an existence argument for witnesses, not a procedure selecting them.
The lambda terms implementing the two row tests are given in §{sec:lambda-graph-tests}.
\end{proof}

\begin{corollary*}[\termdefineas{tree presentations of total program indices}{Tree
presentations of total program indices}]
Fix a parameter $\varepsilon$. Encode a numerical program index $e$ by any $x\in\BaireSpace$ with
$x(0)=e$. The set of such codes for programs that return a numeral on every numerical input, and its
complement, have pair-tree presentations decidable relative to $\varepsilon$.
\end{corollary*}

\begin{proof}[Proof]
Let $R(e,n,k)$ be the finite output-candidate test of §{sec:lambda-input-universal-evaluation}, where
$k=\NatPair{m}{h}$ specifies the proposed output $m$ and a finite search bound $h$.
This test terminates on every triple, even if the program with index $e$ does not terminate on input $n$.
By soundness and completeness of the test, the program with index $e$ is total relative to $\varepsilon$
exactly when $\forall n\,\exists k\ R(e,n,k)$.
Apply the preceding lemma. It constructs finite tree tests, not a decision procedure for totality.
\end{proof}

For an index intended to compute Borel-expression labels, totality is a separate requirement from the
local syntax conditions and the absence of infinite branches. The corollary handles this requirement;
it does not identify the total indices with the valid Borel-expression indices.

## Borel Expressions and Effective Codes {#sec:edst-effective-borel-codes}

\begin{mathmeta}
  \forward{LambdaListDecode}
  \vars{k}{Nat}
\end{mathmeta}

A Borel expression can also be evaluated through finite certificates at the fixed parameter.
Use numerical labels $c(s)$ on finite words: zero means absent, one means union, two means complement,
and $k+3$ means the basic cylinder $U_k:=\cyl{\LambdaListDecode{k}}$.
A valid expression has a present root, a prefix-closed set of present nodes, no children at a leaf,
at least one child at a union, exactly one child at a complement, and no infinite branch.
These are the expression trees of §{sec:borel-codes}, with numerical labels and the list coding of
§{sec:lambda-finite-lists}.

### Constructing and interpreting Borel expressions {#sec:edst-borel-constructors}

\begin{mathmeta}
  \define{BorelValue}
  \vars{i}{Nat}
\end{mathmeta}
Write $\BorelValue{c}$ for the set obtained by evaluating a valid expression $c$ at its root.
For a finite word $s$, write $(i)\concat s$ for the word obtained by adjoining $i$ at the beginning.
The constructors from §{sec:borel-codes-construction} act on label maps as follows:
$$\begin{aligned}
\BorelLeafCode{n}(\emptySeq)&:=n+3,&
\BorelLeafCode{n}((i)\concat s)&:=0,\\
\BorelComplementCode{c}(\emptySeq)&:=2,&
\BorelComplementCode{c}((i)\concat s)&:=
 \begin{cases}c(s)&i=0,\\0&i>0,\end{cases}\\
\BorelUnionCode{(c_i)}(\emptySeq)&:=1,&
\BorelUnionCode{(c_i)}((i)\concat s)&:=c_i(s).
\end{aligned}$$
Thus a complement adds a root with one subtree, while a union attaches the $i$th expression below child $i$.
The first operation consists of a single leaf.

\begin{proposition*}[\termdefineas{Borel-expression constructors}{Borel-expression constructors}]
These operations preserve validity. For valid $c$ and $c_i$,
$$\BorelValue{\BorelLeafCode{n}}=U_n,\qquad
\BorelValue{\BorelComplementCode{c}}=(\BorelValue{c})^{\complement},\qquad
\BorelValue{\BorelUnionCode{(c_i)}}=\bigcup_i\BorelValue{c_i}.$$
\end{proposition*}

\begin{proof}[Proof]
The single leaf satisfies all validity conditions. For the other two constructions, prefix closure and
all local label conditions follow from those in the attached expressions. Every attached root is present,
so the new union root has children and the new complement root has exactly one child.
A descending child chain, after entering child $i$, stays in that subtree. Removing its initial $i$
would give a descending chain in the attached expression. Thus the new child relation is well founded.
More explicitly, well-founded induction inside each attached expression proves accessibility of every
node below the new root; accessibility of the root follows because all its children are accessible.

Restrict the evaluation to the subtree below child $i$ and remove the initial $i$ from its node addresses.
The resulting assignment satisfies exactly the evaluation equations for the attached expression.
Uniqueness of evaluation by well-founded induction therefore identifies the two assignments.
The root equation now gives the stated union or complement. At a single leaf it gives $U_n$ directly.
\end{proof}

\begin{theorem*}[\termdefineas{completeness of external Borel expressions}{Completeness of external Borel expressions}]
A subset of $\BaireSpace$ is Borel if and only if it is $\BorelValue{c}$ for some valid expression $c$.
\end{theorem*}

\begin{proof}[Proof]
Let $\mathcal C$ consist of the sets having valid expressions. It contains each basic cylinder by the
leaf construction. The empty word codes $U_0=\BaireSpace$, so the complement of that leaf codes the empty
set. The complement construction closes $\mathcal C$ under complements. Given a sequence of sets in
$\mathcal C$, choose a valid expression for each; the union construction codes their union. Thus
$\mathcal C$ is a sigma-algebra containing the cylinder basis, and hence contains every Borel set.
Conversely, well-founded induction on an expression shows that every value in its evaluation is Borel:
leaves are cylinders, complement nodes take complements, and union nodes take countable unions.
Apply this at the root.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
直前の外的Borel-expression completeness定理の適用範囲についての注意。
任意のcode選択を固定パラメータでの計算可能な選択と同一視しないと説明しており、具体的な非計算可能例の局所証明ではない。)
--> This theorem concerns arbitrary external label maps. Choosing an expression for each set in a sequence
does not provide a jointly computable label map. In particular the theorem does not assert that every
Borel set has an expression recursive at a prescribed parameter.<!--
formalization: skip-end
-->

\begin{proposition*}[\termdefineas{computable Borel-expression constructors}{Computable Borel-expression constructors}]
Fix $\varepsilon$. A leaf has a computable label map. If a closed lambda program computes the labels of
$c$ relative to $\varepsilon$, then another such program computes the labels of $\BorelComplementCode{c}$.
If one closed program computes $c_i(s)$ from $\NatPair{i}{\LambdaListCode{s}}$ for all $i,s$, then another
computes the labels of $\BorelUnionCode{(c_i)}$ at the same parameter.
\end{proposition*}

\begin{proof}[Proof]
Test whether the input word is empty. Otherwise decode its first entry and remaining word. The leaf
returns zero on nonempty words; the complement retains only first entry zero; the union supplies the
first entry and remaining word to the given joint program. The list encoding, numerical projections,
and branching terms implement these operations. The explicit closed terms and their beta/query
reductions are given in §{sec:lambda-borel-constructor-programs}. They compute labels on every word,
including absent nodes. No test of expression validity or evaluation of Borel membership is used.
\end{proof}

### Borel expressions for bounded ranks {#sec:edst-borel-rank-layers}

\begin{mathmeta}
  \vars{x}{Name}
  \vars{b,i,p}{Nat}
  \vars{a,m,s,t}{Nat}
\end{mathmeta}

The rank bound in §{sec:edst-boundedness} becomes useful only after its initial segments have explicit
Borel expressions. We describe that construction for a countable relation. Fix a well-founded relation
$R$ on $\NN$ and write $r(a)$ for the rank of $a$ in $R$. Let $E_x$ be a relation on $\NN$ depending on
$x\in\BaireSpace$. For each $t,s$, suppose a valid expression $e_{t,s}$ represents
$$E_{t,s}:=\{x:E_x(t,s)\}.$$
The direction of both relations is downward: $R(b,a)$ says that $b$ is below $a$, and $E_x(t,s)$ says
that $t$ is below $s$. The relations $E_x$ need not be well founded.

\begin{mathmeta}
  \define{RankLayer}
\end{mathmeta}
Let $\RankLayer{a}{s}$ be the set of $x$ for which the restriction of $E_x$ to nodes reachable from $s$
by finitely many downward steps is well founded, and the rank at $s$ is at most $r(a)$. The rank at $s$ is used only
when that part is well founded; no ordinal
rank is assigned to a node above an infinite descending chain.

\begin{lemma*}[\termdefineas{bounded-rank recursion}{Bounded-rank recursion}]
For every $a,s$,
$$\RankLayer{a}{s}
 =\bigcap_{t\in\NN}\left(E_{t,s}^{\complement}\cup
       \bigcup_{b:\,R(b,a)}\RankLayer{b}{t}\right).$$
In particular, if $a$ has no $R$-predecessor, this is the set of $x$ for which $s$ has no $E_x$-predecessor.
\end{lemma*}

\begin{proof}[Proof]
Suppose $x\in\RankLayer{a}{s}$ and $E_x(t,s)$. The rank of $t$ is strictly less than the rank of $s$,
and hence strictly less than $r(a)$. Since
$$r(a)=\sup_{b:\,R(b,a)}(r(b)+1),$$
there is $b$ with $R(b,a)$ and the rank of $t$ at most $r(b)$. Thus $x\in\RankLayer{b}{t}$.
This proves inclusion in the displayed right-hand side.

Conversely, suppose $x$ belongs to that right-hand side. For every $E_x$-predecessor $t$ of $s$, there is $b$
with $R(b,a)$ and $x\in\RankLayer{b}{t}$. Thus every such $t$ has a well-founded relation below it,
which proves the same for $s$. The successor of the rank of $t$ is at most $r(b)+1$, and this is at
most $r(a)$. Taking the supremum over the predecessors of $s$ proves the rank bound at $s$.
If $a$ has no predecessor, the inner union is empty, giving the last assertion.
\end{proof}

The same recursion gives a precise local computation step. Fix $x$ and $a$, and write
$$L_a(t,b)\quad\Longleftrightarrow\quad R(b,a)\mathbin{\wedge}x\in\RankLayer{b}{t}.$$

\begin{corollary*}[\termdefineas{two-jump rank step}{A rank step with two jumps}]
Suppose that $E_x(t,s)$ and $L_a(t,b)$ have decision programs relative to one parameter $\varepsilon$,
with each program receiving both of its numerical arguments. Then membership of $x$ in
$\RankLayer{a}{s}$ is decidable as a predicate of $s$ relative to $(\varepsilon')'$.
\end{corollary*}

\begin{proof}[Proof]
The two deciders give a decider for
$$M(s,t,b):=\neg\bigl(E_x(t,s)\mathbin{\wedge}\neg L_a(t,b)\bigr).$$
The numerical-quantifier construction in §{sec:hyperarithmetic-hierarchy} decides
$\forall t\,\exists b\,M(s,t,b)$ using two jumps. If $E_x(t,s)$ is false, every $b$ satisfies the matrix.
If it is true, the matrix holds exactly for lower stages $b$ whose rank layer contains $x$ at $t$.
Thus the quantified matrix is equivalent to the bounded-rank recursion formula.
\end{proof}

The hypothesis requires one decider jointly in $t,b$. <!--
formalization: skip-begin (引用・背景説明・読書案内:
jointなdeciderを要求する点はrankMatrixProgram_decidesへ、
共通jumpからのreader構成はrecursive_order_twoJump_readersへ接続済み。
残りだけは段階別のprogramの存在との混同を防ぐ一般的注意で、具体的反例を証明する箇所ではない。)
--> A separate program for each lower stage does not
supply this decider.<!--
formalization: skip-end
-->  For a recursive well order, the following construction supplies the input functions
for the lower stages, together with a computable map of reader indices.

\begin{proposition*}[\termdefineas{computed readers for rank recursion}{Computed readers for rank recursion}]
Let $W=\Pair{D}{R}$ be a recursive well-order presentation. There are total numerical functions $g,i$, computed
by closed lambda terms, such that $g(a)\in\KleeneO$ for every $a\in D$ and the following holds for every
starting set $A$. Put
$$B_{a,b}:=\begin{cases}
(\IteratedJump{A}{g(b)})''&b\in D,\ bRa,\\
A&b\notin D\lor\neg(bRa).
\end{cases}$$
For $a\in D$, the program $P_{i(a)}$ with input function $\chi_{\IteratedJump{A}{g(a)}}$ returns
$\chi_{B_{a,b}}(m)$ on input $\NatPair{b}{m}$. The functions $g,i$ are independent of $A$ and are total
even at numerical arguments outside $D$.
\end{proposition*}

\begin{proof}[Proof]
Use the total notation assignment $g$ constructed in §{sec:edst-ordinal-notations}. For $a\in D$, its
simultaneous induction gives
$$\begin{gathered}
\KleeneCandidatePrecedes{1}{g(a)},\\
 b\in D,\ bRa\ \Longrightarrow
 \KleeneCandidatePrecedes{\KleeneSuccIter{g(b)}{2}}{g(a)}.
\end{gathered}$$
The numerical function
$$\ell(a,b):=\begin{cases}
\KleeneSuccIter{g(b)}{2}&b\in D,\ bRa,\\
1&b\notin D\lor\neg(bRa)
\end{cases}$$
is total and computable: decide domain membership and comparison, compute $g(b)$ when needed, and apply
the successor constructor twice. For $a\in D$, every $\ell(a,b)$ therefore has a finite certified path
to $g(a)$. Choose syntax codes $e,h$ for closed terms computing $g$ and $\ell$. The reader-index construction
in §{sec:lambda-certified-descent} gives a single total numerical map $\psi(e,h,a)$; put
$$i(a):=\psi(e,h,a).$$
The canonical jump table identifies its output row with $B_{a,b}$, by two successor equations in the predecessor
case and the base equation otherwise. Producing $i(a)$ uses only the two program indices and the stage number;
it neither searches for paths nor tests notation validity.
\end{proof}

The same reader construction works with any fixed number $k$ of successive jumps in place of two.
Replace $\KleeneSuccIter{g(b)}{2}$ by $\KleeneSuccIter{g(b)}{k}$ in the predecessor notation.
The upper-notation construction dominates every finite successor iterate of each predecessor
notation, and the canonical jump table identifies this row by $k$ successor equations.
Both index functions remain total and independent of the starting set.

\begin{corollary*}[
\termdefineas{uniform rank readers from decision indices}{Uniform rank readers from decision indices}]
There are total computable maps $\Pair{d}{r}\mapsto e(d,r)$ and $\Tuple{d,r,k,a}\mapsto i(d,r,k,a)$ with the following
property. For every pair $d,r$, the program $P_{e(d,r)}$ computes a total function $g_{d,r}$.
If the pair consists of closed program indices deciding the domain and relation of a recursive well-order
presentation, this function and the reader $P_{i(d,r,k,a)}$ satisfy the preceding proposition with
$k$ successive jumps in place of two. The upper notation is $g_{d,r}(a)$ and the starting set is arbitrary.
Both index maps are total even on inputs that do not describe a well-order.
\end{corollary*}

\begin{proof}[Proof]
Use the index map $e(d,r)$ from §{sec:edst-ordinal-notations}. The lower-notation compiler and reader compiler
in §{sec:lambda-certified-descent} give total maps $\mu$ and $\psi$. Put
$$i(d,r,k,a):=\psi\bigl(e(d,r),\mu(d,r,e(d,r),k),a\bigr).$$
Numerical composition computes this index from the four inputs. Under the decision hypotheses, the lower-notation
program selects the specified finite successor iterate at each predecessor and the base notation otherwise.
The upper-notation construction provides a finite certified path from each selected notation to the upper one.
Apply the reader theorem to the canonical jump table. Repeated successor equations identify the selected row
with the required finite jump; the base equation handles nonpredecessors. These arguments work for every
starting set. The reader searches for a path only when executed: producing its index uses composition and
syntax operations alone.
\end{proof}

We can now construct the rank-decision indices uniformly. The source relation may have infinite
branches; the predicate being decided includes well-foundedness below the given node.

\begin{theorem*}[\termdefineas{uniform recursive rank decisions}{Uniform recursive rank decisions}]
Let $W=\Pair{D}{R}$ be a recursive well-order presentation and let $E$ be a recursive relation on $\NN$.
For $a\in D$, let $Q_a$ consist of those $s$ for which $E$ is well founded below $s$ and the rank of $s$
is at most the ordinal position $\rho_W(a)$.
There are total numerical functions $g,d$, computed by closed lambda terms, such that $g(a)\in\KleeneO$
for $a\in D$ and, for every starting set $A$, the program $P_{d(a)}$ with input function
$\chi_{(\IteratedJump{A}{g(a)})''}$ decides $s\in Q_a$.
The functions $g,d$ are fixed before $A$ is supplied and are total also outside $D$.
\end{theorem*}

\begin{proof}[Proof]
Fix the preceding notation assignment $g$ and reader-index function $i$. At stage $a$, the reader
$P_{i(a)}$ supplied with $\chi_{\IteratedJump{A}{g(a)}}$ computes every lower input function
$\chi_{(\IteratedJump{A}{g(b)})''}$ for $b\in D$ with $bRa$.
Construct a fixed matrix program with numerical inputs $q,a,s,t,b$. It returns one when $E(t,s)$ is
false. Otherwise it returns zero unless $b\in D$ and $bRa$. In the remaining case it evaluates
$P_q\ChurchNumeral{b}$ to obtain a program index, then runs that program on $t$ with the lower input
function supplied by the reader. These tests precede the lower-program call.

Let $c(q,a)$ be the syntax code obtained by inserting $q,a$ into this matrix template. It is a total
computable function, whether or not the resulting matrix terminates. With the quantifier compilers
$\xi,\upsilon$ from §{sec:hyperarithmetic-hierarchy}, put
$$d_q(a):=\upsilon(\xi(c(q,a))).$$
The self-reference construction in §{sec:lambda-rank-decision-programs} supplies an index $q$ for which
$$P_q\ChurchNumeral{a}\to_\beta^*\ChurchNumeral{d_q(a)}$$
for every $a$. This computation constructs only syntax codes. Set $d=d_q$; its totality does not depend
on termination of any lower-stage decision.

Fix $A$ and induct on $a$ along $W$. At each predecessor $b$, the induction hypothesis identifies the
program whose index $P_q$ returns with a decider for $Q_b$. Thus every matrix trial at $a$ terminates,
and the matrix decides
$$\neg E(t,s)\ \lor\ \bigl(b\in D\land bRa\land t\in Q_b\bigr).$$
The compiled program with index $d(a)$ decides its $\forall t\,\exists b$ quantification using two
jumps of $\chi_{\IteratedJump{A}{g(a)}}$. The bounded-rank recursion identifies this predicate with
$s\in Q_a$. This proves the induction, including stages with no predecessor. All templates and indices
were fixed before $A$ was supplied.
\end{proof}

\begin{corollary*}[\termdefineas{hyperarithmetic rank layers}{Hyperarithmetic rank layers}]
Every $Q_a$ in the preceding theorem is a hyperarithmetic subset of $\NN$.
\end{corollary*}

\begin{proof}[Proof]
Take $A=\emptyset$. The successor equations identify
$\IteratedJump{\emptyset}{\KleeneSuccIter{g(a)}{2}}$ with $(\IteratedJump{\emptyset}{g(a)})''$.
The theorem supplies a total decision program relative to this iterated jump. Its output is the
characteristic function of $Q_a$, as required by the definition of hyperarithmeticity.
\end{proof}

To turn the recursion into an expression, use the following derived constructors:
\begin{mathmeta}
  \define{BorelEmptyCode,BorelIntersectionCode,BorelBinaryUnionCode,RankLayerCode}
\end{mathmeta}
$$\begin{aligned}
\BorelEmptyCode&:=\BorelComplementCode{\BorelLeafCode{0}},\\
\BorelIntersectionCode{\Sequence{d_i}{i\in\omega}}&:=
 \BorelComplementCode{\BorelUnionCode{\Sequence{\BorelComplementCode{d_i}}{i\in\omega}}},\\
\BorelBinaryUnionCode{c}{d}&:=\BorelUnionCode{\Sequence{f_i}{i\in\omega}},\qquad
 f_i:=\begin{cases}c&i=0,\\d&i>0.\end{cases}
\end{aligned}$$
Their values are the empty set, the countable intersection, and the binary union, respectively.
Define $\RankLayerCode{a}{s}$ by well-founded recursion on $R$:
$$\begin{aligned}
d_{a,t,b}&:=\begin{cases}\RankLayerCode{b}{t}&R(b,a),\\
                         \BorelEmptyCode&\neg R(b,a),\end{cases}\\
\RankLayerCode{a}{s}&:=\BorelIntersectionCode{
  \Sequence{\BorelBinaryUnionCode{\BorelComplementCode{e_{t,s}}}
     {\BorelUnionCode{\Sequence{d_{a,t,b}}{b\in\omega}}}}{t\in\omega}}.
\end{aligned}$$
Every union constructor still has children. When there is no lower bound $b$, the relevant children
all carry the empty-set expression; they are not removed from the syntax.

\begin{theorem*}[\termdefineas{Borel expressions for rank layers}{Borel expressions for rank layers}]
Each $\RankLayerCode{a}{s}$ is valid and
$$\BorelValue{\RankLayerCode{a}{s}}=\RankLayer{a}{s}.$$
In particular every such rank layer is Borel.
\end{theorem*}

\begin{proof}[Proof]
Use well-founded induction on $a$, simultaneously for all $s$. The recursive calls are only to
$b$ with $R(b,a)$. Their expressions are valid by induction; the other branches use the valid
empty-set expression. The constructors therefore give a valid expression at $a,s$.
Their interpretation equations and the induction hypothesis identify its value with the right-hand
side of the bounded-rank recursion lemma, and hence with $\RankLayer{a}{s}$.
Finally every valid expression has a Borel value.
\end{proof}

The well-founded recursion also has a description at finite word addresses. Its fixed initial labels are
$$\begin{array}{c|ccccc}
w&\emptySeq&(0)&\Pair{0}{t}&\Tuple{0,t,0}&\Tuple{0,t,0,0}\\\hline
\RankLayerCode{a}{s}(w)&2&1&2&1&2.
\end{array}$$
The other potentially nonzero labels are
$$\begin{aligned}
\RankLayerCode{a}{s}(\Tuple{0,t,0,0,0}\concat v)&=e_{t,s}(v),\\
\RankLayerCode{a}{s}(\Tuple{0,t,0,j})&=1\quad(j>0),\\
\RankLayerCode{a}{s}(\Tuple{0,t,0,j,b}\concat v)&=
 \begin{cases}\RankLayerCode{b}{t}(v)&R(b,a),\\
               \BorelEmptyCode(v)&\neg R(b,a)\end{cases}\quad(j>0).
\end{aligned}$$
All remaining labels are zero. These equations specify a label map even for a relation $R$ that is
not well founded: each call to another rank-layer label consumes five entries of the address.
Well-foundedness of $R$ is needed for validity and the rank interpretation, not for this finite-word recursion.

\begin{lemma*}[\termdefineas{finite labels of rank expressions}{Finite labels of rank expressions}]
For well-founded $R$, the finite-word equations give exactly the label map of $\RankLayerCode{a}{s}$.
\end{lemma*}

\begin{proof}[Proof]
Expand the countable intersection as complement, union, complement. Its first three labels are
$2,1,2$ at the displayed addresses. The binary union adds label $1$. At its child zero, a complement
adds label $2$ and its child zero enters $e_{t,s}$. At each other child, the union over $b$ adds label
$1$, then selects the lower expression or the empty-set expression according to $R(b,a)$.
Every forbidden child of a complement is absent. This is precisely the displayed list of cases.
Induction on $R$, for all finite addresses at once, identifies the recursive calls with the corresponding
lower expressions. Thus the two label maps agree.
\end{proof}

\begin{proposition*}[\termdefineas{computable labels of rank expressions}{Computable labels of rank expressions}]
Fix $\varepsilon$. Suppose one closed lambda program computes $e_{t,s}(v)$ from
$\NatPair{t}{\NatPair{s}{\LambdaListCode{v}}}$ for all $t,s,v$, and another decides $R(b,a)$
from $\NatPair{b}{a}$, both relative to $\varepsilon$. Then one closed program computes
$\RankLayerCode{a}{s}(v)$ jointly in $a,s,v$ at the same parameter.
The finite-word equations remain computable without well-foundedness of $R$; when $R$ is well founded
and the edge expressions are valid, the output is the label map of the valid expression for $\RankLayer{a}{s}$.
\end{proposition*}

\begin{proof}[Proof]
Store either an unfinished query $\Tuple{a,s,v}$ or a finished label $m$ as a natural number, with a tag
distinguishing the two cases. One update follows the finite-word equations. It either returns a finished
label, using the edge program when needed, or replaces $\Tuple{a,s,v}$ by $\Tuple{b,t,u}$ after reading the first
five entries of $v$ and checking $R(b,a)$. Finished states are left fixed. The update is a closed lambda
program built from numerical pairs, list operations, comparisons, and the two supplied programs.
Iterate it $\Length{v}+1$ times by a Church numeral and read the finished label. Every unfinished update
shortens the word by five entries, so induction on the number of updates proves that this bound suffices.
Each update preserves the label specified by the finite-word equations, and all calls retain the same
oracle parameter. For well-founded $R$, the preceding lemma identifies this label with
$\RankLayerCode{a}{s}(v)$. The explicit terms and their reduction proof are given in
§{sec:lambda-borel-constructor-programs}.
\end{proof}

### Testing Borel-expression validity {#sec:edst-borel-validity}

\begin{mathmeta}
  \vars{q,v,w,x,y,z}{Name}
  \vars{d,i,j,n,r,\ell,m_*,r_*,k_*,j_*,u_*}{Nat}
  \vars{s,t,s_*}{Seq(Nat)}
  \vars{e,k}{Nat}
\end{mathmeta}

\begin{proposition*}[\termdefineas{validity in a uniformly computable Borel family}{Validity
in a uniformly computable Borel family}]
Suppose one closed lambda program, at parameter $\varepsilon$, computes $c_e(s)$ from
$\NatPair{e}{\LambdaListCode{s}}$ for every $e,s$. Encode $e$ by the first coordinate of a point of
$\BaireSpace$. The indices satisfying the local syntax conditions, and their complement, have
pair-tree presentations decidable relative to $\varepsilon$. The indices of invalid expressions
also have such a presentation.
\end{proposition*}

\begin{proof}[Proof]
Write $i=\NatPair{\LambdaListCode{s}}{\NatPair{k}{\ell}}$. For this row let $j$ be a proposed child and
let $R(e,i,j)$ be the conjunction of
$$\begin{aligned}
c_e(\emptySeq)&\ne0,\\
c_e(s\concat(k))\ne0&\ \Longrightarrow\ c_e(s)\ne0,\\
3\le c_e(s)&\ \Longrightarrow\ c_e(s\concat(k))=0,\\
c_e(s)=1\ \lor\ c_e(s)=2&\ \Longrightarrow\ c_e(s\concat(j))\ne0,\\
c_e(s)=2\ \land\ c_e(s\concat(k))\ne0\ \land\ c_e(s\concat(\ell))\ne0
 &\ \Longrightarrow\ k=\ell.
\end{aligned}$$
These are finite, jointly decidable tests. The syntax conditions are equivalent to
$\forall i\,\exists j\ R(e,i,j)$. In the forward direction, choose any present child at a union or
complement node, and zero at other nodes. In the reverse direction, the row with $k=\ell=0$ supplies
a present child at each union or complement node; the last clause, over all pairs of children,
gives uniqueness at a complement. The other clauses give the root, prefix, and leaf conditions.
The numerical-quantifier lemma therefore gives presentations of syntax and its failure.

For failure of well-foundedness, let a witness $q$ store
$$q(n)=\NatPair{\LambdaListCode{s_n}}{k_n}.$$
Require $c_e(s_n)\ne0$, $c_e(s_{n+1})\ne0$, and $s_{n+1}=s_n\concat(k_n)$ for every $n$.
Row $n$ needs only the first $n+2$ entries of the point and witness: the first point entry gives $e$,
and two consecutive witness entries give the words and the chosen child. The label program is total,
so these rows are decidable even on arbitrary finite words, with missing entries read as zero.
The bounded-prefix construction yields a pair tree. A branch specifies an infinite child chain.
Conversely, failure of well-foundedness supplies such a chain; record its words and the child number
at each step to obtain a branch. This choice is used only to prove existence of a witness.

An expression is invalid exactly when syntax fails or its child relation is not well-founded.
Take the binary union of the two tree projections. The constructions of the row programs appear
in §{sec:lambda-recursive-borel-separation}.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
次の構成がlabel streamを読み、任意のprogram indexには有限の計算証明を用いることを紹介する方法上の案内。
構成と証明は後続の独立した項目で監査する。)
--> The preceding construction uses a uniformly total label program. To handle arbitrary program indices,
we first read labels directly from an input sequence, then verify their computations by finite certificates.<!--
formalization: skip-end
-->

\begin{lemma*}[\termdefineas{relative tree presentation of invalid label streams}{Invalid label streams}]
For $z\in\BaireSpace$ put $\eta_z(s):=z(\LambdaListCode{s})$. At each fixed parameter $\varepsilon$,
the set of $z$ for which $\eta_z$ is invalid has a pair-tree presentation decidable relative to $\varepsilon$.
\end{lemma*}

\begin{proof}[Proof]
Use the five syntax clauses from the preceding proposition with labels read from $z$. One closed
program decides the row $S(z,i,j)$ for every input sequence: numerical operations compute the
queried word codes, and each label query returns its prescribed digit. The Boolean operations use
the same terms for every input; no separate decision program is chosen for each sequence.
The syntax condition is $\forall i\,\exists j\ S(z,i,j)$, so §{sec:edst-baire-quantifiers} supplies
tree presentations of syntax and its failure.

For failure of well-foundedness, use the same chain witness as before. Each row reads two consecutive
witness entries and the two labels at the encoded words. These label addresses may depend on the
witness values, but the row is still decided by one total program. Apply the universal-row construction
of §{sec:edst-baire-quantifiers} to the coded point and witness, then project onto the point.
The equivalence with a descending child chain is the same as in the preceding proof. Finally take the
union with syntax failure. The accessors are given in §{sec:lambda-recursive-borel-separation}.
\end{proof}

At parameter $\varepsilon$, a numerical index $e$ is a \termdefine{valid Borel-expression program index}
if its program returns a numeral on every input $\LambdaListCode{s}$ and the resulting label map is
a valid Borel expression. List coding is bijective, so the totality requirement covers every numerical input.

\begin{theorem*}[\termdefineas{coanalytic validity of Borel-expression program indices}{Coanalytic
validity of Borel-expression program indices}]
Fix $\varepsilon$. Encode $e$ by any $x\in\BaireSpace$ with $x(0)=e$.
The complement of the set of codes for valid Borel-expression program indices has a pair-tree
presentation decidable relative to $\varepsilon$. Thus validity is coanalytic relative to that parameter,
including when the numbering contains partial programs.
\end{theorem*}

\begin{proof}[Proof]
Let $C_\varepsilon(e,n,k)$ be the finite output-candidate predicate from
§{sec:lambda-input-universal-evaluation}. Write a proposed computation table as
$$v(n)=\NatPair{m_n}{r_n},\qquad
\Theta_\varepsilon(e,v):\Longleftrightarrow\forall n\ C_\varepsilon(e,n,v(n)).$$
Here $m_n$ is the proposed output and $r_n$ is a finite verification bound. Each trial terminates,
even if the indexed program does not. The row program in §{sec:lambda-recursive-borel-separation}
therefore gives a tree presentation of the relation between an index code and an accepted table,
by the universal-row construction.

Decode the table as the label map
$$h_v(s):=m_{\LambdaListCode{s}}.$$
Soundness of the candidate tests shows that the indexed program computes this map whenever
$\Theta_\varepsilon(e,v)$ holds. Conversely, if the program is total, completeness supplies a successful
candidate for each input; choosing them gives a table. This is an existence statement, not an
algorithm that selects tables for arbitrary indices. Numerical-output uniqueness implies that any
accepted table has the same decoded labels as the program's output.

The map extracting the output sequence from a table uses only numerical pair projections. Pull back
the invalid-label-stream set under this map, intersect it with the accepted-table relation, and project
onto the index code. The resulting tree projection consists exactly of indices admitting an accepted
table whose decoded expression is invalid.

Finally take its union with the nontotal-index set from the earlier corollary. An index in the first
set cannot compute a valid expression, by uniqueness of its outputs; an index in the second cannot
do so because it is not total. Conversely, an index that is not valid either is nontotal or has a table,
and in the latter case its decoded expression must be invalid. This proves the claimed complement
representation. All finite tests retain $\varepsilon$; no total universal label evaluator is assumed.
\end{proof}

\begin{proposition*}[\termdefineas{fixed-parameter Borel evaluation}{Borel evaluation at a fixed parameter}]
Suppose a closed lambda program with parameter $\varepsilon$ computes $c(s)$ from $\LambdaListCode{s}$.
If $c$ is valid, both its evaluated set $A_c$ and its complement have pair-tree presentations decidable
by lambda programs at the same parameter.
\end{proposition*}

\begin{proof}[Proof]
Let a witness $w\in\BaireSpace$ store the pair of a truth bit $u_s$ and a selected child number $j_s$ at
coordinate $\LambdaListCode{s}$. Require $u_s\le1$ at every word. For every word $s$ and number $k$,
put $t=s\concat(k)$ and impose the following clauses:
$$\begin{aligned}
c(s)=0&\ \Longrightarrow\ u_s=0,\\
c(s)=1\ \land\ u_s=1\ \land\ j_s=k&\ \Longrightarrow\ c(t)\ne0\ \land\ u_t=1,\\
c(s)=1\ \land\ c(t)\ne0\ \land\ u_t=1&\ \Longrightarrow\ u_s=1,\\
c(s)=2\ \land\ c(t)\ne0&\ \Longrightarrow\ u_s+u_t=1,\\
c(s)=k+3&\ \Longrightarrow\ (u_s=1\ \Longleftrightarrow\ x\in U_k).
\end{aligned}$$
The selected child supplies the existential witness at a true union node. Thus these local clauses are
exactly the truth-assignment rules, with the additional selected-child data. For a valid expression,
well-founded induction gives the unique truth assignment. Choose a true child at each true union node
to obtain a certificate, and assign zero to absent nodes. A certificate with root bit one exists exactly
when $x\in A_c$; a certificate with root bit zero exists exactly when $x\notin A_c$.

Number the rows by $i=\NatPair{\LambdaListCode{s}}{k}$, and set
$$b(i):=\max\{\LambdaListCode{s}+1,\LambdaListCode{t}+1,1,\Length{\LambdaListDecode{k}}\}.$$
The row reads the witness at the codes of $s,t$ and the root, and reads $x$ only through its prefix of
length $\Length{\LambdaListDecode{k}}$. Hence the first $b(i)$ entries of $x,w$ suffice, including the prescribed
root bit. The bound is computed by list concatenation, length, pairing, successor, and maximum.
The clause tester runs the supplied label program at $s,t$, extracts the witness entries, compares
the indicated prefix with $\LambdaListDecode{k}$, and combines the resulting decision bits.
The explicit lambda constructions are given in §{sec:lambda-recursive-borel-separation}.

At length $n$, test each row $i<n$ with $b(i)\le n$, using the prefixes truncated to length $b(i)$.
Require these tests at every shorter prefix as well, so that the accepted equal-length pairs form a tree.
Every row is tested once $n\ge\max\{i+1,b(i)\}$. Consequently a branch is exactly a point together with a
certificate of the prescribed root bit. Projecting the two trees gives $A_c$ and its complement.
These programs decide finite certificate tests; validity is a hypothesis of the conclusion, and the
construction does not decide validity or membership in $A_c$ from $x$.
\end{proof}

\begin{mathmeta}
  \define{GHConditions}
  \forward{forces}
\end{mathmeta}
For a positive integer $d$, let $\GHConditions{d}$ be the partial order of nonempty $\lSigma^1_1$ subsets of $X^d$,
ordered by inclusion, with smaller sets stronger. Work with indices modulo equality, so this is a countable coded
partial order. Distinguish $\GHConditions{2}$, whose conditions are arbitrary analytic sets of pairs, from
$\GHConditions{1}\times\GHConditions{1}$, whose conditions are rectangles. In particular, a condition in
$\GHConditions{2}$ may require its two coordinates to be $E$-equivalent.

\begin{lemma*}[\termdefineas{fixed-parameter analytic condition presentations}{Closed presentations and
refinements of the condition order}]
At a fixed $\varepsilon$, the nonempty relative pair-tree projections form a countable condition order.
There is a sequence of closed presentations $K_e=[T_e]$ covering every condition, where the $T_e$ have
jointly decidable node membership relative to $\varepsilon$. For finite prefixes $s,t$ of the same length,
write
$$W_{e,s,t}:=\pi_0\bigl(K_e\cap(\cyl{s}\times\cyl{t})\bigr).$$
For every condition $P$, each nonempty set $P\cap W_{e,s,t}$ and $P\cap\cyl{s}$ is again a condition.
\end{lemma*}

\begin{proof}[Proof]
Use the indexed trees from §{sec:edst-pair-tree-indices}. Every index gives a relative pair tree, and
every relative pair-tree projection occurs among their projections. Their bodies are closed. There are
only countably many indices, so there are only countably many represented sets, and hence only
countably many nonempty ones. Different indices may represent the same condition; neither equality
of the represented sets nor nonemptiness needs to be decidable.

Restrict $T_e$ by requiring its point prefix to be comparable with $s$ and its witness prefix to be
comparable with $t$. The prefix-restriction construction of §{sec:edst-relative-programs} has body
$K_e\cap(\cyl{s}\times\cyl{t})$, so its projection is exactly $W_{e,s,t}$. Intersect its projection
with $P$ by pairing witnesses. Cylinders themselves have relative pair-tree presentations, so the
same intersection construction handles $P\cap\cyl{s}$. All component programs keep the original
parameter. Nonemptiness is used only to regard the resulting set as a condition.
\end{proof}

This supplies precisely the refinements used in the next proof. Closure under arbitrary analytic
subsets of a condition is not required: those subsets might fail to have a presentation at the fixed
parameter. For finite powers of Baire space, repeat the coordinate-pairing construction of
§{sec:edst-coordinate-projections} to apply the same argument.

\begin{lemma*}[\termdefineas{analytic-condition fusion lemma}{Analytic-condition fusion}]
For each $d$ there is a countable family of downward-closed dense subsets of $\GHConditions{d}$ such that any
decreasing sequence meeting them has exactly one point in the intersection of its conditions. The family can be
chosen to include the requirements that the ordinary diameter be at most $2^{-n}$ for every $n$.
\end{lemma*}

\begin{proof}[Proof]
Identify a finite product of Baire spaces with Baire space. For every recursive closed
$K\IncludedIn X^d\times\BaireSpace$ and finite point and witness prefixes $s,t$, write
$K_{s,t}=K\cap(\cyl{s}\times\cyl{t})$ and include the dense requirement
$$
P\cap\pi_0(K_{s,t})=\emptyset
\quad\text{or}\quad
P\IncludedIn\pi_0(K_{s\concat(i),t\concat(j)})\text{ for some }i,j.
$$
It is dense because a nonempty intersection on the left has a point and a witness whose next digits can be fixed;
intersecting with the corresponding projection gives a stronger analytic condition. Include also the small-diameter
requirements, which are dense by intersecting with cylinders.

Let $\Sequence{P_n}{n\in\omega}$ meet these requirements. Call a set positive along the sequence when it contains some
$P_n$.
Fix $r$ and a recursive closed presentation $P_r=\pi_0(K)$. Its empty-prefix projection is positive. Whenever
$\pi_0(K_{s,t})$ is positive, a later encounter with the requirement for $K,s,t$ must take its second alternative.
We therefore extend both prefixes indefinitely. Their limits $\Pair{x}{y}$ belong to $K$, since $K$ is closed, so
$x\in P_r$. The small-diameter requirements force the same $x$ for every $r$: all positive point cylinders intersect
every sufficiently late $P_n$. Thus $x\in\bigcap_n P_n$, and diameter shrinking proves uniqueness. Notice that the
witness $y$ is constructed separately for every condition $P_r$; membership in a closure is not substituted for
membership in $P_r$.
\end{proof}

For a specified countable family of downward-closed dense sets, call a point generic when it belongs to a condition
from each set in the family. The same convention applies to pairs and rectangle conditions. We always include the
witness tests just constructed when obtaining points by fusion. Countable families of additional tests are listed
explicitly in the arguments that need them.

\begin{proposition*}[\termdefineas{generic point below an analytic condition}{Generic points below a condition}]
Fix a condition $A$ and a countable family $\mathcal F$ of downward-closed dense subsets of the order
below $A$. There is $x\in A$ such that, for every $D\in\mathcal F$, some $Q\in D$ contains $x$.
Here density below $A$ means that every condition contained in $A$ has a stronger condition in $D$.
\end{proposition*}

\begin{proof}[Proof]
Add the witness and shrinking requirements from the analytic-condition fusion lemma, restricting them
to the order below $A$. They remain dense there: refining a condition already below $A$ stays below it.
The enlarged family is countable. Enumerate its members and recursively refine the preceding condition
to meet the next member, starting below $A$. The sequence is decreasing; lower closure preserves every
requirement after it has been met. Witness fusion gives its unique common point $x$, which lies in
$A$ and in the chosen condition from each original dense set. The refinement choices need not be
computable. The conclusion is actual membership in the conditions, not just in their closures.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
countable modelによる古典forcingの別証明方針を付録へ明示的に参照し、ここで採用するlocal-truth
testsとの関係を説明する。generic extensionの構成をこの段落で主張していない。)
--> In the classical forcing presentation, one instead meets the dense sets in a countable model and invokes the truth
lemma and analytic/coanalytic absoluteness; see §{sec:appendix-forcing-background}. Here the countable local-truth
tests are constructed directly. The resulting arguments concern actual membership in the original sets and do not
require the construction of a generic extension.<!--
formalization: skip-end
-->

A useful consequence is that a $\GHConditions{1}$-generic point $x$ decides every lightface analytic set $A$:
its filter meets the dense family of conditions contained in $A$ or disjoint from $A$. Thus if $x\notin A$, some
analytic condition containing $x$ is disjoint from $A$. Also the filter is determined by its point: every analytic
condition containing that point belongs to the filter. Projection preserves genericity for
$\GHConditions{2}$, since restricting one coordinate to a stronger analytic set gives a stronger pair condition
whenever the restriction is nonempty.

\begin{proposition*}[\termdefineas{generic coordinates of an analytic pair condition}{Generic coordinates of a
pair condition}]
Let $P$ be a nonempty relative analytic set of coded pairs whose two coordinate projections lie in a
condition $A$. Given a countable family $\mathcal F$ of dense subsets of the condition order below $A$,
there is a pair in $P$ each of whose coordinates belongs to a condition from every member of
$\mathcal F$. The members of this family need not themselves be downward closed.
\end{proposition*}

\begin{proof}[Proof]
Let $f$ be either coordinate projection and let $D\in\mathcal F$. Below $P$, require a condition $Q$
whose image $f[Q]$ is contained in some $U\in D$. This requirement is downward closed. To see that it
is dense, start with any $Q\IncludedIn P$. Its image is a nonempty condition below $A$ by
§{sec:edst-coordinate-projections}. Choose $U\in D$ with $U\IncludedIn f[Q]$, and put
$$V=Q\cap f^{-1}(U).$$
The set $V$ is nonempty because every point of $U$ has a preimage in $Q$. Coordinatewise inverse images
and intersections give it a presentation at the same parameter. Thus it is a stronger condition and
$f[V]\IncludedIn U$, as required.

Lift every member of $\mathcal F$ in this way for both coordinates. The lifted family is countable,
lower and dense below $P$. The preceding proposition gives an actual point of $P$ meeting all these
lifted tests. Each test then supplies the required condition containing the corresponding coordinate.
In particular, any relation imposed by the original pair condition is retained; the construction does
not replace that condition by the product of its projections.
\end{proof}

### Recursive Borel codes from disjoint projections {#sec:edst-recursive-borel-completeness}

\begin{mathmeta}
  \vars{a,k}{Nat}
  \vars{u_*,w,w_*,v}{Seq(Nat)}
  \vars{x,p}{Name}
  \vars{b}{Nat}
\end{mathmeta}

We now supply a concrete well-founded bound for the rank-layer construction in §{sec:edst-borel-rank-layers}. Fix two
pair trees $T,S$
whose projections $A=\pi_0([T])$ and $B=\pi_0([S])$ are disjoint. Their membership tests are decidable
relative to the same $\varepsilon$. Retain the empty root in each section $T_x,S_x$.
For a word $w$, let $w_1,w_2$ denote its coordinatewise numerical projections, and write $w_{21},w_{22}$
for the projections of $w_2$. Define the rooted tree
$$J:=\{\emptySeq\}\cup\{w:\Pair{w_1}{w_{21}}\in T\text{ and }\Pair{w_1}{w_{22}}\in S\}.$$
Its three coordinates describe a common point and one witness on each side. Membership in $J$ is
again decidable relative to $\varepsilon$.

\begin{lemma*}[\termdefineas{joint-tree rank bound}{Joint-tree rank bound}]
The tree $J$ is well founded. For every $x\in A$, the section $S_x$ is well founded and its root rank
is at most the root rank of $J$.
\end{lemma*}

\begin{proof}[Proof]
An infinite branch through $J$ would give a point with witnesses in both $T$ and $S$, contradicting
disjointness. Adding the empty root does not create a branch: membership at every positive length
implies membership at length zero in the original pair trees by downward closure.
For $x\in A$, fix a witness $p$ with $\Pair{x}{p}\in[T]$. Map a word $v\in S_x$ to
$$\WordPair{\restrict{x}{\Length{v}}}{\WordPair{\restrict{p}{\Length{v}}}{v}}.$$
This word belongs to $J$, has length $\Length{v}$, and the map sends the root to the root and preserves
strict extension. The tree-rank comparison lemma proves the assertion. The witness $p$ is used only
in this rank comparison; the membership program for $J$ does not select such a witness.
\end{proof}

Use word codes as the nodes of a relation on $\NN$. Put $u_b:=\LambdaListDecode{b}$ and define
$$R(b,a)\quad\Longleftrightarrow\quad
u_b,u_a\in J,\quad u_a\prefixOf u_b,\quad \Length{u_a}<\Length{u_b}.$$
Codes of words outside $J$ are isolated. Thus $R$ is well founded, its root is zero, and its decision
program uses only word projections, prefix tests, lengths, and the two original membership programs.
For the section $S_x$, let $E_x(b,a)$ be the same strict-extension relation on its word codes.
The rank bound just proved shows that the layer $\RankLayer{0}{0}$ for these relations contains $A$.
It is disjoint from $B$, since a branch of $S_x$ gives an infinite descending chain from its root.

The edge relation has a uniform open code. Write
$$H(b,a,k)\quad\Longleftrightarrow\quad
u_a\prefixOf u_b,\quad \Length{u_a}<\Length{u_b},\quad \Length{u_k}=\Length{u_b},\quad\Pair{u_k}{u_b}\in S.$$
Then
$$\begin{aligned}
f_{b,a,k}&:=\begin{cases}\BorelLeafCode{k}&H(b,a,k),\\
                         \BorelEmptyCode&\neg H(b,a,k),\end{cases}\\
e_{b,a}&:=\BorelUnionCode{\Sequence{f_{b,a,k}}{k\in\omega}},\\
\BorelValue{e_{b,a}}&=\{x:E_x(b,a)\}.
\end{aligned}$$
Indeed, a cylinder selected by $H$ makes $u_b$ a node of $S_x$, and its prefix $u_a$ is then a node
as well. Conversely, an edge supplies the selected cylinder with word $\restrict{x}{\Length{u_b}}$.
The union and leaf label programs, together with the decision of $H$, compute $e_{b,a}(v)$ jointly in
$b,a,\LambdaListCode{v}$.
The explicit closed terms for this and the relation $R$ appear in §{sec:lambda-recursive-borel-separation}.

\begin{theorem*}[\termdefineas{recursive Borel separation}{Recursive Borel separation}]
If $A,B$ have pair-tree presentations decidable relative to $\varepsilon$ and $A\cap B=\emptyset$,
there is a valid Borel expression $c$ whose labels are computable relative to $\varepsilon$ and
$$A\IncludedIn\BorelValue{c}\IncludedIn B^{\complement}.$$
\end{theorem*}

\begin{proof}[Proof]
Take the relation $R$ of the joint tree and the edge expressions $e_{b,a}$ above. Apply the rank-layer
construction with both root indices zero and set $c=\RankLayerCode{0}{0}$. The relation is well founded
and the edge expressions are valid, so $c$ is valid. Its value is $\RankLayer{0}{0}$, which separates
the two projections by the joint-tree rank bound. The decision program for $R$ and the joint edge-label
program are total at $\varepsilon$. The rank-label program therefore computes every label of $c$ at
that same parameter. This constructs the bound and the label program directly from the pair trees;
no choice of an ordinal notation or of a branch is part of the computation.
\end{proof}

\begin{corollary*}[\termdefineas{recursive Borel-code completeness}{Recursive Borel-code completeness}]
A set of Baire reals is $\lDelta^1_1(\varepsilon)$ if and only if it is the value of a valid Borel
expression whose labels are computable relative to $\varepsilon$.
\end{corollary*}

\begin{proof}[Proof]
By the pair-tree normal form, the set and its complement have decidable pair-tree presentations at
$\varepsilon$. Apply recursive Borel separation to those two presentations. The separating value
contains the set and is contained in the complement of its complement, so it equals the set.
Conversely, Borel evaluation at a fixed parameter supplies decidable pair-tree presentations of the
value and its complement from any valid expression with a label program. Thus both are
$\lSigma^1_1(\varepsilon)$, as required.
\end{proof}

## Effective Refinements {#sec:effective-refinements}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
classicalとeffectiveな定理の違いを紹介する一般的な導入で、特定の追加定理や計算手続きを証明していない。)
-->
Classical theorems acquire sharper effective versions, expressible either as bounds on witnesses by recursive ordinals
or as uniform recursive transformations on indices.<!--
formalization: skip-end
-->

<!--
formalization: skip-begin (引用・背景説明・読書案内:
後続の短いカタログと計算章への読書案内。各数学的主張は対応する後続の命題・証明・本文で個別に監査する。)
-->
This subsection is a compact catalog of what changes when a classical theorem is asked to produce recursive data. The
point is not to reprove the whole subject, but to prepare the reader for the next computational chapters: effective open
sets, computable compactness, and realizers are the operational versions of the lightface classes introduced here.<!--
formalization: skip-end
-->

### Suslin–Kleene theorem {#sec:edst-suslin-kleene}

\begin{mathmeta}
  \vars{x}{Name}
  \vars{n}{Nat}
  \vars{j,k,m}{Nat}
\end{mathmeta}

\begin{theorem*}[\termdefineas{Kleene theorem}{Kleene}]
For subsets of $\omega$, one has $\lDelta^1_1=\HyperarithmeticalSets$.
For subsets of $\BaireSpace$, the corresponding statement is that the $\lDelta^1_1$ sets are exactly those
admitting recursive Borel codes.
\end{theorem*}

\begin{proof}[Proof]
For subsets of the natural numbers, §{sec:edst-hyperarithmetic-inclusion} proves
$\HyperarithmeticalSets\IncludedIn\lDelta^1_1$. We prove the reverse inclusion with one fixed iterated
jump for all numerical inputs. Let $B\IncludedIn\NN$ be $\lDelta^1_1$, and put
$$A:=\{x\in\BaireSpace:x(0)\in B\}.$$
Choose recursive pair trees $T,S$ whose projections are $A,A^{\complement}$. Form their rooted joint
tree $J$ as in §{sec:edst-recursive-borel-completeness}. Its Kleene--Brouwer order has a recursive
presentation $W=\Pair{D}{R}$; let $a\in D$ be the code of its empty root.

For $n\in\NN$, put $x_n(k)=n$ for every $k$ and let $S_n$ be the rooted section of $S$ at $x_n$.
If $n\in B$, choose a witness $p$ with $\Pair{x_n}{p}\in[T]$. The map
$$t\longmapsto\WordPair{\restrict{x_n}{\Length{t}}}{\WordPair{\restrict{p}{\Length{t}}}{t}}$$
sends $S_n$ into $J$ and preserves strict extension. Every strict extension precedes its prefix in the
Kleene--Brouwer order, so this map proves that $S_n$ is well founded and its root rank is at most
$\rho_W(a)$. The bound and its presentation do not depend on $n$ or on the chosen witness.
If $n\notin B$, then $x_n\in A^{\complement}$, so $S_n$ has an infinite branch.

Put all these sections into one numerical relation. If $u_j$ is the word with code $j$, define
$$\begin{aligned}
 E(\NatPair{m}{j},\NatPair{n}{k})\quad\Longleftrightarrow\quad
 &m=n,\quad u_j,u_k\in S_n,\\
 &u_k\preceq u_j,\quad \Length{u_k}<\Length{u_j}.
\end{aligned}$$
§{sec:lambda-projection-programs} constructs a single total lambda decider for this
relation. Its components do not interact. Coding a section therefore preserves well-foundedness below each node and
all bounded-rank predicates, even when other sections have infinite branches. Consequently
$$n\in B\quad\Longleftrightarrow\quad
 \NatPair{n}{0}\in Q_a,$$
where $Q_a$ consists of those nodes below which $E$ is well founded and whose rank is at most $\rho_W(a)$.

Apply the uniform rank-decision theorem in §{sec:edst-borel-rank-layers} to this fixed $W,E,a$ and
starting set $\emptyset$. It gives one program $P_{d(a)}$ that decides $Q_a$ from
$\chi_{(\IteratedJump{\emptyset}{g(a)})''}$. Precompose it with the closed numerical term
$$N:=\lambdaab{n}{\LambdaNumericPair\,n\,\ChurchNumeral{0}}.$$
The resulting program computes $\chi_B$. The input function is the characteristic function of the
iterated jump at $\KleeneSuccIter{g(a)}{2}\in\KleeneO$, fixed independently of $n$. Thus
$B\in\HyperarithmeticalSets$.

For sets of Baire reals, §{sec:edst-recursive-borel-completeness} gives both directions: the joint tree
supplies a well-founded bound, the section-edge programs and rank-label iteration compute a valid
Borel expression, and evaluation certificates give the converse. This constructs the labels of an
expression for a set of reals; it does not compute its membership from one fixed jump.
\end{proof}

The assertion for sets of reals relativizes to give the boldface Suslin theorem
$\bDelta^1_1=\text{Borel}$. A $\bDelta^1_1$ set belongs to $\lDelta^1_1(a)$ for some real parameter $a$.
Its relative recursive Borel code is in particular an ordinary countable Borel code, so the set is Borel.

### Effective Cantor–Bendixson {#sec:edst-effective-cb}

\begin{mathmeta}
  \vars{N,U,V,a,b,c,d,e,i,j,k,m,n,p,t,z}{Nat}
  \vars{s,u,v,u_*,v_*}{Seq(Nat)}
  \vars{I}{Set(Stage)}
  \vars{\xi,\eta,\zeta}{Elem(I)}
  \vars{D}{Set(Nat)}
  \vars{q,g,r,f,\nu,\upsilon,\delta}{Fun(Nat,Nat)}
  \vars{h}{Fun(Prod(Nat,Nat),Nat)}
\end{mathmeta}

\begin{proposition*}[\termdefineas{effective derivative step}{One effective derivative step}]
Let $T\IncludedIn\finseq{2}$ be a subtree whose membership is decidable at a fixed parameter
$\varepsilon$, and put $F:=\TreeBody{T}$. The tree
$$\ClosedTreeCode{\cbderivative{F}}$$
is pruned, has body $\cbderivative{F}$, and has a membership decider using four successive jumps of
$\varepsilon$. The input tree need not be pruned.
\end{proposition*}

\begin{proof}[Proof]
For a binary word $s$, compactness shows that $s\in\ClosedTreeCode{\cbderivative{F}}$ holds exactly when
$F\cap\cyl{s}$ is infinite.
Indeed, an accumulation point in the open cylinder forces infinitely many points of $F$ there:
otherwise a smaller neighborhood could exclude all the other finitely many points. Conversely,
an infinite subset of the compact set $F\cap\cyl{s}$ has an accumulation point in that set. This
point belongs to $\cbderivative{F}$. Since $F$ is closed, all its accumulation points lie in $F$,
so this agrees with the derivative defined in §{sec:cantor-bendixson}. The closed-set tree
representation then proves that $\ClosedTreeCode{\cbderivative{F}}$ is pruned and
$\TreeBody{\ClosedTreeCode{\cbderivative{F}}}=\cbderivative{F}$.

A word $u$ extends to a branch through $T$ exactly when
$$\forall n\in\NN\ \exists v\in\finseq{2}\quad
 \Length{v}=\Length{u}+n,\quad u\prefixOf v,\quad v\in T.$$
The forward implication uses prefixes of the branch. For the reverse implication, apply König's
lemma to the tree localized above $u$, keeping the ancestors of $u$ so that it is downward closed.
A finite bound on its height would contradict the displayed condition.

We now replace branches by finite tables. Decode $c=\NatPair{N}{U}$, where $U$ codes a list of
word codes, and let $u_i$ be its $i$th word. Let $v_i$ similarly come from the table code $V$.
A missing entry denotes the empty word. Define $R_T(s,m,c,n,V)$ by requiring all words used below
to be binary and, for $i,j<m$, requiring
$$\begin{gathered}
 \Length{u_i}=N,\quad s\prefixOf u_i,\quad
 \Length{v_i}=N+n,\quad u_i\prefixOf v_i,\quad v_i\in T,\\
 u_i=u_j\ \Longrightarrow\ i=j.
\end{gathered}$$
Then
$$s\in\ClosedTreeCode{\cbderivative{F}}\quad\Longleftrightarrow\quad
 \forall m\in\NN\ \exists c\in\NN\ \forall n\in\NN\ \exists V\in\NN\ R_T(s,m,c,n,V).$$

For the forward implication, choose $m$ distinct points of $F\cap\cyl{s}$. At a sufficiently large
common length $N\ge\Length{s}$, their prefixes are distinct. Use these prefixes for $U$, and their prefixes
of length $N+n$ for $V$. Conversely, fix $m$ and the corresponding $c$. The same candidates $u_i$
then have extensions at every depth, so König's lemma gives a branch through each. Their common
length and distinctness make these branches distinct. There are therefore at least $m$ points of
$F\cap\cyl{s}$ for every $m$, so this set is infinite. The order of the quantifiers matters: the
table $U$ is fixed before the depth $n$ is supplied.

The matrix $R_T$ is a finite test using list access, lengths, comparisons, prefix tests, and calls
to the decider for $T$. §{sec:lambda-cantor-derivative-programs} gives its closed lambda
construction. Apply the numerical-quantifier compiler of §{sec:lambda-relative-jump} to the
innermost existential quantifier, then the universal one, and repeat. These four steps give the
claimed membership decider. Empty tables cause no exception: their bounded products return one.
\end{proof}

\begin{corollary*}[\termdefineas{uniform derivative program}{Uniformity of the derivative program}]
For every closed tree-test program $P$, there is a closed program $Q$, fixed before any input
parameter is supplied, with the following property. For every parameter $\varepsilon$ and subtree
$T\IncludedIn\finseq{2}$, if $P$ decides membership in $T$ using $\varepsilon$, then $Q$ decides
membership in $\ClosedTreeCode{\cbderivative{\TreeBody{T}}}$ using four successive jumps of
$\varepsilon$. As in the preceding construction, the tree test rejects nonbinary word codes.
\end{corollary*}

\begin{proof}[Proof]
The finite matrix program in §{sec:lambda-cantor-derivative-programs} is built from the fixed
program $P$ by numerical reindexing, Boolean operations, and bounded products. Its syntax uses
neither $T$ nor $\varepsilon$. The four numerical-quantifier transformations also depend only on
the program being transformed. Their composition therefore gives one $Q$ that works for every
parameter and tree satisfying the hypothesis. The preceding proposition identifies its decided
predicate with membership in the derivative tree, including when the original tree is empty.
\end{proof}

\begin{proposition*}[\termdefineas{computable derivative indices}{Computable derivative indices}]
\begin{mathmeta}
  \define{CantorMatrixIndex}
\end{mathmeta}
There is a total function $\delta:\NN\to\NN$ computed by a closed numerical lambda term such that,
whenever $P_e$ decides membership in a subtree $T\IncludedIn\finseq{2}$ at $\varepsilon$,
$P_{\delta(e)}$ decides membership in $\ClosedTreeCode{\cbderivative{\TreeBody{T}}}$ at four successive
jumps of $\varepsilon$. The function $\delta$ is independent of $T$ and $\varepsilon$, and the input
tree test uses the same word-code convention as above.
\end{proposition*}

\begin{proof}[Proof]
Use the finite matrix construction with a membership oracle, obtaining one fixed closed term $M$.
Given $e$, replace that oracle by $P_e$: the resulting term is
$\lambdaab{o}{\lambdaab{z}{M\,(P_eo)\,z}}$.
The syntax-code constructors compute its index $\CantorMatrixIndex{e}$ from $e$, as detailed in
§{sec:lambda-cantor-derivative-programs}. Every query to the membership oracle is then answered
by the supplied tree decider, so this term decides the finite matrix at $\varepsilon$.
Compose this index map with the four numerical-quantifier index transformations. This gives a total
lambda-computable function $\delta$; correctness follows from the finite matrix criterion and the
quantifier transformations. The construction chooses $M$ once, before $e,T,\varepsilon$ are supplied.
\end{proof}

\begin{proposition*}[\termdefineas{closed-tree derivative recursion}{Closed-tree derivative recursion}]
Let $\prec$ well-order a set $I$, let $T\IncludedIn\finseq{2}$ be a subtree, and put $F:=\TreeBody{T}$.
Define, by well-founded recursion,
$$T_\xi:=T\cap\bigcap_{\eta\prec\xi}\ClosedTreeCode{\cbderivative{\TreeBody{T_\eta}}},
\qquad F_\xi:=\TreeBody{T_\xi}.$$
Every $T_\xi$ is a subtree, and
$$F_\xi=F\cap\bigcap_{\eta\prec\xi}\cbderivative{F_\eta}.$$
This equation determines the family uniquely. At the least element it gives $F_\xi=F$; at the successor
of $\eta$ it gives $F_\xi=\cbderivative{F_\eta}$; at a nonzero limit it gives
$$F_\xi=\bigcap_{\eta\prec\xi}F_\eta.$$
If $F_\xi=\cbderivative{F_\xi}$, then $F_\xi$ is the greatest perfect subset of $F$, and every later stage
has the same body. The trees themselves need not be pruned.
\end{proposition*}

\begin{proof}[Proof]
Intersections preserve downward closure. A sequence belongs to the body of an intersection of trees
exactly when all its prefixes belong to every tree, so taking bodies commutes with arbitrary
intersections. The one-step result identifies each derivative-tree body with the corresponding
derived set. This proves the displayed equation. If another family satisfies that equation,
well-founded induction identifies its predecessor sets and hence its set at the current stage.

All stage bodies are closed. Thus $\eta\prec\xi$ implies
$$F_\xi\IncludedIn\cbderivative{F_\eta}\IncludedIn F_\eta.$$
At a successor of $\eta$, the factor $\cbderivative{F_\eta}$ is contained in $F$ and in every earlier
derivative factor, by monotonicity of the derived-set operation. It therefore equals the whole
intersection. At a limit, every predecessor $\eta$ has a later predecessor $\zeta$. A point belonging to
all predecessor bodies belongs to $F_\zeta\IncludedIn\cbderivative{F_\eta}$ for each such $\eta$, proving
the reverse inclusion in the limit equation. Nonzero limits have a predecessor, whose body is
already contained in the original set. Empty predecessor families instead give the initial stage.

If $P\IncludedIn F$ is perfect, well-founded induction gives $P\IncludedIn F_\eta$ at every stage:
use $P=\cbderivative{P}$ and monotonicity to place it in each predecessor derivative.
If a stage equals its own derivative, it is closed and has no isolated points, hence is perfect.
It contains every perfect subset by the preceding induction and is therefore the perfect kernel.
At a later stage the decreasing property gives one inclusion, and preservation of this perfect
subset gives the other.
\end{proof}

\begin{lemma*}[\termdefineas{uniform guarded tree intersections}{Uniform guarded tree intersections}]
Fix a parameter $\varepsilon$. Suppose membership in a binary tree $T$ and a set $G\IncludedIn\NN$
is decidable at this parameter, and one program jointly decides $s\in S_b$ from $\NatPair{b}{\LambdaListCode{s}}$
for a family of binary trees. Then
$$K:=T\cap\bigcap_{b\in G}S_b$$
is a subtree with
$$\TreeBody{K}=\TreeBody{T}\cap\bigcap_{b\in G}\TreeBody{S_b},$$
and its membership is decidable at $\varepsilon'$. A single output program works for all parameters
for which the supplied input programs have the stated behavior.
\end{lemma*}

\begin{proof}[Proof]
The tree and body assertions follow from intersections. Numerically, membership is
$$s\in T\ \land\ \forall b\in\NN\ \bigl(b\in G\Longrightarrow s\in S_b\bigr).$$
Use the total matrix
$$s\in T\ \land\ \bigl(b\in G\Longrightarrow s\in S_b\bigr)$$
and apply the universal-quantifier compiler once. Repeating the initial-tree test under the
quantifier gives exactly the desired conjunction, since the numerical quantifier has a nonempty
domain. §{sec:lambda-cantor-derivative-programs} gives the closed term and its reductions.
\end{proof}

For transfinite computation, use $G=\{b\in D:bRa\}$ at stage $a$. The preceding lemma requires a
joint decider for the predecessor derivative trees. We now construct its program indices and
supply its lower inputs from a common iterated jump. No test for limit stages or choice of cofinal
sequences is needed.

\begin{theorem*}[\termdefineas{uniform Cantor--Bendixson stage decisions}{Uniform Cantor--Bendixson stage decisions}]
\begin{mathmeta}
  \define{CantorReaderIndex,LambdaTwoParameterIndex}
\end{mathmeta}
Fix a recursive well-order presentation $W=\Pair{D}{R}$ and a closed relative program $P$.
There are total numerical functions $g,r$, computed by closed lambda terms, with the following
property. For every starting set $A$ and binary subtree $T$, if $P$ decides membership in $T$
at $\chi_A$, then, for every $a\in D$, we have $g(a)\in\KleeneO$ and $P_{r(a)}$ decides membership
in the tree $T_a$ of the closed-tree derivative recursion at
$$\chi_{(\IteratedJump{A}{g(a)})'}.$$
All tree tests reject nonbinary word codes. The functions $g,r$ are fixed before $A,T$ are supplied
and are total even outside $D$; correctness of the generated stage programs is asserted on $D$.
\end{theorem*}

\begin{proof}[Proof]
Use the computed readers with five successive jumps and put
$$\varepsilon_a:=\chi_{\IteratedJump{A}{g(a)}}.$$
At this input, the reader with index $\CantorReaderIndex{a}$ supplies five jumps of $\varepsilon_b$ on row $b$
when $b\in D$ and $bRa$, and supplies $\chi_A$ otherwise. In particular, row $a$ supplies the
original input, since $R$ is irreflexive. Write $\delta$ for the derivative-index transformation
proved above. §{sec:lambda-cantor-derivative-programs} constructs one closed template $M$
which, given $\NatPair{k}{\NatPair{a}{\NatPair{\LambdaListCode{s}}{b}}}$, tests initial-tree membership using row $a$,
then tests the predecessor condition. Only for a genuine predecessor does it compute $P_k(b)$,
apply $\delta$ to that index, and run the resulting derivative program using row $b$.

Let $z$ be the syntax code of a fixed named representative of $M$, and write $\LambdaTwoParameterIndex{z}{k}{a}$ for the
syntax code of its two specializations. The uniform self-indexed universal-family construction in
§{sec:lambda-rank-decision-programs} computes the self-index $q(z)$ uniformly from $z$. Put
$$r(a):=\upsilon(\LambdaTwoParameterIndex{z}{q(z)}{a}).$$
The program $P_{q(z)}$ computes this function at every numerical stage. Both the self-index and the stage indices
are obtained from the supplied template code using only numerical syntax operations and the universal-quantifier
transformation. No stage program is executed. Thus the indices are available before their correctness is proved.

We prove correctness by well-founded induction on $a$. For a predecessor $b$, the induction
hypothesis gives the tree decider at $\varepsilon_b'$. The derivative compiler needs four more jumps,
so row $b$ supplies exactly its required input. The guarded template therefore decides
$$s\in T\ \land\ \bigl(b\in D\land bRa\Longrightarrow
 s\in\ClosedTreeCode{\cbderivative{\TreeBody{T_b}}}\bigr)$$
at $\varepsilon_a$. The universal-quantifier compiler decides its universal closure in $b$ at
$\varepsilon_a'$. By the tree recursion, this is precisely membership in $T_a$. If there are no
predecessors, the guarded part always returns one and the result is the initial-tree test.
Nonbinary word codes are rejected by that test at every stage.
\end{proof}

\begin{corollary*}[
\termdefineas{Cantor stage indices from decision programs}{Cantor stage indices from decision programs}]
\begin{mathmeta}
  \define{CantorNotationIndex,CantorSelfIndex,CantorStageIndex}
\end{mathmeta}
There are total computable maps $\CantorNotationIndex{d}{t}$, $\CantorSelfIndex{d}{t}{p}$, and
$\CantorStageIndex{d}{t}{p}{a}$ with the following properties.
Their values are indices for the ordinal-notation generator, the self-indexed stage family,
and its individual stage programs, respectively.
For every pair $d,t$, the program $P_{\CantorNotationIndex{d}{t}}$ computes a total numerical function $g_{d,t}$.
For every triple $d,t,p$, the program $P_{\CantorSelfIndex{d}{t}{p}}$ computes $a\mapsto \CantorStageIndex{d}{t}{p}{a}$.
If $d,t$ code closed numerical programs deciding the domain and relation of $W$, with bits one and zero,
and $p$ codes a closed relative tree program, the preceding theorem holds with
$$P=P_p,\qquad g(a)=g_{d,t}(a),\qquad r(a)=\CantorStageIndex{d}{t}{p}{a}.$$
Thus the same numerical generators work for all recursive well-order presentations, initial-tree programs,
starting sets, and trees satisfying those hypotheses. The maps remain total even when these hypotheses fail.
\end{corollary*}

\begin{proof}[Proof]
Take $\CantorNotationIndex{d}{t}$ and the joint reader-index map from the uniform reader construction.
§{sec:lambda-cantor-derivative-programs} gives the predecessor-test index $\kappa(d,t)$ and the index
$\iota(d,t)$ of the numerical function producing five-jump readers. Fix the derivative compiler once.
The stage-template generators from that section now give
$$\begin{aligned}
\CantorSelfIndex{d}{t}{p}&:=q_0\bigl(p,\kappa(d,t),\iota(d,t)\bigr),\\
\CantorStageIndex{d}{t}{p}{a}&:=r_0\bigl(p,\kappa(d,t),\iota(d,t),a\bigr).
\end{aligned}$$
Composition proves totality of these maps and the claimed computation by the self-indexed program.
Under the decision hypotheses, the generated predecessor test and reader-index program satisfy exactly the
hypotheses used in the preceding well-founded induction. The matrix compiler produces that same guarded
stage program and the self-indexed universal compiler gives the same one-jump closure. Apply the preceding
induction with these generated components. It proves the stage decision for every starting set and initial
tree, while preserving the original tree program and all numerical parameters.
\end{proof}

\begin{proposition*}[\termdefineas{Borel codes for tree differences}{Borel codes for tree differences}]
Suppose closed programs $P,Q$ decide membership in binary trees $T,S$ at the same parameter
$\varepsilon$. There are fixed constructions of closed programs computing valid Borel-expression
labels for $\TreeBody{T}$ and $\SetDifference{\TreeBody{T}}{\TreeBody{S}}$ at that same parameter.
No additional jump is needed for these label computations.
\end{proposition*}

\begin{proof}[Proof]
For this construction interpret leaf $n$ as the cylinder $U_n$ of the binary word coded by $n$;
if the decoded word is not binary, put $U_n=\emptyset$. In particular, $U_0=\CantorSpace$, since
zero codes the empty word. Define
$$\begin{aligned}
 e^T_n&:=\begin{cases}
 \BorelEmptyCode,&n\text{ codes a word in }T,\\
 \BorelLeafCode{n},&\text{otherwise},
 \end{cases}\\
 O_T&:=\BorelUnionCode{\Sequence{e^T_n}{n\in\omega}},\qquad
 C_T:=\BorelComplementCode{O_T},\\
 D_{T,S}&:=\BorelComplementCode{\BorelBinaryUnionCode{O_T}{C_S}}.
\end{aligned}$$
A point fails to belong to the body of a tree exactly when one of its finite prefixes is missing
from the tree. Hence
$$\BorelValue{O_T}=\SetDifference{\CantorSpace}{\TreeBody{T}},\qquad
 \BorelValue{C_T}=\TreeBody{T},\qquad
 \BorelValue{D_{T,S}}=\SetDifference{\TreeBody{T}}{\TreeBody{S}}.$$
Nonbinary codes contribute empty leaves and do not change the union. The constructors ensure
validity, even for an empty tree.

To compute a label of $e^T_n$, run the tree decider on $n$ and choose the corresponding empty or
leaf label. This is one joint program in the leaf index and address. Apply the union and complement
label programs of §{sec:edst-borel-constructors}. For the binary union, use the first expression at
child zero and the second at every positive child. Each computation makes only finitely many
calls to the supplied tree tests. §{sec:lambda-cantor-derivative-programs} displays the terms.
\end{proof}

For the stage family of the preceding theorem, suppose the initial tree is recursive and a stage
$a$ has stabilized. The program $P_{r(a)}$ decides $T_a$ at
$\chi_{(\IteratedJump{\emptyset}{g(a)})'}$. A pure numerical decider for the initial tree can be run
at the same parameter by ignoring its input function. The proposition therefore computes both
$C_{T_a}$ and $D_{T,T_a}$ at this parameter. The closed-tree recursion theorem identifies
$\TreeBody{T_a}$ as the greatest perfect subset of $\TreeBody{T}$, so these are respectively Borel
codes for the perfect kernel and the scattered part. Their label maps require no jump beyond the
one already used by the stage decider. This conclusion concerns a specified stage of a recursive
well-order presentation; obtaining that stage uniformly from a supplied ordinal notation is a
separate step.

\begin{proposition*}[\termdefineas{specified stage above a notation bound}{A specified stage above a notation bound}]
For each $a\in\KleeneO$, let $U_a$ be the tree of certified candidate-predecessor descents starting
at $a$, and let $W_a$ be its coded Kleene--Brouwer order. Its root has code $0$, and
$$\KleeneValue{a}\le\rho_{W_a}(0).$$
Membership in the domain of $W_a$ is decidable jointly in $a$ and the node code by a total numerical
program, and its comparison program is independent of $a$.
For any initial binary tree, the closed-tree derivative recursion at the root of $W_a$ has the
same body as any stable stage whose ordinal position is at most $\KleeneValue{a}$.
\end{proposition*}

\begin{proof}[Proof]
§{sec:lambda-certified-descent} gives the finite certificate test and the joint domain
program. It tests only finitely many certificates on each input, even when the starting number
is not a valid notation. Validity is used to prove that the descent tree is well founded, not to
run its domain test. The empty word always belongs to the tree and has code zero.

Every candidate predecessor has a certificate. The descent-rank comparison therefore bounds
$\KleeneValue{a}$ by the strict-extension rank of the root. Every proper extension precedes its
prefix in Kleene--Brouwer order. Induction on strict extension bounds each node's rank by its
position in that order, giving the displayed inequality at the root.

The stage tree depends only on ordinal position. To see this, compare the recursion on a well
order with the same recursion indexed by ordinals. Induct on the position of the current element.
Its predecessors occur at exactly the smaller ordinal positions, each once. The induction
hypothesis identifies the earlier stage trees, so the derivative factors and their intersection
are identical. In particular the bodies agree. If a stage at position $\alpha$ is stable, the
persistence result gives the same body at every position at least $\alpha$. Apply this with
$$\alpha\le\KleeneValue{a}\le\rho_{W_a}(0).$$
This selects the root stage without searching for the first stable stage.
\end{proof}

\begin{corollary*}[\termdefineas{root stage indices from ordinal notations}{Root stage indices from ordinal notations}]
\begin{mathmeta}
  \define{DescentDomainIndex}
\end{mathmeta}
There are total computable maps $a\mapsto \nu(a)$ and $\Pair{a}{p}\mapsto h(a,p)$ with the following
property. If $a\in\KleeneO$, then $\nu(a)\in\KleeneO$. If $p$ codes a closed program deciding a
binary tree $T$ at $\chi_A$, then $P_{h(a,p)}$ decides the stage tree at the root of $W_a$ at
$$\chi_{(\IteratedJump{A}{\nu(a)})'}.$$
The same maps work for every starting set and tree. If a stage is stable at a position at most
$\KleeneValue{a}$, the computed tree has that stable body. Both numerical maps are total on all
inputs, without testing whether the supplied number is a valid notation or the supplied tree
program has the required behavior.
\end{corollary*}

\begin{proof}[Proof]
Use the total map $\DescentDomainIndex{a}$ and the fixed comparison index $t$ from §{sec:lambda-certified-descent}.
Let $\CantorNotationIndex{d}{t}$ and $\CantorStageIndex{d}{t}{p}{a}$ be the preceding stage generators, and let
$P_{\CantorNotationIndex{d}{t}}$ compute
$g_{d,t}$. Define
$$\begin{aligned}
\nu(a)&:=g_{\DescentDomainIndex{a},t}(0),\\
h(a,p)&:=\CantorStageIndex{\DescentDomainIndex{a}}{t}{p}{0}.
\end{aligned}$$
The second map is a composition of total numerical maps. For the first, compute the index
$\CantorNotationIndex{\DescentDomainIndex{a}}{t}$ and run the universal numerical evaluator at input $0$. This
terminates for every
$a$, because the stage generator produces a total numerical program for every pair of input
indices. Thus both maps are total before any validity assumption is imposed. For a valid notation,
the domain and comparison programs present $W_a$. Apply the stage-decision theorem to this
presentation at its root, whose node code is $0$, and use the preceding stable-stage comparison.
\end{proof}

\begin{corollary*}[\termdefineas{uniform codes at a notation bound}{Uniform codes at a notation bound}]
\begin{mathmeta}
  \define{TreeDifferenceLabelIndex,PureTreeProgramIndex,CantorKernelLabelIndex,CantorScatteredLabelIndex}
\end{mathmeta}
There are total computable maps $a\mapsto \nu(a)$, $\Pair{a}{p}\mapsto \CantorKernelLabelIndex{a}{p}$, and
$\Pair{a}{p}\mapsto \CantorScatteredLabelIndex{a}{p}$
with the following property. For $a\in\KleeneO$, we have $\nu(a)\in\KleeneO$. Suppose $p$ codes a
closed program that decides a recursive binary tree $T$ at the constant-zero parameter, and the
derivative sequence stabilizes at a position at most $\KleeneValue{a}$. Then the programs
$P_{\CantorKernelLabelIndex{a}{p}}$ and $P_{\CantorScatteredLabelIndex{a}{p}}$ compute valid Borel codes for the
perfect kernel and scattered part
of $\TreeBody{T}$, respectively, at
$$\chi_{(\IteratedJump{\emptyset}{\nu(a)})'}.$$
The numerical generators are total on all inputs; their correctness has the stated hypotheses.
\end{corollary*}

\begin{proof}[Proof]
Take the total maps $\nu(a),h(a,p)$ from the root-stage corollary and the label-index constructions
from §{sec:lambda-cantor-derivative-programs}. Write $f(e)$ for the tree-body label index,
$\TreeDifferenceLabelIndex{e}{j}$ for the tree-difference label index, and
$\PureTreeProgramIndex{p}$ for the index of the initial-tree program with its input function ignored. Put
$$\begin{aligned}
\CantorKernelLabelIndex{a}{p}&:=f\bigl(h(a,p)\bigr),\\
\CantorScatteredLabelIndex{a}{p}&:=\TreeDifferenceLabelIndex{\PureTreeProgramIndex{p}}{h(a,p)}.
\end{aligned}$$
Composition proves totality. Under the hypotheses, the root-stage program decides a tree whose
body is the stable body. The closed-tree recursion theorem identifies it as the greatest perfect
subset of the initial body. The first label compiler gives the Borel code of this tree body.
The program with index $\PureTreeProgramIndex{p}$ decides the initial tree at the same parameter, so the second label
compiler gives the difference between the initial body and that perfect kernel. Both label maps
use exactly the input function used by the root-stage decider.
\end{proof}

In particular, fixing a valid notation and a closed initial-tree program fixes the upper notation
and both label programs before the recursive tree is supplied. Choose a closed named representative
of that initial program once and evaluate the numerical maps at the fixed notation and syntax code.

\begin{theorem*}[\termdefineas{bounded effective Cantor--Bendixson theorem}{Bounded effective Cantor--Bendixson}]
Let $F=[T]\IncludedIn\CantorSpace$ be a $\lPi^0_1$ closed set given by a recursive binary tree $T$. If the
Cantor--Bendixson derivative sequence of $F$ stabilizes below a recursive ordinal
$\alpha<\churchKleeneOrd$, then the \termuse{perfect kernel} has a hyperarithmetic closed-tree code and the
\termuse{scattered part} has a hyperarithmetic Borel code, uniformly from $T$ and a notation for $\alpha$.
\end{theorem*}

\begin{proof}[Proof]
Let $a$ be the supplied notation and $p$ the index of the initial-tree decider. The root-stage
corollary computes $\nu(a)$ and $h(a,p)$; the tree decided by $P_{h(a,p)}$ has the stable body,
hence is a closed-tree code for the perfect kernel. The preceding corollary computes $\CantorKernelLabelIndex{a}{p}$
and $\CantorScatteredLabelIndex{a}{p}$ for the two Borel label maps. All three generated programs use the same parameter
$\chi_{(\IteratedJump{\emptyset}{\nu(a)})'}$, which is hyperarithmetic because $\nu(a)\in\KleeneO$.
No search for the first stable stage is used. The ordinal level of the parameter need not be
$\alpha+1$.
\end{proof}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
jump-by-stageのcompact/binaryかつrecursive-bound付きの適用範囲はrecursive_cantor_stage
_decidersに接続済み。残りは前章の古典分解定理への参照と、一般Baire空間へ同じjump
accountingを拡張してはならないという文脈上の注意。具体的な非hyperarithmetic反例や新しい導出をこの段落で提示せず、
局所証明として扱わない。)
-->
The classical theorem of §{sec:cantor-bendixson} decomposes $F$ into a perfect kernel plus a countable scattered part.
<!--
formalization: skip-end
-->
Effectively, the safe jump-by-stage conclusion requires both a recursive ordinal bound and compact finite branching.
<!--
formalization: skip-begin (引用・背景説明・読書案内:
jump-by-stageのcompact/binaryかつrecursive-bound付きの適用範囲はrecursive_cantor_stage
_decidersに接続済み。残りは前章の古典分解定理への参照と、一般Baire空間へ同じjump
accountingを拡張してはならないという文脈上の注意。具体的な非hyperarithmetic反例や新しい導出をこの段落で提示せず、
局所証明として扱わない。)
--> For a general $\lPi^0_1$ subset of $\BaireSpace$, even one derivative step involves a $\Sigma^1_1$ branch-existence
test, so the preceding hyperarithmetic accounting does not apply.<!--
formalization: skip-end
-->

### Effective Lusin–Suslin {#sec:edst-effective-ls}

\begin{mathmeta}
  \vars{e,i,j,n,p}{Nat}
  \vars{s,t,s_*,w_*}{Seq(Nat)}
  \vars{x,y}{Name}
  \vars{m,r}{Nat}
\end{mathmeta}

A recursive injective continuous map $f:F\to\BaireSpace$ on a $\lPi^0_1$ closed set
$F\IncludedIn\BaireSpace$ has $\lDelta^1_1$ image and a $\lDelta^1_1$ inverse. The uniform version
requires image and inverse indices computed from the supplied map and domain indices.
The closed-graph construction below isolates the prefix tests and image formula needed for this
proof. In a pair-tree presentation of the graph, put the output in the first coordinate and its
possible preimage in the second.

\begin{proposition*}[\termdefineas{uniform closed-graph indices}{Uniform closed-graph indices}]
Fix $\varepsilon$. There is a total computable map $\Pair{e}{p}\mapsto\gamma(e,p)$ with the following
property. Suppose $P_p$ decides a prefix tree $T$ at $\varepsilon$, put $F=[T]$, and let
$f:F\to\BaireSpace$. Suppose that, for every $x\in F$ and $n\in\NN$, the program $P_e$ with input
function $\NamePair{\varepsilon}{x}$ returns $f(x)(n)$ on numerical input $n$. Then
$$[T_{\gamma(e,p)}]=\{\Pair{f(x)}{x}:x\in F\}.$$
The index map and the finite-node tests are total for all input indices. Correctness of the graph
presentation requires termination of the map program only on its stated domain.
\end{proposition*}

\begin{proof}[Proof]
First compute the index $\delta(p)$ of the closed pair-node program
$$\lambdaab{o}{\lambdaab{z}{P_p o(\LambdaNumericProjection{2}z)}}.$$
The corresponding indexed tree has body $\BaireSpace\times F$: a branch survives exactly when
all prefixes of its second coordinate pass the domain test. Syntax substitution computes this
index without executing the domain program. For the graph condition, use rows
$i=\NatPair{n}{\NatPair{m}{r}}$. On a prefix pair of length $i+1$, test whether a computation
certificate within bound $r$ returns $m$ at coordinate $n$; if so, require that the output prefix
has that digit. The stage-address bound of §{sec:lambda-stage-address-bound} makes the finite
input prefix sufficient. §{sec:lambda-closed-graph-indices} gives a single row tester
with the map index supplied as numerical data. Conjoin the domain-tree test with all graph rows
whose prescribed prefixes fit, and apply the finite-check-tree construction. This gives a jointly
decidable family, so numerical specialization gives $\gamma(e,p)$.

For correctness, the domain tests force $x\in F$. At such a point every output coordinate has a
finite computation certificate. Thus the graph rows force $y(n)=f(x)(n)$ for every $n$.
Conversely, on the actual graph every certified output has the correct value by uniqueness of
numerical outputs, so all tests hold. The tree has exactly the output and preimage coordinates.
If the map is injective, each output section therefore contains at most one branch.
\end{proof}

\begin{proposition*}[\termdefineas{uniform separated preimage prefix tests}{Uniform separated preimage prefix tests}]
Fix $\varepsilon$ and use the total indexed pair trees $T_e$ of §{sec:edst-pair-tree-indices}.
There are total computable maps $c(e,j),d(e,j)$ with the following property. Suppose
$$ \Pair{y}{x}\in[T_e],\ \Pair{y}{x'}\in[T_e]\quad\Longrightarrow\quad x=x'.$$
For a finite word $s$, put
$$\begin{aligned}
C_s&:=\pi_0\bigl([T_{c(e,\LambdaListCode{s})}]\bigr),\\
C'_s&:=\pi_0\bigl([T_{d(e,\LambdaListCode{s})}]\bigr).
\end{aligned}$$
Then $C_s=(C'_s)^{\complement}$, and on the graph
$$ \Pair{y}{x}\in[T_e]\quad\Longrightarrow\quad
  \bigl(y\in C_s\ \Longleftrightarrow\ x\in\cyl{s}\bigr).$$
Thus the prefix tests and their complements have uniform analytic presentations at the original
parameter. Generating their indices does not test uniqueness of the sections.
\end{proposition*}

\begin{proof}[Proof]
Let $A_s^+$ and $A_s^-$ be the projections obtained by requiring the second coordinate to belong
to $\cyl{s}$ and its complement, respectively. The finite tests of
§{sec:lambda-closed-graph-indices} give both presentations jointly in the tree index and word code.
Uniqueness makes these projections disjoint: two preimages of the same output must coincide and
cannot satisfy opposite prefix tests. Apply uniform separation to obtain
$$A_s^+\IncludedIn C_s\IncludedIn(A_s^-)^{\complement},\qquad C_s=(C'_s)^{\complement}.$$
On a graph pair the second coordinate either belongs to the cylinder, placing the output in the
first projection, or fails to belong, placing it in the second. This proves the displayed equivalence.
The two numerical index maps are compositions of the slice generators and the separation generators.
All these generators are total before the uniqueness assumption is imposed.
\end{proof}

\begin{corollary*}[
\termdefineas{preimage prefix indices from map and domain indices}{Preimage prefix indices from map and domain indices}]
For an injective map satisfying the hypotheses of the closed-graph proposition, the prefix-test indices
are computed directly from its map and domain indices by
$$\begin{aligned}
c_*(e,p,j)&:=c\bigl(\gamma(e,p),j\bigr),\\
d_*(e,p,j)&:=d\bigl(\gamma(e,p),j\bigr).
\end{aligned}$$
Their projections are complementary. For every domain point, the first test holds at its image
exactly when that point belongs to the cylinder with word code $j$.
\end{corollary*}

\begin{proof}[Proof]
The graph compiler preserves the graph itself, so injectivity gives the unique-section hypothesis
of the prefix-test proposition. Compose its two total numerical maps with the graph-index map.
The graph identity identifies the projection with the range and gives the asserted prefix equivalence.
\end{proof}

The sets $C_s$ may overlap away from the image. Make their tests disjoint at each length and
compatible under restriction. Write $w_j$ for the unique word with $\LambdaListCode{w_j}=j$. Define
$$\begin{aligned}
B_s&:=\SetDifference{C_s}{\bigcup_{\substack{j<\LambdaListCode{s}\\\Length{w_j}=\Length{s}}}C_{w_j}},\\
H_s&:=\bigcap_{0\le n\le\Length{s}}B_{\restrict{s}{n}}.
\end{aligned}$$
Only finitely many tests occur in each expression. At a fixed length the sets $B_s$ are disjoint,
and $t\extendsPrefix s$ implies $H_t\IncludedIn H_s$. On the graph, an output belongs to $H_s$
exactly when its preimage belongs to $\cyl{s}$.

\begin{lemma*}[\termdefineas{closed graph image by coherent prefix tests}{Closed graph image by coherent prefix tests}]
For the preceding prefix tests,
$$\pi_0([T_e])=
 \bigcap_{n\in\NN}\ \bigcup_{\Length{s}=n}
 \{y:y\in H_s\land \Pair{\restrict{y}{n}}{s}\in T_e\}.$$
No choice of shrinking open neighborhoods is needed for this image formula.
\end{lemma*}

\begin{proof}[Proof]
If $\Pair{y}{x}\in[T_e]$, choose $s=\restrict{x}{n}$ at every length. The graph-prefix equivalence gives
$y\in H_s$, and the branch condition gives membership of the finite pair.
Conversely, choose a word $s_n$ at every length on the right-hand side. For $n\le m$, the word
$\restrict{s_m}{n}$ has length $n$, and the output belongs to its coherent test. Disjointness at that
length forces $s_n=\restrict{s_m}{n}$. These compatible words define a sequence $x$ with
$\restrict{x}{n}=s_n$ for all $n$. Every finite pair belongs to the tree, so $\Pair{y}{x}\in[T_e]$.
The argument includes the empty-graph case: satisfying the right-hand side would produce a branch.
\end{proof}

The inverse prefix sets satisfy the exact identity
$$\{y:\exists x\ (\Pair{y}{x}\in[T_e]\land x\in\cyl{s})\}
   =\pi_0([T_e])\cap C_s.$$
For a graph of an injection, the left-hand side is the inverse image of the domain cylinder under
the inverse map. The separated test supplies its restriction to the image; the image formula
supplies the additional condition that the output actually has a preimage.

\begin{theorem*}[\termdefineas{uniform effective Lusin--Suslin theorem}{Uniform effective Lusin--Suslin}]
Fix $\varepsilon$. There are total computable index maps $M_+,M_-,I_+,I_-$ with the following property.
Suppose the domain program $P_p$ decides a prefix tree, its body is $F$, and the map program $P_e$
computes an injective map $f:F\to\BaireSpace$ as in the closed-graph proposition. Put
$$A:=f[F],\qquad A_s:=\{f(x):x\in F\cap\cyl{s}\}$$
Writing $j=\LambdaListCode{s}$, the generated pair trees satisfy
$$\begin{aligned}
\pi_0([T_{M_+(\NatPair{e}{p})}])&=A,&
\pi_0([T_{M_-(\NatPair{e}{p})}])&=A^{\complement},\\
\pi_0([T_{I_+(\NatPair{\NatPair{e}{p}}{j})}])&=A_s,&
\pi_0([T_{I_-(\NatPair{\NatPair{e}{p}}{j})}])&=A_s^{\complement}.
\end{aligned}$$
Thus the image and the inverse images of cylinders under the inverse map are uniformly
$\lDelta^1_1(\varepsilon)$. The generators are total on all numerical inputs; their correctness
requires the stated domain and map hypotheses. The map program need terminate only on its domain.
\end{theorem*}

\begin{proof}[Proof]
First generate the graph index and its separated prefix tests. In the image formula, each finite
condition that a prefix pair belongs to the graph tree is decidable from that prefix. It and its
negation therefore have uniform tree presentations, by the finite-prefix construction of
§{sec:lambda-lusin-image-programs}. Build the coherent tests and their negative counterparts together:
complement exchanges the two presentations, intersection uses intersection on the positive side and
union on the negative side, and union reverses these roles. Apply the parameter-preserving countable
operations of §{sec:lambda-projection-programs} to the word codes and then to the
lengths. The image identity proves that the positive presentation projects to the image; De Morgan's
identities prove that the negative presentation projects to its complement. Intersect the image with
each separated prefix test to obtain the inverse prefix sets, and take the union of the two negative
presentations for their complements. Every stage retains the graph index and the relevant word and
length codes as numerical inputs. Specialize the resulting fixed joint finite-node programs and compose
with the graph-index generator. This gives all four total index maps without testing injectivity,
nonemptiness, or termination of the supplied map program.
\end{proof}

### Spector–Gandy theorem {#sec:edst-spector-gandy}

<!-- formalization: skip-begin (Spector--Gandy and admissible-set theory are cited external inputs) -->
The constructible hierarchy is defined by transfinite recursion: $L_0:=\emptyset$, $L_{\alpha+1}$ consists of the
first-order definable subsets of $L_\alpha$ with parameters from $L_\alpha$, and
$L_\lambda:=\bigcup_{\alpha<\lambda}L_\alpha$ at limits. The level $L_{\churchKleeneOrd}$ is the smallest
\termdefine{admissible set} containing $\omega$. Here an admissible set is a transitive set modeling Kripke--Platek set
theory, so it supports the effective transfinite recursions needed below.

The deepest connection between effective DST and admissible set theory is:

\begin{theorem*}[\termdefineas{Spector--Gandy theorem}{Spector--Gandy}]
A set $A\IncludedIn\omega$ is $\lPi^1_1$ iff there is a $\Sigma_1$ formula $\vartheta$ such that
$$
n\in A
\quad\Longleftrightarrow\quad
L_{\churchKleeneOrd}\models\vartheta(n).
$$

\end{theorem*}

For subsets of $\BaireSpace$, the correct analogue is relativized point by point. If $\alpha_x$ denotes the
Church--Kleene ordinal relative to $x$, the admissible structure is $L_{\alpha_x}[x]$, not
$L_{\churchKleeneOrd}$ with an arbitrary real $x$ as a parameter. The theorem connects effective DST to the admissible
set theory developed by Barwise, Kripke, and Platek; see
[@MansfieldWeitkamp1985, Ch. 5] for a recursion-theoretic exposition.
<!-- formalization: skip-end -->
