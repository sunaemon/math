# Standard Borel Classification and Spaces of Closed Sets {#sec:standard-borel-classification-closed-sets}

<!-- formalization: skip-begin (chapter prerequisites and learning goals) -->

The definition and concrete Cantor--Baire isomorphism in §{sec:standard-borel-spaces} can be read without this
chapter. Here the Lusin--Suslin theorem in §{sec:lusin-souslin-theorem} supplies Borel images and inverses,
completing the general classification. Perfect sets come from §{sec:perfect-set-theorem}; the Effros--Borel
construction additionally uses the Hilbert-cube embedding and Polish refinement in
§{sec:polish-embeddings-refinements}. First follow how two Borel embeddings give an isomorphism, then how hit
sets turn closed subsets into measurable data. The proof for spaces of closed sets is needed when closed sets themselves
become parameters, rather than for the first examples of Borel coding.

<!-- formalization: skip-end -->

## Kuratowski's Isomorphism Theorem {#sec:kuratowski-isomorphism}

\begin{mathmeta}
  \vars{a}{Name}
  \vars{n}{Nat}
\end{mathmeta}
\index{Kuratowski's isomorphism theorem}

\begin{theorem*}[\termdefine{Kuratowski's isomorphism theorem}] Any two uncountable Polish spaces are
Borel-isomorphic; in particular, the Borel $\sigma$-algebra of any uncountable Polish space is isomorphic to that of
$\R$.
\end{theorem*}

\begin{proof}[Proof] It suffices to prove every uncountable Polish space $X$ is Borel-isomorphic to the Cantor space
$\CantorSpace$. The argument abstracts the Cantor--Baire construction in
§{sec:cantor-baire-borel-isomorphism}. There, one large Borel piece was matched by
a concrete homeomorphism and the countable leftovers were patched by hand. For an arbitrary uncountable Polish space the
pieces need not be so explicit, but two Borel embeddings give the same structure, and Borel Schröder--Bernstein performs
the bookkeeping.

(i) \emph{Code points of $X$ by Cantor reals.} Fix a countable base $\IndexedFamily{U_n}{n\in\NN}$ for $X$ and define
$$
\varphi:X\to\CantorSpace,
\qquad
\varphi(x)_n=\mathbf{1}[x\in U_n].
$$
For each $n\in\NN$,
$$\varphi^{-1}(\{a\in\CantorSpace:a_n=1\})=U_n.$$
Thus $\varphi$ is \termuseas{Borel-measurable map}{Borel measurable}, since the coordinate cylinders generate the
Borel $\sigma$-algebra of $\CantorSpace$. If $x\ne y$, choose a basic open set with
$x\in U_n\IncludedIn\SetDifference{X}{\{y\}}$. Then $\varphi(x)_n=1$ and $\varphi(y)_n=0$, proving injectivity.
By the Lusin--Suslin theorem of §{sec:lusin-souslin-theorem}, $\varphi(A)$ is Borel in $\CantorSpace$ for every
Borel set $A\IncludedIn X$. In particular, $\varphi(X)$ is Borel, and the inverse from this image to $X$ is Borel.

(ii) \emph{Find a Cantor copy inside $X$.} Apply the
\termuseas{Cantor--Bendixson theorem}{Cantor–Bendixson theorem} to $X$ as a closed subset of itself. The
\termuse{scattered part} is countable, so the \termuse{perfect kernel} is nonempty because $X$ is uncountable. By
\termuseas{perfect set theorem}{the perfect set theorem} in §{sec:perfect-set-theorem}, this nonempty perfect Polish
subspace contains a homeomorphic copy $P$ of $\CantorSpace$. Since $P$ is compact and $X$ is Hausdorff, $P$ is closed in
$X$, hence Borel. The homeomorphism $\psi:\CantorSpace\to P\IncludedIn X$ is therefore a Borel injection with Borel
image.

Thus we have Borel injections
$$
X \overset{\varphi}{\longrightarrow} \CantorSpace,
\qquad
\CantorSpace \overset{\psi}{\longrightarrow} X
$$
with Borel images. The Borel Schröder--Bernstein theorem below then patches the parts not already matched by these
embeddings, producing a Borel bijection $X\to\CantorSpace$ with Borel inverse. This is the abstract version of the
explicit countable-leftover patch in the Cantor--Baire example.
\end{proof}

## Borel Schröder–Bernstein {#sec:borel-schroder-bernstein}

\begin{mathmeta}
  \vars{p}{Nat}
\end{mathmeta}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
Borel版Cantor–Bernsteinの導入と、先行章のLusin–Suslinをブラックボックスとして使う旨の説明。
具体的な構成・証明は直後の定理と証明で別に対応しており、ここで追加の局所的証明を述べていない。)
-->
The classical Cantor–Bernstein construction lifts to the Borel category, with one nontrivial input: the Borel image of a
Borel set under a Borel injection is Borel. This is the Lusin–Suslin theorem of §{sec:lusin-souslin-theorem}; we use it
as a black box here, and the result is sometimes stated as a corollary of Lusin–Suslin.<!--
formalization: skip-end
-->

\begin{theorem*}[\termdefineas{Borel Schröder--Bernstein theorem}{Borel Schröder–Bernstein}] Let $X$ and $Y$ be Polish
spaces, and let $f : X \to Y$ and $g : Y \to X$ be Borel injections with Borel images. Then there exists a Borel
bijection $h : X \to Y$ whose inverse is also Borel.

\end{theorem*}

\begin{proof}[Proof] Define recursively
$$X_0 := \SetDifference{X}{g(Y)}, \qquad X_{n+1} := (g \circ f)(X_n), \qquad X_\infty := \bigcup_{n \in \omega} X_n.$$
Each $X_n$ is Borel: $X_0$ because $g(Y)$ is Borel by hypothesis; and inductively $X_{n+1}$ is the image of the Borel
set $X_n$ under the Borel injection $g \circ f$, hence Borel by Lusin–Suslin. Therefore $X_\infty$ is Borel, and so is
$\SetDifference{X}{X_\infty}$. By construction
\begin{equation*}
(g \circ f)(X_\infty) \;=\; \bigcup_{n \ge 1} X_n \;=\; \SetDifference{X_\infty}{X_0}. \tag{$\ast$}
\end{equation*}

Define $h : X \to Y$ piecewise:
$$h(x) =
\begin{cases}
f(x) & x \in X_\infty, \\[2pt]
g^{-1}(x) & x \in \SetDifference{X}{X_\infty}.
\end{cases}$$
This is well-defined: $\SetDifference{X}{X_\infty} \IncludedIn \SetDifference{X}{X_0} = g(Y)$, so $g^{-1}(x)$ exists,
and $g$ is
injective. Lusin–Suslin applied to $g$ shows that $g^{-1} : g(Y) \to Y$ is Borel; the restrictions $f|_{X_\infty}$ and
$g^{-1}|_{\SetDifference{X}{X_\infty}}$ are Borel as restrictions of Borel maps to Borel sets. Hence $h$ is Borel.

\emph{Injectivity.} Suppose $h(x_1) = h(x_2)$. The cases $x_1, x_2 \in X_\infty$ and $x_1, x_2 \in
\SetDifference{X}{X_\infty}$
reduce to injectivity of $f$ and $g^{-1}$ respectively. The mixed case has $x_1 \in X_\infty$, $x_2 \in
\SetDifference{X}{X_\infty}$, with $f(x_1) = g^{-1}(x_2)$, hence $x_2 = (g \circ f)(x_1) \in
\SetDifference{X_\infty}{X_0}$ by $(\ast)$ —
contradicting $x_2 \notin X_\infty$.

\emph{Surjectivity.} Let $y \in Y$. If $g(y) \in X_\infty$, then $g(y) \in g(Y)$ rules out $g(y) \in X_0$, so $g(y) \in
X_n$ for some $n \ge 1$, i.e. $g(y) = (g \circ f)(x)$ for some $x \in X_{n-1} \IncludedIn X_\infty$; injectivity of $g$
gives $y = f(x) = h(x)$. Otherwise $g(y) \in \SetDifference{X}{X_\infty}$, and $h(g(y)) = g^{-1}(g(y)) = y$.

\emph{Borel inverse.} The bijectivity argument also identifies the inverse: $h^{-1}(y) = f^{-1}(y)$ when $y \in
f(X_\infty)$, and $h^{-1}(y) = g(y)$ otherwise. Lusin–Suslin gives both that $f(X_\infty)$ is Borel and that $f^{-1} :
f(X_\infty) \to X_\infty$ is Borel; the second branch is the restriction of the Borel map $g$. Hence $h^{-1}$ is Borel.
\end{proof}

<!-- formalization: skip (expository discussion of why the cited Lusin--Suslin input is essential) -->
The Lusin–Suslin dependence is essential: this is not a purely set-theoretic statement strengthened by a measurability
adjective. Lusin–Suslin is what makes images of Borel sets under injective Borel maps Borel, and it also gives the Borel
inverse on those images.

## Classification of Standard Borel Spaces {#sec:standard-borel-classification}

\begin{mathmeta}
  \vars{X}{Set}
\end{mathmeta}

Kuratowski's theorem and the countable-cardinality cases together yield a complete classification of the measurable
spaces that arise from Polish topologies.



\begin{theorem*}[\termdefineas{standard Borel space classification theorem}{Classification of standard Borel spaces}] Up
to Borel isomorphism, the standard Borel spaces are exactly:

\begin{itemize}
\item for each $0 \le n < \omega$, the finite discrete space $\Pair{n}{\PowerSet{n}}$;
\item the countably infinite discrete space $\Pair{\NN}{\PowerSet{\NN}}$;
\item the unique uncountable standard Borel space, represented for example by $\Pair{\R}{\mathcal B(\R)}$.
\end{itemize}

Two standard Borel spaces are Borel-isomorphic iff they have the same cardinality.

\end{theorem*}

\begin{proof}[Proof] Cardinality is preserved by Borel isomorphism, so distinct cardinalities give distinct classes.

\emph{Countable case.} Every subset of a countable Polish space $X$ is a countable union of singletons.
Singletons are closed because $X$ is $T_1$, hence Borel, so $\mathcal B(X) = \PowerSet{X}$.
Consequently, every bijection between countable standard Borel spaces, as well as its inverse, is Borel.
A finite space with $n$ points is therefore Borel-isomorphic to $\Pair{n}{\PowerSet{n}}$, including $n=0$;
a countably infinite space is Borel-isomorphic to $\Pair{\NN}{\PowerSet{\NN}}$.

\emph{Uncountable case.} \termuseas{Kuratowski's isomorphism theorem}{Kuratowski's theorem} in
§{sec:kuratowski-isomorphism} gives a Borel isomorphism between any two uncountable Polish spaces; the same isomorphism
witnesses Borel isomorphism between any two uncountable standard Borel spaces, since each is presented by some
uncountable Polish topology.
\end{proof}

Fix a countable open basis for $X$. Record each Borel code by the label at every finite address, using $0$ for
absence, $1$ for a union, $2$ for a complement, and $n+3$ for a leaf naming the $n$th basic open set.
A fixed enumeration of the finite addresses turns this record into an element of $\BaireSpace$.
The record determines the root label and all labelled subtrees, so different codes give different records.
The coding theorem in §{sec:borel-codes-every-borel} makes the decoding map
$$D:\BorelCodes\to\mathcal B(X),\qquad c\mapsto A_c$$
surjective. Consequently,
$$\Card{\mathcal B(X)}\le\Card{\BorelCodes}\le\Card{\BaireSpace}=2^{\alephNull}.$$

If $X$ is uncountable, the cardinality dichotomy gives $\Card{X}=2^{\alephNull}$.
The map $x\mapsto\{x\}$ injects $X$ into $\mathcal B(X)$, since distinct points give distinct closed singletons.
Together with the upper bound, this yields
$$2^{\alephNull}=\Card{X}\le\Card{\mathcal B(X)}\le2^{\alephNull},\qquad \Card{\mathcal B(X)}=2^{\alephNull}.$$

In contrast, Cantor's theorem gives
$$\Card{\PowerSet{\R}}=2^{2^{\alephNull}}>2^{\alephNull}.$$
Thus $\Pair{\R}{\PowerSet{\R}}$ is *not* a standard Borel space. Any Polish topology on the underlying set $\R$ has only
$2^{\alephNull}$ Borel sets, so none can generate the full power set. The standard Borel hypothesis therefore
restricts the $\sigma$-algebra, not merely the cardinality of the underlying set.

## Transporting an Analytic Non-Borel Set {#sec:analytic-nonborel-transfer}

Recall the Polish tree space and its analytic non-Borel set of ill-founded trees from §{sec:analytic-sets}.
The classification just proved now transports that example to an arbitrary uncountable Polish space.

In particular, $\mathcal T$ is uncountable, since every subset of a countable Polish space is a countable union of
closed singletons and hence Borel. For any uncountable Polish space $X$, \termuse{Kuratowski's isomorphism theorem}
in §{sec:kuratowski-isomorphism} gives a Borel isomorphism $e:\mathcal T\to X$. The preceding Borel-image argument
shows that $e(D)$ is analytic. If $e(D)$ were Borel, the identity
$$e^{-1}(e(D))=D$$
and measurability of $e$ would make $D$ Borel, a contradiction. Thus $e(D)$ is an analytic non-Borel subset of $X$;
by \termuse{Suslin's theorem}, it is not coanalytic either.

## The Effros–Borel Space of Closed Sets {#sec:effros-borel}

\begin{mathmeta}
  \vars{s}{Seq}
\end{mathmeta}
<!--
formalization: skip-begin (引用・背景説明・読書案内:
未リンク部分は見出しと、閉集合が既出のどの構成で使われるかを列挙する導入。
閉集合を点とする可測空間とそのσ代数の説明はEffrosBorel.measurableSpaceへ接続済みで、
導入の参照一覧を新たな証明として数えない。)
--> Closed subsets are the basic units throughout this text: pruned trees in §{sec:closed-sets-trees}, the Lusin--Suslin
prefix proof of §{sec:lusin-souslin-proof}, supports of probability measures in §{sec:prob-measure-space}, and orbit
closures of Polish-group actions in §{sec:polish-group-orbit-er}.<!--
formalization: skip-end
-->  Treating them as the *points* of a measurable space
requires a $\sigma$-algebra on the set $\ClosedSets{X}$ of closed subsets of $X$ introduced in
§{sec:closed-sets-trees}. Spaces whose points are subsets of another space are called
\termdefineas{hyperspace}{hyperspaces}. Here each point is itself a closed set. We first specify the measurable
structure on this collection; a topology will enter later in the proof.

The standard choice is the **\termdefineas{Effros--Borel space}{Effros–Borel structure}**: the $\sigma$-algebra
generated by the \termdefineas{hit set}{hit sets}
$$\{C \in \ClosedSets{X} : C \cap U \ne \emptyset\},$$
where $U$ ranges over the open subsets of $X$.
By complementation, the \termdefineas{miss set}{miss sets} $\{C : C \cap U = \emptyset\}$ generate the same
$\sigma$-algebra.

\begin{theorem*} For every Polish space $X$, $\Pair{\ClosedSets{X}}{\text{Effros–Borel}}$ is a standard Borel space
[@Kechris1995, Theorem 12.6].

\end{theorem*}

\begin{proof}[Proof] \emph{Baire-space case.} By §{sec:closed-sets-trees}, the map
$$
\begin{aligned}
\ClosedSets{\BaireSpace}
&\;\longrightarrow\;2^{\finseq{\omega}},\\
C
&\;\mapsto\; T_C := \{s : \cyl{s} \cap C \ne \emptyset\},
\end{aligned}
$$
is a bijection onto the pruned trees, viewed as a subset of $2^{\finseq{\omega}}$. For a subtree $T$, pruning is
equivalent to the condition
$$\forall s\in T\;\exists a\in\omega\quad s\concat\SingletonSeq{a}\in T.$$
Indeed, a branch through a node supplies such an immediate extension. Conversely, starting from any node, choose
successive immediate extensions. Their union is an infinite sequence through that node; every finite prefix lies in
$T$ because $T$ is closed under initial segments. The empty tree satisfies the condition and represents the empty set.

Closure under initial segments is a closed condition on the indicator of $T$: each implication between two fixed
coordinates is clopen, and there are only countably many pairs of finite words. For each fixed $s$, the displayed
extension condition is open, since it either excludes $s$ or requires one of its countably many immediate extensions.
Thus pruned trees form a $\bPi^0_2$ subset of $2^{\finseq{\omega}}$. By \termuse{Alexandrov's theorem} in
§{sec:alexandrov-theorem}, this is a Polish subspace. Each Effros–Borel generator
$\{C : C \cap \cyl{s} \ne \emptyset\}$ corresponds under the bijection to the clopen condition $\{T : s \in T\}$.
These coordinate conditions generate the Borel structure of the indicator product and its subspace. Conversely,
every open subset of $\BaireSpace$ is a countable union of cylinders, so every open hit is a countable union of
cylinder hits. Hence the bijection and its inverse are measurable, and $\ClosedSets{\BaireSpace}$ is standard Borel.

\emph{General Polish $X$.} Embed $X$ as a $\bPi^0_2$ subset of the \termuse{Hilbert cube}
$\hat X := \HilbertCube$ using §{sec:hilbert-cube-embedding}. The map
$$\Phi : \ClosedSets{X} \to \ClosedSets{\hat X}, \qquad C \mapsto \AmbientClosure{\hat X}{C},$$
is injective: closure-in-subspace equals (closure-in-ambient) $\cap$ subspace, so $\AmbientClosure{\hat X}{C} \cap X =
\AmbientClosure{X}{C} = C$ recovers $C$ from $\Phi(C)$. The image is
$$\Phi(\ClosedSets{X}) = \{\tilde C \in \ClosedSets{\hat X} : \AmbientClosure{\hat X}{\tilde C\cap X}=\tilde C\}.$$
Writing $X = \bigcap_n W_n$ with each $W_n$ open in $\hat X$, the Baire category theorem in the Polish space $\tilde C$
reduces "$\tilde C \cap X$ dense in $\tilde C$" to "$\tilde C \cap W_n$ dense in $\tilde C$ for every $n$" —
equivalently, for every basic open $U_k$ of $\hat X$ and every $n$, $\tilde C \cap U_k \ne \emptyset$ implies $\tilde C
\cap (U_k \cap W_n) \ne \emptyset$. Each clause is an implication between two Effros–Borel hit sets, and the countable
conjunction over $\Pair{n}{k}$ is again Effros–Borel. So $\Phi(\ClosedSets{X})$ is Effros–Borel in
$\ClosedSets{\hat X}$.

The nonempty members of $\ClosedSets{\hat X}$ form a compact Polish \termuse{hyperspace} under the Hausdorff metric;
adjoining
$\emptyset$ as an isolated point preserves compactness and Polishness [@Kechris1995, §4.F]. Its topology is the Vietoris
topology. Fix a countable open basis of $\hat X$. Finite families from this basis give a countable Vietoris basis:
a closed set must be contained in the union of the chosen basic opens and meet each of them. The containment
condition is a miss of the compact complement of that union; the other conditions are open hits.

Each compact miss is Effros–Borel. Indeed, for compact $K\IncludedIn\hat X$, the set
$\{\tilde C:\tilde C\cap K=\emptyset\}$ is the union, over $m\ge1$, of the complements of the hit sets for the open
$1/m$-neighborhoods of $K$. When both sets are nonempty, disjointness gives positive distance by compactness.
If either set is empty, the same equivalence holds directly. Consequently all members of the countable Vietoris
basis are Effros–Borel, and every Vietoris open set is Effros–Borel. Conversely, open hits are Vietoris open. Thus the
two $\sigma$-algebras coincide, so $\ClosedSets{\hat X}$ is standard Borel and $\Phi(\ClosedSets{X})$ is a Borel
subspace.

It remains to check that this identification has the Effros--Borel structure on both sides. If $U \IncludedIn \hat X$ is
open, then
$$\AmbientClosure{\hat X}{C}\cap U\ne\emptyset
\quad\Longleftrightarrow\quad
C\cap(U\cap X)\ne\emptyset,$$
because $C$ is dense in its ambient closure. Thus $\Phi$ pulls every hit generator in $\ClosedSets{\hat X}$ back to a
hit generator in $\ClosedSets{X}$. Conversely, on $\Phi(\ClosedSets{X})$, the inverse sends $\tilde C$ to
$\tilde C\cap X$. If $O=U\cap X$ is open in $X$ with $U$ open in $\hat X$, then density of $\tilde C\cap X$ in
$\tilde C$ gives
$$
(\tilde C\cap X)\cap O\ne\emptyset
\quad\Longleftrightarrow\quad
\tilde C\cap U\ne\emptyset.
$$
So the inverse also pulls Effros hit generators back to Effros hit generators. Hence $\ClosedSets{X}$ is
Borel-isomorphic to the Borel subspace $\Phi(\ClosedSets{X}) \IncludedIn \ClosedSets{\hat X}$. By
§{sec:polish-topology-refinement}, a Borel subset of a Polish space can be made clopen by a Borel-preserving Polish
refinement, so this subspace is standard Borel. Therefore $\ClosedSets{X}$ is standard Borel.
\end{proof}

<!-- formalization: skip (external Fell-topology comparison) -->
When $X$ is \termdefineas{locally compact space}{locally compact} Polish, the Effros–Borel structure is the Borel
structure of the \termdefine{Fell topology}, with subbase $\{C : C \cap U \ne \emptyset\}$ for $U$ open and $\{C : C
\cap K = \emptyset\}$ for $K$ compact, and $\ClosedSets{X}$ is itself compact Polish. For general Polish $X$, the
Effros–Borel structure is defined directly from the given topology, without choosing a Polish topology on the
space of closed sets.

<!-- formalization: skip (payoff introduction) -->
Two payoffs are used implicitly elsewhere in the text.

*Trees as a Borel parameter space.* The Baire-space case identifies $\ClosedSets{\BaireSpace}$ with the standard Borel
space of
pruned trees. Constructions parameterized by a closed set — the analytic-set scheme of
§{sec:souslin-operation-suslin-schemes}, the Lusin--Suslin prefix proof of §{sec:lusin-souslin-proof}, and the
\termuseas{perfect kernel}{Cantor–Bendixson kernel} of §{sec:cantor-bendixson} — thereby become constructions
parameterized by an element of a standard Borel space, with all the ordinary descriptive-set-theoretic machinery
available.

<!-- formalization: skip-begin (external Kuratowski--Ryll-Nardzewski theorem cited to Kechris, with comparison to
  Jankov--von Neumann) -->
*Borel selectors.* The
\termdefineas{Kuratowski--Ryll-Nardzewski selection theorem}{Kuratowski–Ryll-Nardzewski selection theorem} says that
every Effros–Borel-measurable map $\mu : Y \to \ClosedSets{X}$ from a standard Borel space $Y$ with nonempty
values admits a Borel \termdefineas{Borel selector}{selector} $f : Y \to X$ satisfying $f(y) \in \mu(y)$ for every $y$.
Conceptually, this is the closed-valued Borel counterpart of the first-eligible-basic-set construction used for
Jankov--von Neumann uniformization in §{sec:uniformization}. There the relevant hit predicates are analytic, so the
resulting selector is only measurable for the analytic-generated $\sigma$-algebra. Effros–Borel measurability instead
yields a genuinely Borel selector [@Kechris1995, Theorem 12.13].
<!-- formalization: skip-end -->
