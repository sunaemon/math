# Cantor Space and Baire Space {#sec:cantor-baire-space}

\begin{mathmeta}
  \vars{n,p}{Nat}
  \vars{s}{Seq}
\end{mathmeta}


This chapter focuses on Polish sequence spaces $A^\omega$ whose alphabet $A$ is discrete. To be Polish, the discrete
alphabet must be \termuse{countable}: if $A$ were uncountable, then the
first-coordinate projection $\pi_0 : A^\omega \to A$ would split the space as
$A^\omega = \InternalDisjointUnion_{a \in A} \pi_0^{-1}(\{a\})$ into uncountably many pairwise disjoint nonempty open
sets, so $A^\omega$ would not be separable. Thus $A^\omega$ is Polish exactly when the alphabet $A$ is countable.

<!-- formalization: skip-begin (chapter overview: motivation and forward references, not proof obligations) -->
For finite alphabets, there is essentially one nontrivial case. If $2\le n<\omega$, then $n^\omega$ is homeomorphic to
Cantor space $\CantorSpace$, as follows from Brouwer's characterization in
§{sec:clopen-scheme-characterizations}. For a countably infinite alphabet, $A^\omega$ is homeomorphic to Baire space
$\BaireSpace$. Recall from §{sec:sequence-spaces} that Cantor space and Baire space are not homeomorphic: Cantor space
is compact, while Baire space is not.

This chapter describes open and closed subsets of \termuse{Cantor space} and \termuse{Baire space} using cylinders
and trees, and proves topological characterizations of the two spaces using partitions into clopen sets.
Cantor space is the compact finitely branching case; Baire space is the noncompact countably branching case.
For Cantor space, compactness implies that every clopen set is a finite union of cylinders.

The closed-set representation by trees will also be used in the Cauchy representation of arbitrary Polish spaces
in §{sec:cauchy-representation-admissibility}.

Concrete models of both spaces are collected in §{sec:concrete-cantor-baire-models}.

<!-- formalization: skip-end -->

\begin{mathmeta}
  \define{finseq,emptySeq,concat,prefixOf,notPrefixOf,properPrefixOf,extendsPrefix,wordRepeat}
\end{mathmeta}

We write $\finseq{A} = \bigcup_{n \in \omega} \seqPower{A}{n}$ for finite sequences with entries in $A$. If $s \in
\seqPower{A}{n}$, then $\Length{s} := n$; the empty sequence $\emptySeq$ is the unique element of $\seqPower{A}{0}$. For
a
finite sequence $s$ and a finite or infinite sequence $t$ with matching entries, $s \concat t$ denotes concatenation.

The prefix relation $s\prefixOf y$ means that the finite sequence $s$ is an initial segment of $y$, where $y$ may be
finite or infinite. We write $s\notPrefixOf y$ for its negation, $s\properPrefixOf y$ for proper prefix, and
$t\extendsPrefix s$ when $t$ extends $s$.

For a finite word or symbol $w$ and $n\in\omega$, $\wordRepeat{w}{n}$ is the concatenation of $n$ copies of $w$.
For $n=0$, the result is the empty word $\emptySeq$.

<!-- formalization: skip (notation for infinite periodic repetition, used below only for nonempty words) -->
For nonempty $w$, $\wordRepeat{w}{\omega}$ denotes the infinite periodic word. This repetition notation is distinct from
function-space exponentiation: the result is a word, not a set of sequences.

\begin{mathmeta}
  \define{cyl}
\end{mathmeta}

## Cylinder Sets and the Standard Base {#sec:cylinder-base}

\begin{mathmeta}
  \vars{s,t}{Seq}
  \vars{n}{Nat}
  \vars{k}{Nat}
\end{mathmeta}

<!-- formalization: skip (section lead-in) -->
Throughout this section, $A$ is either $2$ or $\omega$. The product space $A^\omega$ has a common prefix basis.

For a
finite sequence $s\in\finseq{A}$, the \termdefine{cylinder} determined by $s$ is
$$
\cyl{s}:=\{x\in A^\omega:s\prefixOf x\}.
$$

The cylinders form the \termdefineas{standard base}{standard countable base} for the product topology in both cases.
Indeed, $\finseq{A}$ is countable, since it is a countable union of finite powers of the countable alphabet $A$. Each
cylinder is product-open because
$$
\cyl{s}=\bigcap_{i<\Length{s}}\pi_i^{-1}(\{s_i\}),
$$
where $\pi_i:A^\omega\to A$ is the $i$-th coordinate projection and $A$ is discrete. Conversely, a basic product
neighborhood of $x$ restricts only finitely many coordinates. If those coordinates lie below $n$, then
$\cyl{\restrict{x}{n}}$ contains $x$ and is contained in that neighborhood. Thus every product-open set is a union of
cylinders.

Each cylinder is also closed: its complement is
$$
\SetDifference{A^\omega}{\cyl{s}}
=
\bigcup\{\cyl{t}:t\in\seqPower{A}{\Length{s}},\ t\ne s\},
$$
which is open as a union of cylinders. Hence every cylinder is clopen, and both $\CantorSpace$ and $\BaireSpace$ are
zero-dimensional.

The branching degree is the main difference. In Cantor space, the partition at level $n$ is finite:
$$
\CantorSpace=\InternalDisjointUnion_{t\in\seqPower{2}{n}}\cyl{t},
\qquad
\Card{\seqPower{2}{n}}=2^n<\infty.
$$
By contrast, in Baire space the partition at level $n$ is countable:
$$
\BaireSpace=\InternalDisjointUnion_{t\in\seqPower{\omega}{n}}\cyl{t},
\qquad
\seqPower{\omega}{n}\text{ is countable}.
$$
Thus the same level-by-level prefix partition exists in both spaces, but the Baire-space partition is countably
branching rather than finite and binary.

\begin{mathmeta}
  \define{SeqMetric}
\end{mathmeta}

We use the \termdefine{standard sequence metric} on $A^\omega$:
$$
\SeqMetric{x}{y}:=
\begin{cases}
0, & x=y,\\
2^{-\min\{i:x_i\ne y_i\}}, & x\ne y.
\end{cases}
$$

\begin{claim*} $\SeqMetricName$ is a metric on both $\CantorSpace$ and $\BaireSpace$, and in each case $\SeqMetricName$
is compatible with the product topology. More precisely, $\cyl{\emptySeq}=A^\omega$, and if $s$ is nonempty and
$x\in\cyl{s}$, then, with respect to $\SeqMetricName$,
$$
\cyl{s}=\MetricBall{\SeqMetricName}{x}{2^{-(\Length{s}-1)}}.
$$

\end{claim*}

\begin{proof}[Proof] Symmetry and definiteness are immediate from the definition. For the triangle inequality, it is
enough to prove the stronger ultrametric inequality
$$
\SeqMetric{x}{y}\le
\max\{\SeqMetric{x}{z},\SeqMetric{z}{y}\}.
$$
If $x=y$ this is trivial. Otherwise let $k$ be the least coordinate at which $x$ and $y$ differ. At coordinate $k$, the
value $z_k$ differs from at least one of $x_k$ and $y_k$. Hence either $\SeqMetric{x}{z}\ge 2^{-k}$ or
$\SeqMetric{z}{y}\ge 2^{-k}$, while $\SeqMetric{x}{y}=2^{-k}$.
This proves the ultrametric inequality and therefore the triangle inequality.

It remains to compare the metric balls with cylinders. Fix $x\in\cyl{s}$ and put $k=\Length{s}$. A point $y$ belongs to
$\cyl{s}$ exactly when $x$ and $y$ agree on the first $k$ coordinates. If $k=0$, this says only that
$\cyl{\emptySeq}=A^\omega$. If $k>0$, agreement on the first $k$ coordinates is equivalent to
$\SeqMetric{x}{y}<2^{-(k-1)}$: any disagreement before coordinate $k$ has distance at least $2^{-(k-1)}$, while
agreement through coordinate $k-1$ gives distance at most $2^{-k}$ unless $x=y$. Hence, for nonempty $s$,
$\cyl{s}=\MetricBall{\SeqMetricName}{x}{2^{-(\Length{s}-1)}}$.

Conversely, given a metric ball $\MetricBall{\SeqMetricName}{x}{\varepsilon}$ around $x$, choose $n$ with
$2^{-n}<\varepsilon$. The nonempty-prefix equality gives
$$
\cyl{\restrict{x}{n+1}}
=\MetricBall{\SeqMetricName}{x}{2^{-n}}
\IncludedIn\MetricBall{\SeqMetricName}{x}{\varepsilon}.
$$
Since the cylinders already form the standard base for the product topology, the metric topology and the product
topology coincide.
\end{proof}

<!-- formalization: skip-begin (chapter transition and forward references) -->
We next use the \termuseas{standard base}{cylinder base} to represent open and closed sets by sets of finite sequences.
<!-- formalization: skip-end -->

## Cylinder Codes and Prefix Trees {#sec:closed-sets-trees}

\begin{mathmeta}
  \vars{x}{Name}
  \vars{n}{Nat}
  \vars{s,t}{Seq}
\end{mathmeta}

<!-- formalization: skip (section overview) -->
The common cylinder language now becomes a tree language. We first set up prefix trees, up-sets, and saturation
uniformly for $A^\omega$, with $A=2$ or $A=\omega$. We then specialize to the Baire case for the open-set and closed-set
coding used later for arbitrary Polish spaces, and finally record the Cantor-space version as the binary
finite-branching case.

A \termdefine{tree} is a partially ordered set in which, for each element $t$, the set $\{s:s\le t\}$ is well-ordered
by the inherited order.
For $A=2$ or $A=\omega$, the full prefix \termuse{tree} is $\Pair{\finseq{A}}{\prefixOf}$.
For $t\in\finseq{A}$, the non-strict down-set of $t$ in the full prefix \termuse{tree} is exactly the set of initial
segments of $t$:
$$
\RestrictedSet{\finseq{A}}{\prefixOf t}
=
\{\restrict{t}{n}:n\le \Length{t}\}
\cong \Length{t}+1
\quad\text{as posets},
$$
so it is well-ordered.
Thus $\Pair{\finseq{A}}{\prefixOf}$ is a tree.


The cylinders under reverse inclusion give the same tree:
$$
\begin{aligned}
\Pair{\finseq{A}}{\prefixOf}
&\xrightarrow{\;\sim\;}
\Pair{\{\cyl{s}:s\in\finseq{A}\}}{\supseteq},\\
s&\mapsto\cyl{s}.
\end{aligned}
$$

<!-- formalization: skip (motivation for canonical open-set codes) -->
Different sets of finite prefixes can represent the same open set as a union of cylinders. To obtain a canonical code,
we collect all prefixes whose cylinders are contained in that open set. The following definitions describe these codes.

An \termdefine{up-set} is a set $B\IncludedIn\finseq{A}$ such that $s\in B$ and $s\prefixOf t$ imply $t\in B$.
An up-set $B$ is \termdefine{saturated} when every prefix whose branches all eventually reach $B$ already lies in $B$:
if for every $x\in\cyl{s}\IncludedIn A^\omega$ there is some $n\in\omega$ with $\restrict{x}{n}\in B$, then $s\in B$.

<!-- formalization: skip-begin (notation declarations; their meanings are formalized in the claims below) -->
\begin{mathmeta}
  \define{OpenSets,PrefixUpSets,CylinderCode,OpenCylinderCode}
\end{mathmeta}
<!-- formalization: skip-end -->

<!-- formalization: skip (notation-only names for the posets of open sets and prefix up-sets) -->
Write $\OpenSets{X}$ for the poset of open subsets of a topological space $X$, and write $\PrefixUpSets{A}$ for the
poset of prefix up-sets in $\finseq{A}$.

<!-- formalization: skip (lead-in to the formalized Galois-connection claim) -->
For the Baire case $A=\omega$, cylinders link openness in $\BaireSpace$ to the up-set property in $\finseq{\omega}$ via
a \termdefine{Galois connection}.

\begin{claim*} The assignments
$$
\begin{aligned}
\CylinderCode{\cdot}:\PrefixUpSets{\omega}&\to\OpenSets{\BaireSpace},
&
\CylinderCode{B}&:=\bigcup_{s\in B}\cyl{s},\\
\OpenCylinderCode{\cdot}:\OpenSets{\BaireSpace}&\to\PrefixUpSets{\omega},
&
\OpenCylinderCode{U}&:=\{s\in\finseq{\omega}:\cyl{s}\IncludedIn U\}
\end{aligned}
$$
form a Galois connection:
$$
\CylinderCode{B}\IncludedIn U
\quad\Longleftrightarrow\quad
B\IncludedIn\OpenCylinderCode{U}.
$$

\end{claim*}

\begin{proof}[Proof] If $B$ is an up-set, then $\CylinderCode{B}$ is open.
If $U$ is open, then $\OpenCylinderCode{U}$ is an up-set because $\cyl{t}\IncludedIn\cyl{s}$ whenever $s\prefixOf t$.
If $\CylinderCode{B}\IncludedIn U$ and $s\in B$, then $\cyl{s}\IncludedIn\CylinderCode{B}\IncludedIn U$, so
$s\in\OpenCylinderCode{U}$.
Conversely, if $B\IncludedIn\OpenCylinderCode{U}$, then every cylinder $\cyl{s}$ with $s\in B$ is contained in $U$,
hence $\CylinderCode{B}\IncludedIn U$.
\end{proof}

\begin{claim*} Open sets in $\BaireSpace$ are in one-to-one correspondence with saturated up-sets of $\finseq{\omega}$.
The correspondence sends an open set $U$ to $\OpenCylinderCode{U}$, and its inverse sends a saturated up-set $B$ to
$\CylinderCode{B}$.

\end{claim*}

\begin{proof}[Proof] If $U$ is open, then every $x\in U$ lies in some cylinder $\cyl{s}\IncludedIn U$.
Thus $U=\CylinderCode{\OpenCylinderCode{U}}$.
The up-set $\OpenCylinderCode{U}$ is saturated: if every branch through $s$ eventually reaches
$\OpenCylinderCode{U}$, then every point of $\cyl{s}$ lies in $U$, so $\cyl{s}\IncludedIn U$ and hence
$s\in\OpenCylinderCode{U}$.
If $B$ is saturated, then applying $\OpenCylinderCode{\cdot}$ to $\CylinderCode{B}$ returns $B$.
Indeed, $B\IncludedIn\OpenCylinderCode{\CylinderCode{B}}$ is immediate.
Conversely, if $s\in\OpenCylinderCode{\CylinderCode{B}}$, then every $x\in\cyl{s}$ has some prefix in $B$.
Saturation of $B$ therefore gives $s\in B$.
This proves that the two assignments are inverse.
\end{proof}

<!-- formalization: skip-begin (notation declarations; their meanings are formalized in the following prose) -->
\begin{mathmeta}
  \define{TreeBody,ClosedSets,PrefixSubtrees,ClosedTreeCode}
\end{mathmeta}
<!-- formalization: skip-end -->

A \termdefine{subtree} is a set $T\IncludedIn\finseq{\omega}$ downward closed under initial segments:
if $t\in T$ and $s\prefixOf t$, then $s\in T$.
Write $\PrefixSubtrees{\omega}$ for the poset of subtrees of the full prefix tree, ordered by inclusion.

For any set $T\IncludedIn\finseq{\omega}$, its \termdefine{body} is
$$
\begin{aligned}
\TreeBody{T}
&:=
\bigcap_{s\notin T}(\SetDifference{\BaireSpace}{\cyl{s}})\\
&=
\{x\in\BaireSpace:\restrict{x}{n}\in T\text{ for every }n\in\omega\}.
\end{aligned}
$$
These are the infinite branches through $T$.

A subtree $T$ is \termdefine{pruned} if every node lies on some branch through $T$:
for every $s\in T$ there exists $x\in\TreeBody{T}$ with $s\prefixOf x$.
Since the complement of a downward-closed set is upward-closed, $T$ is pruned exactly when
$\SetDifference{\finseq{\omega}}{T}$
is a saturated up-set:
$$
\SetDifference{\finseq{\omega}}{T}
=
\OpenCylinderCode{\CylinderCode{\SetDifference{\finseq{\omega}}{T}}}.
$$
Indeed, suppose first that $T$ is pruned.
If every branch through $s$ eventually reaches $\SetDifference{\finseq{\omega}}{T}$, then no branch through $T$ extends
$s$.
Prunedness therefore forces $s\notin T$, so $s\in\SetDifference{\finseq{\omega}}{T}$.
Thus the complementary up-set is saturated.
Conversely, suppose $\SetDifference{\finseq{\omega}}{T}$ is saturated and let $s\in T$.
If no branch through $T$ extended $s$, then every $x\in\cyl{s}$ would have some prefix outside $T$, so saturation would
give $s\notin T$, a contradiction.
Hence some $x\in\TreeBody{T}$ extends $s$, and $T$ is pruned.

<!-- formalization: skip (notation-only name for the poset of closed sets) -->
Write $\ClosedSets{X}$ for the poset of closed subsets of a topological space $X$.

\begin{claim*} $\ClosedSets{\BaireSpace}$ is in one-to-one correspondence with the pruned elements of
$\PrefixSubtrees{\omega}$, via $T\mapsto\TreeBody{T}$ and
$F\mapsto \ClosedTreeCode{F}:=\{s\in\finseq{\omega}:\cyl{s}\cap F\ne\emptyset\}$.
\end{claim*}

\begin{proof}[Proof] Let $F\IncludedIn\BaireSpace$ be closed.
Apply the preceding open-set correspondence to the open complement $\SetDifference{\BaireSpace}{F}$.
The complementary prefix set is
$$
\SetDifference{\finseq{\omega}}{\OpenCylinderCode{\SetDifference{\BaireSpace}{F}}}
=
\{s\in\finseq{\omega}:\cyl{s}\cap F\ne\emptyset\}
=
\ClosedTreeCode{F}.
$$
Thus the closed-set code is the complement of the saturated code for the open complement.
Since $\OpenCylinderCode{\SetDifference{\BaireSpace}{F}}$ is a saturated up-set, $\ClosedTreeCode{F}$ is a pruned
subtree by the preceding
equivalence.
Moreover, $F=\TreeBody{\ClosedTreeCode{F}}$.
If $x\in F$, then every cylinder $\cyl{\restrict{x}{n}}$ meets $F$, so every prefix $\restrict{x}{n}$ lies in
$\ClosedTreeCode{F}$.
If $x\notin F$, closedness of $F$ makes $\SetDifference{\BaireSpace}{F}$ open, so some cylinder $\cyl{\restrict{x}{n}}$
is
contained in $\SetDifference{\BaireSpace}{F}$; hence $\restrict{x}{n}\notin\ClosedTreeCode{F}$ and
$x\notin\TreeBody{\ClosedTreeCode{F}}$.

Conversely, if $T$ is a pruned subtree, then
$$
\SetDifference{\BaireSpace}{\TreeBody{T}}
=
\bigcup\{\cyl{s}:s\notin T\},
$$
so $\TreeBody{T}$ is closed.
Finally, $\ClosedTreeCode{\TreeBody{T}}=T$.
If $s\in T$, prunedness gives some $x\in\TreeBody{T}\cap\cyl{s}$.
If $s\notin T$, then no point of $\cyl{s}$ lies in $\TreeBody{T}$.
This proves that the two assignments are inverse.
\end{proof}

Cantor space $\CantorSpace$ is the binary version of the same tree picture. Its full prefix tree is
$\Pair{\finseq{2}}{\prefixOf}$, and a subtree $T\IncludedIn\finseq{2}$ has body
$$
\TreeBody{T}:=\{x\in\CantorSpace:\restrict{x}{n}\in T\text{ for every }n\in\omega\}.
$$
Exactly as above, closed subsets of $\CantorSpace$ are the bodies of pruned binary trees.

The finite branching adds compactness. $\CantorSpace$ is compact by Tychonoff's theorem, since it is a product of
compact finite discrete spaces, and it is \termuseas{perfect space}{perfect} because every binary cylinder has the two
proper subcylinders $\cyl{s\concat(0)}$ and $\cyl{s\concat(1)}$.

\begin{lemma*}[\termdefineas{König's lemma}{Lemma (König)}]
If $T\IncludedIn\finseq{2}$ is a binary subtree and $\TreeBody{T}=\emptyset$, then some level is empty:
there is an $n$ such that no $s\in\seqPower{2}{n}$ belongs to $T$.
\end{lemma*}

\begin{proof}[Proof]
Since $\TreeBody{T}=\emptyset$,
$$
\CantorSpace=\bigcup\{\cyl{s}:s\notin T\}.
$$
Compactness gives a finite subcover by cylinders $\cyl{s_0},\ldots,\cyl{s_{m-1}}$ with each $s_i\notin T$.
Let $N=\max_i \Length{s_i}$. If some $t\in T$ had length $N$, choose any branch $x\in\cyl{t}$.
The finite subcover puts $x$ in some $\cyl{s_i}$.
Since $\Length{s_i}\le N$, this means $s_i\prefixOf t$, contradicting downward closure of $T$.
\end{proof}

By compactness, or equivalently by this finite-branching König bound, clopen subsets of $\CantorSpace$ are finite
unions of binary cylinders.

<!-- formalization: skip (forward pointers to later uses of the compact binary cylinder picture) -->
This compact binary cylinder picture is used later for
Stern--Brocot boundary paths, infinite subsets of $\omega$, perfect-set constructions, Cohen forcing, and fair-coin
measure.

For example, intersections become intersections of trees:
$$
\TreeBody{S}\cap\TreeBody{T}
=
\TreeBody{S\cap T}.
$$

Even when $S$ and $T$ are pruned, $S\cap T$ may not be.
For example, let
$$
S=\{\wordRepeat{0}{n}:n\in\omega\},
\qquad
T=\{\wordRepeat{1}{n}:n\in\omega\}.
$$
Both are pruned, witnessed by the constant branches $0^\omega$ and $1^\omega$, respectively.
But $S\cap T=\{\emptySeq\}$, whose body is empty, so the root has no branch through $S\cap T$.

The pruned subtree corresponding to $\TreeBody{S}\cap\TreeBody{T}$ under the bijection is
$\ClosedTreeCode{\TreeBody{S\cap T}}$.

## Clopen Schemes and Topological Characterizations {#sec:clopen-scheme-characterizations}

\begin{mathmeta}
  \vars{i,n}{Nat}
  \vars{s}{Seq}
  \vars{q,r}{Real}
\end{mathmeta}

<!-- formalization: skip (cross-reference to the bounded-metric reduction formalized in Chapter 1) -->
The \termuse{bounded complete compatible metric lemma} in §{sec:polish-key-properties} lets the applications below
choose their complete compatible metrics bounded by $1$.

\begin{lemma*}[\termdefineas{clopen scheme lemma}{Clopen-scheme lemma}]
Let $X$ be a nonempty complete metric space with metric $d\le 1$. Let $T\IncludedIn\finseq{\omega}$ be a
\termuse{subtree}. Suppose $\IndexedFamily{U_s}{s\in T}$ is a family of nonempty clopen subsets of $X$ such that:

\begin{enumerate}
\item $\emptySeq\in T$ and $U_{\emptySeq}=X$;
\item $U_s=\InternalDisjointUnion\{U_{s\concat(i)}: i\in\omega \text{ and } s\concat(i)\in T\}$ for each $s\in T$;
\item $\MetricDiameter{d}{U_s}\le 2^{-\Length{s}}$.
\end{enumerate}

Then $X$ is homeomorphic to $\TreeBody{T}$.
\end{lemma*}

\begin{proof}[Proof]
For $b\in\TreeBody{T}$, the sets $U_{\restrict{b}{n}}$ are nested, closed, nonempty, and have diameters tending to $0$.
Choose $a_n\in U_{\restrict{b}{n}}$. Then $\Sequence{a_n}{n\in\omega}$ is Cauchy, hence converges to some point of $X$.
Since each
$U_{\restrict{b}{n}}$ is closed, the limit lies in every $U_{\restrict{b}{n}}$; uniqueness follows from the shrinking
diameters. Define
$$
h(b)=\text{the unique point of }\bigcap_n U_{\restrict{b}{n}}.
$$

\begin{itemize}
\item \emph{Surjectivity}: given $z\in X$, start with $s_0=\emptySeq$ and choose the unique successor $s_{n+1}$ of $s_n$
with $z\in U_{s_{n+1}}$. The compatible nodes define a branch $b\in\TreeBody{T}$, and
$z\in\bigcap_n U_{\restrict{b}{n}}=\{h(b)\}$.
\item \emph{Injectivity}: if $b\ne c$, take the first coordinate at which they differ. The corresponding one-step
extensions of their common prefix are distinct sibling nodes, so $h(b)$ and $h(c)$ lie in disjoint clopen pieces.
\item \emph{Continuity of $h$}: if $\restrict{b}{n}=\restrict{c}{n}$, then $h(b)$ and $h(c)$ lie in the same set
$U_{\restrict{b}{n}}$, whose diameter is at most $2^{-n}$.
\item \emph{Continuity of $h^{-1}$}: for $s\in T$, the same branch construction starting inside $U_s$ shows that the
image of the tree cylinder $\{b\in\TreeBody{T}:s\prefixOf b\}$ is exactly $U_s$, which is open in $X$.
\end{itemize}

Thus $h$ is a homeomorphism from $\TreeBody{T}$ onto $X$.
\end{proof}

<!-- formalization: skip (transition) -->
The two characterizations below use this lemma in parallel.

\begin{theorem*}[\termdefineas{Brouwer's Cantor-space characterization}{Brouwer's characterization}]
The Cantor space $\CantorSpace$ is, up to homeomorphism, the unique nonempty zero-dimensional, perfect, compact metric
space.
\end{theorem*}

\begin{proof}[Proof] \emph{The model space.} The Cantor space $\CantorSpace$ is compact by Tychonoff,
metrizable by the standard sequence metric, zero-dimensional because its cylinders are clopen, and perfect because every
cylinder has two proper subcylinders.

\emph{The converse scheme.} Let $X$ be a nonempty compact zero-dimensional perfect metric space, and fix a complete
compatible metric $d \le 1$. Construct a finitely branching tree $T\IncludedIn\finseq{\omega}$ and a
\termdefine{Cantor clopen scheme} $\IndexedFamily{U_s}{s\in T}$ of nonempty clopen subsets of $X$ such that:

\begin{enumerate}
\item $\emptySeq\in T$ and $U_{\emptySeq}=X$;
\item the set $\{i\in\omega:s\concat(i)\in T\}$ is finite and has at least two elements for each $s\in T$;
\item $U_s=\InternalDisjointUnion\{U_{s\concat(i)}: i\in\omega \text{ and } s\concat(i)\in T\}$ for each $s\in T$;
\item $\MetricDiameter{d}{U_s}\le 2^{-\Length{s}}$.
\end{enumerate}

Inductively, suppose $s\in T$ and $U_s$ is already defined. Compactness and zero-dimensionality give a finite clopen
cover of $U_s$ by sets of diameter $\le 2^{-\Length{s}-1}$. Disjointify the cover and discard empty sets to obtain a
finite
clopen partition with the same diameter bound. If the partition has only one piece, split that piece into two nonempty
clopen subsets; this is possible because $U_s$ is a nonempty open subspace of a perfect zero-dimensional space. Declare
the resulting partition to be $\{U_{s\concat(i)}:i<k_s\}$, where $2\le k_s<\omega$, and put those successors into $T$.

\emph{Applying the common lemma.} The \termuseas{clopen scheme lemma}{clopen-scheme lemma} gives
$X\cong\TreeBody{T}$. It remains only to identify
$\TreeBody{T}$ with $\CantorSpace$. At a node $s$, list the immediate successors as
$s\concat(i_0),\ldots,s\concat(i_{m-1})$, with $m\ge 2$. If the current binary cylinder is $\cyl{q_s}$, split it into
the $m$ cylinders with stems $q_s\concat c_j$, where
$$
c_j=
\begin{cases}
\wordRepeat{1}{j}\concat(0),&j+1<m,\\
\wordRepeat{1}{j},&j+1=m.
\end{cases}
$$
These cylinders are pairwise disjoint and cover $\cyl{q_s}$: a binary tail either has a first $0$ before position
$m-1$, or it begins with $m-1$ many $1$'s. Assign the cylinder with stem $q_s\concat c_j$ to the successor
$s\concat(i_j)$. Starting with $q_{\emptySeq}=\emptySeq$ and recursing down the tree produces a binary cylinder scheme
indexed by $T$, and each successor step appends a nonempty word.

Now each binary stream determines a unique branch through $T$ by following the unique cylinder that contains it at every
level. Conversely, a branch through $T$ determines nested binary cylinders whose stem lengths tend to infinity, hence a
unique binary stream. These assignments are inverse, and the tree cylinder determined by $s$ corresponds to $\cyl{q_s}$.
The cylinders $\cyl{q_s}$ form a basis for $\CantorSpace$: along the branch determined by any binary stream, their
stem lengths tend to infinity, so they refine every cylinder neighborhood of that stream. Thus the bijection carries a
basis of $\TreeBody{T}$ onto a basis of $\CantorSpace$, making both it and its inverse continuous.
Hence $\CantorSpace\cong\TreeBody{T}$, and therefore $X\cong\CantorSpace$.
\end{proof}

\begin{corollary*}[Bounded-branching tree bodies]
Given $k:\finseq{\omega}\to\omega$, define the bounded-branching \termuse{subtree}
$$
T_k:=\{s\in\finseq{\omega}:s_i<k(\restrict{s}{i})\text{ for every }i<\Length{s}\}.
$$
If $k(s)\ge2$ for every $s\in T_k$, then $\TreeBody{T_k}$ is homeomorphic to $\CantorSpace$.
\end{corollary*}

\begin{proof}[Proof]
Each $s\in T_k$ has precisely the immediate successors $s\concat(i)$ with $i<k(s)$. Apply the binary prefix coding
in the proof of Brouwer's characterization.
\end{proof}

<!-- formalization: skip-begin (transition to the Baire-space characterization) -->
The next characterization is the Baire-space analogue: compactness for $\CantorSpace$ is replaced by nowhere local
compactness for $\BaireSpace$.

<!-- formalization: skip-end -->

\begin{theorem*}[\termdefineas{Alexandrov--Urysohn theorem}{Theorem (Alexandrov–Urysohn)}]
$\BaireSpace$ is, up to homeomorphism, the unique nonempty zero-dimensional Polish space in which no point has a
compact neighborhood.

\end{theorem*}

A metric subspace is \termdefine{totally bounded} if, for every $\varepsilon>0$, finitely many open balls of
radius $\varepsilon$ cover it. We use the standard compactness criterion: a complete metric subspace is compact
if and only if it is totally bounded.

Such a space is automatically \termuseas{perfect space}{perfect}: an isolated point would have its singleton as a
compact neighborhood.

\begin{proof}[Proof] \emph{The model space.} The space $\BaireSpace$ is Polish by §{sec:sequence-spaces} and
zero-dimensional because cylinders are clopen.
For nowhere local compactness: every neighborhood of $x$ contains a cylinder $\cyl{s}$, and the sequence $\Sequence{s
\concat (n)
\concat \wordRepeat{0}{\omega}}{n\in\omega}$ inside $\cyl{s}$ disagrees pairwise at coordinate $\Length{s}$, so admits
no
convergent subsequence. Any compact set containing this neighborhood would contain the sequence and force
a convergent subsequence in itself; so no neighborhood of $x$ lies in a compact set.

\emph{The converse scheme.} Fix a complete compatible metric $d \le 1$ on $X$. Let $T:=\finseq{\omega}$. Construct a
\termdefine{Baire clopen scheme} $\IndexedFamily{U_s}{s\in T}$ of nonempty clopen subsets of $X$ such that:

\begin{enumerate}
\item $\emptySeq\in T$ and $U_{\emptySeq}=X$;
\item $U_s=\InternalDisjointUnion\{U_{s\concat(n)}: n\in\omega\}$ for each $s\in T$;
\item $\MetricDiameter{d}{U_s}\le 2^{-\Length{s}}$.
\end{enumerate}

Inductively, suppose a nonempty clopen set $U_s$ is given. As an open subspace of $X$, $U_s$ inherits
zero-dimensionality and nowhere local compactness. The set $U_s$ is not compact: if it were, it would be a compact
neighborhood of each of its points, contradicting nowhere local compactness of $X$. Since $U_s$ is closed in the
complete metric space $X$, it is complete; noncompactness therefore means it is not totally bounded. Pick $\epsilon_s >
0$ such that $U_s$ admits no finite cover by sets of diameter $\le \epsilon_s$, and put
$\eta_s=\min(2^{-\Length{s}-1},\epsilon_s)$.

By zero-dimensionality and second countability, choose a countable clopen cover $\IndexedFamily{B_n}{n\in\omega}$ of
$U_s$ by
subsets of $U_s$ such that $\MetricDiameter{d}{B_n}\le\eta_s$ for every $n$. Set
$$
W_n:=\SetDifference{B_n}{\bigcup_{k<n}B_k}.
$$
Each $W_n$ is clopen, $W_n\IncludedIn B_n$, and the $W_n$ are pairwise disjoint. Since the $B_n$ cover $U_s$,
$$
U_s=\InternalDisjointUnion_{n\in\omega} W_n
$$
after allowing empty pieces, and each $W_n$ has diameter at most $\eta_s$. Infinitely many $W_n$ are nonempty: otherwise
the nonempty $W_n$ would form a finite cover of $U_s$ by sets of diameter $\le \epsilon_s$, contradicting the choice of
$\epsilon_s$. Choose a bijective enumeration $e:\omega\to\{n\in\omega:W_n\ne\emptyset\}$ and set
$U_{s\concat(n)}:=W_{e(n)}$. The resulting successor family is a countable pairwise disjoint clopen cover of $U_s$ by
nonempty sets, and every successor has diameter at most $2^{-\Length{s}-1}$.

\emph{Applying the common lemma.} The \termuseas{clopen scheme lemma}{clopen-scheme lemma}, applied to $T$, gives
$X\cong\TreeBody{\finseq{\omega}}=\BaireSpace$.
\end{proof}

The Alexandrov–Urysohn theorem yields a non-arithmetic proof that the irrationals in $\R$ are homeomorphic to
$\BaireSpace$. The irrationals form a nonempty Polish space by \termuse{Alexandrov's theorem} in
§{sec:alexandrov-theorem}. The relative intervals $\OpenInterval{q}{r}\cap\SetDifference{\R}{\QQ}$, where $q<r$ are
rational, form a
clopen base, verifying zero-dimensionality. It remains to show that no point has a compact neighborhood. If a compact
set $K\IncludedIn\SetDifference{\R}{\QQ}$ contained a relative
open neighborhood of an
irrational,
then that neighborhood would contain a sequence of irrationals converging in $\R$ to a rational. The sequence would lie
in $K$, but compactness of $K$ as a subspace of $\SetDifference{\R}{\QQ}$ would force a subsequential limit in
$\SetDifference{\R}{\QQ}$,
contradicting uniqueness of limits in $\R$. Thus no irrational has a compact neighborhood. This complements the
continued-fraction homeomorphism in §{sec:simple-continued-fractions}.
