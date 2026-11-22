# Appendix: Metrics and Topology {#sec:appendix-metric-spaces}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
付録の内容とChoquet metrizationへの用途を案内する導入文。新たな数学的主張・証明はない。)
-->
This appendix collects the basic definitions of topology, density, compatible metrics, completeness, and countability
used throughout the book. It then proves the metric-space cover refinements used in the Choquet metrization argument.
<!--
formalization: skip-end
-->

## Topologies, Bases, and Dense Sets {#sec:appendix-topology-basics}

\begin{mathmeta}
  \vars{N,n}{Nat}
\end{mathmeta}

<!-- formalization: skip-begin (standard topological definitions, not separate proof obligations) -->
A \termdefine{topology} on a set $X$ is a family $\tau\IncludedIn\PowerSet{X}$ containing $\emptyset$ and $X$ and
closed under arbitrary unions and finite intersections. The pair $\Pair{X}{\tau}$ is a \termdefine{topological space};
the members of $\tau$ are its \termdefineas{open set}{open sets}. A set is \termdefine{closed} if its complement in
$X$ is open.

A \termdefine{neighborhood} of $x\in X$ is a set containing an open set that contains $x$. A
\termdefineas{base for a topology}{base} is a family $\mathcal B$ of open sets such that every open set is a union
of members of $\mathcal B$. Equivalently, whenever $x\in U$ and $U$ is open, some $B\in\mathcal B$ satisfies
$x\in B\IncludedIn U$.

A subset $D\IncludedIn X$ is \termdefineas{dense subset}{dense} in $X$ if every nonempty open subset of $X$ meets
$D$. A space is \termuseas{separable}{separable} if it has a countable dense subset.

A sequence $\Sequence{x_n}{n\in\omega}$ \termdefineas{convergent sequence}{converges} to $x$ if, for every
neighborhood $U$ of $x$, there is $N\in\omega$ such that $x_n\in U$ for all $n\ge N$.
<!-- formalization: skip-end -->

## Compatible Metrics and Completeness {#sec:appendix-compatible-complete-metrics}

\begin{mathmeta}
  \vars{N,n}{Nat}
\end{mathmeta}

<!-- formalization: skip-begin (standard metric definitions, not separate proof obligations) -->
A \termdefine{metric} on $X$ is a function $d:X\times X\to\LeftClosedInterval{0}{\infty}$ such that, for all $x,y,z\in
X$,
$$d(x,y)=0\ \Longleftrightarrow\ x=y,\qquad
 d(x,y)=d(y,x),\qquad d(x,z)\le d(x,y)+d(y,z).$$
The pair $\Pair{X}{d}$ is a \termdefine{metric space}. Its open balls are
$$\Ball{x}{r}:=\{y\in X:d(x,y)<r\}\qquad(r>0).$$
The topology induced by $d$ consists of the unions of open balls. A metric $d$ is
\termdefineas{compatible metric}{compatible} with a topology $\tau$ if this induced topology is exactly $\tau$.
Thus compatibility requires both that every ball be open and that every open set be a union of balls.
A topological space is \termdefine{metrizable} if it admits a compatible metric.

A sequence $\Sequence{x_n}{n\in\omega}$ is a \termdefine{Cauchy sequence} for $d$ if
$$\forall\varepsilon>0\;\exists N\in\omega\;\forall m,n\ge N\quad d(x_m,x_n)<\varepsilon.$$
The metric $d$ is \termdefineas{complete metric}{complete} if every $d$-Cauchy sequence converges to a point of $X$
with respect to $d$. A topological space is \termuse{completely metrizable} if it admits a complete compatible metric.
Completeness refers to the chosen metric; complete metrizability refers to the topology. In particular, the existence
of one complete compatible metric does not assert that every compatible metric is complete.
<!-- formalization: skip-end -->

## Distance to a Set {#sec:appendix-distance-to-set}

\begin{lemma*}[Distance to a nonempty set]
Let $F$ be a nonempty subset of a metric space $\Pair{X}{d}$, and put
$d(x,F):=\inf\{d(x,z):z\in F\}$. Then
$$\Abs{d(x,F)-d(y,F)}\le d(x,y)\qquad\Pair{x}{y}\in X.$$
In particular, the function $x\mapsto d(x,F)$ is continuous.
\end{lemma*}

\begin{proof}
For every $z\in F$, the triangle inequality gives
$$d(x,F)\le d(x,z)\le d(x,y)+d(y,z).$$
Taking the infimum over $z\in F$ yields $d(x,F)\le d(x,y)+d(y,F)$.
Interchanging $x$ and $y$ gives the reverse bound and hence the claimed absolute-value inequality.
The inequality implies continuity directly.
\end{proof}

## First and Second Countability {#sec:appendix-countability}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}

<!-- formalization: skip-begin (standard countability definitions, not separate proof obligations) -->
A \termdefine{neighborhood base} at $x$ is a family $\mathcal N_x$ of open neighborhoods of $x$ such that every
neighborhood of $x$ contains a member of $\mathcal N_x$. A space is
\termdefineas{first-countable space}{first countable} if every point has a countable neighborhood base.
It is \termdefineas{second-countable space}{second countable} if its topology has a countable base.
The first condition allows a different countable family at each point; the second requires one countable family for
the entire space.
<!-- formalization: skip-end -->

\begin{proposition*}[Separability and second countability]
For metrizable spaces, separability is equivalent to second countability.
\end{proposition*}

\begin{proof}
Choose a compatible metric. If $D$ is a countable dense subset, the balls $\Ball{a}{q}$ with $a\in D$ and
$q\in\RestrictedSet{\QQ}{>0}$ form a countable base. Indeed, for $x\in U$ with $U$ open, choose $\varepsilon>0$
with $\Ball{x}{\varepsilon}\IncludedIn U$, then $a\in D$ with $d(x,a)<\varepsilon/3$ and a rational $q$ with
$d(x,a)<q<\varepsilon-d(x,a)$. The triangle inequality gives
$x\in\Ball{a}{q}\IncludedIn\Ball{x}{\varepsilon}\IncludedIn U$.
Conversely, choose one point from each nonempty member of a countable base. The chosen points form a countable dense
subset, since every nonempty open set contains a nonempty basic open set.
\end{proof}

\begin{corollary*}[Separability of subspaces]
Every subspace of a separable metrizable space is separable.
\end{corollary*}

\begin{proof}
A countable base $\mathcal B$ for $X$ restricts to the countable base $\{B\cap A:B\in\mathcal B\}$ for a subspace
$A\IncludedIn X$. Thus $A$ is second countable, and choosing one point from each nonempty basic open set proves
that $A$ is separable. This also covers the empty subspace, whose empty subset is dense.
\end{proof}

\begin{lemma*}[Closed sets and sequences]
In a first-countable space, a set is closed iff it contains the limit of every convergent sequence drawn from it.
\end{lemma*}

\begin{proof}
A closed set contains every limit of a sequence of its points. Conversely, let $A$ contain every such limit and
let $x\in\Closure{A}$. Choose a countable neighborhood base at $x$ and replace each member by the intersection of
itself and all its predecessors to obtain a decreasing base $\Sequence{U_n}{n\in\omega}$.
Each $U_n$ meets $A$, so choose
$x_n\in A\cap U_n$. Then $x_n\to x$, and hence $x\in A$. Thus $\Closure{A}\IncludedIn A$, so $A$ is closed.
\end{proof}

\begin{proposition*}[Sequential criterion for continuity]
Let $X$ be first countable and let $Y$ be a topological space. A map $f:X\to Y$ is continuous iff it preserves
convergence of sequences. In particular, this criterion applies when $X$ and $Y$ are metrizable.
\end{proposition*}

\begin{proof}
Continuity preserves convergence: the inverse image of a neighborhood of $f(x)$ is a neighborhood of $x$.
Conversely, suppose $f$ preserves convergence, and let $C\IncludedIn Y$ be closed. If a sequence in $f^{-1}(C)$
converges to $x$, its image converges to $f(x)\in C$, since $C$ is closed. Thus $f^{-1}(C)$ contains the limit of
every convergent sequence drawn from it. The preceding lemma shows that $f^{-1}(C)$ is closed, so $f$ is continuous.
Every metrizable space is first countable: for a compatible metric, the balls $\Ball{x}{1/(n+1)}$, $n\in\omega$,
form a countable neighborhood base at $x$.
\end{proof}

## Paracompactness {#sec:appendix-metric-paracompactness}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}
\index{paracompactness}

\begin{theorem*}[Metric paracompactness]
Every open cover of a metric space has a locally finite open refinement.
\end{theorem*}

\begin{proof}
Let $(U_i)_{i\in I}$ be an open cover of $\Pair{X}{d}$, and well-order $I$.
For each $x$, let $i(x)$ be the least index with $x\in U_{i(x)}$, and put $r_n=2^{-n}$ for $n\in\NN$.
Recursively define the open sets
$$D_{n,i}=\bigcup\left\{\Ball{x}{r_n}:i(x)=i,\quad
\Ball{x}{3r_n}\IncludedIn U_i,\quad
x\notin\bigcup_{m<n}\bigcup_{j\in I}D_{m,j}\right\}.$$
Thus centers at a new level must avoid all earlier sets. Every $D_{n,i}$ is contained in $U_i$.
These sets cover $X$: given $x$, choose $n$ so large that $\Ball{x}{3r_n}\IncludedIn U_{i(x)}$.
Either an earlier set already contains $x$, or $x$ is an allowed center at level $n$ and belongs to $D_{n,i(x)}$.

To prove local finiteness, choose $x\in D_{n,i}$ and then $k$ with $\Ball{x}{r_k}\IncludedIn D_{n,i}$.
Put $N=n+k+1$ and $B=\Ball{x}{r_N}$. No $D_{m,j}$ with $m\ge N$ meets $B$.
Indeed, if $y$ belonged to their intersection, its defining center $z$ would satisfy
$$d(z,x)<r_m+r_N\le 2r_{k+1}=r_k.$$
This puts $z$ in the earlier set $D_{n,i}$, contrary to its eligibility at level $m$.

For each $m<N$, at most one $D_{m,j}$ meets $B$.
Suppose two distinct labels $j<\ell$ occurred, with points $y,z$ in the respective intersections and defining centers
$y',z'$.
Then
$$d(z',y')<2(r_m+r_N)\le 2(r_m+r_{m+1})=3r_m.$$
Consequently $z'\in U_j$, contradicting the minimality of $i(z')=\ell$.
The neighborhood $B$ therefore meets at most $N$ members of the refinement. This proves local finiteness.
\end{proof}

## Star-refinements {#sec:appendix-metric-star-refinements}
\index{star-refinement}

If $\mathcal V$ is an open cover and $V\in\mathcal V$, write
$$\operatorname{St}(V,\mathcal V):=\bigcup\{V'\in\mathcal V:V'\cap V\ne\emptyset\}.$$
An open cover $\mathcal V$ \termdefineas{star-refinement}{star-refines} an open cover $\mathcal U$ if for every
$V\in\mathcal V$ there is $U\in\mathcal U$ such that $\operatorname{St}(V,\mathcal V)\IncludedIn U$.

\begin{theorem*}[Metric star-refinement]
Every open cover of a metric space has a locally finite open star-refinement.
\end{theorem*}

\begin{proof}
The case of the empty space is immediate. If $X\in\mathcal U$, the one-element cover $\{X\}$ suffices, so assume every
member of
$\mathcal U$ is proper.
Put
$$\rho_U(x)=\min\{1,d(x,\SetDifference{X}{U})\},\qquad
\rho(x)=\sup_{U\in\mathcal U}\rho_U(x),\qquad \delta(x)=\rho(x)/2.$$
Each distance is now to a nonempty closed set. The functions $\rho_U$ take values in $\ClosedInterval{0}{1}$ and are
$1$-Lipschitz.
Taking their supremum preserves the Lipschitz bound: for every $U$,
$$\rho_U(x)\le\rho_U(y)+d(x,y)\le\rho(y)+d(x,y),$$
and then interchange $x,y$. Since the cover is open, $\rho(x)>0$.
Choose $U$ with $\rho_U(x)>\delta(x)$; then $\Ball{x}{\delta(x)}\IncludedIn U$.
Thus $\delta$ is positive and $1$-Lipschitz, and each of its radius balls refines the original cover.

Apply §{sec:appendix-metric-paracompactness} to the cover $\{\Ball{x}{\delta(x)/16}:x\in X\}$.
Let $\mathcal V$ be a locally finite open refinement of this cover. For each $V\in\mathcal V$, choose $c(V)$ with
$V\IncludedIn\Ball{c(V)}{\delta(c(V))/16}$.
If $V'\cap V\ne\emptyset$, put $a=\delta(c(V))$, $b=\delta(c(V'))$, and $t=d(c(V'),c(V))$.
An intersection point and the Lipschitz estimate give
$$t<(a+b)/16,\qquad b\le a+t.$$
Hence $b<17a/15<2a$. Every $y\in V'$ consequently satisfies
$$d(y,c(V))<b/16+t<(a+2b)/16<5a/16<a.$$
It follows that $\operatorname{St}(V,\mathcal V)\IncludedIn\Ball{c(V)}{\delta(c(V))}$, and this ball is contained in a
member of $\mathcal U$.
Thus $\mathcal V$ is the required star-refinement.
\end{proof}

## Zero Dimension {#sec:appendix-zero-dimension}

<!--
formalization: skip-begin (引用・背景説明・読書案内:
この節で証明する零次元の場合と一般論の文献を案内する範囲宣言。一般次元の比較定理を証明する箇所ではない。)
--> This section explains the dimension terminology used in §{sec:sequence-spaces}.
For metrizable spaces, we first define the three dimensions and then prove only the equivalence of their
zero-dimensional cases.
For the general theory, see [@Engelking1995].<!--
formalization: skip-end
-->

### Definitions of dimension and the zero-dimensional cases {#sec:dimension-zero-definitions}

\begin{mathmeta}
  \define{AmbientBoundary,SmallInductiveDimension,LargeInductiveDimension,CoveringDimension}
  \vars{n}{Nat}
\end{mathmeta}

For $A\IncludedIn X$, its \termdefine{boundary} in $X$ is
$$\AmbientBoundary{X}{A}:=\AmbientClosure{X}{A}\cap\AmbientClosure{X}{\SetDifference{X}{A}}.$$
For an open set $V$, this becomes
$$\AmbientBoundary{X}{V}=\SetDifference{\AmbientClosure{X}{V}}{V}.$$
Thus an open set has empty boundary exactly when it is also closed.

<!--
formalization: skip-begin (引用・背景説明・読書案内:
境界の部分空間位相と整数添字による再帰の読解指示。一般次元のwell-definednessと位相不変性はEngelking1978
Sections 1.1/1.6を明示して引用する外部背景であり局所証明ではない。)
--> In the inductive definitions below, each boundary carries the subspace topology.
The recursion is on the integer bound $n$, not on the space $X$.
The well-definedness and topological invariance of these dimensions are standard background; we refer to
Sections 1.1 and 1.6 of [@Engelking1978] for their foundations.<!--
formalization: skip-end
-->

\begin{definition*}[Small inductive dimension]
To define the \termdefine{small inductive dimension} $\SmallInductiveDimension{X}$, first define its bounds recursively.
The condition $\SmallInductiveDimension{X}\le -1$ means $X=\emptyset$.
For $n\in\NN$, the condition $\SmallInductiveDimension{X}\le n$ means that every $x\in X$ and every open neighborhood
$U$ of that point admit an open set $V$ satisfying
$$x\in V\IncludedIn U,\qquad \SmallInductiveDimension{\AmbientBoundary{X}{V}}\le n-1.$$
Set $\SmallInductiveDimension{X}$ equal to the least $n\in\{-1\}\cup\NN$ for which this bound holds, or to $\infty$ if
no such $n$ exists.
\end{definition*}

In particular, $\SmallInductiveDimension{X}\le 0$ means that each point $x$ and its open neighborhood $U$ admit an open
set $V$ with
$$x\in V\IncludedIn U,\qquad \AmbientBoundary{X}{V}=\emptyset.$$
Indeed, the boundary must have dimension $-1$, so it must be empty. Thus every open neighborhood of a point contains a
clopen neighborhood of that point.

\begin{definition*}[Large inductive dimension]
The \termdefine{large inductive dimension} $\LargeInductiveDimension{X}$ is defined in the same way, replacing points by
closed sets.
The condition $\LargeInductiveDimension{X}\le -1$ means $X=\emptyset$.
For $n\in\NN$, the condition $\LargeInductiveDimension{X}\le n$ means that every closed set $F$ and every open set $U$
containing it admit an open set $V$ with
$$F\IncludedIn V\IncludedIn U,\qquad \LargeInductiveDimension{\AmbientBoundary{X}{V}}\le n-1.$$
Again the value is the least integer bound, or $\infty$ if none exists.
\end{definition*}

Consequently, $\LargeInductiveDimension{X}\le 0$ means that a clopen set can be inserted between any closed set and any
open set containing it.

An open cover $\mathcal V$ is an \termdefine{open refinement} of an open cover $\mathcal U$ if each member of
$\mathcal V$ is contained in some member of $\mathcal U$. Both families must cover the whole space.

\begin{definition*}[Lebesgue covering dimension]
For $n\in\NN$, the condition $\CoveringDimension{X}\le n$ means that every finite open cover of $X$ has a finite open
refinement
such that each point belongs to at most $n+1$ members.
The \termdefine{Lebesgue covering dimension} $\CoveringDimension{X}$ is $-1$ when $X=\emptyset$; otherwise it is the
least $n\in\NN$
with this property, or $\infty$ if no such $n$ exists.
\end{definition*}

For $\CoveringDimension{X}\le 0$, the refinement must therefore have pairwise disjoint members.
After empty members are discarded, it is a partition into clopen sets: the complement of each member is the union of the
others.
All three dimensions are $-1$ exactly for the empty space, so for a nonempty space the corresponding bound by $0$ means
that the dimension is $0$.

### Why the conditions agree here {#sec:dimension-zero-equivalence}

\begin{proposition*}[\termdefineas{zero-dimension equivalence}{The three conditions for zero dimension}]
For a separable metrizable space $X$, the following conditions are equivalent:
$X$ has a clopen base, $\SmallInductiveDimension{X}\le 0$, $\LargeInductiveDimension{X}\le 0$, and
$\CoveringDimension{X}\le 0$.
\end{proposition*}

\begin{proof}
The empty space satisfies all four conditions, so suppose $X$ is nonempty.
The equivalence between a clopen base and $\SmallInductiveDimension{X}\le 0$ follows directly from the definition.

Suppose $X$ has a clopen base. Separability and metrizability imply second countability. A second-countable space,
and each of its open subspaces, is Lindelöf: from any open cover, for each basic open set contained in some member of
the cover, choose one such member. Cover each member of a countable base by clopen subsets and choose a countable
subcover.
Taking these subcovers together gives a countable clopen base.

Let $\mathcal U$ be any open cover. Enumerate the members of this clopen base that are contained in some member of
$\mathcal U$ as $C_0,C_1,\ldots$, allowing repetitions if the family is finite. They cover $X$. Put
$$D_n:=\SetDifference{C_n}{\bigcup_{j<n}C_j}.$$
The sets $D_n$ are clopen, pairwise disjoint, and cover $X$: each point $x$ belongs to $D_n$ for the
least $n$ with $x\in C_n$. Moreover, each $D_n$ lies in some member of $\mathcal U$.

Given a closed set $F\IncludedIn U$ with $U$ open, apply this construction to
$\{U,\SetDifference{X}{F}\}$. The union
$$V:=\bigcup\{D_n:D_n\cap F\ne\emptyset\}$$
is contained in $U$ and contains $F$. It is clopen because both it and its complement are unions of members of the
partition. Thus $\LargeInductiveDimension{X}\le 0$.

For a finite open cover $U_1,\ldots,U_r$, choose for each $n$ an index $i(n)$ with $D_n\IncludedIn U_{i(n)}$ and set
$$V_i:=\bigcup_{i(n)=i}D_n\qquad(1\le i\le r).$$
These sets form a finite pairwise disjoint open refinement. Hence $\CoveringDimension{X}\le 0$.

Conversely, $\LargeInductiveDimension{X}\le 0$ gives a clopen base by taking $F=\{x\}$, which is closed in a metrizable
space. If $\CoveringDimension{X}\le 0$, apply its defining property to $\{U,\SetDifference{X}{\{x\}}\}$, where $U$ is
an open neighborhood of $x$. The member of the disjoint refinement containing $x$ is clopen and is contained in $U$.
This also gives a clopen base and completes the proof.
\end{proof}

\begin{remark*}[Reading the examples in the main text]
In Cantor space and Baire space, fixing finitely many coordinates gives clopen cylinders. Thus both spaces have
dimension $0$ in all three senses. In contrast, the connected space $\R$ has no clopen set other than
$\emptyset$ and $\R$, so it has no clopen base. Here dimension concerns the topology, not the cardinality of the space.
\end{remark*}
