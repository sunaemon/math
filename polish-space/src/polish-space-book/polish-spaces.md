# Polish Spaces {#sec:polish-spaces}

## Definition {#sec:polish-definition}

<!-- formalization: skip (Polish-space definition lead-in; the definition is formalized as the mathlib
  PolishSpace class) -->
A topological space $X$ is a \termdefine{Polish space} if:

<!-- formalization: skip (separability and complete-metrizability clauses; the completely-metrizable
  clause is booklinked to IsCompletelyMetrizableByMetric) -->

1.  $X$ is \termdefine{separable}: there exists a countable dense subset $D \IncludedIn X$.

2.  $X$ is \termdefine{completely metrizable}: there exists a metric $d$ on $X$ such that $(X, d)$ is a complete metric
    space and $d$ induces the topology of $X$.

<!-- formalization: skip (definitional remark, not a separate proof obligation) -->
The metric is not part of the data — only the topology is. A given Polish space is typically compatible with many
distinct complete metrics, none of them canonical.

## Examples {#sec:polish-examples}

\begin{mathmeta}
  \forward{Fsigma,Gdelta}
\end{mathmeta}

*   \termdefine{Euclidean space} $\R^n$ with the standard topology. For $n=1$, the rationals $\QQ \IncludedIn \R$ are
    countable and dense in $\R$, while the standard metric $d(x, y) = |x - y|$ is complete on $\R$. The
    higher-dimensional cases use the Euclidean metric and the countable dense set $\QQ^n$.
*   The \termdefineas{irrational}{irrationals} $\SetDifference{\R}{\QQ}$ with the subspace topology from $\R$.
    The claim after Alexandrov's theorem in §{sec:alexandrov-theorem} proves that $\SetDifference{\R}{\QQ}$ is
    $\Gdelta$ in $\R$; Alexandrov's theorem then proves that this subspace is Polish.
*   Every \termdefine{infinite-dimensional separable Banach space} with its norm topology, for example $\ell^2$,
    $\ell^p$ for $1<p<\infty$, and $C[0,1]$. Separability is part of the hypothesis, and completeness is exactly the
    Banach-space condition.

<!-- formalization: skip (illustrative discussion; the criterion is Alexandrov's theorem, formalized) -->
The irrationals also illustrate that subspaces need not preserve completeness of the inherited metric: the Euclidean
metric inherited from $\R$ is not complete on $\SetDifference{\R}{\QQ}$, since Cauchy sequences of irrationals can
converge to
rationals, yet a different complete metric induces the same topology. So a non-closed Polish subspace of a Polish space
may require a metric different from the inherited one; Alexandrov's theorem in §{sec:alexandrov-theorem} gives the
general criterion for which subspaces are Polish.


## Non-examples {#sec:polish-non-examples}

<!-- formalization: skip (the rationals' non-Polishness is the example after Alexandrov's theorem
  in §{sec:alexandrov-theorem}) -->

*   The rationals $\QQ$ with the subspace topology from $\R$ are separable but *not* completely metrizable, hence not
    Polish. The example after Alexandrov's theorem in §{sec:alexandrov-theorem} proves that this space is not Polish.

*   The Banach space $\ell^\infty$ with the sup norm is complete but not separable, hence not Polish. Indeed, the binary
    sequences in $\{0,1\}^\omega$ are pairwise distance $1$ apart, so the balls of radius $1/3$ around them are pairwise
    disjoint. A countable dense set would have to meet each of these uncountably many disjoint balls, which is
    impossible.

## Key Properties {#sec:polish-key-properties}

<!-- formalization: skip (sectioning/motivation prose) -->
We record the basic closure and non-closure facts early, since they are used repeatedly in the concrete models and
coding constructions below. The deeper $\Gdelta$-characterization, Alexandrov's theorem, is proved in
§{sec:alexandrov-theorem}.

\begin{recall*}[Separability and second countability]
For metrizable spaces, separability is equivalent to second countability.
\end{recall*}

If $D$ is countable and dense, then the balls $\Ball{a}{q}$ with $a \in D$ and $q \in \RestrictedSet{\QQ}{>0}$ form a
countable base. Conversely, choosing one point from each nonempty basic open set in a countable base gives a countable
dense subset.


\begin{recall*}[Sequential criterion for first-countable spaces]
In a first-countable space, a set is closed iff it contains the limit of every convergent sequence drawn from it.
\end{recall*}

<!-- formalization: skip (remark following the recalled sequential criterion) -->
Therefore two first-countable topologies on the same set agree if they have the same convergent sequences with the same
limits.


\begin{lemma*}[\termdefineas{bounded complete compatible metric lemma}{Bounded complete compatible metric}]
If a complete metric $d$ induces the topology of $X$, then
$$
\hat d(x,y) := \min\{d(x,y),1\}
$$
is also a complete metric inducing the same topology, and $\hat d(x,y)\le 1$ for all $x,y\in X$.
\end{lemma*}

\begin{proof}[Proof]
The triangle inequality follows from
$$
\min\{d(x,z),1\}\le \min\{d(x,y)+d(y,z),1\}
\le \min\{d(x,y),1\}+\min\{d(y,z),1\}.
$$
For every $0<r<1$, the $d$-ball and the $\hat d$-ball of radius $r$ around the same center are equal. Hence $d$ and
$\hat d$ induce the same topology.

It remains to check completeness. Let $(x_n)_n$ be $\hat d$-Cauchy. Given $\epsilon>0$, choose
$0<\delta<\min\{\epsilon,1\}$. Eventually $\hat d(x_m,x_n)<\delta$, and then $d(x_m,x_n)<\delta<\epsilon$.
Thus $(x_n)_n$ is $d$-Cauchy, so it $d$-converges to some $x$. Since $\hat d\le d$, the same sequence
$\hat d$-converges to $x$.
\end{proof}


<!-- formalization: skip (sectioning/motivation prose) -->
The next closure properties are the routine ways new Polish spaces are built from old ones. The proofs all have the same
shape: keep a complete compatible metric, then check separability through second countability or countable dense sets.

\begin{proposition*}[Closed subspaces]
Closed subspaces of Polish spaces are Polish.
\end{proposition*}

\begin{proof}[Proof]
Let $X$ be a Polish space, choose a complete compatible metric $d$ on $X$, and let $C \IncludedIn X$ be closed. The
restriction $\restrict{d}{C\times C}$ induces the subspace topology and is complete: a Cauchy sequence in $C$ is Cauchy
in $X$, hence converges in $X$, and the limit lies in $C$ because $C$ is closed. Separability is hereditary for metric
spaces by the equivalence with second countability above.
\end{proof}


\begin{proposition*}[Open subspaces]
Open subspaces of Polish spaces are Polish.
\end{proposition*}

\begin{proof}[Proof]
Let $U \IncludedIn X$ be open. The case $U = X$ is trivial, so assume $U \ne X$. The restricted metric
$\restrict{d}{U\times U}$ is generally not complete, because a Cauchy sequence in $U$ may converge in $X$ to a boundary
point. Define a new metric on $U$ by
$$d'(x, y) \;:=\; d(x, y) \;+\; \left| \frac{1}{d(x,\, \SetDifference{X}{U})} - \frac{1}{d(y,\, \SetDifference{X}{U})}
\right|,$$
where $d(z,S):=\inf\{d(z,s):s\in S\}$. This is well-defined because $d(x, \SetDifference{X}{U})>0$ for every $x\in U$.
This metric induces the subspace topology. Since $d \le d'$, convergence in $d'$ implies convergence in $d$. Conversely,
suppose $x_n \to x$ in $d$ and all $x_n,x$ lie in $U$. The function $z \mapsto d(z, \SetDifference{X}{U})$ is continuous
and positive at $x$, so
$$\frac{1}{d(x_n, \SetDifference{X}{U})} \longrightarrow \frac{1}{d(x, \SetDifference{X}{U})}.$$
Hence $d'(x_n,x)\to 0$.

The metric $d'$ is complete. If $(x_n)$ is $d'$-Cauchy in $U$, then $\bigl(1/d(x_n, \SetDifference{X}{U})\bigr)_n$ is
Cauchy in $\R$ and hence bounded. Thus the points $x_n$ stay a positive distance from $\SetDifference{X}{U}$. The
sequence is also $d$-Cauchy, so it converges in $X$ to some point $x$. The positive distance from
$\SetDifference{X}{U}$ forces $x \in U$, and the preceding topology comparison gives $x_n \to x$ in $d'$. The same
second-countability argument used for closed subspaces gives separability of $U$.
\end{proof}


\begin{proposition*}[Countable disjoint unions]
Countable disjoint unions of Polish spaces are Polish.
\end{proposition*}

\begin{proof}[Proof]
Given Polish spaces $(X_n)_{n \in \NN}$, choose complete compatible metrics $d_n \le 1$ on the $X_n$. On the topological
sum $\ExternalDisjointUnion_{n \in \NN} X_n$, define
$$d((n, x), (m, y)) \;=\;
\begin{cases}
d_n(x, y), & n = m, \\
1, & n \ne m.
\end{cases}$$
This metric induces the disjoint-union topology: each summand is clopen, and balls of radius $< 1$ stay inside a single
summand. It is complete because a Cauchy sequence is eventually trapped in one summand, where it converges by
completeness of $d_n$. It is separable because a countable union of countable dense subsets is countable and dense.
\end{proof}


\begin{proposition*}[Countable products]
Countable products of Polish spaces are Polish.
\end{proposition*}

\begin{proof}[Proof]
Given Polish spaces $(X_n)_{n \in \NN}$, choose complete compatible metrics $d_n \le 1$ on the $X_n$ and define on
$\prod_{n \in \NN} X_n$
$$d\big((x_n), (y_n)\big) \;=\; \sum_{n \in \NN} 2^{-n}d_n(x_n,y_n).$$
Each summand $2^{-n}d_n(x_n,y_n)$ is at most $2^{-n}$, so the series converges, and the metric axioms follow
term by term from the metric axioms for the $d_n$. Thus $d$ is a metric.

This metric induces the product topology. Indeed, write $x^k_n$ and $x_n$ for the $n$th coordinates of $x^k$ and $x$. If
$x^k \to x$ in $d$, then for each fixed $n$,
$$2^{-n}d_n(x^k_n,x_n) \le d(x^k,x),$$
so $d_n(x^k_n,x_n)\to 0$. Thus $d$-convergence implies coordinate-wise convergence. Conversely, suppose $x^k_n \to x_n$
for every $n$. Given $\varepsilon>0$, choose $M$ so that $\sum_{n\ge M}2^{-n}<\varepsilon/2$. For the finitely many
coordinates $n<M$, choose $K$ such that whenever $k\ge K$,
$$\sum_{n<M}2^{-n}d_n(x^k_n,x_n)<\varepsilon/2.$$
Then for $k\ge K$,
$$d(x^k,x) \le \sum_{n<M}2^{-n}d_n(x^k_n,x_n)+\sum_{n\ge M}2^{-n}<\varepsilon.$$
Hence coordinate-wise convergence implies $d$-convergence. Therefore $d$ induces the product topology.

For completeness, let $(x^k)_k$ be $d$-Cauchy. Then each coordinate sequence $(x^k_n)_k$ is Cauchy for $d_n$, so it
converges to some $x_n \in X_n$. By the convergence criterion just proved, the point $x=(x_n)_n$ is the $d$-limit of
$(x^k)_k$. For separability, if the product is empty there is nothing to prove. Otherwise fix countable dense sets
$D_n \IncludedIn X_n$ and a reference point $x^* \in \prod X_n$. The countable set of sequences agreeing with $x^*$ in
all but finitely many coordinates, with the differing coordinates ranging over the corresponding $D_n$, is dense.
\end{proof}


\begin{remark*}[Important non-closure: quotients]
A quotient of a Polish space need not be Polish: the quotient topology may fail to be Hausdorff or metrizable. Likewise,
continuous images of Polish spaces are not listed as a Polish-space closure property; they belong to the later theory of
analytic sets. This is why classification problems are usually studied through their equivalence relations and Borel
reductions rather than by forming topological quotient spaces directly.
\end{remark*}

## Baire Category {#sec:baire-category}

<!-- formalization: skip-begin (Baire-category motivation and the standard nowhere-dense/meager definitions) -->
Completeness has a strong topological consequence: Polish spaces cannot be exhausted by countably many closed
nowhere-dense pieces. This is the Baire-category principle, and it is one of the main reasons complete metrizability
matters.

For Baire-category arguments, a set is \termdefineas{nowhere dense set}{nowhere dense} if the interior of its closure is
empty, \termdefineas{meager set}{meager} if it is a countable union of nowhere-dense sets, and
\termdefineas{comeager set}{comeager} if its complement is meager. All three notions depend on the ambient space; we
leave it implicit when
context fixes it.
<!-- formalization: skip-end -->


\begin{theorem*}[\termdefineas{Baire category theorem}{Theorem (Baire category)}]
Every Polish space is a \termdefineas{Baire space (category sense)}{Baire space} in the category sense: countable
intersections of dense open sets are dense. Equivalently, no nonempty open subset of a Polish space is meager in itself.
\end{theorem*}


\begin{proof}[Proof] Let $X$ be Polish, fix a complete compatible metric $d$, let $U\IncludedIn X$ be nonempty open, and
let $(G_n)_{n\in\omega}$ be dense open subsets of $U$ in the relative topology. We show that $U\cap\bigcap_n G_n$ is
nonempty.

Construct nonempty open sets $V_n\IncludedIn U$ recursively so that
$$
\begin{aligned}
\Closure{V_{n+1}} &\IncludedIn V_n\cap G_n,\\
\MetricDiameter{d}{\Closure{V_n}} &\le 2^{-n}.
\end{aligned}
$$
Start with any nonempty open $V_0\IncludedIn U$ whose closure has diameter at most $1$. Given $V_n$, the set $V_n\cap
G_n$ is nonempty because $G_n$ is dense in $U$. Since $U$ is open in $X$, the set $V_n\cap G_n$ is open in $X$, so it
contains a ball $\Ball{x}{r_0}$ contained in $V_n\cap G_n$. Choose $0<r<r_0$ small enough that
$\Closure{\Ball{x}{r}}\IncludedIn \Ball{x}{r_0}$ and $\MetricDiameter{d}{\Closure{\Ball{x}{r}}}\le 2^{-(n+1)}$, and put
$V_{n+1}:=\Ball{x}{r}$.

Pick $x_n\in V_n$. The nesting and diameter bounds make $(x_n)$ Cauchy: for $m\ge n$, both $x_m$ and $x_n$ lie in
$\Closure{V_n}$, whose diameter is at most $2^{-n}$. Completeness gives a limit $x\in X$. Since each $\Closure{V_n}$ is
closed and contains the tail of the sequence, $x\in\Closure{V_n}$ for every $n$. The nesting also gives
$\Closure{V_{n+1}}\IncludedIn G_n$, so $x\in G_n$ for every $n$, and $x\in U$. Thus $U\cap\bigcap_n G_n\ne\emptyset$.
Since $U$ was an arbitrary nonempty open set, $\bigcap_n G_n$ is dense in $X$.

Now suppose a nonempty open $U$ were meager in itself, say $U=\bigcup_n N_n$ with each $N_n$ nowhere dense in $U$. Then
$\SetDifference{U}{\AmbientClosure{U}{N_n}}$ is dense open in $U$ for each $n$, so the first part gives a point in their
intersection, contradicting $U=\bigcup_n N_n$.
\end{proof}

\begin{mathmeta}
  \forward{BaireSpace}
\end{mathmeta}

<!-- formalization: skip (terminology clarification, not a proof obligation) -->
This use of "Baire" is distinct from the specific \termforward{Baire space} $\BaireSpace$ introduced in
§{sec:sequence-spaces}. The theorem says every Polish space is a
\termuseas{Baire space (category sense)}{Baire space} in the category sense; Baire space is one particular Polish space
that serves as a universal coding space.

## Alexandrov's Theorem {#sec:alexandrov-theorem}

\begin{mathmeta}
  \define{Fsigma,Gdelta}
\end{mathmeta}

A subset of a topological space is \termdefineas{Fsigma set@$\Fsigma$ set}{$\Fsigma$} if it is a countable union of
closed sets, and \termdefineas{Gdelta set@$\Gdelta$ set}{$\Gdelta$} if it is a countable intersection of open sets.


\begin{theorem*}[\termdefineas{Alexandrov's theorem}{Theorem (Alexandrov)}]
Let $X$ be a Polish space and $A \IncludedIn X$. Then $A$ is Polish in the subspace topology if and only if $A$ is
$\Gdelta$ in $X$.

\end{theorem*}


<!-- formalization: skip (prose restatement of Alexandrov's theorem, which is itself formalized) -->
Thus $\Gdelta$ subsets are exactly the Polish subspaces of Polish spaces. This is why the irrationals are Polish
although the inherited Euclidean metric on $\SetDifference{\R}{\QQ}$ is incomplete.

\begin{proof}[Proof]

\textbf{From $\Gdelta$ to Polish.} Write
$$A = \bigcap_{n \in \NN} U_n$$
with each $U_n \IncludedIn X$ open. By the open-subspace result above, each $U_n$ is Polish. Choose a complete
compatible metric $d_n \le 1$ on each $U_n$.
Replacing any complete compatible $\rho_n$ by $d_n=\min\{\rho_n,1\}$ preserves small balls and Cauchy sequences.

The diagonal embedding
$$\iota : A \to \prod_{n} U_n, \qquad \iota(x) = (x, x, x, \ldots)$$
is a homeomorphism onto its image. The product $\prod_n U_n$ is Polish.

We show that $\iota(A)$ is closed in $\prod_n U_n$. Suppose
$$\iota(a^k)=(a^k,a^k,\ldots)$$
converges in the product to $(b_1,b_2,\ldots)$. Then $a^k \to b_n$ in each $U_n$, hence also in $X$. Since $X$ is
Hausdorff, limits in $X$ are unique, so all $b_n$ are one and the same point $x$. Because $x=b_n \in U_n$ for every $n$,
we have $x \in A$, and the limit point is $\iota(x)$.

Thus $\iota(A)$ is closed. Hence $A$ is homeomorphic to a closed subspace of a Polish space, and is Polish.

\textbf{From Polish to $\Gdelta$.} Suppose $A$ carries a complete metric $\rho$ inducing the subspace topology from $X$,
and fix a complete compatible metric $d$ on $X$. For each $n \ge 1$, using explicit $d$-balls in $X$, define
$$V_n \;=\; \bigcup\, \{\MetricBall{d}{x}{\delta} \,:\, x \in X,\; \delta > 0,\;
\MetricDiameter{\rho}{\MetricBall{d}{x}{\delta} \cap A} < 1/n\},$$
a union of open $d$-balls in $X$. Hence each $V_n$ is open. Since $\rho$ induces the subspace topology on $A$, every
point of $A$ has arbitrarily small $X$-neighborhoods whose trace on $A$ has small $\rho$-diameter, so
$A \IncludedIn V_n$ for every positive integer $n$.

We claim $A = \AmbientClosure{X}{A} \cap \bigcap_{n\ge 1} V_n$, where $\AmbientClosure{X}{A}$ denotes the closure of $A$
in $X$.
The closure factor excludes points away from $A$; the $V_n$'s force nearby traces of $A$ to have vanishing
$\rho$-diameter.

The inclusion $A \IncludedIn \AmbientClosure{X}{A} \cap \bigcap_{n\ge 1} V_n$ follows immediately from the preceding
paragraph.

For the reverse inclusion, take
$$x \in \AmbientClosure{X}{A} \cap \bigcap_{n\ge 1} V_n.$$
For each positive integer $n$, choose an open neighborhood $B_n$ of $x$ in $X$ such that
$$\MetricDiameter{\rho}{B_n \cap A} < 1/n.$$
Replacing $B_n$ by
$$B_1 \cap \cdots \cap B_n \cap \MetricBall{d}{x}{1/n},$$
we may assume
$$B_1 \supseteq B_2 \supseteq \cdots
\qquad\text{and}\qquad
\MetricDiameter{d}{B_n}\to 0.$$
Since $x \in \AmbientClosure{X}{A}$, every $B_n$ meets $A$. Choose $a_n \in B_n \cap A$.

The sequence $(a_n)$ is $\rho$-Cauchy because the $\rho$-diameters of the traces $B_n \cap A$ tend to $0$. Since $\rho$
is complete, $a_n \to a$ in $\rho$ for some $a \in A$. The $\rho$-topology agrees with the subspace topology, so $a_n
\to a$ in $X$. On the other hand, $\MetricDiameter{d}{B_n}\to 0$ and $a_n \in B_n$ force $a_n \to x$ in $X$. Uniqueness
of limits in the metric space $X$ gives $a=x$, hence $x \in A$.

The set $\AmbientClosure{X}{A}$ is closed, and closed subsets of metric spaces are $\Gdelta$. Also, $\bigcap_n V_n$ is
$\Gdelta$ because each $V_n$ is open. Therefore
$$A=\AmbientClosure{X}{A}\cap\bigcap_n V_n$$
is $\Gdelta$ in $X$.
\end{proof}

\begin{claim*}[Examples in $\R$ with the usual topology]
The rationals $\QQ$ are $\Fsigma$ but not $\Gdelta$, and the irrationals $\SetDifference{\R}{\QQ}$ are $\Gdelta$ but not
$\Fsigma$.
\end{claim*}


\begin{proof}[Proof]
The rationals $\QQ = \bigcup_{q \in \QQ} \{q\}$ are $\Fsigma$, since singletons are closed. They are not $\Gdelta$:
$\QQ$ is meager, since each singleton is closed and nowhere dense, while a dense $\Gdelta$ subset of $\R$ is comeager
by the \termuse{Baire category theorem} in §{sec:baire-category}. If $\QQ$ were $\Gdelta$, it would be both meager and
comeager, so its complement $\SetDifference{\R}{\QQ}$ would also be meager. Then $\R$ would be a union of two
\termuseas{meager set}{meager sets}, contradicting the Baire category theorem. By duality, the irrationals
$\SetDifference{\R}{\QQ}$ are $\Gdelta$ but not $\Fsigma$.
\end{proof}

<!-- formalization: skip (discussion linking the example/non-example to Alexandrov's theorem) -->
Thus \termuse{Alexandrov's theorem} proves that $\SetDifference{\R}{\QQ}$ is Polish in the subspace topology, while
$\QQ$ is not
Polish in the subspace topology. This supplies the example and non-example recorded at the start of the chapter.


## Sequence Spaces {#sec:sequence-spaces}

\begin{mathmeta}
  \define{BaireSpace,CantorSpace,HilbertCube,RealSequenceSpace}
\end{mathmeta}

<!-- formalization: skip (dimension-convention framing) -->
We use the following dimension convention from this point on.

A space is \termdefine{zero-dimensional} if it has a base
of clopen sets.

<!-- formalization: skip (small/large-inductive and covering-dimension agreement cited to Engelking) -->
Since every Polish space is separable and metrizable, this agrees on Polish spaces with the standard
small inductive, large inductive, and covering-dimension notions at dimension $0$. We do not otherwise use finite- or
infinite-dimensional dimension theory; see [@Engelking1995] for the general background.


<!-- formalization: skip-begin (perfect-space definition and the product-space preamble) -->
A space is \termdefineas{perfect space}{perfect} if it has no isolated points.


Here $2$ and $\omega$ are countable discrete spaces, hence Polish because their discrete metrics are complete and the
spaces are countable. Also $[0,1]$ is a closed subspace of $\R$, and $\R$ itself is Polish. Hence the countable product
theorem gives the following standard Polish product spaces, each with the product topology:
<!-- formalization: skip-end -->

*   The \termdefine{Cantor space} $\CantorSpace$. Brouwer's characterization identifies it as the compact
    zero-dimensional \termuseas{perfect space}{perfect} model.
*   The \termdefine{Baire space} $\BaireSpace$. The Alexandrov–Urysohn characterization identifies it as the
    nowhere locally compact analogue of Cantor space.
*   The \termdefine{Hilbert cube} $\HilbertCube$. The Hilbert cube is moreover compact by Tychonoff, and it is the
    universal compact target for Polish spaces: every Polish space is homeomorphic to a subspace of $\HilbertCube$.
*   The \termdefine{space of real sequences} $\RealSequenceSpace$. Anderson's theorem gives a homeomorphism
    $\RealSequenceSpace\cong \ell^2$, and Anderson--Kadec says that every infinite-dimensional separable Fréchet
    space, hence every infinite-dimensional separable Banach space, is homeomorphic to $\ell^2$; see
    [@BessagaPelczynski1975] for the infinite-dimensional topology behind these statements. Thus every
    infinite-dimensional separable Banach space from §{sec:polish-examples} is homeomorphic to
    $\RealSequenceSpace$.

<!-- formalization: skip-begin (separating-invariants discussion and comparison table) -->
The following quick invariants separate the four examples up to homeomorphism. Tychonoff's theorem makes $\CantorSpace$
and $\HilbertCube$ compact, because $2$ and $[0,1]$ are compact. The spaces $\BaireSpace$ and
$\RealSequenceSpace$ are not compact: if either product were compact, then each coordinate projection would have
compact image, forcing $\omega$ or $\R$ to be compact. Zero-dimensionality separates the Cantor/Baire models from the
Hilbert-cube/real-sequence models: $\CantorSpace$ and $\BaireSpace$ have clopen cylinder bases, while
$\HilbertCube$ and $\RealSequenceSpace$ are nontrivial connected products and hence not zero-dimensional.


| space | compact? | zero-dimensional? | connected? |
|---|---:|---:|---:|
| $\CantorSpace$ | yes | yes | no |
| $\BaireSpace$ | no | yes | no |
| $\HilbertCube$ | yes | no | yes |
| $\RealSequenceSpace$ | no | no | yes |

These sequence spaces are not isolated examples. They are the main coordinate systems of the theory: Cantor space for
compact zero-dimensional behavior, Baire space for general coding by finite information, the Hilbert cube for compact
embeddings, and $\RealSequenceSpace$ for infinite-dimensional separable analysis. Baire space plays the central role,
because every Polish space can be represented by Cauchy names in a subspace of $\BaireSpace$.

<!-- formalization: skip-end -->
