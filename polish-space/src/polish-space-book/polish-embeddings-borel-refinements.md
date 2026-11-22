# Polish Embeddings and Borel-Preserving Refinements {#sec:polish-embeddings-refinements}

<!-- formalization: skip-begin (chapter motivation, scope, and reference) -->
The Cauchy representations in §{sec:cauchy-representation-admissibility} describe points by infinite sequences while
retaining the original topology; a point can have more than one name. This chapter asks what changes if we seek a
one-to-one representation. We first embed a Polish space into the \termuse{Hilbert cube} $\HilbertCube$, preserving
its topology. We then keep only its Borel structure fixed and obtain a closed presentation in $\BaireSpace$.

The main step is a \termdefine{Borel-preserving refinement}: we add open sets while keeping the topology Polish and
leaving its Borel $\sigma$-algebra unchanged. A zero-dimensional refinement admits a closed Baire-space presentation,
in which points correspond to branches of a tree. This completes the passage from a general Polish space to a space
of codes on which Borel questions can be studied. We then examine two applications of refinement, to stochastic
processes and discrete-time dynamics. The systematic reference is [@Kechris1995, §§4, 13].
<!-- formalization: skip-end -->

## The Hilbert Cube and Universal Compact Embedding {#sec:hilbert-cube-embedding}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}

<!-- formalization: skip (background on the Hilbert cube beyond its role in the theorem) -->
Recall the \termuse{Hilbert cube} $\HilbertCube$ from §{sec:sequence-spaces}. Classically it is an
infinite-dimensional compact metrizable space, and it has a rich topological characterization theory. None of that
dimension theory is used here: its role is only that it is a compact Polish product large enough to contain every Polish
space as a $\Gdelta$ subspace.

\begin{theorem*}[\termdefine{Hilbert-cube embedding}] Every Polish space $X$ is homeomorphic to a $\Gdelta$ subset of
$\HilbertCube$.

\end{theorem*}

\begin{proof}[Proof] The empty space is homeomorphic to the empty $\Gdelta$ subset of $\HilbertCube$, so assume that
$X$ is nonempty. By the \termuse{bounded complete compatible metric lemma} in §{sec:polish-key-properties}, choose a
complete compatible metric $d\le 1$. Fix a countable dense $\IndexedFamily{x_n}{n\in\omega} \IncludedIn X$ and define
$$\iota : X \to \HilbertCube, \qquad \iota(x) \;=\; \Sequence{d(x, x_n)}{n\in\omega}.$$
Each coordinate is $1$-Lipschitz, so $\iota$ is continuous.

\emph{Injective.} If $x \ne y$, pick $x_n$ with $d(x_n, x) < d(x,y)/2$. The triangle inequality gives $d(x_n, y) >
d(x,y)/2$, so $\iota(x)_n \ne \iota(y)_n$.

\emph{Inverse continuous on $\iota(X)$.} Suppose $\iota(y_k) \to \iota(y)$ in $\HilbertCube$. Given
$\varepsilon > 0$, pick $x_n$ with $d(x_n, y) < \varepsilon/3$. Coordinatewise convergence gives
$d(y_k, x_n) \to d(y, x_n) < \varepsilon/3$, so for $k$ large
$d(y_k, y) \le d(y_k, x_n) + d(x_n, y) < \varepsilon$.

Thus $\iota$ is a homeomorphism onto $\iota(X)$. The image is Polish, so by \termuse{Alexandrov's theorem} in
§{sec:alexandrov-theorem} it is $\Gdelta$ in $\HilbertCube$.
\end{proof}

<!-- formalization: skip-begin (transition from topological embedding to Borel coding) -->
The Hilbert-cube embedding preserves all the original topological information. A closed presentation in
$\BaireSpace$ requires a different choice: every subspace of $\BaireSpace$ is zero-dimensional, so a general Polish
space cannot embed there without a change of topology. For questions about Borel sets and Borel maps, we can allow
such a change as long as the Borel $\sigma$-algebra is preserved.
<!-- formalization: skip-end -->

## Polish Topology Refinement {#sec:polish-topology-refinement}

\begin{mathmeta}
  \vars{k,m,n}{Nat}
\end{mathmeta}

<!-- formalization: skip-begin (motivation for topology refinement) -->
The Borel structure of a Polish space does not determine a unique topology. It determines a whole family of compatible
Polish topologies, and refining the topology is often the cleanest way to turn Borel information into clopen or
continuous information without changing any Borel sets. This is a controlled operation: new open sets are added only
from the old Borel $\sigma$-algebra, and the resulting topology is still Polish.

The basic refinement result is the following.
<!-- formalization: skip-end -->

\begin{theorem*}[\termdefine{Kuratowski's refinement theorem}] Let $\Pair{X}{\tau}$ be Polish and let
$\IndexedFamily{B_n}{n\in\omega}$
be a countable family of $\tau$-Borel subsets. There exists a Polish topology $\tau'\supseteq\tau$ on $X$ such that

\begin{enumerate}
\item $\mathcal B(\tau')=\mathcal B(\tau)$;
\item each $B_n$ is clopen in $\tau'$;
\item moreover, $\tau'$ may be chosen zero-dimensional.
\end{enumerate}

\end{theorem*}

\begin{proof}[Proof]
We first record a joining observation. Suppose $\Sequence{\tau_m}{m\in\omega}$ is a countable sequence of Polish
topologies on $X$ such that each $\tau_m$ refines $\tau$ and $\mathcal B(\tau_m)=\mathcal B(\tau)$. Let $\tau_\infty$ be
the topology induced by the diagonal map
$$
x\longmapsto \Tuple{x,x,x,\ldots}
$$
from $X$ into $\prod_m \Pair{X}{\tau_m}$. The diagonal image is closed. Indeed, if two coordinates have distinct values,
the
original Hausdorff topology $\tau$ separates them by disjoint open sets, and these sets are open in the corresponding
$\tau_m$'s. Hence $\tau_\infty$ is Polish by the closed-subspace and countable-product results of
§{sec:polish-key-properties}. It refines every $\tau_m$. Conversely, its diagonal model has a countable base of
finite-coordinate boxes. Each such box pulls back to a finite intersection of sets open in some $\tau_m$'s and is
therefore $\tau$-Borel. Every $\tau_\infty$-open set is a countable union of these basic sets, so
$\mathcal B(\tau_\infty)=\mathcal B(\tau)$. If every $\tau_m$ is zero-dimensional, finite-coordinate clopen boxes form
a base of the product, and their traces form a clopen base of the diagonal subspace. Thus $\tau_\infty$ is
zero-dimensional.

Next prove the one-set case. Let $\mathcal C$ be the class of $\tau$-Borel sets $B\IncludedIn X$ for which there is a
Polish topology $\tau_B\supseteq\tau$ satisfying $\mathcal B(\tau_B)=\mathcal B(\tau)$ and making $B$ clopen. We show
that $\mathcal C$ is a $\sigma$-algebra containing every $\tau$-open set.

If $B$ is $\tau$-open, then $B$ is Polish by §{sec:polish-key-properties}, and $\SetDifference{X}{B}$ is closed, hence
Polish.
Put on $X$ the topological sum of the two subspaces $B$ and $\SetDifference{X}{B}$. This topology refines $\tau$, makes
$B$ clopen, and is Polish by the countable-disjoint-union result of §{sec:polish-key-properties}. It has the same Borel
sets as $\tau$, because its open sets are unions of relatively open subsets of $B$ and $\SetDifference{X}{B}$, all of
which are $\tau$-Borel.

The class $\mathcal C$ is closed under complements, since a topology that makes $B$ clopen also makes
$\SetDifference{X}{B}$
clopen. Now suppose $B=\bigcup_m B_m$ with each $B_m\in\mathcal C$. Choose $\tau_m$ making $B_m$ clopen, and form the
joined topology $\tau_\infty$ above. Then every $B_m$ is clopen in $\tau_\infty$, so $B$ is $\tau_\infty$-open. Apply
the open-set case, now with $\tau_\infty$ as the starting Polish topology, to obtain a further Polish refinement making
$B$ clopen and preserving the same Borel $\sigma$-algebra. Hence $B\in\mathcal C$. Therefore $\mathcal C$ is a
$\sigma$-algebra containing $\tau$, so it contains every $\tau$-Borel set.

For the given countable family $\{B_n\}$, choose for each $n$ a Polish refinement $\tau_n$ with the same Borel sets in
which $B_n$ is clopen. The joined topology $\tau'$ from the first paragraph is Polish, refines $\tau$, has $\mathcal
B(\tau')=\mathcal B(\tau)$, and makes every $B_n$ clopen.

It remains to prove the zero-dimensional addendum. We show that any Polish topology admits a zero-dimensional
Polish refinement with the same Borel sets. Choose a countable base $\{U_k\}$ for $\tau$ and let
$$
e:X\to X\times \CantorSpace,\qquad e(x)=\Pair{x}{\Sequence{\mathbf 1_{U_k}(x)}{k\in\omega}},
$$
and give $X$ the topology pulled back from the product. This topology is generated by the sets $U_k$ and
$\SetDifference{X}{U_k}$, so it is zero-dimensional and refines $\tau$. Its image is the set of all $\Pair{x}{a}$
satisfying,
for every $k$,
$$
a(k)=1\Longleftrightarrow x\in U_k.
$$
For each $k$, write $C^1_k=\{a:a(k)=1\}$ and $C^0_k=\{a:a(k)=0\}$. The $k$th condition is
$$
\bigl(U_k\times C^1_k\bigr)\cup\bigl((\SetDifference{X}{U_k})\times C^0_k\bigr),
$$
a $\Gdelta$ subset of $X\times \CantorSpace$. The first piece is open, while the second is closed and hence $\Gdelta$ by
§{sec:alexandrov-theorem}; finite unions of $\Gdelta$ sets are $\Gdelta$. Thus the image of $e$ is $\Gdelta$ in
$X\times \CantorSpace$, and the pulled-back topology is Polish. It has the countable $\tau$-Borel subbasis
$\{U_k,\SetDifference{X}{U_k}:k\in\omega\}$. Hence every new open set is a countable union of finite intersections of
$\tau$-Borel sets, so its Borel sets are still $\mathcal B(\tau)$.

Apply this construction to the topology $\tau'$ already obtained for the family $\{B_n\}$. The resulting topology
is finer than $\tau'$, so every $B_n$ remains clopen. It is zero-dimensional and Polish and has the same Borel sets,
which proves the addendum.
\end{proof}

\begin{corollary*}[\termdefine{Borel maps become continuous}] Let $f:X\to Y$ be a Borel map between Polish spaces. There
is a Polish topology $\tau'\supseteq\tau_X$ on $X$ with the same Borel $\sigma$-algebra in which $f$ is continuous.

\end{corollary*}

\begin{proof}[Proof] Apply \termuse{Kuratowski's refinement theorem} to the countable family
$\{f^{-1}(V_n):n\in\omega\}$, where $\{V_n\}$ is a countable base of $Y$. In the refined topology these preimages are
clopen, so $f$ has open preimages of basic opens.
\end{proof}

<!-- formalization: skip (transition to two derived variants) -->
Two small variants are used implicitly.

*   **Several maps at once.** If $f_m:X\to Y_m$ is a countable family of Borel maps into Polish spaces, refine with
    respect to all sets $f_m^{-1}(V^m_k)$, where $\IndexedFamily{V^m_k}{k\in\omega}$ is a base of $Y_m$. Then every
    $f_m$ is continuous in the
    same refined topology.
*   **Making a Borel subspace open or closed.** If $B\IncludedIn X$ is Borel, include $B$ in the family. Then $B$
    becomes clopen, so it is a Polish subspace in the refined topology. This is the step used in the reduction in the
    proof of the \termforward{Lusin--Suslin theorem} in §{sec:lusin-souslin-proof}.

## Closed Presentation in Baire Space {#sec:closed-presentation-baire}

<!-- formalization: skip (transition from refinement to the Baire-space presentation) -->
We now use the zero-dimensional refinement to construct the desired closed presentation. Successive clopen
partitions give finite prefixes, and a point is determined by the unique branch of pieces containing it.

\begin{corollary*}[\termdefineas{closed presentation in Baire space}{Closed presentation in Baire space}] After a
\termuseas{Borel-preserving refinement}{Borel-preserving Polish refinement}, every Polish space is homeomorphic to a
closed subspace of $\BaireSpace$. More precisely, every zero-dimensional Polish space is homeomorphic to a closed subset
of $\BaireSpace$.

\end{corollary*}

\begin{proof}[Proof] First prove the zero-dimensional statement. The empty space is homeomorphic to the empty closed
subset of $\BaireSpace$, so assume that $X$ is nonempty. Fix a complete compatible metric $d\le 1$. To obtain a
countable clopen base, cover each member of a countable base by clopen subsets contained in it, take a countable
subcover by Lindelöfness, and unite these subcovers. Recursively build countable clopen partitions $\mathcal P_n$ of $X$
such that:

\begin{enumerate}
\item $\mathcal P_0=\{X\}$;
\item $\mathcal P_{n+1}$ refines $\mathcal P_n$;
\item every member of $\mathcal P_n$ has $d$-diameter at most $2^{-n}$;
\item every $P\in\mathcal P_n$ is the disjoint union of the members of $\mathcal P_{n+1}$ contained in $P$.
\end{enumerate}

Given $\mathcal P_n$, cover each $P\in\mathcal P_n$ by countably many clopen subsets of diameter at most $2^{-(n+1)}$,
then disjointify the cover inside $P$ and discard the empty differences. This gives the next partition.

Index the refinement tree by finite sequences: the root is $X$, and the children of a node are the clopen pieces into
which it is partitioned at the next stage. Let $T\IncludedIn\finseq{\omega}$ be the set of finite sequences that
occur. Every retained piece is nonempty and is covered by the next partition, so it has a nonempty successor. Thus $T$
is a pruned subtree of $\finseq{\omega}$, and its body $\TreeBody{T}$ is closed in $\BaireSpace$ by
§{sec:closed-sets-trees}. The family of pieces indexed by $T$ has root $X$, splits each piece into a disjoint union of
its successors, and gives every level-$n$ piece diameter at most $2^{-n}$. The
\termuseas{clopen scheme lemma}{clopen-scheme lemma} of §{sec:clopen-scheme-characterizations} therefore gives
$X\cong\TreeBody{T}$.

For a general Polish space $\Pair{X}{\tau}$, use the zero-dimensional conclusion of
\termuse{Kuratowski's refinement theorem}. The refined topology $\tau'$ is Polish, has the same Borel
$\sigma$-algebra, is finer than $\tau$, and is zero-dimensional. The zero-dimensional statement then embeds
$\Pair{X}{\tau'}$ as a closed subspace of $\BaireSpace$.
\end{proof}

<!-- formalization: skip (consequences of changing only the compatible Polish topology) -->
The construction gives a bijection between the original space and the branches of a pruned tree, preserving the
\termuse{standard Borel space}. Thus Borel subsets and Borel maps can be transferred to the closed subspace of
$\BaireSpace$, where finite prefixes and trees are available. It also preserves Borel equivalence relations and
\termuse{Borel reducibility}. Unlike the Cauchy representation of §{sec:cauchy-representation-admissibility}, this
presentation assigns one code to each point; the price is that it preserves the Borel structure rather than the
original topology.

## Standard Borel Spaces and the Family of Compatible Polish Topologies {#sec:standard-borel-many-polish}

\begin{mathmeta}
  \vars{n}{Nat}
\end{mathmeta}

<!-- formalization: skip (structural reading of the refinement results) -->
Read in the direction of the proofs, \termuse{Kuratowski's refinement theorem} and the two corollaries above build a
finer topology from a chosen countable family of Borel sets and Borel maps. Read structurally, they say that a
\termuse{standard Borel space} $\Pair{X}{\mathcal B}$ in the sense of §{sec:standard-borel-spaces} admits a whole
family of compatible Polish topologies, rich enough to make any countable Borel arrangement clopen, any countable Borel
map continuous, or the whole topology zero-dimensional.

\begin{theorem*}[\termdefineas{compatible Polish topologies theorem}{Compatible Polish topologies}] Let
$\Pair{X}{\mathcal
B}$ be a \termuse{standard Borel space}. Then:

\begin{enumerate}
\item (Refinement.) For any countable subfamily $\IndexedFamily{B_n}{n\in\omega} \IncludedIn \mathcal B$, there is a
zero-dimensional Polish topology $\tau$ on $X$ with $\mathcal B(\tau) = \mathcal B$ in which every $B_n$ is clopen.
\item (Closed presentation.) With such a choice of $\tau$, the space $X$ is homeomorphic to a closed subspace of
$\BaireSpace$.
\item (Continuity refinement.) For any countable family of Borel maps $f_m : X \to Y_m$ to Polish spaces, some Polish
topology on $X$ generating $\mathcal B$ makes every $f_m$ continuous.
\end{enumerate}

\end{theorem*}

\begin{proof}[Proof] By definition of standard Borel, fix any Polish topology $\tau_0$ on $X$ with
$\mathcal B(\tau_0) = \mathcal B$. From there, (1) is the zero-dimensional form of
\termuse{Kuratowski's refinement theorem} applied to $\tau_0$ and $\{B_n\}$. Apply the zero-dimensional part of
\termuse{closed presentation in Baire space} to that same topology to obtain (2); the $B_n$ remain clopen. Finally, (3)
is the countable-map variant of \termuse{Borel maps become continuous}.
\end{proof}

<!-- formalization: skip-begin (the structure preserved by coding) -->
A \termuseas{Borel-preserving refinement}{Borel-preserving Polish refinement} lets us make countably many Borel sets
clopen or countably many Borel maps into fixed Polish spaces continuous. Borel sets and Borel reducibility
are preserved, but continuous reducibility and Wadge degrees need not be. For example, a Borel set that was not open
can become clopen after refinement. Arguments about these topological notions must therefore keep track of the chosen
topology.
<!-- formalization: skip-end -->

## Applications of Refinement {#sec:refinement-applications}

<!-- formalization: skip (transition from coding to applications) -->
The closed presentation above makes Borel questions accessible through sequences and trees. Refinement also lets us
apply topological arguments directly to Borel sets and Borel maps. The first example uses compactness to obtain
continuity in the original topology on a large set; the second makes a Borel evolution into a homeomorphism.

### Stochastic Processes {#sec:refinement-stochastic-processes}

\begin{mathmeta}
  \vars{K}{Nat}
\end{mathmeta}

<!-- formalization: skip-begin (transition to the following Lusin theorem example) -->
The next example uses compactness to recover continuity in the original topology on a set of large probability.
<!-- formalization: skip-end -->

\begin{example*}[Continuous dependence of sample paths on a set of large probability]
Let $\Pair{\Omega}{\tau}$ be Polish, let $\mathbb P$ be a Borel probability measure on it, and let
$$
X:\Omega\to C(\ClosedInterval{0}{1}),\qquad X(\omega)(t)=X_t(\omega),
$$
be Borel measurable, where $C(\ClosedInterval{0}{1})$ has the uniform topology. Thus each sample path is already
continuous in time;
the map from a sample point to its entire path need not be continuous. For every $0<\varepsilon<1$, there is a
$\tau$-compact set $K\IncludedIn\Omega$ with $\mathbb P(K)>1-\varepsilon$ such that $\restrict{X}{K}$ is continuous in
the
original topology.

To prove this, refine $\tau$ to a Polish topology $\tau'$ making $X$ continuous and preserving the Borel sets. The same
$\mathbb P$ is still a Borel probability measure. We use the fact that a Borel probability measure on a Polish space
has compact sets of arbitrarily large probability, proved as \termforwardas{Ulam theorem}{Ulam's theorem} in
§{sec:borel-measures-radon}. Choose a $\tau'$-compact $K$ with $\mathbb P(K)>1-\varepsilon$. The identity map
$$
\Pair{K}{\restrict{\tau'}{K}}\longrightarrow\Pair{K}{\restrict{\tau}{K}}
$$
is a continuous bijection from a compact space to a Hausdorff space, hence a homeomorphism. Thus the two subspace
topologies agree on $K$, and $\restrict{X}{K}$ is continuous for the original topology as well.

In particular, $X(K)$ is compact in $C(\ClosedInterval{0}{1})$. The paths on $K$ are uniformly bounded and share a
common modulus of
continuity:
$$
\sup\{\Abs{X_t(\omega)}:\omega\in K,\ t\in\ClosedInterval{0}{1}\}<\infty,
$$
$$
\lim_{\delta\downarrow0}\sup\{\Abs{X_t(\omega)-X_s(\omega)}:
\omega\in K,\ s,t\in\ClosedInterval{0}{1},\ \Abs{t-s}\le\delta\}=0.
$$
Indeed, evaluation is continuous for the uniform topology, so $\Pair{\omega}{t}\mapsto X_t(\omega)$ is continuous on the
compact metric space $K\times\ClosedInterval{0}{1}$. It is therefore bounded and uniformly continuous, giving both
assertions.
After excluding an event of probability less than $\varepsilon$, we have simultaneous control of the sizes and time
variations of all remaining sample paths. The refinement changes the topology on the sample space; continuity of each
individual sample path in time was an assumption throughout.
\end{example*}

### Discrete-Time Dynamics {#sec:refinement-dynamics}

\begin{mathmeta}
  \vars{k,m}{Nat}
\end{mathmeta}

For a map from a space to itself, both the domain and the codomain acquire the new topology. A single application of
the continuity-refinement corollary only gives continuity into the old codomain topology. We resolve this by refining
repeatedly, making the inverse images of each stage's open sets open at the next stage.

\begin{lemma*}[\termdefineas{iterated continuity refinement lemma}{Iterated continuity refinement}]
Let $\Pair{X}{\tau}$ be Polish and let $\Sequence{f_m}{m\in\omega}$ be a countable family of Borel maps from $X$ to
itself.
There is a Polish topology $\tau_*\supseteq\tau$ with $\mathcal B(\tau_*)=\mathcal B(\tau)$ such that every
$$
f_m:\Pair{X}{\tau_*}\to\Pair{X}{\tau_*}
$$
is continuous.
\end{lemma*}

\begin{proof}[Proof]
Start with $\tau_0=\tau$. Suppose that a Polish topology $\tau_n$ with the same Borel sets has been constructed.
Choose a countable base $\{U_{n,k}:k\in\omega\}$ for $\tau_n$. Each $f_m$ is Borel for $\tau_n$, since its Borel
$\sigma$-algebra agrees with the original one. Apply \termuse{Kuratowski's refinement theorem} to the countable family
$$
\{f_m^{-1}(U_{n,k}):m,k\in\omega\}
$$
to obtain a Polish topology $\tau_{n+1}\supseteq\tau_n$ with the same Borel sets in which these sets are clopen.
Then each $f_m:\Pair{X}{\tau_{n+1}}\to\Pair{X}{\tau_n}$ is continuous.

Let $\tau_*$ be the topology generated by $\bigcup_n\tau_n$. The joining argument in the proof of
\termuse{Kuratowski's refinement theorem} identifies it with the topology induced by the diagonal map into
$\prod_n(X,\tau_n)$. The image is closed because the common Hausdorff topology $\tau$ separates any two unequal
coordinates, so $\tau_*$ is Polish. Finite-coordinate basic open sets pull back to finite intersections of
$\tau$-Borel sets, and there are countably many such basic sets. Hence every $\tau_*$-open set is $\tau$-Borel;
together with $\tau\IncludedIn\tau_*$, this gives $\mathcal B(\tau_*)=\mathcal B(\tau)$.

For every $U\in\tau_n$, the construction gives $f_m^{-1}(U)\in\tau_{n+1}\IncludedIn\tau_*$. Since the sets in
$\bigcup_n\tau_n$ generate $\tau_*$ and inverse images commute with unions and finite intersections, each $f_m$
is continuous from $\Pair{X}{\tau_*}$ to itself.
\end{proof}

\begin{example*}[A measurable dynamical system becomes topological]
A \termdefine{Borel automorphism} of a Polish space $X$ is a bijection $T:X\to X$ such that both $T$ and $T^{-1}$
are Borel measurable. It describes an invertible discrete-time evolution, whose orbit through a point is
$$
\ldots,T^{-1}x,x,Tx,T^2x,\ldots.
$$
Apply the lemma to the two maps $T$ and $T^{-1}$. They become continuous for the same finer Polish topology
$\tau_*$, so $T$ is a homeomorphism of $\Pair{X}{\tau_*}$. The points, orbits, and invariant Borel sets have not
changed.

Continuity now allows us to pass to limits in the equations of motion. For $n\ge1$, write $T^n$ for the $n$-fold
iterate and put
$$
P_n:=\{x\in X:T^n x=x\}.
$$
This is the set of points that return after $n$ steps, so their least periods may be proper divisors of $n$.
It is closed in $\tau_*$: the map $x\mapsto\Pair{x}{T^n x}$ is continuous, and the diagonal in
$\Pair{X}{\tau_*}\times\Pair{X}{\tau_*}$ is closed. In particular, the fixed-point set $P_1$ is closed. If a sequence of
points
in $P_n$ converges in the refined topology, its limit still returns after $n$ steps. Thus a Borel evolution admits a
Polish topology in which its update rule is a homeomorphism and its finite-period constraints are closed.
\end{example*}

<!-- formalization: skip-begin (relation to Polish-group actions) -->
The discrete-time example concerns an action generated by one Borel automorphism. The
\termforward{Becker--Kechris theorem} in §{sec:polish-group-continuization} treats Borel actions of Polish groups:
it supplies a Polish topology with the same Borel sets making the action continuous.
That topology need not refine a previously chosen Polish topology;
the construction must take the group topology into account.
<!-- formalization: skip-end -->

<!-- formalization: skip (part boundary) -->
\part{Definability and Classification}\label{part-definability-classification}
