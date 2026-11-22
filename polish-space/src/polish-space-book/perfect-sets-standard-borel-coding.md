# Perfect Sets and Standard Borel Coding {#sec:perfect-sets-standard-borel}

<!-- formalization: skip-begin (chapter motivation and scope) -->
The previous sections organized Polish spaces by open sets, closed trees, Borel ranks, and Borel codes. This chapter
adds two complementary structural tools. \termforwardas{perfect set}{Perfect-set} arguments explain the *geometric size*
of closed sets: every uncountable closed subset of a Polish space contains a homeomorphic copy of Cantor space.
The extension to analytic sets is stated in §{sec:regularity-independence}. Standard Borel coding explains the
*measurable structure* of Polish spaces: once we forget the particular topology and retain only the Borel sets, all
uncountable
Polish spaces become measurably isomorphic.

The same tree picture remains in the background. A \termuse{perfect set} is witnessed by a binary tree of shrinking
neighborhoods, where every split survives to the limit. Standard Borel coding then turns topological objects such as
points, closed sets, and maps into elements of standard Borel parameter spaces.

The arguments in this chapter use only the preceding chapters. We introduce standard Borel spaces by their
definition and the explicit Cantor--Baire isomorphism. The general classification and the Effros--Borel space
of closed sets are developed in §{sec:standard-borel-classification-closed-sets}, after the embedding,
refinement, and Lusin--Suslin tools they require. No use of those later proofs is needed to continue from here
to Cauchy names.

<!-- formalization: skip-end -->

## Perfect Sets {#sec:perfect-sets}

A point $x$ is a \termdefine{limit point} (or *accumulation point*) of $A$ if every neighborhood of $x$ meets
$\SetDifference{A}{\{x\}}$, and a point $x \in A$ is an \termuse{isolated point} of $A$ if some neighborhood of $x$
meets $A$
only at $x$. A subset $A$ of a topological space is \termdefineas{perfect set}{perfect} if it is closed and has no
isolated points — equivalently, $A$ equals its set of limit points. A space is *\termuseas{perfect space}{perfect}* if
it is perfect as a subset of itself.

<!-- formalization: skip-begin (standard perfect-space examples) -->
Examples and non-examples:

*   $\R$, the closed interval $\ClosedInterval{0}{1}$, and the Cantor space $\CantorSpace$ are perfect.

<!-- formalization: skip-end -->

*   $\{0\} \cup \{1/n : n \in \RestrictedSet{\NN}{\ge 1}\} \IncludedIn \R$ is closed but not perfect —
    each $1/n$ is isolated.
*   $\ZZ \IncludedIn \R$ is closed but every point is isolated, so it is not perfect.

<!-- formalization: skip (transition to the main theorems) -->
Two classical theorems govern the perfect subsets of Polish spaces.

## The Cantor–Bendixson Theorem {#sec:cantor-bendixson}
\index{Cantor--Bendixson theorem}
\index{Cantor--Bendixson derivative}

\begin{theorem*}[\termdefineas{Cantor--Bendixson theorem}{Cantor–Bendixson theorem}]
Every closed subset $F$ of a Polish space admits a decomposition
$$F = P \cup S$$
where $P$ is perfect, $S$ is countable, and $P \cap S = \emptyset$. The set $P$ is called the
\termdefine{perfect kernel} of $F$, and $S$ its \termdefine{scattered part}.
This decomposition is unique.
\end{theorem*}

\begin{mathmeta}
  \define{cbderivative}
\end{mathmeta}

\begin{proof}[Proof] For a subset $A$ of a topological space, define the
\emph{\termdefineas{Cantor--Bendixson derivative}{Cantor–Bendixson derivative}} $\cbderivative{A}$ to be the set of
points $x\in A$ such that every open neighborhood of $x$ meets $\SetDifference{A}{\{x\}}$. Thus it is $A$ with
its isolated points removed. Some authors instead define $\cbderivative{A}$ as the set of \emph{all}
limit points of $A$, including those outside $A$; the two definitions coincide when $A$ is closed, which is the only
case used here. In a $T_1$ space, if $A$ is closed then so is $\cbderivative{A}$, and $A$ is perfect precisely when $A =
\cbderivative{A}$.

Iterate by transfinite recursion on ordinals, using intersections at nonzero limit ordinals $\lambda$:
$$\cbderivative[0]{F} = F, \qquad \cbderivative[\alpha+1]{F} = \cbderivative{(\cbderivative[\alpha]{F})}, \qquad
\cbderivative[\lambda]{F} = \bigcap_{\beta < \lambda} \cbderivative[\beta]{F}.$$
Equivalently, all stages are given by the single recursion
$$\cbderivative[\alpha]{F}
= F\cap\bigcap_{\beta<\alpha}\cbderivative{(\cbderivative[\beta]{F})}.$$
At a successor stage, the last derivative factor is contained in all the earlier factors.
At a nonzero limit, every earlier stage has a later predecessor stage contained in its derivative.
These observations give the successor and limit equations above and show that all stages are closed and decreasing.

The chain must stabilize. Otherwise all stages would be distinct, contradicting the fact that the subsets of $F$
form a set: take an ordinal whose cardinality exceeds that of the power set of $F$.
If two stages coincide, the decreasing property forces the intervening successor stage to coincide as well.
There is therefore
a least ordinal $\alpha_0$ with $\cbderivative[\alpha_0+1]{F} = \cbderivative[\alpha_0]{F}$ — the
\termdefineas{Cantor--Bendixson rank}{Cantor–Bendixson rank} of $F$. Second countability of $X$ forces $\alpha_0 <
\omegaOneOrd$. Fix a countable base $\IndexedFamily{B_n}{n\in\NN}$ for the topology of $X$. At every $\alpha <
\alpha_0$, the
successor step is strict:
$\cbderivative[\alpha+1]{F} \StrictlyIncludedIn \cbderivative[\alpha]{F}$. Choose a basic open $B_{n(\alpha)}$ that
meets $\cbderivative[\alpha]{F}$ but not $\cbderivative[\alpha+1]{F}$. The map $\alpha \mapsto n(\alpha)$ is injective
on all $\alpha<\alpha_0$: if $n(\alpha) = n(\beta)$ with $\alpha < \beta$, then $B_{n(\beta)} \cap
\cbderivative[\beta]{F} \IncludedIn B_{n(\alpha)} \cap \cbderivative[\alpha+1]{F} = \emptyset$, contradicting the choice
at $\beta$. Thus $\alpha_0$ has only countably many predecessors, giving $\alpha_0 < \omegaOneOrd$. Set
$$P \;=\; \cbderivative[\alpha_0]{F}, \qquad S \;=\; \SetDifference{F}{P}.$$
Then $P = \cbderivative{P}$, so $P$ is closed and has no isolated points — it is perfect (possibly empty).

\emph{$S$ is countable.} Reusing the countable base $\{B_n\}$ above, observe that for each $x \in S$, since $x \in
\cbderivative[0]{F}$ but $x \notin \cbderivative[\alpha_0]{F}$, there is a smallest ordinal at which $x$ is removed.
This ordinal is necessarily a successor — at a limit $\lambda$, every point surviving all earlier stages also lies in
$\cbderivative[\lambda]{F} = \bigcap_{\beta < \lambda} \cbderivative[\beta]{F}$. So there is a unique $\phi(x)$ with
$$x \in \SetDifference{\cbderivative[\phi(x)]{F}}{\cbderivative[\phi(x)+1]{F}},$$
meaning $x$ is isolated in $\cbderivative[\phi(x)]{F}$. Choose $n(x) \in \NN$ such that $B_{n(x)} \cap
\cbderivative[\phi(x)]{F} = \{x\}$.

The map $x \mapsto n(x)$ from $S$ to $\NN$ is injective: if $n(x) = n(y) = n$ with $\phi(x) \le \phi(y)$ (without loss
of generality), then $y \in \cbderivative[\phi(y)]{F} \IncludedIn \cbderivative[\phi(x)]{F}$ and $y \in B_n$, so $y \in
B_n \cap \cbderivative[\phi(x)]{F} = \{x\}$, forcing $y = x$. Hence $\Card{S} \le \alephNull$.

\emph{Uniqueness.} The constructed $P$ is the largest perfect subset of $F$: if $Q \IncludedIn F$ is perfect, then $Q =
\cbderivative{Q} \IncludedIn \cbderivative{F}$, and inductively $Q \IncludedIn \cbderivative[\alpha]{F}$ for every
ordinal
$\alpha$, so $Q \IncludedIn P$. Conversely, suppose $F = Q \cup R$, where $Q$ is perfect, $R$ is countable, and
$Q\cap R=\emptyset$. We show $P \IncludedIn Q$.
The difference $\SetDifference{P}{Q} \IncludedIn \SetDifference{F}{Q} = R$ is countable. Since $Q$ is closed,
$\SetDifference{P}{Q}$ is open in $P$. Suppose it contains a point $x$.
Choose a closed neighborhood $V$ of $x$ disjoint from $Q$, and let $U$ be the interior of $V$.
Then $U\cap P$ is nonempty and has no isolated points, so
$$C=\Closure{U\cap P}$$
is a nonempty perfect set. Indeed, a point of $C$ outside $U\cap P$ is a limit of points of $U\cap P$, and a
point of $U\cap P$ is not isolated in $U\cap P$ and hence not isolated in $C$; so $C$ is closed with no isolated
points. Moreover,
$$C\IncludedIn V\cap P\IncludedIn\SetDifference{P}{Q}.$$
The perfect set theorem in §{sec:perfect-set-theorem}, proved independently below by the Cantor-scheme
construction, gives a copy of the Cantor space in $C$, contradicting countability.
Hence $\SetDifference{P}{Q} = \emptyset$. Thus $P = Q$ and consequently $S = R$.
\end{proof}

## Perfect Set Theorem and Cardinality Dichotomy {#sec:perfect-set-theorem}

\begin{mathmeta}
  \vars{a}{Name}
  \vars{n,p}{Nat}
  \vars{N}{Nat}
  \vars{s}{Seq}
\end{mathmeta}

\begin{theorem*}[\termdefine{perfect set theorem}] Every nonempty perfect Polish space contains a homeomorphic copy of
the Cantor space $\CantorSpace$.
\end{theorem*}

\begin{proof}[Proof] Let $\Pair{X}{d}$ be a nonempty perfect Polish space, with $d$ complete and compatible. We build a
\termdefine{Cantor scheme} of nonempty open sets $\{U_s : s \in \finseq{2}\}$ satisfying:

\begin{enumerate}
\item $\Closure{U_{s \concat (i)}} \IncludedIn U_s$ for $i \in 2$;
\item $\Closure{U_{s \concat (0)}} \cap \Closure{U_{s \concat (1)}} = \emptyset$;
\item $\MetricDiameter{d}{U_s} \le 2^{-\Length{s}}$.
\end{enumerate}

Start with an open ball $U_\emptyset$ of radius $1/2$ around any point of $X$.
Its closure has diameter at most $1$. Suppose $U_s$ has been chosen.
Since $U_s$ is nonempty open and $X$ has no isolated points, choose distinct points $x_0,x_1 \in U_s$.
Choose $r_0,r_1>0$ with $\Ball{x_i}{r_i}\IncludedIn U_s$ for $i=0,1$, and set
$$\epsilon:=\min\left\{\frac{r_0}{2},\frac{r_1}{2},\frac{d(x_0,x_1)}{3},2^{-(\Length{s}+2)}\right\}>0.$$
The closures of the open balls
$$\Closure{\Ball{x_0}{\epsilon}},\qquad \Closure{\Ball{x_1}{\epsilon}}$$
lie in $U_s$, since $\epsilon<r_i$. They are disjoint, since $2\epsilon<d(x_0,x_1)$.
Each closure has diameter at most $2\epsilon\le 2^{-(\Length{s}+1)}$ by the triangle inequality. Define
$$U_{s \concat (i)} := \Ball{x_i}{\epsilon} \qquad (i=0,1).$$
This completes the induction. In particular, the diameter bound holds for the closures as well.

For each $a \in \CantorSpace$, the closed sets
$$\Closure{U_{\restrict{a}{0}}} \supseteq \Closure{U_{\restrict{a}{1}}} \supseteq \Closure{U_{\restrict{a}{2}}}
\supseteq \cdots$$
are nested, nonempty, and have diameters tending to $0$. Choose $x_n \in \Closure{U_{\restrict{a}{n}}}$.
For $m,n\ge N$, both points belong to $\Closure{U_{\restrict{a}{N}}}$, so
$$d(x_m,x_n)\le 2^{-N}.$$
Thus $\Sequence{x_n}{n\in\omega}$ is Cauchy and converges to some point $h(a) \in X$ by completeness.
Since each $\Closure{U_{\restrict{a}{n}}}$ is closed and eventually contains the tail of the sequence,
$h(a)$ lies in every $\Closure{U_{\restrict{a}{n}}}$. The intersection contains only this one point,
because its diameter is bounded by $2^{-n}$ for every $n$. Thus $h(a)$ is uniquely determined by
$$\{h(a)\}=\bigcap_{n \in \omega} \Closure{U_{\restrict{a}{n}}}.$$

The map $h : \CantorSpace \to X$ is injective. If $a \ne b$, let $n$ be the first coordinate where they differ. Then
$h(a)$ and $h(b)$ lie in the disjoint closed sets $\Closure{U_{\restrict{a}{n+1}}}$ and
$\Closure{U_{\restrict{b}{n+1}}}$.

It is continuous: if $a$ and $b$ agree on the first $n$ coordinates, then $h(a),h(b) \in \Closure{U_{\restrict{a}{n}}}$,
whose diameter is at most $2^{-n}$. Consequently,
$$d(h(a),h(b))\le 2^{-n}.$$
Agreement on a long enough prefix therefore forces the images to be arbitrarily close.

Finally, $h$ is a homeomorphism onto its image. The Cantor space $\CantorSpace$ is compact, and every metric space is
Hausdorff; therefore a continuous injection from $\CantorSpace$ into $X$ is a homeomorphism onto its compact image.
\end{proof}

<!-- formalization: skip-begin (lead-in to the following cardinality dichotomy) -->
Combining the two yields the \termdefine{cardinality dichotomy} for closed subsets of Polish spaces:
<!-- formalization: skip-end -->

*   Every closed subset of a Polish space is either countable or has cardinality exactly $2^{\alephNull}$.

Indeed, an uncountable closed set has a nonempty \termuse{perfect kernel} by the
\termuseas{Cantor--Bendixson theorem}{Cantor–Bendixson theorem}, and the \termuse{perfect set theorem} embeds
$\CantorSpace$ into that kernel. Conversely, the base-indicator map used in
§{sec:kuratowski-isomorphism} injects every Polish space into $\CantorSpace$.

<!-- formalization: skip (ZFC and continuum-hypothesis context; the closed-set dichotomy is the in-scope claim
  above) -->
A subset of a Polish space has the \termdefine{perfect set property} if it is countable or contains a nonempty
perfect subset. The preceding results show that every closed subset of a Polish space has this property. Its extension
to analytic sets is stated in §{sec:regularity-independence}. The cardinality dichotomy is a consequence:
provably in ZFC, no Polish space has cardinality strictly between $\alephNull$ and $2^{\alephNull}$.
This is *not* the full continuum hypothesis, which concerns arbitrary subsets of $\R$ and
is independent of ZFC; rather, it is one of the earliest illustrations of how the Polish hypothesis tames the otherwise
wild cardinal behavior of general topological spaces, and it is a cornerstone of classical descriptive set theory.

### Finite Borel Strictness on Polish Spaces {#sec:finite-borel-strictness-polish}

<!-- formalization: skip-begin (roadmap to the following general-space strictness theorem) -->
The perfect set theorem extends the finite-level strictness proved in §{sec:finite-borel-universal} from sequence
spaces to every uncountable Polish space.
<!-- formalization: skip-end -->

\begin{theorem*}[Finite Borel strictness]
For every uncountable Polish space $X$ and every integer $n\ge1$, the classes $\bSigma^0_n$ and $\bPi^0_n$ of subsets
of $X$ are distinct.
\end{theorem*}

\begin{proof}[Proof]
The Cantor--Bendixson theorem and the perfect set theorem give a closed embedding
$g:\CantorSpace\to X$. Induction on the Borel level shows that every $\bSigma^0_n$ set $A$ in $\CantorSpace$
has the form $A=g^{-1}(B)$ for some $\bSigma^0_n$ set $B$ in $X$, and likewise for $\bPi^0_n$.
At the first level this is the definition of the induced topology. The induction step uses
$$
\begin{aligned}
g^{-1}(\SetDifference{X}{B})&=\SetDifference{\CantorSpace}{g^{-1}(B)},\\
g^{-1}\Bigl(\bigcup_k B_k\Bigr)&=\bigcup_k g^{-1}(B_k).
\end{aligned}
$$
By §{sec:finite-borel-universal}, choose $D\in\bPi^0_n$ in $\CantorSpace$ with $D\notin\bSigma^0_n$.
Lift it to a set $T\in\bPi^0_n$ in $X$ with $g^{-1}(T)=D$. If $T$ belonged to $\bSigma^0_n$, continuity of $g$
would put $D$ in the same class, a contradiction. Thus the two classes on $X$ are distinct.
\end{proof}

## Standard Borel Spaces {#sec:standard-borel-spaces}
\index{standard Borel space}

<!-- formalization: skip (motivation for forgetting the topology and retaining the Borel structure) -->
If we forget the topology and retain only Borel sets, Polish spaces become even more uniform: every uncountable Polish
space has the same measurable structure as the Cantor space.

A bijection between measurable spaces is a \termdefine{Borel isomorphism} if both it and its inverse are
measurable. For topological spaces, we equip each space with its Borel $\sigma$-algebra.

\begin{definition*}
\emph{A measurable space $\Pair{X}{\mathcal B}$ is a \termdefine{standard Borel space} [@Kechris1995,
Def. 12.5] if there exists a Polish topology $\tau$ on $X$ with $\mathcal B(\tau) = \mathcal B$.}

The Polish topology is data used to certify that $\Pair{X}{\mathcal B}$ is standard Borel; it is not part of the data of
$\Pair{X}{
\mathcal B}$ itself, and many different Polish topologies on $X$ can certify the same $\mathcal B$. The refinement
construction in §{sec:polish-topology-refinement} shows how to choose such topologies.

\end{definition*}

### Cantor–Baire Borel isomorphism {#sec:cantor-baire-borel-isomorphism}

\begin{mathmeta}
  \vars{p}{Name}
  \vars{k}{Nat}
  \vars{A}{Set(Nat)}
  \vars{\Phi}{Fun(Set(Nat),Name)}
\end{mathmeta}
\index{Borel isomorphism!Cantor--Baire}

The model example is the Borel equivalence of Cantor space and Baire space. They cannot be homeomorphic: Cantor space is
compact, while Baire space is nowhere locally compact. But they have the same \termdefine{Borel structure}.

Under the identification $\PowerSet{\omega}\cong\CantorSpace$, the \termuse{gap map} from
§{sec:infinite-subsets-omega} identifies the infinite-subset part of Cantor space with Baire space:
$$
\infiniteSubsets{\omega}
\;\xrightarrow{\;\mathrm{gap}\;}\;
\BaireSpace.
$$
The complement
$$
\mathrm{Fin}:=\{A\IncludedIn\omega:\Card{A}<\omega\}
$$
is countable, since each finite subset is determined by its increasing finite enumeration.
Thus Cantor space splits into a large Baire-like $\Gdelta$ piece plus a countable leftover:
$$
\CantorSpace
=
\infiniteSubsets{\omega} \internalDisjointUnion \mathrm{Fin}.
$$

To turn this into an actual Borel bijection $\CantorSpace\cong_B\BaireSpace$, reserve a countably infinite Borel subset
of Baire space, for instance
$$
R:=\{p\in\BaireSpace:\exists N\in\omega\;\forall n\ge N\;p(n)=0\}.
$$
Each element of $R$ is a finite word followed by zeros, so $R$ is countable.
The sequences $\Tuple{k,0,0,\ldots}$ for $k\in\omega$ are distinct elements, so it is countably infinite.
Let $E:=\mathrm{gap}^{-1}(R)\IncludedIn\infiniteSubsets{\omega}$, also countably infinite. Choose a bijection
$$
e:\mathrm{Fin}\internalDisjointUnion E\;\to\;R.
$$
Any such map is Borel, since every subset of a countable subset of a Polish space is Borel.
Define
$$
\Phi(A)=
\begin{cases}
e(A), & A\in \mathrm{Fin}\internalDisjointUnion E,\\
\mathrm{gap}(A), & A\in \SetDifference{\infiniteSubsets{\omega}}{E}.
\end{cases}
$$
Then $\Phi:\CantorSpace\to\BaireSpace$ is bijective, with inverse
$$
\Phi^{-1}(p)=
\begin{cases}
e^{-1}(p), & p\in R,\\
\mathrm{gap}^{-1}(p), & p\notin R.
\end{cases}
$$
The formulas are inverse on each pair of pieces. Both maps are Borel: on the countable pieces every map is Borel,
and on the remaining pieces they are restrictions of the gap homeomorphism and its inverse.

<!-- formalization: skip-begin (lead-in to the following table) -->
At the first nontrivial Borel levels, the pieces line up as follows:
<!-- formalization: skip-end -->

*   The large pieces are $\SetDifference{\infiniteSubsets{\omega}}{E}$ and
    $\SetDifference{\BaireSpace}{R}$. Both are $\Gdelta$ ($\bPi^0_2$): the original large pieces are $\Gdelta$, while
    $E$ and $R$ are countable and hence $\Fsigma$.
*   The countable leftover pieces are $\mathrm{Fin}\internalDisjointUnion E$, an $\Fsigma$ ($\bSigma^0_2$) subset of
    $\CantorSpace$, and $R$, an $\Fsigma$ ($\bSigma^0_2$) subset of $\BaireSpace$.

Thus this particular isomorphism matches the large $\Gdelta$ pieces and the countable $\Fsigma$ pieces. It should not be
read as preserving Borel rank for arbitrary sets.

For every $B\IncludedIn\BaireSpace$, Borelness is preserved in both directions:
$$
B\in\mathcal B(\BaireSpace)
\quad\Longleftrightarrow\quad
\Phi^{-1}(B)\in\mathcal B(\CantorSpace),
$$
and similarly in the other direction. For the displayed implication, if $B$ is Borel in $\BaireSpace$, then
$$
\Phi^{-1}(B)
=
e^{-1}(B\cap R)
\;\cup\;
\mathrm{gap}^{-1}(\SetDifference{B}{R}).
$$
The first term is a subset of the countable set $\mathrm{Fin}\internalDisjointUnion E$, hence Borel in
$\CantorSpace$. The second term is Borel because $\SetDifference{B}{R}$ is Borel and the gap map is continuous on
$\infiniteSubsets{\omega}$, with
$\infiniteSubsets{\omega}$ itself Borel in $\CantorSpace$.

Conversely, if $A\IncludedIn\CantorSpace$ is Borel, then
$$
\Phi(A)
=
e(A\cap(\mathrm{Fin}\internalDisjointUnion E))
\;\cup\;
\mathrm{gap}(A\cap(\SetDifference{\infiniteSubsets{\omega}}{E})).
$$
The first term is countable, hence Borel in $\BaireSpace$. The second term is Borel because
$A\cap(\SetDifference{\infiniteSubsets{\omega}}{E})$ is Borel in the Polish space $\infiniteSubsets{\omega}$, and the
gap map is
a homeomorphism $\infiniteSubsets{\omega}\cong\BaireSpace$. Thus $\Phi$ is an isomorphism of Borel $\sigma$-algebras.

<!-- formalization: skip-begin (contextual warning about topology versus Borel structure) -->
What is preserved here is the generated $\sigma$-algebra, not the topology. Open cylinders in Baire space need not
become open subsets of Cantor space under this particular $\Phi$, and Borel ranks need not be preserved level-by-level
by an arbitrary \termuse{Borel isomorphism}. This is the point of the distinction: the hierarchy records topological
complexity, while standard Borel theory studies only the coarser measurable structure.

<!-- formalization: skip-end -->
